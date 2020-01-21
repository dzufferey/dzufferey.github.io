# Bulk Synchronous Model

Up until now, we saw models where processes synchronize on some actions (lock, messages) and are independent on the others.
This model comes from the classical von Neumann architecture or SISD (single instruction, single data).
However, this is not an efficient architecture to process large datasets.
When the same program is executed over and over again on different data, a SIMD (single instruction, multiple data) architecture is more efficient.
In this model, the hardware itself takes care of the executing the program efficiently with a high degree of parallelism.
GPUs are (mostly) implementing SIMD architectures.

## Models for SIMD programs

Models for SIMD programs fall under the umbrella of bulk synchrony.
In this class, we will discuss a simplified model based on the paper [The Design and Implementation of a Verification Technique for GPU Kernels](https://www.doc.ic.ac.uk/~afd/homepages/papers/pdfs/2015/TOPLAS.pdf) by Adam Betts, Nathan Chong, Alastair F. Donaldson, Jeroen Ketema, Shaz Qadeer, Paul Thomson, and John Wickerson, 2015.

### Syntax

We consider a model where all the programs $P(N,i)$ executes a single method composed of the following statements:

$\mathit{stmt}$ define the control flow:

$
\begin{array}{lcl}
\mathit{stmt} & ::= & \mathit{basicStmt} \\\\
              &   | & \mathit{stmt}; ~ \mathit{stmt} \\\\
              &   | & if ~ \mathit{localExpr} ~ \mathit{stmt} ~ else ~ \mathit{stmt} \\\\ 
              &   | & while ~ \mathit{localExpr} ~ \mathit{stmt} \\\\
              &   | & barrier
\end{array}
$


The $\mathit{basicStmt}$ are the assignments, read, and write operations:

$
\begin{array}{lcl}
\mathit{basicStmt} & ::= & \mathit{var} ~ := ~ \mathit{localExpr} \\\\
                   & |   & \mathit{var} ~ := ~ shared[\mathit{localExpr}] \\\\
                   & |   & shared[\mathit{localExpr}] ~ := ~ \mathit{localExpr}
\end{array}
$

Every thread has its own local copy of the variables ($\mathit{var}$) but the memory is shared.
We represent the memory as a single infinite array called $shared$.

Finally, the $\mathit{localExpr}$ are values and expressions over values.

$
\begin{array}{lcl}
\mathit{localExpr} & ::= & \mathit{var} \\\\
                   & |   & i \\\\
                   & |   & N \\\\
                   & |   & \mathit{constant} \\\\
                   & |   & \mathit{localExpr} ~ \mathit{op} ~ \mathit{localExpr} \\\\
\mathit{op}        & ::= & + \\\\
                   & |   & - \\\\
                   & |   & * 
\end{array}
$

where $i$ is the local thread identifier, $\mathit{var}$ is a variable identifier, $constant$ are numerical values, and $N$ is the number of threads.


### Semantics (synchronous, delayed visibility)

Before giving the details of the semantics, let us explain some specificities of the model.

#### Lockstep (predicated) executions
    
In a SIMD program, all threads execute together in lockstep.
This means that they follow exactly the same path.
When encountering a branch or loop, the program must execute every path at the same time.
This is achieved through _predicated_ execution.

The hardware has special registers which carries the values of predicate (expression) and the statements only have an effect when the predicate is true.
For instance, in the case of branches, both side are executed and the predicate's value decide which path has its result committed.

For instance, consider the program:
```
x := 0;
y := 0;
if (i < m) {
    x := 1;
} else {
    y := 1;
}
```
What get executed is closer to
```
x := 0;
y := 0;
p := i < m;
p ⇒ x := 1;
¬p ⇒ y := 1;
```
The notation $p ⇒ \mathit{stmt}$ means the effect the statements (writing to a variable/memory) only happens when $p$ is true.

For loops
```
x := i;
while (x > 0) {
    x := x - 1;
}
```
we get something similar:
```
x := i;
p := x > 0;
while (∃ i. i.p) {
    p ⇒ x := x - 1;
    p ⇒ p := x > 0;
}
```
As long as one thread is in the loop, evey thread stays in the loop.

Downside is that for each branch, both path are executed (lot of operations are thrown away) and loop is executed as long as one thread is in the loop.
Therefore, GPUs are more efficient on code which is very regular and has a simple control flow, e.g., matrix multiplication.

__Remark.__
Predicated execution is very similar to the mechanism used for speculative execution.


#### Barrier and data races

Memory accesses also have some limitations.
In particular, a thread should not write or read from a location written by another thread unless a $barrier$ has been executed.
$barrier$ synchronizes the state of the memory accross all threads but between barrier the thread memory accesses must not overlap.

The following program is not correct:
```
if (i > 0) {
    shared[i] := (shared[i-1] + shared[i]) / 2;
}
```
But it should be written as
```
if (i > 0) {
    tmp1 := shared[i-1];
}
barrier;
if (i > 0) {
    tmp2 := shared[i];
    shared[i] := (tmp1 + tmp2) / 2;
}
```

#### Rules

We decompose the transition rules into local rules for the execution of the statements and global rules for the lockstep semantics of all the threads.

We will use $t$ to denote the state a thread.
* $t.l$ means accessing $l$ at thread $t$.
* $t.l ← e$ returns a new state where $l$ has value $e$ and the rest is unchanged.
* $R$, $W$ are special variables to represent the read and written memory locations. They do not occur in the origial program.
* $i$, $N$ can be access but not written.

__Shadow memory.__
To simplify the semantics, each thread keeps a local copy of the global memory.
These copies are synchronized when a barrier occurs.


__Local rules.__

We write $e↓t$ for the evaluation of a $\mathit{localExpr}$ $e$ at thread $t$.

Local rules have a thread state and predicated $\mathit{basicStmt}$ on the left hand side and return a new thread state.

* skip
  \\[{
  ¬t.p
  }\over{
  (t, (p ⇒ \mathit{basicStmt})) → t
  }\\]
* assignment
  \\[{
  t.p \qquad  t' = (t.l ← e↓t)
  }\over{
  (t, (p ⇒ l := e)) → t'
  }\\]
* read
  \\[{
  t.p \qquad  v = e↓t \qquad t' = (t.l ← t.shared[v]) \qquad t″ = (t'.R ← t'.R ∪ v)
  }\over{
  (t, (p ⇒ l := shared[e])) → t″
  }\\]
* write
  \\[{
  t.p \qquad v₁ = e₁↓t \qquad v₂ = e₂↓t \qquad t' = (t.shared[v₁] ← v₂) \qquad t″ = (t'.W ← t'.W ∪ v₁)
  }\over{
  (t, (p ⇒ shared[e₁] := e₂)) → t″
  }\\]

__Synchronization rules.__

Let $T = (t₁, ~…, ~ t_N)$ be the state of all threads and $T[j]$ the $j$th thread in $T$ ($T[j].i = j$).

To check for data race we use the following predicate:

$
race(T) ~~ ⇔ ~~ ∃ k,l.~ k≠l ∧ T[k].W ∩ (T[l].R ∪ T[l].W) ≠ ∅
$

And a function to merge the copies of the shared memory:

$
merge(T)[l] = \\left\\{\begin{array}{ll}
  T[j].shared[l] \qquad &   \text{if} ~ ∃ j.~ l ∈ T[j].W \\\\
  T[0].shared[l]        &   \text{otherwise}
\end{array}\\right.
$


* basic statements
  \\[{
  ∀ j. ~ (T[j], p ⇒ basicStmt) → T'[j]  \qquad  ¬race(T')
  }\over{
  (T, p ⇒ basicStmt) → T'
  }\\]
* date race
  \\[{
  ∀ j. ~ (T[j], p⇒ basicStmt) → T'[j]  \qquad  race(T')
  }\over{
  (T, p ⇒ basicStmt) → error
  }\\]
* barrier skip
  \\[{
  ∀ j. ~ ¬T[j].p
  }\over{
  (T, p ⇒ barrier) → T
  }\\]
* barrier error
  \\[{
  ∃ j, k. ~ T[j].p ∧ ¬T[k].p
  }\over{
  (T, p ⇒ barrier) → error
  }\\]
* barrier sync
  \\[{
  ∀ j. ~ T[j].p \qquad T'[j] = ((T[j].shared ← merge(T)).R ← ∅).W ← ∅
  }\over{
  (T, p ⇒ barrier) → T'
  }\\]

__Control-flow rules.__

Finally, we need a few rules for the control flow.
These rules work on sequences of statements.

We write "$a :: b$" to extract the head of a sequence of statement or extend a sequence.
$::$ is not the same as $;$.
$::$ is for predicated statement and $;$ for statements.
$⇒$ binds more strongly than $::$, i.e.,  "$p ⇒ s :: s$" is "$(p ⇒ s) :: s$".

* basic
  \\[{
  (T, p ⇒ \mathit{basicStmt} :: s) → T'
  }\over{
  (T, p ⇒ \mathit{basicStmt} :: s) → (T', s)
  }\\]
* barrier
  \\[{
  (T, p ⇒ barrier :: s) → T'
  }\over{
  (T, p ⇒ barrier :: s) → (T', s)
  }\\]
* sequence
  \\[{}\over{
  (T, p ⇒ s₁; s₂ :: s) → (T, p⇒ s₁ :: p⇒ s₂ :: s)
  }\\]
* if
  \\[{
  \text{fresh} ~ p₁, p₂
  }\over{
  (T, p ⇒ if ~ c ~ s₁ ~ else ~ s₂ ~::~ s) → (T, p₁ := p ∧ c ~::~ p₂ := p ∧ ¬c ~::~ p₁ ⇒ s₁ ~::~ p₂ ⇒ s₂ ~::~ s)
  }\\]
* while
  \\[{
  \text{fresh} ~ p₁ \qquad ∃ j. T[j].p
  }\over{
  (T, p ⇒ while ~ c ~ b ~::~ s) → (T, p₁ := p ∧ c ~::~ p₁ ⇒ b ~::~ p₁ ⇒ while ~ c ~ b ~::~ s)
  }\\]
  \\[{
  ∀ j. ~ ¬T[j].p
  }\over{
  (T, p ⇒ while ~ c ~ b ~::~ s) → (T, s)
  }\\]
* error
  \\[{
  (T, p ⇒ basicStmt) → error
  }\over{
  (T, p ⇒ basicStmt :: s) → error
  }\\]


## Analysis (Sound but Incomplete)

### Pairwise Properties 

Instead of looking at arbitrary properties, we are going to limit ourselves to check the absence of data race and incorrect barrier.
These are the two properties that cause errors at the level of the semantics.

What is important to notice is that these properties are _pairwise_ properties.
To violate these properties we need only two processes:
- data race: $∃ k,l. ~ k≠l ∧ T[k].W ∩ (T[l].R ∪ T[l].W) ≠ ∅$
- barrier error: $∃ j, k.~ T[j].p ∧ ¬T[k].p$

This will be the crux of the two threads reduction.

### Adversarial abstraction

Until now, nothing prevents the undecidability argument to be adapted to this model.
To simplify the problem, we need to apply some abstraction.
The paper proposes an adversarial abstraction.

The shared state is ignored.
Read operations are replaced nondeterministic assignments.
The intuition is that the properties we look at most often depends on the control-flow and the local variables rather than the data.

The abstraction replace the read and write rules with:
* read
  \\[{
  t.p \qquad  v = e↓t \qquad  t' = (t.l ← v').R ← t.R ∪ v
  }\over{
  (t, (p ⇒ l := shared[e])) → t'
  }\\]
* write
  \\[{
  t.p \qquad  v = e₁↓t \qquad  t' = (t.shared ← shared').W ← t.W ∪ v
  }\over{
  (t, (p ⇒ shared[e₁] := e₂)) → t'
  }\\]

With an adversarial abstraction, the problem become simpler as it is not possible anymore to encode a Turing machine.
The abstraction still contains the traces of the original program.
Therefore, if the abstracted program is correct then the original program is also correct.
However, it is possible that a correct program becomes incorrect with the adversarial abstraction.


[The paper](https://www.doc.ic.ac.uk/~afd/homepages/papers/pdfs/2015/TOPLAS.pdf) also describe a more advanced "equality abstraction".


### Two threads reduction (cut-off bound)

Even though we want to check that a program is correct for any `N`.
We can look at only two threads.
This property that all the bug show up for a finite `N` is called a cut-off bound.
In this case, it is `2`.

Applying the adversarial abstraction _decouples_ the threads.
The read and write of each thread is independent from all the other thread.
Since the properties we are looking at are pairwise we just need to find the two threads which trigger the error.
However, we don't know which one a priori.

The idea is to create a single program which nondeterministically guesses which two threads are causing the error and then executes these two thread in lockstep.
Then, it is possible to use an off-the-shelf [symbolic execution engine](https://en.wikipedia.org/wiki/Symbolic_execution) to check the programs are correct.

Let look at an example inspired from [this code](https://github.com/KhronosGroup/OpenCL-CTS/blob/cl22_trunk/test_conformance/basic/test_barrier.c).
I am taking a bit of freedom with the notation...

```c
sum(global int[] a, int size, global int[] tmp_sum, global int* sum)
{
    tmp_sum[i] := 0;
    for (int k:=i; k < size; k+=N) {
        tmp_sum[i] += a[k];
    }

    //each iteration fold the partial sum in half
    local int n := N; //number of element to process
    for (int k := (n+1)/2; n>1; k := (k+1)/2)
    {
        barrier();
        if (i + k < n)
            tmp_sum[i] += tmp_sum[i + k];
        n := k;
    }

    if (i = 0)
        *sum := tmp_sum[0];
}
```

The first part is to partially instrument for our semantics (read/write, loops):
```c
sum(global int[] a, int size, global int[] tmp_sum, global int* sum)
{
    R := ∅;
    W := ∅;
    tmp_sum[i] := 0;
    W := W ∪ {tmp_sum[i]};
    local int k := i;
    C := k < size;
    while(C){
        tmp_sum[i] += a[k];
        R := R ∪ {a[k], tmp_sum[i]};
        W := W ∪ {tmp_sum[i]};
        k += N;
        C := k < size;
    }

    local int n := N;
    k := (n+1)/2
    C = n > 1;
    while (C) {
        barrier();
        R := ∅;
        W := ∅;
        if (i + k < n) {
            tmp_sum[i] += tmp_sum[i + k];
            R := R ∪ {tmp_sum[i], tmp_sum[i+k]};
            W := W ∪ {tmp_sum[i]};
        }
        n := k;
        k := (k+1)/2;
        C := n > 1;
    }

    if (i = 0) {
        *sum := tmp_sum[0];
        R := R ∪ {tmp_sum[0]};
        W := W ∪ {sum};
    }
}
```

Then we can apply the adversarial abstraction (remove read and write, predicated statements).
To simulate the predicated execution, we use the ternary conditional operator `condition ? true_val : false_val`.
```c
sum(global int[] a, int size, global int[] tmp_sum, global int* sum)
{
    R := ∅;
    W := ∅;
    W := W ∪ {tmp_sum[i]};
    k := i;
    C := k < size;
    while(C){
        R := C ? R ∪ {a[k], tmp_sum[i]} : R;
        W := C ? W ∪ {tmp_sum[i]} : W;
        k := C ? k+N : k;
        C := C ? k < size : C;
    }

    n := N;
    k := (n+1)/2
    C := n > 1;
    while (C) {
        barrier();
        R := C ? ∅ : R;
        W := C ? ∅ : W;
        R := C && (i + k < n) ? R : R ∪ {tmp_sum[i], tmp_sum[i+k]};
        W := C && (i + k < n) ? W : W ∪ {tmp_sum[i]};
        n := C ? k : n;
        k := C ? (k+1)/2 : k;
        C := C ? n > 1 : C;
    }

    R := (i = 0) ? R : R ∪ {tmp_sum[0]};
    W := (i = 0) ? W ∪ {sum};
}
```

Finally, we can do the two threads encoding and finish the instrumentation:
```c
sum(global int[] a, int size, global int[] tmp_sum, global int* sum)
{
    assume(i ≠ j);
    R₁ := ∅;                            R₂ := ∅;
    W₁ := ∅;                            W₂ := ∅;
    W₁ := W₁ ∪ {tmp_sum[i]};            W₂ := W₂ ∪ {tmp_sum[j]};
    assert(tmp_sum[i] ∉ W₂);            assert(tmp_sum[j] ∉ W₁);
    int k₁ := i;                        int k₂ := j;
    C₁ := k₁ < size;                    C₂ := k₂ < size;
    while(C₁ || C₂) {
        R₁ := C₁ ? R₁ ∪ {a[k₁], tmp_sum[i]} : R₁;   R₂ := C₂ ? R₂ ∪ {a[k₂], tmp_sum[j]} : R₂;
        W₁ := C₁ ? W₁ ∪ {tmp_sum[i]} : W₁;          W₂ := C₂ ? W₂ ∪ {tmp_sum[j]} : W₂;
        assert(¬C₁ ∨ tmp_sum[i] ∉ W₂);              assert(¬C₂ ∨ tmp_sum[j] ∉ W₁);
        assert(¬C₁ ∨ a[k₁] ∉ W₂);                   assert(¬C₂ ∨ a[k₂] ∉ W₁);
        k₁ := C₁ ? k₁+N : k₁;                       k₂ := C₂ ? k₂+N : N;
        C₁ := C₁ ? k₁ < size : C₁;                  C₂ := C₂ ? k₂ < size : C₂;
    }


    n₁ := N;                            n₂ := N;
    k₁ := (n₁+1)/2                      k₂ := (n₂+1)/2
    C₁ := n₁ > 1;                       C₂ := n₂ > 1;
    while (C₁ || C₂) {
        assert( C₁ = C₂ );
        R₁ := C₁ ? ∅ : R₁;                                                  R₂ := C₂ ? ∅ : R₂;
        W₁ := C₁ ? ∅ : W₁;                                                  W₂ := C₂ ? ∅ : W₂;
        R₁ := C₁ && (i + k₁ < n₁) ? R₁ ∪ {tmp_sum[i], tmp_sum[i+k₁]} : R₁;  R₂ := C₂ && (i + k₂ < n₂) ? R₂ ∪ {tmp_sum[j], tmp_sum[j+k₂]} : R₂;
        W₁ := C₁ && (i + k₁ < n₁) ? W₁ ∪ {tmp_sum[i]} : W₁;                 W₂ := C₂ && (i + k₂ < n₂) ? W₂ ∪ {tmp_sum[j]} : W₂;
        assert(¬C₁ ∨ tmp_sum[i] ∉ W₂);                                      assert(¬C₂ ∨ tmp_sum[j] ∉ W₁)
        assert(¬C₁ ∨ tmp_sum[i+k₁] ∉ W₂);                                   assert(¬C₂ ∨ tmp_sum[j+k₂] ∉ W₁);
        n₁ := C₁ ? k₁ : n₁;                                                 n₂ := C₂ ? k₂ : n₂;
        k₁ := C₁ ? (k₁+1)/2 : k₁;                                           k₂ := C₂ ? (k₂+1)/2 : k₂;
        C₁ := C₁ ? n₁ > 1 : C₁;                                             C₂ := C₂ ? n₂ > 1 : C₂;
    }

    R₁ := (i = 0) ? R₁ : R₁ ∪ {tmp_sum[0]};     R₂ := (j = 0) ? R₂ : R₂ ∪ {tmp_sum[0]};
    W₁ := (i = 0) ? W₁ ∪ {sum};                 W₂ := (j = 0) ? W₂ ∪ {sum};
    assert(i ≠ 0  ∨  sum ∉ W₂);                 assert(j ≠ 0  ∨  sum ∉ W₁);
}
```
