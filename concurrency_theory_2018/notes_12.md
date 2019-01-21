# Weak Memory Models

We are used to think that in a shared memory system, e.g., multicore processors, all the processes see the same memory.
However, due to optimizations both at the software (compiler) and hardware level, this is not true.
The guarantees that are provided by the hardware/software stack is _weaker_ and allows behaviors that would not be possible if the view of the memory was the same for every processes.

These notes are based on the paper [A Load-Buffer Semantics for Total Store Ordering](https://lmcs.episciences.org/4228) by Parosh Aziz Abdulla, Mohamed Faouzi Atig, Ahmed Bouajjani, and Tuan Phong Ngo, 2018.

## Consistency Models

In this lecture we will focus on TSO (roughly what x86 processors can provide).
To give a better understanding of the context, we first give an overview of different memory models.

* **Sequential Consistency (SC)**:
    Read and write operations to the shared memory are instantaneous and visible by all processes.
    This is what most programmers wrongly expect.
    Today, SC is obtained by deactivating all compiler optimization and running the concurrent program on a single CPU by time slicing.
* **Total Store Order (TSO)**:
    Reading takes the current state of the memory but write operations are buffered (one FIFO buffer per processor).
    A processor sees its own write instantaneously but other processors see the write later when the value is taken from the buffer and actually written in memory.
* **Partial Store Order (PSO)**
    Generalize TSO with a memory partitionned in mutliple regions and one write buffer per process per region.
* ...

Visually, these memory model look like:
* SC
    ```graphviz
    digraph SC{
      rankdir=LR
      ranksep=0.75;
      node [shape = square];
      p1 [label="CPU"];
      p2 [label="CPU"];
      m [label="Memory", shape = cylinder];
      p1 -> m [ label = "write"];
      m -> p1 [ label = "read"];
      p2 -> m [ label = "write"];
      m -> p2 [ label = "read"];
    }
    ```
* TSO
    ```graphviz
    digraph TSO{
      rankdir=LR
      ranksep=0.75;
      node [shape = square];
      p1 [label="CPU"];
      p2 [label="CPU"];
      m [label="Memory", shape = cylinder];
      node [shape = box];
      b1 [label="write buffer"];
      b2 [label="write buffer"];
      p1 -> b1 [ label = "write"];
      b1 -> p1 [ label = "read own"];
      b1 -> m [ label = "write"];
      m -> p1 [ label = "read"];
      p2 -> b2 [ label = "write"];
      b2 -> p2 [ label = "read own"];
      b2 -> m [ label = "write"];
      m -> p2 [ label = "read"];
    }
    ```
* PSO
    ```graphviz
    digraph PSO{
      rankdir=LR
      ranksep=0.75;
      node [shape = square];
      p1 [label="CPU"];
      p2 [label="CPU"];
      m1 [label="Memory", shape = cylinder];
      m2 [label="Memory", shape = cylinder];
      node [shape = box];
      b11 [label="write buffer"];
      b21 [label="write buffer"];
      b12 [label="write buffer"];
      b22 [label="write buffer"];
      p1 -> b11 [ label = "write"];
      b11 -> p1 [ label = "read own"];
      b11 -> m1 [ label = "write"];
      m1 -> p1 [ label = "read"];
      p2 -> b21 [ label = "write"];
      b21 -> p2 [ label = "read own"];
      b21 -> m1 [ label = "write"];
      m1 -> p2 [ label = "read"];
      p1 -> b12 [ label = "write"];
      b12 -> p1 [ label = "read own"];
      b12 -> m2 [ label = "write"];
      m2 -> p1 [ label = "read"];
      p2 -> b22 [ label = "write"];
      b22 -> p2 [ label = "read own"];
      b22 -> m2 [ label = "write"];
      m2 -> p2 [ label = "read"];
    }
    ```

## Litmus Tests for Weak Memory Models

__Notations.__
Rather than considering complete programs, we focus on the read and write operations.

Consider the program:
```
x = 1;
print(y);
```
and an execution which prints `0`.
    
We represent this as:
```
write(x, 1);
read(y, 0);
```

$x$, $y$, … are names for shared memory addresses (we don't model local memory).
Different names represent different addresses.

#### Example 1

Consider:
```
initial state:
--------------
    x = 0;
    y = 0;

program A   ∥   program B
------------∥------------
x = 1;      ∥   y = 1;
print(y);   ∥   print(x);
```

The what are the possible output for this program:
* under SC: `A:1, B:1`, `A:1, B:0`, `A:0 B:1`
* under TSO: the SC output and additionally `A:0, B:0`

Let us look in more details at executions:
* For the output `A:1, B:1`, a possible execution is `write_A(x, 1); write_B(y, 1); read_A(y, 1); read_B(x, 1);`
* For the output `A:1, B:0`, a possible execution is `write_A(x, 1); read_A(y, 0); write_B(y, 1); read_B(x, 1);`
* For the output `A:0, B:1`, a possible execution is `write_B(y, 1); read_B(x, 0);  write_A(x, 1); read_A(y, 1);`

However, `A:0, B:0` is not possible under SC.
Let us look at the dependencies between operations:
* For `A`:
  - `write_A(x, 1);` happens before `read_A(y, 0);` (program order)
  - `read_A(y, 0);` happens before `write_B(y, 1);` (otherwise the read would be 1)
* For `B`
  - `write_B(y, 1);` happens before `read_B(x, 0);` (program order)
  - `read_B(x, 0);` happens before `write_A(x, 1);` (otherwise the read would be 1)

Together theses dependencies form a cycle which means no executions can create this output.

However, under TSO the story is different since the written values are buffered and later written.
Let make the step where a write is taken form the buffer put into the memory explicit.
Let us call `update_A(x, 1);` the memory update corresponding to `write_A(x, 1);`.

Then we can get the following execution: `write_A(x, 1); write_B(y, 1); read_A(y, 0); read_B(x, 0); update_A(x, 1); update_B(y, 1);`

#### Memory Fences

The addition of a writer buffer is for performance reason.
Accessing the memory is slow.
While a write is in the buffer, the processor can proceed and execute the following instructions.
Unfortunately, the write buffers can introduce unwanted behaviors in concurrent programs.

Along with the write buffer also comes new instructions which gives back some control to the programmer.
The `fence` instruction block the execution until all the content of the processor write buffer has been written into the memory.


#### Example 1′

Consider:
```
initial state:
--------------
    x = 0;
    y = 0;

program A   ∥   program B
------------∥------------
x = 1;      ∥   y = 1;
fence;      ∥   fence;
print(y);   ∥   print(x);
```

This example behaves the same with SC and TSO.


#### Example 2

Consider:
```
initial state:
--------------
    x = 0;
    y = 0;

program A   ∥   program B
------------∥------------
x = 1;      ∥   print(y);
y = 1;      ∥   print(x);
```

The possible output under SC and TSO are `0 0`, `0 1`, `1 1`.

Under PSO (assuming `x`, `y` are in different memory regions), we can additionally get `1 0`.
Because `x` and `y` are in different memory regions the propagations may happen in different order.


## TSO Model

Let us now define a model for Program executing under TSO semantics.

### Syntax

let $\mathbb{A}$ be a finite set of memory addresses and $\mathbb{D}$ a finite set of state values.

The operations that are program can execute are:
* $nop$ (no operation)
* $read(\mathbb{A}, \mathbb{D})$
* $write(\mathbb{A}, \mathbb{D})$
* $fence$
* $arw(\mathbb{A}, \mathbb{D}, \mathbb{D})$ (atomic-read-write)

The set of operation make the set $\Sigma$.

A program is a NFA $(Q, \Sigma, δ, q_0)$ where
* $Q$ is a finite set of states,
* $\Sigma$ is the set of operations as defined above,
* $δ ∈ Q×\Sigma×Q$ is the transition function
* $q_0$ is the initial state

### Semantics

Let us fix a finite set of processes $\mathbb{P}$.
W.l.o.g. we assume that all the processes are copies of the same program.

The state, or configuration, of a TSO system is a triple $(q,b,m)$ where
* $q: \mathbb{P} → Q$ is the local state of each process,
* $b: \mathbb{P} →  (\mathbb{A}×\mathbb{D})^\*$ gives the content of the write buffers,
* $m: \mathbb{A} → \mathbb{D}$ is the state of the memory.

The initial state is $(q,b,m)$ where $∀ p ∈ \mathbb{P}.~ q[p] = q_0 ∧ b[p] = ε$ and $∀ x ∈ \mathbb{A}.~ m[x] = 0$ where $0 ∈ \mathbb{D}$ is default data value.

The transitions for one process are defined as follow:

* Nop
  \\[{
    t = (q_p, nop, q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p']
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Write
  \\[{
    t = (q_p, write(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b' = b[p ← (x,v)⋅b[p]]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b',m)
  }\\]
* Update
  \\[{
    t = update_p \qquad
    b[p] = w⋅(x,v) \qquad
    b' = b[p ← w] \qquad
    m' = m[x ← v]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q,b',m')
  }\\]
* Read-Own
  \\[{
    t = (q_p, read(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p]|_{\\{x\\}×\mathbb{D}} = (x,v)⋅w
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Read
  \\[{
    t = (q_p, read(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p]|_{\\{x\\}×\mathbb{D}} = ε \qquad
    m[x] = v
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Fence
  \\[{
    t = (q_p, fence, q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p] = ε
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* ARW
  \\[{
    t = (q_p, arw(x, v₁, v₂), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p] = ε \qquad
    m[x] = v₁ \qquad
    m' = m[x ← v₂]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m')
  }\\]

__Remark.__
Notice that since we have a finite set of processes, memory addresses, and range for the data values, the only source of unboundedness in the system is the buffers.

This semantics is quite close to what an hardware implementation.
However, it is not obvious how to analyze.
There has been some intricate reduction to LCS (see this paper: [On the Verification Problem for Weak Memory Models](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/popl175-atig.pdf)).
The idea of using the lossiness is that some write are not observed the same way by the process writing and the other processes.
Therefore, it is a bit like loosing some write.

## Dual TSO (DTSO) Model

Rather than opting for the direct approach, we will use some more recent result which define new semantics ccalled Dual TSO and prove it equivalent to the TSO semantics w.r.t. the control state reachability problem.
DTSO is much simpler to frame as a WSTS than TSO.

DTSO replace the write buffers by read buffers.
An oracle guess the read that will be done in the future by a process and put the values in the read buffer.
To simulate the "Read-Own" the values written by a process are always enqueued in its buffer.
The read buffer are lossy.
A process can get stuck if there is not the appropriate value in the read buffer but this is fine as we only look at control-state reachability, not deadlock.

### Syntax

Same as TSO.

### Semantics

Let us fix a finite set of processes $\mathbb{P}$.
W.l.o.g. we assume that all the processes are copies of the same program.

The state, or configuration, of a TSO system is a triple $(q,b,m)$ where
* $q: \mathbb{P} → Q$ is the local state of each process,
* $b: \mathbb{P} →  (\mathbb{A}×\mathbb{D} ~∪~ \mathbb{A}×\mathbb{D}×\\{own\\})^\*$ gives the content of the read buffers,
* $m: \mathbb{A} → \mathbb{D}$ is the state of the memory.

The transitions for one process are defined as follow:

* Nop
  \\[{
    t = (q_p, nop, q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p']
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Write
  \\[{
    t = (q_p, write(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b' = b[p ← (x,v,own)⋅b[p]] \qquad
    m' = m[x ← v]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b',m')
  }\\]
* Propagate 
  \\[{
    t = update^x_p \qquad
    m[x] = v \qquad
    b' = b[p ← (x,v)⋅b[p]]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q,b',m)
  }\\]
* Delete
  \\[{
    t = delete_p \qquad
    b[p] = w⋅w' \qquad
    |w'| > 0 \qquad
    b' = b[p ← w]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q,b',m)
  }\\]
* Read-Own
  \\[{
    t = (q_p, read(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p]|_{\\{x\\}×\mathbb{D}×\\{own\\}} = (x,v,own)⋅w
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Read
  \\[{
    t = (q_p, read(x,v), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p]|_{\\{x\\}×\mathbb{D}×\\{own\\}} = ε \qquad
    b[p] = w⋅(x,v)
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* Fence
  \\[{
    t = (q_p, fence, q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p] = ε
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m)
  }\\]
* ARW
  \\[{
    t = (q_p, arw(x, v₁, v₂), q_p') \qquad
    q(p) = q_p \qquad
    q' = q[p ← q_p'] \qquad
    b[p] = ε \qquad
    m[x] = v₁ \qquad
    m' = m[x ← v₂]
  }\over{
    (q,b,m)  \stackrel{t}{→}  (q',b,m')
  }\\]

The Nop, Fence, ARW are as before but the other rules have been modified.

__Remark.__
When reading a paper and there are multiple papers on the subject, it is always good to compare them.
Even though peer review is supposed to catch most mistake, there can still be errors.
For instance, compare the "Read from Buffer" rules in the [conference version](http://drops.dagstuhl.de/opus/volltexte/2016/6171/) and the [journal version](https://lmcs.episciences.org/4228) of the paper.



### DTSO as a WSTS

We are interested in the control-state reachability problem, i.e., can a process reach a particular local state.

The transition rules for DTSO include the "Delete" rule, that will form the main part of the lossiness we need to show DTSO make a WSTS.
However, The "Delete" only removes from the head of the buffer and the "Read-Own" reads from the back of the buffer.
Therefore, we cannot just use the normal embedding over word to order the buffer and get compatibility.

One of the advantage of DTSO over TSO is that the we can compare two processes in a configuration just by looking at the memory and their own read buffer.
This will make it possible to consider an unbounded number of processes.

#### Ordering

__Ordering on a Read Buffer.__

Given a strings $w$ in $(\mathbb{A}×\mathbb{D} ~∪~ \mathbb{A}×\mathbb{D}×\\{own\\})^\*$, we can format the string, written $w_{own}$ as
\\[
w_{own} = (w_1, (x_1,v_1,own), w_2, …, w_n, (x_n,v_n,own), w_{n+1})
\\]
with the following conditions:
* $w = w_1⋅(x_1,v_1,own)⋅w_2⋅…⋅w_n⋅(x_n,v_n,own)⋅w_{n+1}$
* $i ≠ j ⇒ x_i ≠ x_j$
* $(x,v,own) ∈ w_i ⇒ ∃ j. j < i ∧ x = x_j$

Intuitively $w_{own}$ identify the most recent own write in the buffer for each variable.

Given two strings $w$ in $(\mathbb{A}×\mathbb{D} ~∪~ \mathbb{A}×\mathbb{D}×\\{own\\})^\*$, we can format the strings as
\\[
w_{own} = (w_1, (x_1,v_1,own), w_2, …, w_n, (x_n,v_n,own), w_{n+1})
\\]

\\[
w_{own}' = (w_1', (x_1',v_1',own), w_2', …, w_m', (x_m',v_m',own), w_{m+1}')
\\]

then $w ⊑ w'$ iff
* $m = n$
* $x_i = x'_i$ and $v_i = v'_i$ for all $i ∈ [1, n]$
* $w_i ≤ w'_i$ for all $i ∈ [1, n]$ where $≤$ is the word embedding

__Ordering on a Single Process.__

Let two configurations $(q,b,m)$ and $(q',b',m')$ and two processes $p$, $p'$.

We say that $p ≤ p'$ if
* $q[p] = q'[p']$
* $b[p] ⊑ b'[p']$
* $m = m'$

__Ordering for a Multiple Processes.__

For two configurations $(q,b,m)$ and $(q',b',m')$ and over two set of processes $\mathbb{P}$ and $\mathbb{P'}$,
$(q,b,m) ≤ (q',b',m')$ iff
* there is an injective function $f$ from $\mathbb{P}$ to $\mathbb{P'}$ such that $∀ p ∈ \mathbb{P}.\ q[p] = q'[f(p)] ∧ b[p] ⊑ b'[f(p)]$
* $m = m'$

__WQO.__

To prove that the ordering is a WQO, we can first observe that
* As $\mathbb{A}$ and $\mathbb{D}$ are finite, the memory $m$ have only a finite number of different possible states
* The ordering on processes is an embedding of finite multiset of well-quasi-ordered elements

Therefore, the only new part is $w ⊑ w'$.

1st observation: $w_{own} = (w_1, (x_1,v_1,own), w_2, …, w_n, (x_n,v_n,own), w_{n+1})$, $n ≤ |\mathbb{A}|$. 

The idea is then to reformat $w_{own}$ as a pair $(~((x_1,v_1,own), …, (x_n,v_n,own)), ~~ (w_1, …, w_{n+1})~)$

2nd observation: $((x_1,v_1,own), …, (x_n,v_n,own))$ comes fomr a finite set because $\mathbb{A}$ and $\mathbb{D}$ are finite and $n ≤ |\mathbb{A}|$.

Therefore, the set of $((x_1,v_1,own), …, (x_n,v_n,own))$ odered by $=$ is a WQO.

This means that the first elements in the pair is a WQO.

When two first elements are equal then we know that the second elements are equally sized tuples of words.
Using Dickson's and Higman's lemmas, we can deduce that $⊑$ is a WQO.

__Compatibility.__

We can reduce the compatibility to checking that $p ≤ p'$ is compatible.
Let us look at the cases from the transition rules:
* Nop, Fence, and ARW are trivial cases as they don't modify the buffers.
* Write and Propagate rely on the fact that $w ⊑ w' ⇒ a⋅w ⊑ a⋅w'$.
* Delete also preseves the ordering.
* Read-Own is monotonic because $⊑$ preserves the most recent write for each variable.
* Read may need to apply some number of Delete as in LCS.
  Notice that because of the usage of Delete before Read we non-strict compatibility.


### Equivalence of TSO and DTSO

Intuitively, both TSO and DTSO allow some read over write reordering.

In the TSO, we get an execution that behave as the SC execution `write; read` with the sequence `write; update; read`.
We can "reorder" and get the SC execution `read; write` with the sequence `write; read; update`.

In the DTSO, we get an execution that behave as the SC execution `write; read` with the sequence `write; propagate; read`.
We can "reorder" and get the SC execution `read; write` with the sequence `propagate; write; read`.

#### Example

If we look back at the
```
initial state:
--------------
    x = 0;
    y = 0;

program A   ∥   program B
------------∥------------
x = 1;      ∥   y = 1;
print(y);   ∥   print(x);
```

DTSO also allows an execution that output `A:0, B:0`:
`propagate_A(y, 0); propagate_B(x, 0); write_A(x, 1); write_B(y, 1); read_A(y, 0); read_B(x, 0);`


#### DTSO to TSO

TODO sketch of equivalence ...

#### TSO to DTSO

TODO sketch of equivalence ...
