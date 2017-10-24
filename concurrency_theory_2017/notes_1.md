# Finite state machines

## Definitions


#### DFA Example

Words finishing with 1 over the alphabet {0,1}.

```
→ (a)
(a)   −0→ (a)
(a)   −1→ ((b))
((b)) −1→ ((b))
((b)) −0→ (a)
```

_Notation._
* `(a)` is the state `a`.
* `((.))` is an accepting state.
* `−0→` is a transition with label `0`.

#### DFA

A _deterministic finite automaton_ (DFA) `M` is a 5-tuple `(Q, Σ, δ, q₀, F)` where

* `Q` is a finite set of states
* `Σ` is a finite alphabet (set of input symbols)
* `δ` is the transition function (`Q × Σ → Q`)
* `q₀` is the initial state (`q₀ ∈ Q`)
* `F` is the set of accepting states (`F ⊆ Q`)

Let `w = a₁ a₂ … a_n` be a word over the alphabet `Σ`.
The automaton `M` accepts `w` if there is a sequence of states, `r₀ r₁ … r_n`, such that:
* `r₀ = q₀`
* `r_{i+1} = δ(r_i, a_{i+1})` for i = 0, …, n−1
* `r_n ∈ F`


#### NFA Example

Word with 1 as the 3rd symbol before the end

```
→ (a)
(a) −0→ (a)
(a) −1→ (a)
(a) −1→ (b)
(b) −0→ (c)
(b) −1→ (c)
(c) −0→ ((d))
(c) −1→ ((d))
```

#### NFA

A _non-deterministic finite automaton_ (NFA) `M` is a 5-tuple `(Q, Σ, δ, q₀, F)` where

* `Q` is a finite set of states
* `Σ` is a finite alphabet (set of input symbols)
* `δ` is the transition function (`Q × Σ → 2^Q`)
* `q₀` is the initial state (`q₀ ∈ Q`)
* `F` is the set of accepting states (`F ⊆ Q`)

Let `w = a₁ a₂ … a_n` an be a word over the alphabet `Σ`.
The automaton `M` accepts `w` if there is a sequence of states, `r₀ r₁ … r_n`, such that:
* `r₀ = q₀`
* `r_{i+1} ∈ δ(r_i, a_{i+1})` for i = 0, …, n−1
* `r_n ∈ F`

#### Language

The _language_ of an automaton `M`, denoted `L(M)`, is the set of words accepted by `M`.

#### Trace

A _trace_ of an automaton `M` is an alternating sequence `r₀ a₁ r₁ a₂ … a_n r_n` such that
* `r₀ = q₀`
* `r_{i+1} ∈ δ(r_i, a_{i+1})` for i = 0, …, n−1

A trace is _accepting_ if `r_n ∈ F`.


## Operation (Closure properties)

* intersection/union
* complementation
* emptiness/universality

_Remark._
The intersection and union are defined for automata with the same alphabet.
Complementation preserves the alphabet.

_Remark._
Intersection and union are computed with a product construction.
Complementation is easy for DFA but hard for NFA.
Emptiness and universality are solved by minimizing the automaton.


### Synchronized Product

Given automaton `M₁` and `M₂`, the synchronized product `M₁ ⊗ M₂` is the automaton `M` where:

* `Q = Q₁ × Q₂`
* `Σ = Σ₁ ∪ Σ₂`
* `δ` is the transition function
  - `δ((q₁,q₂), a) = (δ₁(q₁, a), δ₂(q₂, a))` if `a ∈ Σ₁` and `a ∈ Σ₂`
  - `δ((q₁,q₂), a) = (q₁, δ₂(q₂, a))` if `a ∉ Σ₁` and `a ∈ Σ₂`
  - `δ((q₁,q₂), a) = (δ₁(q₁, a), q₂))` if `a ∈ Σ₁` and `a ∉ Σ₂`
* `q₀ = (q₀₁,q₀₂)`
* `F = F₁ × F₂`


#### Example

Here the accepting states describe executions allowed by the program/lock.

**NFA representing a lock**

```
→ ((u))
((u)) −lock→ ((l))
((l)) −unlock→ ((u))
```

**Program using a lock**
```
int balance;

void increase(int x) {
    lock();
    balance += x;
    unlock();
}
```

**Control-flow automaton (CFA)**

```
→ ((0))
((0)) −lock→ ((1))
((1)) −balance += x→ ((2))
((2)) −unlock→ ((3))
```

**Synchronized Product**

```
→ ((0,u))
((0,u)) −lock→ ((1,l))
((1,l)) −balance += x→ ((2,l))
((2,l)) −unlock→ ((3,u))
```

This is the _lazy_ construction that only constructs state if needed.
The full construction would generate extra states: `((0,l))`, `((1,u))`, `((2,u))`, `((3,l))`.



### Determinization (Powerset construction)

_Assuming no ε-transitions_

Given a NFA `N` we construct a DFA `D` with:

* `Q_D = 2^{Q_N}`
* `Σ_D = Σ_N`
* `δ_D(q_D, a) = { q′ | ∃ q ∈ q_D. δ_N(q, a) = q′ }`
* `q₀_D = { q₀_N }`
* `F_D = { q | q ∩ F_N ≠ ∅ }`

__Theorem.__ `L(N) = L(D)`

_Proof._

In two steps:
1. `w ∈ L(N) ⇒ w ∈ L(D)`
2. `w ∈ L(D) ⇒ w ∈ L(N)`

(1)
* Let `t_N` be an accepting trace of `N` for `w`. `t` exists be definition of `L(N)`.
* Let `t_D` by the trace of `w` on `D`.
  We show that `t_D` "contains" `t_N` by induction on the traces:
  - 0: `q₀ ∈  { q₀ } = q₀_D`,
  - i → i+1:
    + by induction hypothesis: `r_i ∈ r_i_D`
    + by definition of `t_N` and `δ_D`: `r_{i+1} ∈ δ_N(r_i, a_i)` and, therefore, `r_{i+1} ∈ r_{i+1}_D`.
* By hypothesis, the last state of `t_N`: `q_n ∈ F_N`.
  By the above, we have `q_n ∈ q_n_D`.
  Therefore, `q_n_D ∩ F_N ≠ ∅`.
  Thus, `t_D` is accepting.

(2) As homework …

##### Example of Determinization

Let the following NFA:
```
→ (1)
 (1)  −s→ (2),(4)
 (1)  −d→ (5)
 (2)  −s→ (4),((6))
 (2)  −d→ (1),(3),(5)
 (3)  −s→ (2),((6))
 (3)  −d→ (5)
 (4)  −s→ (2)
 (4)  −d→ (1),(5)
 (5)  −s→ (2),(4),((6))
 (5)  −d→ (1),(3)
((6)) −s→ (3),(5)
((6)) −d→ (2)
```
It represents the grid:
```
1 2 3
4 5 6
```
where it is possible to more `s`traight or `d`iagonally.

Determinizing it gives:
```
→ ({1})
 ({1})     −s→ ({2,4})
 ({1})     −d→ ({5})
 ({2,4})   −s→ ({1,3,5})
 ({2,4})   −d→ (({2,4,6}))
 ({5})     −s→ (({2,4,6}))
 ({5})     −d→ ({1,3})
 ({1,3})   −s→ (({2,4,6}))
 ({1,3})   −d→ ({5})
 ({1,3,5}) −s→ (({2,4,6}))
 ({1,3,5}) −d→ ({1,3,5})
(({2,4,6}) −s→ ({1,3,5})
(({2,4,6}))−d→ (({2,4,6}))
```

## Verifying Properties

### Properties

Properties of concurrent systems are broadly divided in two categories:
* _Safety_: properties that are violated by finite traces
* _Liveness_: properties that can only be violated by infinite traces

In this class we focus on _safety_ properties and a few _eventuality_ properties.
General classes of temporal properties (LTL, CTL, μ-calculus, weak/strong fairness, …) are out of scope.

#### Example

* Assertion
* Termination
* Termination within 15 steps
* Deadlock-freedom
* Livelock-freedom


## Verification

As Paths in graphs:
- Safety is reachability: path from the initial state to an error state.
- Eventuality is nested reachability: lasso path with the stem starting at the initial state and the loop does not go to any "progress" state.

As automata construction:
- language inclusion: `A ⊆ B` reduces to `A ∩ ¬B = ∅`, or `A ⊗ ¬B = ∅` if the alphabet are different.
- (co-)Büchi automaton …

#### Example

Using the lock+program above, we can check that the program uses the lock correctly.

First, we complement the lock:
```
→ (u)
(u) −lock→ (l)
(l) −unlock→ (u)
(u) −unlock→ ((err))
(l) −lock→ ((err))
((err)) −lock→ ((err))
((err)) −unlock→ ((err))
```
Then take the product (only reachable states shown):
```
→ (0,u)
(0,u) −lock→ (1,l)
(1,l) −balance += x→ (2,l)
(2,l) −unlock→ (3,u)
```
The automaton is empty.
No accepting state is reachable and, therefore, the program is safe.


### State-space Exploration (Model Checking)

Checking safety properties reduces to an emptiness check, we need to find an accepting path.
Since we negate the property to check, an accepting path is a counterexample!

Basic algorithm for checking safety properties:

```
F = {q₀}    // frontier
V = {}      // visited
while F ≠ ∅  do
    choose s in F
    F ← F ∖ {s}
    if s ∉ V then
        V ← V ∪ {s}
        if ¬safe(d)
            return UNSAFE
        else
            F ← F ∪ δ(s,_)
return SAFE
```

Variations:
* using a queue for F makes a BFS
* using a stack for F makes a DFS
* this is a forward search, it can also do a backward search

#### Encoding data as automaton

We can encode _bounded_ datatypes as finite automaton:
* boolean value `b`
    ```
    → (f)
    (f) −b = true→ (t)
    (f) −b = false→ (f)
    (t) −b = true→ (t)
    (t) −b = false→ (f)
    ```
* integer `i`
    ```
    → (0)
    (0) −i += 1→ (1)
    (0) −i -= 1→ (-1)
    …
    ```

However, this is very expensive.
Programs are exponentially more succinct than automaton.


### The Spin Model-Checker

You can download spin at: http://spinroot.com/

To run spin, I recommend using the following script: https://github.com/tcruys/runspin

#### Promela

You can find more explanation in the [manual](http://spinroot.com/spin/Man/Manual.html) or even [Wikipedia](https://en.wikipedia.org/wiki/Promela).

The input language for Spin is _Promela_ (Process/Protocol Meta Language).

_Primitive Types:_
* `bool`
* `byte` (unsigned: 0 to 255)
* `short` (16-bits signed integer)
* `int` (32-bits signed integer)

It is possible to have arrays.
`bool ready[2] = false;` is an array of size 2 containing boolean values that are initialized to false.

_Statements:_
* assignments: `x = 1;`
* test: `x == 1;` (also `!=`, `<`, `>`, `<=`, `>=`)
* `(condition -> valueTrue : valueFalse)`
* if-blocks
    ```
    if
    :: condition_1 -> body_1
    :: condition_2 -> body_2
    ...
    :: condition_n -> body_n
    :: else -> ...
    fi;
    ```
    If multiple alternatives are enabled, spin will explore all of them.
    `else` is optional.
    `else` is enabled only if no other condition is enabled.
* do-loops
    ```
    do
    :: condition_1 -> body_1
    :: condition_2 -> body_2
    ...
    :: condition_n -> body_n
    :: else -> ...
    od;
    ```
    Like `if` in a `while(true)`.
    The `break` statement is the only way to exit a loop.
* assertions: `assert(condition);`
* atomic blocs:
    ```
    atomic {
        ...
    }
    ```
    executes all the statement in the block as a single step (no interleaving).
* `printf` as in C.
* `skip` doesn't do anything.

`;` and `->` are separators.
In particular, `;` is not needed after the last statement.

Tests are normal statement that executes only when they are true and block otherwise.
`x != 0` simulates `while (x == 0) {}`.

Each statement executes atomically;

_Processes:_
* processes
  ```
  proctype name(args){
      ...
  }
  ```
  Processes are started with `run name(values)`.

  Alternatively it is possible to mark processes as active:
  ```
  active [2] proctype client(){
      ...
  }
  ```
  `[2]` is an optional parameter that starts 2 processes.

  The `_pid` variable is a special integer variable which as unique for each process.
* `init { ... }` block is like the `main` in C but without arguments.
  If there are active processes, `init` is not needed.

##### Examples

```
byte b = 0;
init{
    do
    :: b < 128 -> b = b + 1
    :: else -> break
    od
}
```

```
byte b = 0;
init{
    do
    :: b < 128 -> b = b + 1
    od
}
```

```
byte b = 0;
init{
    do
    :: b < 128 ->
       b = b + 1;
       printf("%d\n", b)
    od
}
```

```
byte b = 0;
init{
    do
    :: b = b + 1
    od
}
```

```
init{
    if
    :: true -> skip
    :: else -> assert(false)
    fi
}
```

```
init{
    if
    :: true -> skip
    :: true -> assert(false)
    fi
}
```

_Peterson's algorithm_


```
bool flag0;
bool flag1;
bool turn;
byte mutex;

active proctype P0() {
    do
    ::  flag0=true;
        turn=0;
        !flag1 || (turn == 1);
        mutex++;
        /* critical section */
        assert(mutex == 1);
        mutex--;
        flag0=false;
    od;
}


active proctype P1() {
    do
    ::  flag1=true;
        turn=1;
        !flag0 || (turn == 0);
        mutex++;
        /* critical section */
        assert(mutex == 1);
        mutex--;
        flag1=false;
    od;
}
```

```
bool flag[2];
bool turn;
byte mutex;

active [2] proctype P()
{
    do
    ::  flag[_pid] = true;
        turn = _pid;
        !flag[1-_pid] || turn == 1-_pid;
        mutex++;
        /* critical section */
        assert(mutex == 1);
        mutex--;
        flag[_pid] = false
    od;
}
```

