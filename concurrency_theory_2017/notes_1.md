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

extra unneeded states: `((0,l))`, `((1,u))`, `((2,u))`, `((3,l))`



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

_Remark._
We can encode datatypes as automaton:
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

http://spinroot.com/spin/whatispin.html

#### Promela

http://spinroot.com/spin/Man/Manual.html

#### Running Spin

https://github.com/tcruys/runspin


### Symmetry Reduction

We will see if enough time during the 2nd lecture…


# Homework

1. Determinize the "1 as the 3rd symbol before the end" NFA
2. 2nd step of the proof of correctness of the determinization
3. Generalize the "lock + program" example to more programs
4. Encode the dining philosopher in Spin (4 philosophers). Show it has a deadlock. What happens to the running time when you increase the number of philosophers?
5. Encode <a href="https://en.wikipedia.org/wiki/Lamport%27s_bakery_algorithm">Lamport's backery algorithm</a> in Spin. Can you prove it safe? (be sure the search depth is enough.)
