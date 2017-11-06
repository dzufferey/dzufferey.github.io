# Petri Nets

You can find more detailed definitions and complete explanations in the [lecture notes by Roland Meyer](https://www.tcs.cs.tu-bs.de/documents/ConcurrencyTheory_WS_20112012/lecture_notes.pdf).
We cover the following parts:
* 1.1 Syntax and Semantics
* 2.1 Marking Equations
* 2.4 Verification by Linear Programming

__Clarification about "safe".__

Unfortunately, the term safe is overloaded in the contex of Petri Net. It can mean:
1. safe = 1-bounded
2. safe as satisfies a safety (reachability) property.

In particular, the part about verification using LP is about the 2nd meaning.


#### Example Petri Net

(A) simple Petri Net with 2 places and 1 transition:
```
(∙) → | → ( )
```

_Notations._
- `( )` represents a place without token and `(∙)` represents a place one token.
  Places can have more than one token: `(:)`, `(⫶)`, ...
- `|` is a transition. Transition can also be written as horizontal bars or squares.
- The arrows between places and transitions indicates how many tokens a transition consumes/produces.
  Transition can consume and produce more than 1 token per place.
  In such cases, the edge is labeled by the number of tokens.

Transition consumes token on their incoming arrows and produce tokens on their outgoing arrow.
In this example, firing the transition produces:
```
( ) → | → (∙)
```

(B) more interesting Petri Net with 2 places and 2 transition:
```
| → (∙) → | → ( )
```
Now we have the choice between two transitions:
```
| → ( ) → | → (∙)
```
or
```
| → (:) → | → ( )
```

## Definitions

### Petri Net Syntax

A _Petri Net_ `N` is a triple `(S, T, W)` where
* `S` is a finite set of places
* `T` is a finite set of transitions
* `W` is a weight function over `(S × T) ∪ (T × S) → ℕ`

A _marking_ of `N` is a function `M: S → ℕ`.

A _marked Petri Net_ is the pair `(N,M₀)` where `N` is a Petri Net and `M₀` is the initial making.
We also write it as `(S, T, W, M₀)`.

In the rest of this document, we assume that `N = (S,T,W,M₀)` is a marked Petri net.

#### Example

The example (A) corresponds to:
* `S = {p, q}` where  `p` is the left place and `q` is the right place
* `T = {t}`
* `W` is
  - `W(p,t) = 1`
  - `W(q,t) = 0`
  - `W(t,p) = 0`
  - `W(t,q) = 1`
* `M₀` is `[p →  1, q → 0]`.


### Petri Net Semantics

A transition `t` in `(S,T,W)` with marking `M` is _enabled_ iff `∀ p ∈ S. M(s) ≥ W(s,t)`.

If no transition is enabled at `M` then it is a _deadlock_.

An enabled transition `t` can _fire_ and produce a new marking `M′`, such that, `∀ p ∈ S. M′(s) = M(s) - W(s,t) + W(t,s)`.

Transitions induce a _firing relation_ which contain triples `(M₁,t,M₂)` iff
- `t` is enabled in `M₁` and
- `M₂` is obtain by firing `t` at `M₁`.
The firing relation is usually written `M₁ [t〉 M₂`.

The set of _reachable markings_ is `R(M₁) = { M₂ | ∃ π ∈ T*. M₁ [π〉 M₂ }`.
We use `R(N)` for `R(M₀)`.

The _reachability graph_ `R(N)` is the graph where
- there is a node for every marking in `R(N)` and
- the edges is the firing relation restricted to `R(N)`.

#### Example

In the example (A), after firing the transition we obtain the new marking `M′ = [p → 0, q → 1]`.
`M′` is a deadlock.
The reachability graph of (A) has two nodes.

In the example (B), the reachability graph is infinite.

#### Example

Let look back at the "lock and increment" example from [the first week](notes_1.md).

1. The corresponding Petri Net is:
  * `S = {u, l, 0, 1, 2, 3}`
  * `T = {lock, unlock, balance += x}`
  * `W`:
    - `W(u, lock) = 1`, `W(0, lock) = 1`, `W(lock, l) = 1`, `W(lock, 1) = 1`,
    - `W(1, balance += x) = 1`, `W(balance += x, 2) = 1`
    - `W(l, unlock) = 1`, `W(2, unlock) = 1`, `W(unlock, u) = 1`, `W(unlock, 3) = 1`,
    - otherwise `0`
  * `M₀ = [u → 1, l → 0, 0 → 1, 1 → 0, 2 → 0, 3 → 0]`
2. We can add more "increment" programs by adding more places and transitions.
  * `S = {u, l, A0, A1, A2, A3, B0, B1, B2, B3}`
  * `T = {A:lock, A:unlock, B:lock, B:unlock, A:balance += x, B:balance += x}`
  * `W`:
    - `W(u, X:lock) = 1`, `W(X0, X:lock) = 1`, `W(X:lock, l) = 1`, `W(X:lock, 1) = 1` for `X ∈ {A,B}`
    - `W(X1, X:balance += x) = 1`, `W(X:balance += x, X2) = 1` for `X ∈ {A,B}`
    - `W(l, X:unlock) = 1`, `W(X2, X:unlock) = 1`, `W(X:unlock, u) = 1`, `W(X:unlock, X:3) = 1` for `X ∈ {A,B}`
    - otherwise `0`
  * `M₀ = [u → 1, A0 → 1, B0 → 1, _ → 0]`
3. Or we can add more "increment" programs by adding more tokens: `M₀(0) = 2` for 2 threads.
4. We can even add many more threads by adding a transition `spawn` with: `M(spawn, 0) = 1`.


## Properties

Between this week and next week we will discuss the following questions:

* _Reachability_: Is a marking `M` reachable? Is there a sequence of transitions `t₁ t₂ … t_n` such that `M₀ [t₁〉 M₁ [t₂〉 M₂ … [t_n〉 M`?
* _Coverability_: Is it possible to cover `M`, i.e., reach a marking `M′` such that `M′ ≥ M`?
* _Boundedness_: Is there a bound `k` such that for all reachable marking `M` and state `s` the number of tokens is bounded by `k` (`M(s) ≤ k`) ?
* _Termination_: Is there an infinite firing sequence starting at `M₀`?

#### Example

_Reachability._
Let us look at mutual exclusion in the Petri Net (1-4).
Mutual exclusion is violated if it is possible to reach a marking in:
1. `{ M | M(2) = 2 }`
2. `{ M | M(A2) + M(B2) = 2 }`
3.  same as (1)
4.  same as (1)

_Coverability._
We can relax the property above to any number more than `1`: `{ M | M(2) > 1 }`.
Coverability is reachability in upward-closed sets.
More on that next week.

_Boundedness._
* (A) is 1-bounded, also called safe, and (B) is unbounded.
* (1) and (2) are safe, (3) is 2-bounded, (4) is unbounded.

Termination.
* (A) terminates
* (B) does not terminate.


### Analysis of Petri Nets using Linear Programming

We will now discuss a _sound but incomplete_ method for the reachability problem.

_Remark._
Given a verification question of the form: "Is program P correct?"
* A _sound_ method returns "yes" _only if_ P is correct.
* A _complete_ method returns "yes" _if_ P is correct.
Sound methods can fail to correctly classify correct programs.
Complete methods can fail to correctly classify incorrect programs.

_Caveat._
Often the question "is a program correct?" is exchanged with "is there a bug?".
This change the meaning of _false positive/negative_.
"Is there a bug?" is the De Facto interpretation:
- _false positive/alarm_: a correct program is marked as incorrect.
- _false negative_: an incorrect program is marked as correct.

### Marking Equations

Let `n = |S|` be the number of places and `m = |T|` be the number of transitions.

If we order the places in `S`.
We can represent states as vector in `ℕ^n`.

We can also represents the transitions as vectors that get added or subtracted from the current vector.
For a given transition `t`, we have:
* Forward vector:
    ```
    W(_, t) = ⌈  W(s₁, t) ⌉
              │     ⫶     │
              ⌊ W(s_n, t) ⌋
    ```
* Backward vector:
    ```
    W(t, _) = ⌈  W(t, s₁) ⌉
              │     ⫶     │
              ⌊ W(t, s_n) ⌋
    ```

Putting the transitions together gives matrices:
* Forward matrix:       `F = (W(_, t₁) … W(_, t_m))`
* Backward matrix:      `B = (W(t₁, _) … W(t_m, _))`
* Connectivity matrix:  `C = B - F`

#### Examples

The connectivity matrix of (A) is

```
⌈ -1 ⌉
⌊  1 ⌋
```

The connectivity matrix of (B) is
```
⌈ -1 1 ⌉
⌊  1 0 ⌋
```

### Co-linear Properties

We can think about reachability/safety properties as function from `ℕ^n → 𝔹` that returns true if the properties hold in a given marking.

A property is _co-linear_ if its violation can be expressed by a linear inequality `A∙M ≥ B`.

#### Example

The reachability and coverability examples above are co-linear.

For instance, we can rewrite `{ M | M(2) > 1 }` as:
```
  u l 0 1 2 3
[ 0 0 0 0 1 0 ] ∙ M ≥ [ 2 ]
```


### LP Verification System

Given a Petri Net `N = (S,T,W,M₀)`, let
`C` be the connectivity matrix,
`A _ ≥ B` a co-linear property, and
`X` is a vector of size `|T|`.

`X` represents the number of time each transition fires.

We can create the following LP program:
```
    Variables:      M, X
    Optimize:       ----
    Subject to:     M ≥ 0
                    X ≥ 0
                    M = M₀ + C∙X
                    A∙M ≥ B
```

__Theorem.__
If the LP system above is infeasible then `N` is safe.

_Proof._

By contradiction, assume the system is infeasible and `N` is unsafe.
If `N` is unsafe, there is a sequence `π` of firing such that `M₀ [π〉M` and `A∙M ≥ B`.
We can take the _Parihk image_ of `π` and obtain a vector `X`.

The Parikh image of `π` counts how many each each transition occurs in the trace.
For instance, the Parikh image of `t₁ t₂ t₁` over `{t₁, t₂, t₃}` returns is `(2 1 0)`.

By definition of `C`, we have that `M = M₀ + C∙X`.
The other conditions of the LP are trivial satisfied and, therefore, it is feasible.
This contradicts our hypothesis.

#### Incompleteness 1: ℕ vs ℚ

For `M` and `X`, we can use rational which makes the check simpler (polynomial time) but less precise or integer which is more precise and also more expensive (NP).

Consider the following Petri Net:
```
    2   2
(:) → | → ( )
```
and the property: `M(q) = 1`.
The LP problem can return `X = [ 0.5 ]` if solving over ℚ.

#### Incompleteness 2: merging forward and backward edges

Consider the following net:
```
    1
( ) ⇄ |
    2
```
It is deadlocked.

However, because the connectivity matrix merges the forward and backward edges, the LP for this net is that same as for the following net:
```
( ) ← |
```
This net is not in a deadlock.

#### Incompleteness 3: reconstructing the transition sequence

The last source of inaccuracy is the fact that the LP find the Parikh image of a trace.
To find a real counterexample, we need to turn the transition counts in a sequence of transition.
This is not always possible.
In some sense, the LP is not checking if transitions are enabled.

Consider:
```
    1   2
( ) → | → ( )
    ↖ | ↙
```
which gives the matrix:
```
⌈ -1  1 ⌉
⌊  2 -1 ⌋
```
Given the objective `M = [0 1]^T`, the LP gives `X = [1 1]^T`.
However, it is not possible to turn `X` into a trace.
No transition is enabled.
