# Petri Nets Continued...

_Notations._
For this part, we assume a Petri Net `N = (S,T,W,M₀)`,
`C` is the connectivity matrix,
`n = |S|`, and
`m = |T|`.

## Structural properties

For the structural properties of Petri nets, you can find more detailed definitions and complete explanations in the [lecture notes by Roland Meyer](https://www.tcs.cs.tu-bs.de/documents/ConcurrencyTheory_WS_20112012/lecture_notes.pdf):
* 2.2 Invariants
* 2.3 Traps and Siphons


### Invariants

An _invariant_ is a predicate which is true for any reachable state of a Petri net.

An invariant must be preserved by all the transitions in the net.
(Assuming every transition fires at least once.)

### Structural invariants

An invariant is _structural_ iff it is can be be expressed as vector in `I ∈ ℚ^n` and `I^T ∙ C = 0`.

`I` is a vector of coefficients for each place such that the transition `M [〉 M′` preserves the number of tokens with `I` as weights: `I^T∙M = I^T∙M′`.

#### Example

Let us consider the lock example:
```
    lock()
    ↗ | ↘
(∙)       ( )
 u  ↖ | ↙  l
   unlock()
```
With
```
C = ⌈ -1  1 ⌉
    ⌊  1 -1 ⌋
```

`I^T = [1 1]` is a structural invariants.
For any reachable `M`, we have `M(u) + M(l) = I^T∙M₀ = 1`.

__Theorem.__
Let `I` be a structural invariants of `N`.
For any reachable marking `M ∈ R(M₀)`, `I^T∙M = I^T∙M₀`.

_Proof._
* Let `π` be the trace from `M₀` to `M`, i.e., `M₀ [π〉M`.
* We have that `M = M₀ + C∙Parikh(π)`.
* Multiplying both sides by `I^T` gives `I^T∙M = I^T∙(M₀ + C∙Parikh(π))`.
* Distributing `∙` over `+` gives `I^T∙M = I^T∙M₀ + I^T∙C∙Parikh(π)`.
* By definition of `I`, we have `I^T∙C = 0` and, thus, `I^T∙C∙Parikh(π) = 0`.
* This simplifies the equation to `I^T∙M = I^T∙M₀`.

__Corollary.__
If `I` is a structural invariant of `N`, `M` a marking of `N`, and `I^T∙M ≠ I^T∙M₀`, then `M` is not reachable.

#### Example

Let consider a sightly simplified version of our running example:
```
     u   l
    (∙) ( )
     ↓ ⤱ ↓
lock −   − unlock
     ↑ ↘ ↑ ↘
|→  ( ) ( ) ( ) → |
     x   c   y         
```

With the ordering on the places be `(u l x c y)`, we have
```
    ⌈ -1  1  0  0 ⌉
    │  1 -1  0  0 │
C = │ -1  0  1  0 │
    │  1 -1  0  0 │
    ⌊  0  1  0 -1 ⌋
```

`I^T = [1 0 0 1 0]` is a structural invariant and we have that `I^T∙M₀ = 1`.

We can use that to conclude that there is at most 1 token in `c` and, therefore, mutual exclusion is preserved.

### Siphons and Traps

Consider the following net:

```
   ↗ | ↘              ↗ | ↘
( )     ( ) → | →  (∙)     ( )
a  ↖ | ↙  b        c  ↖ | ↙  d
```

Can `{a,b}` receive a token?

Can `{c,d}` become empty?

__Auxiliary definitions:__
* The _preset_ of a transition `t` is `preset(t) = { s | W(s,t) ≥ 1 }`.
* The _postset_ of a transition `t` is `postset(t) = { s | W(t,s) ≥ 1 }`.
* The _preset_ of a place `s` is `preset(s) = { t | W(t,s) ≥ 1 }`.
* The _postset_ of a place `s` is `postset(s) = { t | W(s,t) ≥ 1 }`.

The `preset` and `postset` generalize to sets of places/transitions by taking the union.


#### Siphons

A _siphon_ is a set of places `D ⊆ S` such that `preset(D) ⊆ postset(D)`.

More concretely, every transition that put a token in a siphon must also take a token from the siphon.
A siphon that becomes empty stays empty.

We say that a siphon is
* _proper_ iff `D ≠ ∅`,
* _marked_ under `M` iff `∃ s ∈ D. M(s) > 0`, and
* _empty_ iff `∀ s ∈ D. M(s) = 0`.

__Theorem.__
If a siphon `D` is empty under `M` then for any `M [〉 M′` `D` is empty under `M′`.

__Proof.__
* By contradiction, assume there is a `t` such that `M [t〉 M′` and `D` is marked under `M′`.
* By definition of siphon, `t` must consume a token from `D` in `M`.
* However, by hypothesis `D` is empty under `M` and, thus, `t` is not enabled which gives a contradiction.

__Corollary.__
If `D` is empty under `M` then `D` is empty under any marking in `R(M)`.

#### Traps

Traps are the dual of siphons.
A marked trap will never become empty.

A _trap_ is a set of places `Q ⊆ S` such that `postset(Q) ⊆ preset(Q)`.

More concretely, every transition that take a token from a trap must also put a token in the trap.

__Theorem.__
If a trap `Q` is marked under `M` then for any `M [〉 M′` `Q` is marked under `M′`.

__Proof.__
By contradiction, assume there is a `t` such that `M [t〉 M′` and `Q` is empty under `M′`.
Therefore, `t` must have consumed all the token in `Q`.

However, by definition of trap, `t` must also put at least one token in `Q` and, thus, `Q` cannot be empty (contradiction).

__Corollary.__
If `Q` is marked under `M` then `Q` is marked under every marking in `R(M)`.

#### Example

What are the siphons and traps in:
```
     u   l
    (∙) ( )
     ↓ ⤱ ↓
lock −   − unlock
     ↑ ↘ ↑ ↘
|→  ( ) ( ) ( ) → |
     x   c   y         
```

#### Applications of siphons and traps

Siphons can offer a quick check for some reachability question.
For instance, it is not possible to cover a siphon empty under `M₀`.

__0-1 Petri net.__
The following two results are only valid to Petri net where the weights on the edges are either `0` or `1`.

__Proposition.__
If `M` is a deadlock (no transition is enabled) then `{ s | M(s) = 0 }` is an empty proper siphon.

__Proposition.__
If every proper siphon of `M` includes an initially marked trap then `M` is deadlock-free.

__Examples.__
Find an empty/marked proper siphon/traps in:

```
a (∙) ( ) b
   ↓ ⤱ ↓ 
   −   − 
   ↑ ⤩ ↑ 
c ( ) ( ) d
```
* traps & siphons: `{a,b}`, `{c,d}`, `{a,d}`, `{b, c}`, `{a,b,c}`, `{a,b,d}`, `{a,c,d}`, `{b,c,d}`, `{a,b,c,d}`
* marked: `{a,b}`, `{a,d}`, `{a,b,c}`, `{a,b,d}`, `{a,c,d}`,`{a,b,c,d}`
* empty: `{c,d}`, `{b, c}`, `{b,c,d}`

```
  a (∙) ( ) b
     ↓ ⤱ ↓ 
     −   − 
     ↑ ↘ ↑ ↘
| → ( ) ( ) ( ) → |
     c   d   e
```
* marked traps & siphons: `{a,b}`

```
a ( ) ( ) b
   ↓ ⤱ ↓
   −   −
   ↑ ↘ ↑ ↘
  (:) ( ) ( ) → |
   c   d   e
```
* siphons: `{a,b}`, `{c,d,e}`, `{a,b,c,d,e}`
* traps: `{a,b}`
* marked: `{c,d,e}`, `{a,b,c,d,e}`
* empty: `{a,b}`


The converse of the propositions above are not true.
Can you find an examples?

__Free-choice nets.__
A Petri net is _free-choice_ iff `∀ s t. W(s, t) = 1 ⇒ W(preset(t), postset(s)) = 1`.

The following patterns are allowed
```
( ) → |
( ) ↗
```

```
( ) → |
    ↘ |
```

```
( ) → |
    ⤨
( ) → |
```

But this is not allowed
```
( ) → |
    ↘
( ) → |
```

If `N` is a free-choice net, we have the following (Commoner's theorem): `N` is deadlock-free iff every proper siphon of `N` includes an initially marked trap.
The proof can be found in the Chapter 4 of [Free Choice Petri Nets](https://www7.in.tum.de/~esparza/bookfc.html). 


## Monotonicity

Until now, we only saw sufficient but not necessary conditions to check properties of Petri nets.
We will now introduce some complete procedure for termination, boundedness, and termination.

### Ordering on markings

- `N ≥ M` iff `∀ s. N(s) ≥ M(s)`
- `N > M` iff `∀ s. N(s) ≥ M(s) ∧ ∃ s. N(s) > M(s)`

`≥` is not a total order.
For instance, `(0,1)` and `(1,0)` are not comparable.

### Definition of monotonicity

_Observation._
Consider `M [t〉 M′` and `N ≥ M`.
`t` is also enabled at `N` and, if we fire `t`, we get `N [t〉 N′` with `N′ ≥ M′`.

__Theorem.__
`M [t〉M′  ⇒  (M+N) [t〉 (M′+N)`


More abstractly, monotonicity is usually represented using the following illustration:
```
∀ M, M′, N.    M  ≤  N
∃ N′.          ↓     ↓
               M′ ≤  N′
```
Put differently, `≤` is a simulation relation.
Larger states can simulate smaller ones.
By "simulate", we mean can take the same transitions (and maybe even more).



### Finite reachability tree

Algorithm to decide if a Petri net always terminates:

```
TerminationCheck(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        ancestors ← { A | a can reach M in E }
        if ∃ A ∈ ancestors. A ≤ M then
            return NON-TERMINATING
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return TERMINATING
```

#### Example

Consider the following net:
```
   ↗ | ↘                        ↗ | ↘
( )     ( ) ← | ← (∙) → | →  ( )     ( )
   ↖ | ↙                        ↖ | ↙ 
  2
```
We order the state from left to right.
For conciseness, we write vector horizontally.
For instance, the initial state is `(0 0 1 0 0)`.

Let us call the transitions:
* `t₁ = ( 0  1 -1  0  0)`
* `t₂ = ( 2 -1  0  0  0)`
* `t₃ = (-1  1  0  0  0)`
* `t₄ = ( 0  0 -1  1  0)`
* `t₅ = ( 0  0  0 -1  1)`
* `t₆ = ( 0  0  0  1 -1)`

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0) NON-TERMINATING with t₄ (t₅ t₆)*
(0 0 1 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0)
```

#### Claims

* `TerminationCheck` terminates
* When `TerminationCheck` returns `NON-TERMINATING` we can extract extract a lasso-shaped trace where the stem starts from `M₀` and the loop is a non-decreasing cycle.
* When `TerminationCheck` returns `TERMINATING` we can extract a finite tree which contains all the reachable states.

Let us look in more details at the first one:
* If the algorithm does not terminate we have an infinite sequence of markings `𝓜` such that `∀ i, j. i ≤ j ⇒ 𝓜[i] > 𝓜[j] ∨ 𝓜[i] incomparable with 𝓜[j]`.
* This is not possible if
  1. there is no infinite decreasing chain, and
  2. there is no infinite antichain (sequence where all the elements are incomparable).
* In a decreasing chain, at each step at least one of the places must have less token. Since we have a finite number of places and we cannot have negative token, it is not possible to decrease forever.
* In an antichain, all the states are incomparable... This is part of the homework and the solution will be given next week when we discuss WSTS.


### Boundedness

The Petri net are strictly monotonic:
```
∀ M, M′, N.    M  <  N
∃ N′.          ↓     ↓
               M′ <  N′
```
and we can modify the algorithm to decide boundedness.

```
BoundednessCheck(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        ancestors ← { A | a can reach M in E }
        if ∃ A ∈ ancestors. A < M then
            return UNBOUNDED
        else if ∃ A ∈ ancestors. A = M then
            skip
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return BOUNDED
```

#### Example

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0)
(0 0 1 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0) → (1 1 0 0 0) UNBOUNDED with t₁ (t₂ t₃)*
```

#### Claims

* `BoundednessCheck` terminates
* When `BoundednessCheck` returns `UNBOUNDED` we can extract extract a lasso-shaped trace where the stem starts from `M₀` and an increasing cycle.

### Karp-Miller tree

Let us generalize the algorithms above to decide coverability.

We nee to introduce a _limit element_ `ω` that represent an "unbounded" number of tokens.
`ω` has the following properties:
* `ω = ω`, `ω = ω+1`, `ω = ω-1`
* `ω > n` for any finite `n`

We cal also extend markings to _generalized markings_ which are function from `S → ℕ ∪ ω`.


_Acceleration._
Given `M` and `M′` with `M′ > M`, we return `M″` such that:
* `M″(s) = M(s)` if `M(s) = M′(s)`
* `M″(s) = ω` if `M(s) > M′(s)`


```
KarpMillerTree(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
            ancestors ← path between M₀ and M′ in E
            M′ ← accelerate(ancestors, M′)
            E ← E ∪ { (M,M′) }
            if ∀ A ∈ ancestors. A < M′ then
                F ← F ∪ M′
    return E

accelerate(ancestors, M)
    while ∃ A ∈ ancestors. A < M ∧ accelerate(A, M) ≠ M
        M ← accelerate(A, M)
    return M
```

#### Example

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0)
(0 0 1 0 0)                                                         ↗ (ω ω 0 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0) → (ω 1 0 0 0) → (ω ω 0 0 0) → (ω ω 0 0 0)
```

#### Claims

* The Karp-Miller tree is finite.
* The `KarpMillerTree` procedure terminates.
* For any `M`, if there is `M′` in `KarpMillerTree(N)` with `M ≤ M′` then `N` can cover `M`.

#### A bounded and terminating example

```
a (∙) ( ) b
   ↓ ⤱ ↓
   −   −
   ↑ ↘ ↑ ↘
  (:) ( ) ( ) → |
   c   d   e
```

We get the following tree:
```
(1 0 2 0 0) → (0 1 1 1 0) → (1 0 1 0 1) → (0 1 0 1 1) → (1 0 0 0 2) → (1 0 0 0 1) → (1 0 0 0 0)
                                 |             ↓
                                 |        (0 1 0 1 0) → (1 0 0 0 1) → (1 0 0 0 0)
                                 ↓
                            (1 0 1 0 0) → (0 1 0 1 0) → (1 0 0 0 1) → (1 0 0 0 0)
```
