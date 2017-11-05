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

An invariant is _structural_ iff it is can be be expressed as vector in `I ∈ ℚ^m` and `I^T ∙ C = 0`.

`I` is a vector of coefficients for each place such that the transition `M [〉M′` preserves the number of tokens with `I` as weights: `I^T∙M = I^T∙M′`.

#### Example

Let us consider the lock example:
```
    lock()
    ↗ | ↘
(∙)       ( )
 u  ↖ | ↙  l
   unlock()
```

`I^T = [1 1]` is a structural invariants.
For any reachable `M`, we have `M(u) + M(l) = I^T∙M₀ = 1`.

__Theorem.__
Let `I` be a structural invariants of `N`.
For any reachable marking `M ∈ R(M₀)`, `I^T∙M = I^T∙M₀`.

_Proof._

Let `π` be the trace from `M₀` to `M`, i.e., `M₀ [π〉M`.
We have that `M = M₀ + C∙Parikh(π)`.

Multiplying both sides by `I^T` gives `I^T∙M = I^T∙(M₀ + C∙Parikh(π))`.

Distributing `∙` over `+` gives `I^T∙M = I^T∙M₀ + I^T∙C∙Parikh(π)`.

By definition of `I`, we have `I^T∙C = 0` and, thus, `I^T∙C∙Parikh(π) = 0`.
This simplifies the equation to `I^T∙M = I^T∙M₀`.

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

Consider the folowing net:

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
If a siphon `D` is empty under `M` then for any `M [〉M′` `D` is empty under `M′`.

__Proof.__
By contradiction, assume there is a `t` such that `M [t〉M′` and `D` is marked under `M′`.

By definition of siphon, `t` must consume a token from `D` in `M`.
However, by hypothesis `D` is empty under `M` and, thus, `t` is not enabled which gives a contradiction.

__Corollary.__
If `D` is empty under `M` then `D` is empty under any marking in `R(M)`.

#### Traps

Traps are the dual of siphons.
A marked trap will never become empty.

A _trap_ is a set of places `Q ⊆ S` such that `postset(Q) ⊆ preset(Q)`.

More concretely, every transition that take a token from a trap must also put a token in the trap.

__Theorem.__
If a trap `Q` is marked under `M` then for any `M [〉M′` `Q` is marked under `M′`.

__Proof.__
By contradiction, assume there is a `t` such that `M [t〉M′` and `Q` is empty under `M′`.
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

__Proposition.__
If `M` is a deadlock (no transition is enabled) then `{ s | M(s) = 0 }` is an empty proper siphon. 

__Proposition.__
If every proper siphon of `M` includes an initially marked trap then `M` is deadlock-free.

__Examples.__
Find an empty/marked proper siphon/traps in:

```
(∙) ( )    │    (∙) ( )    │        (∙) ( )           │    (∙) ( )    
 ↓ ⤱ ↓     │     ↓ ⤱ ↓     │         ↓ ⤱ ↓            │     ↓ ⤱ ↓
 −   −     │     −   −     │         −   −            │     −   −
 ↑ ⤩ ↑     │     ↑ ⤩ ↑     │         ↑ ↘ ↑ ↘          │     ↑ ↘ ↑ ↘
( ) ( )    │    (∙) ( )    │    |→  ( ) ( ) ( ) → |   │    (:) ( ) ( ) → |
```


The converse of the propositions above are not true.
Can you find an examples?


## Monotonicity

Until now, we only saw sufficient but not necessary conditions to check properties of Petri nets.
We will now introduce some complete procedure for termination, boundedness, and termination.

#### Ordering on markings

- `N ≥ M` iff `∀ s. N(s) ≥ M(s)`
- `N > M` iff `∀ s. N(s) ≥ M(s) ∧ ∃ s. N(s) > M(s)`

_Observation._
Consider `M [t〉M′` and `N ≥ M`.
`t` is also enabled at `N` and, if we fire `t`, we get `N [t〉N′` with `N′ ≥ M′`.

This is usually represented using the following illustration:
```
∀ M, M′, N.    M  ≤  N
∃ N′.          ↓     ↓
               M′ ≤  N′
```

In the Petri Net case, monotonicity can be stated as:

__Theorem.__
`M [π〉M′  ⇒  (M+N) [π〉(M′+N)`


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
            for each t ∈ T with t enabled at M and M′ such that M [t〉M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return TERMINATING
```

#### Example

TODO ...


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
            for each t ∈ T with t enabled at M and M′ such that M [t〉M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return BOUNDED
```

#### Example

TODO ...


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
        for each t ∈ T with t enabled at M and M′ such that M [t〉M′
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

Claims:
* The Karp-Miller tree is finite.
* The `KarpMillerTree` procedure terminates.
* For any `M`, if there is `M′` in `KarpMillerTree(N)` with `M ≤ M′` then `N` can cover `M`.

#### Example

TODO ...
