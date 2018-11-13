# Homework 4

_Instructions_
* Due *before* November 20 (you can send them until Maonday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf or text format and any other srouce file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).

## Perliminaries: Petri nets with transfer and reset edges

Let us consider two generalizations of Petri Nets:
* _transfer nets_ which have special edges that transfer the tokens from one place to another
* _reset nets_ which have special edges that consume all the tokens in a place

### Definitions

An _Extended Petri Net_ $N$ is a 4-tuple $(S, T, W, R)$ where
* $S$ is a finite set of places
* $T$ is a finite set of transitions
* $W$ is a weight function over $(S × T) ∪ (T × S) → ℕ$
* $R$ is a transfer/reset function over $T → (S ∪ \\{⊥\\}) × (S ∪ \\{⊥\\})$

$⊥$ (bottom) is a dummy element used as placeholder for transition/places which are not connected to any reset/transfer edge.

We categorize the nets according to $R$ as follow:
* If $R(t) = (⊥, ⊥)$ for all $t$ then the net is a normal Petri net.
* If $R(t) = (s, ⊥) ∧ s ≠ ⊥$ then there is a _reset edge_ from $s$ to $t$ and the net is a _reset net_.
* If $R(t) = (s, s') ∧ s ≠ ⊥ ∧ s' ≠ ⊥$ then the transition $t$ is a _transfer edge_ from $s$ to $s'$ and the net is a _transfer net_.

Furthermore, $R$ respects the following:
* $R(t) = (s, s') ∧ s' ≠ ⊥ ⇒ s ≠ ⊥$.
* $R(t) = (s, s') ∧ s ≠ ⊥ ∧ s' ≠ ⊥ ⇒ s ≠ s'$.
* On top of normal edges a net can have either transfer or reset edges but not both.

Let us explain what firing a transition means in the context of extended Petri net.

$t$ is enabled at $M$ iff $∀ s ∈ S.\ M(s) ≥ W(s,t)$.
This is similar to Petri nets.

$M [t〉 M'$ is computed as follow:
1. $t$ must be enabled at $M$
2. create an intermediate marking $M₁$ where $M₁(s) = M(s) - W(s,t)$.
3. assume $R(t) = (s₁,s₂)$ create an intermediate marking $M₂$ to apply the reset/transfer:
  * if $s ≠ s₁ ∧ s ≠ s₂$ then $M₂(s) = M₁(s)$
  * if $s = s₁$ then $M₂(s) = 0$
  * if $s = s₂$ then $M₂(s) = M₁(s) + M₁(s₁)$
4. compute the final marking: $M'(s) = M₂(s) + W(t,s)$.

#### Reset net example

Consider the following reset net where `⥇` represent the reset edge:
```
(∙)       ( )
    ↘   ↗
(:) ⥇ |
```

After firing the transition we get:
```
( )       (∙)
    ↘   ↗
( ) ⥇ |
```

#### Transfer net example

Consider the following transfer net where `⇒` represent the transfer edges:
```
(∙)       ( )
    ↘   ↗
(:) ⇒ | ⇒ (∙)
```

After firing the transition we get:
```
( )       (∙)
    ↘   ↗
( ) ⇒ | ⇒ (⫶)
```

## Exercise: boundedness for transfer and reset nets

In the [lecture notes 3](viewer.html?md=concurrency_theory_2018/notes_3.md), we have seen an algorithm to decide whether a Petri net is bounded or not.
In this exercise, we will try to generalize this algorithm to transfer and reset nets.

The `BoundednessCheck` algorithm relies on the fact that once we have found a sequence of transition which leads to a strictly larger marking, we can repeat this sequence due to that monotonicity of Petri nets.

Assume we have $M [π〉 M'$ with two marking $M$, $M'$ such that $M < M'$ and $π$ a sequence of transitions.
The crux of the algorithm is based on the following observations:
1. Using some linear algebra we can show $M [π^i〉M + i⋅(M'-M)$.
2. Because $M < M'$, $i⋅(M'-M)$ contains at least $i$ tokens.

__Task 1.__
* Under similar assumptions but for a transfer net, give an example to show that $M [π^i〉M + i⋅(M'-M)$ is not true for transfer nets.
* Under similar assumptions but for a rest net, give an example to show that $M [π^i〉M + i⋅(M'-M)$ is not true for rest nets.

__Task 2.__
* Do you think the `BoundednessCheck` is still correct for transfer nets? Justify.
* Do you think the `BoundednessCheck` is still correct for reset nets? Justify.


## Exercise: modified KM tree for Petri nets

Recall an **incorrect** version of the `KarpMillerTree` from [lecture notes 3](viewer.html?md=concurrency_theory_2018/notes_3.md).

```
KarpMillerTreeIncorrect(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        ancestors ← { A | A can reach M in E }
        if ∃ A ∈ ancestors. A = M then
            skip
        else if ∃ A ∈ ancestors. A < M then
            M ← accelerate(A, M) //in-place update (also change M in E)
            F ← F ∪ {M}
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return E
```

The fix that we saw in class consists in accelerating over every smaller ancestors instead of just one.

Let us consider another strategy:

```
KarpMillerTree2(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        ancestors ← { A | A can reach M in E }
        if ∃ A ∈ ancestors. A = M then
            skip
        else if ∃ A ∈ ancestors. A < M then
            E ← removeSuccessor(E, A) //remove any successor of A
            A ← accelerate(A, M) //in-place update (also change A in E)
            F ← F ∪ {A}
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E ← E ∪ { (M,t,M′) }
                F ← F ∪ M′
    return E
```

We say that a marking $M$ is covered by `KarpMillerTree2` if there exists a marking $M'$ in the tree returned by `KarpMillerTree2` such that $M≤M'$.

__Tasks.__
1. Explain what was the problem with `KarpMillerTreeIncorrect` and give an example that shows this problem
2. Does `KarpMillerTree2` fixes this problem? Is does it solve the covering problem for Petri net?
  - If yes, give a proof sketch:
    * Explain why the algorithm terminates.
    * If `KarpMillerTree2` covers a marking $M$ then $(S,T,W,M₀)$ also covers $M$.
    * If a marking $M$ can be covered by $(S,T,W,M₀)$, it is also covered in `KarpMillerTree2`.
  - If no, give a counter example.
