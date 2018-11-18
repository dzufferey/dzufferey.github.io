# Forward Analysis of WSTS

Usually, forward search is more efficient than backward search.
This explains why people are still searching from generic forward algorithm for WSTS.
The Karp-Miller tree was introduced in 1969.
Work on generalizing it is still ongoing.
As it is still not yet fully "figure out", we will focus on understanding what goes wrong when we try to generalize the Karp-Miller tree.


## Labelled TS

Compared to previous week, we are going for a definition of WSTS that includes labeling on the transitions.

A _labeled WSTS_ is a 4 tuple $(S,Σ,→,≤)$ with:
* $S$ is a set of states (can be infinite),
* $Σ$ is a finite set of labels,
* $→ ⊆ S × Σ × S$ is a transition relation,
* $≤$ is a WQO over $S$,
* strong monotonicity respecting labels: $∀ x₁ a x₂ y₁. ∃ y₂. →(x₁, a, x₂) ∧ x₁ ≤ y₁ ⇒ →(y₁, a, y₂) ∧ x₂ ≤ y₂$.

_Notation._
For the transitions, we write $→(x₁, a, x₂)$ or $x₁ \stackrel{a}{→} x₂$ for $(x₁, a, x₂) ∈ →$.

The transition relation generalizes from single labels to words with the following inductive definition:
$
\left\\{
\begin{array}{l}
   x \stackrel{ε}{→} x  \\\\
   x₁ \stackrel{a⋅w}{→} x₂ ⇔ ∃ x'.\ x₁ \stackrel{a}{→} x' ∧ x' \stackrel{w}{→} x₂ 
\end{array}
\right.
$

It is possible to relax the definition of strong monotonicity to the simple monotonicity.
This is not needed unless the system has silent transitions, usually written $τ$.

A labeled WSTS has _strong-strict monotonicity_ is it has strong monotonicity and at the same time: $∀ x₁ a x₂ y₁.\ ∃ y₂.\ x₁ \stackrel{a}{→}x₂ ∧ x₁ < y₁ ⇒  y₁ \stackrel{a}{→}y₂ ∧ x₂ < y₂$.

For simplicity, in this documents we write WSTS for labeled WSTS.

## Karp-Miller tree generalization challenge: acceleration may depend on the transitions

Consider the following transfer net with labelled transitions:
```
   2
    ↙ |a ↖
(∙) ⇒ |b ⇒ ( )
    ↘ |c ↗
```

We have:
* $(1,0) \stackrel{b}{→} (0,1) \stackrel{a}{→} (2,0)$
* $(1,0) \stackrel{c}{→} (0,1) \stackrel{a}{→} (2,0)$

From $(1,0)$ to $(2,0)$, "$ba$" and "$ca$" are the same.
However, if we want to iterate these transitions the sequences diverge:
* $(2,0) \stackrel{b}{→} (0,2) \stackrel{a}{→} (2,1) \stackrel{b}{→} (0,3) \stackrel{a}{→} (2,2) \stackrel{b}{→} (0,4) \stackrel{a}{→} (2,3) → …$
* $(2,0) \stackrel{c}{→} (1,1) \stackrel{a}{→} (3,0) \stackrel{c}{→} (2,1) \stackrel{a}{→} (4,0) \stackrel{c}{→} (3,1) \stackrel{a}{→} (5,0) → …$


## Karp-Miller tree generalization challenge: finite representation of infinite sets

The backward algorithm works with upward-closed sets which have a finite representation (finite basis).

The Karp-Miller tree works with downward-closed sets.
Unfortunately, downward-closed sets do not have a finite representation unless we add new elements.
In the case of Petri nets, we added "$ω$" as limit element.
This construction can be generalized to general WQO set using _ideals_.

### Manipulating downward-closed sets

A set $S$ is _directed_ iff $∀ x,y ∈ S. ∃ z ∈ S. x ≤ z ∧ y ≤ z$.

A set $S$ is an _ideal_ iff it is downward-closed and directed.

We denote by $Idl(X)$ the set of all ideals in $X$.

As elements can form basis for upward-closed sets, it is possible to decompose downward-closed sets in a finite number of ideals.

__Theorem.__
If $(X,≤)$ is a WQO and $D ⊆ X$ with $D = ↓D$ then $∃ I₀ … I_n ∈ Idl(X). D = I₀ ∪ … ∪ I_n$.

_Proof._
By contradiction, assume that there is no such sequence.
We have two cases:
* It is not possible to decompose $D$ into ideals.
  $⋃_{d ∈ D} ↓d$ is a trivial (but potentially infinite) decomposition into ideals, so this case cannot happen.
* It is only possible to decompose $D$ into an infinite number of ideals ($I₀ I₁ …$).
  - Without loss of generality, assumes that $∀ i,j. i≠j ⇒ I_i ⊈ I_j$.
  - From the sequence of ideals, we can create a sequence of elements $x₀ x₁ …$ such that $∀ i,j.\ x_i ∈ I_i ∧ (i≠j ⇒ x_i ∉ I_j)$.
  - By definition of downward-closed, $∀ i,j. i≠j ⇒ x_i ≰ x_j ∧ x_j ≰ x_i$.
  - Therefore, $x₀ x₁ …$ is an infinite antichain and it contradicts the hypothesis.

While this proof is quite simple it is not constructive, constructive proof are more involved.
See Theorem 3.3 in [Well Behaved Transition Systems](https://arxiv.org/pdf/1608.02636.pdf) for a constructive proof.


### Ideals as limits

We can decompose downward-closed sets into a finite number of ideal, but each ideal can still be an infinite set.
To make it possible to use ideals, we need to give a "finite representation of each ideal".

In the case of Petri nets, we can use $(ℕ ∪ \\{ω\\})^n$ to represent ideals.
For instance, in the Karp-Miller algorithm a generalized marking $(1 ~ 2 ~ ω)$ represents the ideal $↓1 × ↓2 × ℕ$.

To have an efficient representation of downward-closed set, we want to decompose them in maximal ideals:
$$$
\mathit{IdealDecomposition}(D) = \\{ I ~|~ I ∈ Idl(X) ∧ I ⊆ D ∧ (∀ J ∈ Idl(X).\ I≠J ∧ J ⊆ D ⇒ I ⊈ J)\\}$
$$$

By the theorem above, the decomposition exists and must be finite.


## Karp-Miller tree generalization challenge: comparing sets

The Karp-Miller tree compare limits configurations which actually represents ideals, which are sets, not element.
The properties of the WQO only hold when we look at elements.
Let us look at what happens when we compare sets.


### ω²-WQO and BQO

Unfortunately, WQO are not "closed" under infinitary operations, e.g., powerset, infinite trees, lexicographic ordering over strings.

_About the exam:_
The part related to Rado's structure/BQO/ω²-WQO is there to try to explain what goes wrong with WQO only.
You don't need to understand the details of the example contruction.
You only need to understand why we need BQO/ω²-WQO, i.e., we can lift the ordering to ideals and still have a WQO.


#### Ordering on sets

When discussing sets of ordered elements, there are multiple ways to lift the ordering of the elements to the sets.

Unfortunately, the subset relation ($⊆$) does not transfer well to sets of elements because it just check for elements rather than comparing them in the ordering.


__Proposition.__
Let $(X,≤)$ be a WQO with $X$ an infinite set. $(2^X, ⊆)$ is not a WQO.

_Proof._
* Let $x₀ x₁ …$ be an infinite sequence of element from $X$ such that $∀ i j.\ i ≠ i ⇒ x_i ≠ x_j$. Such sequence exists because $X$ is infinite.
* Use that sequence to construct a new sequence of singleton sets $\\{x₀\\} \\{x₁\\} …$. Every set in that sequence contain an element which is not in any other set. Therefore, this sequence is an infinite antichain w.r.t. $⊆$.

Therefore, we need to look for ways of comparing sets and taking the ordering into account.
The first possibility is to look at sets closed under $≤$.


_Notation._
Below we will write normal quantifiers as bounded quantifiers.
Bounded quantifiers are shorthands for
* $(∀ p ∈ P. φ) ⇔ (∀ p. p ∈ P ⇒ φ)$
* $(∃ p ∈ P. φ) ⇔ (∃ p. p ∈ P ∧ φ)$


__Downward-closed sets.__
When we deal with downward-closed sets, the subset ordering ($⊆$) is the most common approach.

When expanding the definitions we get:
* $↓P ⊆ ↓Q$
* $∀ p.\ p ∈ ↓P ⇒ p ∈ ↓Q$                                by definitions of $⊆$
* $∀ p.\ p ∈ ↓P ⇒ ∃ q. q ∈ Q ∧ p ≤ q$                    by definition of $↓$
* $∀ p.\ (∃ p'. p' ∈ P ∧ p ≤ p') ⇒ ∃ q. q ∈ Q ∧ p ≤ q$   by definition of $↓$
* $∀ p.\ ∃ q. p ∈ P ⇒ q ∈ Q ∧ p ≤ q$                     by instantiating $p'$ with $p$
* $∀ p ∈ P.\ ∃ q ∈ Q. p ≤ q$

When we manipulate downward-closed sets as a finite union of ideal, it means that every ideal of $P$ is contained in an ideal of $Q$.
This is good as we can check for inclusion by comparing the basis elements.


__Upward-closed sets.__

The case of upward-closed sets is similar:
* $↑P ⊆ ↑Q$
* $∀ p.\ p ∈ ↑P ⇒ p ∈ ↑Q$                                by definition of $⊆$
* $∀ p.\ p ∈ ↑P ⇒ ∃ q. q ∈ Q ∧ q ≤ p$                    by definition of $↑$
* $∀ p.\ (∃ p'. p' ∈ P ∧ p' ≤ p) ⇒ ∃ q. q ∈ Q ∧ q ≤ p$   by definition of $↑$
* $∀ p.\ ∀ p'. p' ∈ P ∧ p' ≤ p ⇒ ∃ q. q ∈ Q ∧ q ≤ p$
* $∀ p.\ p ∈ P ⇒ ∃ q. q ∈ Q ∧ q ≤ p$                     by case split on $p=p'$ and simplification
* $∀ p ∈ P. ∃ q ∈ Q. q ≤ p$
* $Q ⊑ P$                                                __definition of $⊑$__

This lead to the $⊑$ relation is often found in the literature about ordering on sets.
The $⊑$ applies on any kind of sets, not only upward-closed but on upward-closed sets it matches inclusion.
Notice that the order of $P$ and $Q$ is swapped.


#### Rado structure

Back to the example

Let $X_R = \\{(m, n) ∈ ℕ² ~|~ m < n\\}$.

Visually this space is the region covered by `·` in the plot:
```
⋮ ⋮ ⋮ ⋮ ⋮
3 · · ·
2 · ·
1 ·
0
  0 1 2 3 ⋯
```

Let $(m₀,n₀) ≤_R (m₁,n₁)$ iff $(m₀=m₁ ∧ n₀≤n₁) ∨ n₀<m₁$.

For instance, $↑(1,3)$ corresponds to the element marked by `x`:
```
⋮   ⋮     ⋮ ⋮ ⋮  
7 · x · · x x x  
6 · x · · x x  
5 · x · · x  
4 · x · ·  
3 · x ·  
2 · ·
1 ·
0
  0 1 2 3 4 5 6 ⋯
```

__Proposition.__
$(X_R, ≤_R)$ is a WQO.

_Proof._
* By contradiction, assume a bad sequence $(a₀,b₀) (a₁,b₁) …$
* By definition of $≤_R$ and bad sequence: $∀ j>0.\ a_j ≤ b₀$
* Since, we have finitely many values smaller than $b₀$, there is an infinite subsequence $(b,b_{i₀}) (b,b_{i₁}) (b,b_{i₂}) …$ for some $b ≤ b₀$.
* Since $(ℕ,≤)$ is a WQO we have $k<l$ such that $b_{i_k} ≤ b_{i_l}$.
* Therefore, $(b,b_{i_k}) ≤_R (b,b_{i_l})$ which is a contradiction.


Let us look at sets of elements.
In particular, consider the following set $ψ_i = \bigcup_{0≤k<i} ↑(k,i)$.

Visually $ψ₂$ looks like:
```
⋮ ⋮ ⋮   ⋮ ⋮ ⋮ ⋮  
7 x x · x x x x  
6 x x · x x x  
5 x x · x x  
4 x x · x  
3 x x ·  
2 x x
1 ·
0
  0 1 2 3 4 5 6 ⋯
```

Visually $ψ₃$ looks like:
```
⋮ ⋮ ⋮ ⋮   ⋮ ⋮ ⋮  
7 x x x · x x x  
6 x x x · x x  
5 x x x · x  
4 x x x ·  
3 x x x  
2 · ·
1 ·
0
  0 1 2 3 4 5 6 ⋯
```

__Proposition.__
$∀ i j.\ (i,j) ∉ ψ_i$.

_Proof._
* $∀ (k,i).\ (k,i) ∈ ψ_i ⇒ k<i$
* $ψ_i = \bigcup_{0≤k<i} ↑(k,i)$ so we need to show that $∀ k<i.\ (k,i) ≰_R (i,j)$
* By definition of $≤_R$, $∀ k<i.\ ¬( (k=i ∧ i≤j) ∨ i<i )$ which is true.

__Proposition.__
$∀ i j k. j < k ⇒ (i,j) ∉ ψ_k$.

_Proof._
* $ψ_k = \bigcup_{0≤l<k} ↑(l,k)$ so we need to show that $∀ l<k, i<j<k. (l,k) ≰_R (i,j)$
* By definition of $≤_R$, $∀ l<k, i<j<k. ¬ ( (l=i ∧ k≤j) ∨ k<i )$.
* This simplifies to $∀ l<k, i<j<k. ¬ ( (l=i ∧ ⊥) ∨ ⊥ )$ which is true.

__Lemma.__
$ψ₁ ψ₂ …$ is an infinite antichain according to set inclusion ($⊆$).

_Proof._
* Consider $ψ_i$ and $ψ_j$ with $i<j$.
* $ψ_j ⊈ ψ_i$
  - $(i,j) ∈ ψ_j$ because $ψ_j = \bigcup_{0≤k<j} ↑(k,j)$ and $0≤i<j$
  - $(i,j) ∉ ψ_i$ by the proposition above.
* $ψ_i ⊈ ψ_j$
  - $(i-1,i) ∈ ψ_i$ because $ψ_i = \bigcup_{0≤k<i} ↑(k,i)$, $0≤i-1<i$, and $i≥1$
  - $(i-1,i) ∉ ψ_j$ by the proposition above


__Corollary.__
$(2^X,⊆)$ is not a WQO.


For $X,Y ⊆ 2^{X_R}$, let $X ⊑_R Y$ iff $∀ y ∈ Y. ∃ x ∈ X. x ≤_R y$.

__Corollary.__
$(2^X,⊑_R)$ is not a WQO.

_Proof._
* notice that $↑X ⊑_R ↑Y$ implies $↑Y ⊆ ↑X$
* $↑ψ_i = ψ_i$
* Therefore, $ψ₁ ψ₂ …$ is a bad sequence.


More details in [Better is Better than Well: On Efficient Verification of Infinite-State Systems](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.7970).


#### BQO

BQO are a subclass of WQO closed under infinitary operations.

__Theorems.__
* A BQO is a WQO.
* $(X,≤)$ is a BQO then $(X^k,componentwise ordering)$ is a BQO.
* $(X,≤)$ is a BQO then $(X^\*,lexicographic ordering)$ is a BQO.
* $(X,≤)$ is a BQO then $(2^X,⊑)$ is a BQO (powerset).

The definition is quite technical so we are skipping it, but is can easily be found online.


#### ω²-WQO

A WQO is ω²-WQO iff it does not embed Rado structure.

__Theorem.__
If $(X,≤)$ is a ω²-WQO then $(2^X,⊑)$ is a WQO.

__Theorem.__
If $(X,≤)$ is a ω²-WQO then $(Idl(X),⊆)$ is a WQO.

BQO are ω²-WQO.

More details in [A Note on Well Quasi-Orderings for Powersets](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.35.673).


#### Relevance in our context

The algorithm we will see enumerates elements $Idl(X)$ where $X$ is the state-space of a WSTS.
The algorithm relies needs that there is no infinite antichains in $Idl(X)$.


## Completion of WSTS

Given a WSTS $(S,Σ,→,≤)$ where $≤$ is a ω²-WQO, we can define the _completion_ of S as a WSTS $(Idl(S),Σ,⇝,⊆)$ such that
$⇝(I, a, J)  ⇔  J ∈ IdealDecomposition(↓post(I,a))$

The completion defines a new WSTS that operates on the ideals of the original system and lifts the transition relation to these ideals.

### Properties of the completion

Let us relate the completion to the original transition systems and show that the covering is preserved.

First, we want to show that if a state can be covered in the orignial system then the completion can cover it.
It will help us prove the soundness of the algorithm.
This is captured by the following proposition:

__Proposition.__
Let $\mathcal{S} = (S,Σ,→,≤)$ be a WSTS with strong monotonicity and its completion$\mathcal{C} = (Idl(S),Σ,⇝,⊆)$.
$$$
    ∀ x,y ∈ S, w ∈ Σ*, I ∈ Idl(S). →(x,w,y) ∧ x ∈ I  ⇒  ∃ J ∈ Idl(S). y ∈ J ∧ ⇝(I, w, J)
$$$

_Proof._
By induction on $w$
- case $w = ε$: $J=I$
- case $w = a w'$:
  * we have $x →_a x' →_{w'} y$
  * $x' ∈ post_\mathcal{S}(x, a) ⊆ ↓post_\mathcal{S}(x, a)$
  * $↓post_\mathcal{S}(x, a)$ can be decomposed into ideals, one of them containing $x'$. Let call that ideal $I'$.
  * by definition: $⇝(I, a, I')$
  * by the induction hypothesis: $∃ J ∈ Idl(S). ⇝(I', w', J) ∧ y ∈ J$


Second, we show that if the completion can cover a state then the original system can do the same.
This will help prove the completennes of the algorithm, i.e., no spurious counterexample.
This is captured by the following proposition:

__Proposition.__
Let $\mathcal{S} = (S,Σ,→,≤)$ be a WSTS with strong monotonicity and its completion $\mathcal{C} = (Idl(S),Σ,⇝,⊆)$.
$$$
    ∀ I,J ∈ Idl(S),\ w ∈ Σ*.\ ∃ y ∈ S. ⇝(I, w, J) ∧ y ∈ J  ⇒  ∃ x ∈ I. y' ∈ S. →(x, w, y') ∧ y ≤ y'
$$$

_Proof._
By induction on $w$:
- case $w = ε$: $x=y=y'$
- case $w = a w'$:
  * we have $I ⇝_a I' ⇝_{w'} J$
  * by induction hypothesis: $∃ z y'. z ∈ I' ∧ y' ∈ J ∧ y ≤ y'$
  * by definition of $⇝$: $∃ x z'. x ∈ I ∧ z' ∈ I' ∧ →(x, a, z') ∧ z ≤ z'$
  * by strong monotonicity we get $y″$ such that  $→(x, w, y″) ∧ y ≤ y' ≤ y″$


Putting both propositions together, we get the following:

__Theorem.__
Let $\mathcal{S} = (S,Σ,→,≤)$ be a WSTS with strong monotonicity and its completion $ \mathcal{C} = (Idl(S),Σ,⇝,⊆)$.
$$$
    ∀ I ∈ Idl(S), w ∈ Σ*. ↓post_\mathcal{S}(I, w) = ⋃_{J ∈ post_\mathcal{C}(I, w)} J
$$$

_Proof._
Two parts ($⊆$, $⊇$):
- $↓post_\mathcal{S}(I, w) ⊆ \bigcup_{J ∈ post_\mathcal{C}(I, w)} J$
  * pick $y ∈ ↓post_\mathcal{S}(I, w)$
  * by definition, $∃ x y'. x∈I ∧ y≤y'$
  * applying the 1st proposition: there is $J$ such that $↓y' ∈ J$ and $⇝(I, w, J)$
  * Therefore, $y ∈ ↓y' ⊆ J$ and $J ∈ post_\mathcal{C}(I, w)$
- $\bigcup_{J ∈ post_\mathcal{C}(I, w)} J ⊆ ↓post_\mathcal{S}(I, w)$
  * for any $J$ pick $y ∈ J$ and apply the 2nd proposition: we get $x ∈ I$ and $y'$ such that $→(x, w, y') ∧ y ≤ y'$
  * This means $y ∈ ↓post_\mathcal{S}(x, w) ⊆ post_\mathcal{S}(I, w)$


## Karp-Miller tree generalization challenge: acceleration and "length" of traces

Upward-closed sets are represented by their basis which is a set of elements.
When sets grow larger, the basis get smaller.
Because we WQO are well-founded, the bases cannot get forever smaller and we use this fact to prove the termination of the backward algorithm.

The Karp-Miller tree uses acceleration instead.
Let see wherether that works for BQO in general.


### Ordinal number to compare the length of infinite traces

How long is infinite?
Can two (countably) infinite sequences have different length?

Ordinal numbers can give a more fine-grained measure of length for infinite sequences.
$ω$ is the first limit ordinal number, i.e., number without a direct predecessor.

__Remark.__
$ω$ as the first limit ordinal is not the same as $ω$ the limit element in the KM tree.
This is some unfortunate symbol overloading occurring in the literature.

Let us try to understand how ordinal number works.
The easiest way to think about ordinal number (IMO) is to think of them as sequences and addition is concatenation.
Two numbers are equal if it is possible to find a mapping between them that preserve the sequences' orders.

Let us try to understand why (1) $ω = 1 + ω$ and (2) $ω ≠ ω + 1$.

Let us try to visualize this.
We write $o ≈ seq$ to show that the ordinal number $o$ is the "size" of the sequence $seq$.
For (1) the mapping looks like
```
ω     ≈ 1 2 3 4 5 …
        | | | | |
1 + ω ≈ 1 1 2 3 4 …
```

For (2) we get
```
ω     ≈ 1 2 3 4 5 …
        | | | | |
ω + 1 ≈ 1 2 3 4 5 … 1
```
It is not possible to match the last elements while preserving the order.

The multiplication of ordinal number is defined as the Cartesian product of the sequence they represent and the pairs of elements are ordered by a variation of the lexicographic order where the first element is less significant than the second one.

Let us look at the more complicated examples (3) $ω·2 = ω+ω ≠ ω$ and (4) $ω = 2·ω$.

For (3) we have
```
ω   ≈ 1  2  3  4  5  …
      |  |  |  |  |  
ω·2 ≈⎛1⎞⎛2⎞⎛3⎞⎛4⎞⎛5⎞ … ⎛1⎞⎛2⎞⎛3⎞⎛4⎞⎛5⎞ …
     ⎝0⎠⎝0⎠⎝0⎠⎝0⎠⎝0⎠ … ⎝1⎠⎝1⎠⎝1⎠⎝1⎠⎝1⎠ …
```

For (4) we get
```
ω   ≈ 1  2  3  4  5  6  …
      |  |  |  |  |  |
2·ω ≈⎛0⎞⎛1⎞⎛0⎞⎛1⎞⎛0⎞⎛1⎞ …
     ⎝1⎠⎝1⎠⎝2⎠⎝2⎠⎝3⎠⎝3⎠ …
```


### Acceleration

An infinite sequence of ideals $I₀ I₁ I₂ …$ is an _acceleration candidate_ if $I₀ ⊂ I₁ ⊂ I₂ ⊂ …$.

Let $S = (S,Σ,→,≤)$ be a WSTS with completion $C$ and $C$ has strong-strict monotonicity.
Let $w ∈ Σ*$ and $I ∈ Idl(S)$.
The _acceleration_ of $I$ under $w$ is:
```
                ⎧ ⋃_{k∈ℕ} post_C^k(I,w)     if I ⊂ post_C(I,w)
post_C^∞(I,w) = ⎨
                ⎩ I                         otherwise
```

By definition of $post_C^∞$ and $post_C$ ($⇝$), the acceleration of an ideal is also an ideal.

Notice that acceleration only does something on acceleration candidates.
We can try to capture what acceleration by ordering ideals in _acceleration levels_ such that acceleration takes an ascending chain from one level and returns an ideal of the next level.

```
            ⎧ Idl(X)    if n = 0
lvl(X, n) = ⎨
            ⎩ { 𝓘 | 𝓘 = ⋃_{k∈ℕ} I_k where I_k ∈ lvl(X, n-1) and I₀ I₁ I₂ … is an acceleration candidate }   if n > 0
```

#### Example
In the case of generalized markings in Petri net, a level of $n$ means that the marking contains at least n $ω$ elements.

To avoid confusion, we will write $ℕ$ instead of $ω$ for the limit elements in generalized marking.

Let us look at the following Petri net:
```
| → ( )
  ↗
| → ( )
```

1. If we keep on firing the top transition we get the sequence $(0,0) ~ (1,0) ~ (2,0) ~ …$.
   Since the sequence is always strictly increasing it is an acceleration candidate.
   By taking the union of that chain we get $\bigcup_{i∈ℕ} (i,0) = (ℕ,0)$.
   To get $(ℕ,0)$ from $(0,0)$, we traverse a chain of length $ω$.
2. If we continue firing the bottom transition we get the sequence $(ℕ,0) ~ (ℕ,1) ~ (ℕ,2) ~ …$.
   Since the sequence is always strictly increasing it is an acceleration candidate.
   By taking the union of that chain we get $\bigcup_{i∈ℕ} (ℕ,i) = (ℕ,ℕ)$.
   To get $(ℕ,ℕ)$ from $(ℕ,0)$, we traverse a chain of length $ω$.
3. If we keep on firing the bottom transition from the start we get the sequence $(0,0) ~ (1,1) ~ (2,2) ~ …$.
   Since the sequence is always strictly increasing it is an acceleration candidate.
   By taking the union of that chain we get $\bigcup_{i∈ℕ} (i,i) = (ℕ,ℕ)$.
   To get $(ℕ,ℕ)$ from $(0,0)$, we traverse a chain of length $ω$.

Acceleration can make different of amount of progress depending on the transitions.
If we take (1) and (2) it takes $ω⋅2$ steps to saturate the system.
On the other hand, if we follow (3) $ω$ steps is enough.

The goal of acceleration levels is to bound the number of time we need to accelerate.
Intuitively, levels bound the length of the longest strictly increasing chain between any two ideals.
In particular, if $X$ has a finite number of levels that length is less than $ω²$.

In the case of Petri net, the maximum level is directly connected to the number of places.
$d$ places means $d+1$ different levels.


__Proposition.__
Let $S = (X,Σ,→,≤)$ be as WSTS with strong monotonicity and $C$ its completion.
If $C$ is deterministic and has strong-strict monotonicity then
1. $∀ I ∈ Idl(X), w ∈ Σ⁺.\ post_C(I, w) ≠ ∅ ∧ I ∈ lvl(X, n) ⇒ post_C(I, w) ∈ lvl(X, n)$
2. $∀ I ∈ Idl(X), w ∈ Σ⁺.\ I ⊂ post_C(I, w) ∧ I ∈ lvl(X, n) ⇒ post_C^∞(I, w) ∈ lvl(X, n+1)$

The proof can be found in [Forward Analysis for WSTS, Part III: Karp-Miller Trees](https://arxiv.org/abs/1710.07258).

### Ideal Karp-Miller Tree

A _very-WSTS_ $S$ is a WSTS such that:
* $S$ is strongly monotonic
* the completion of $S$ is a deterministic WSTS with strong-strict monotonicity
* $Idl(X)$ has finitely many acceleration levels.

__Computational requirements.__
1. ideals can be effectively manipulated (union, ideal decomposition, membership, inclusion, …)
2. $post_C$ is computable where $C$ is the completion of $S$
3. $post_C^∞$ is computable where $C$ is the completion of $S$

The first two requirements define the class of _completion-post-effective_ WSTS.
The last requirement define the class of _∞-completion-effective_ WSTS.

```
Input: very-WSTS S completion-post-effective and ∞-completion-effective, initial state s₀
Output: the covering set of S

C := the completion of S
I₀ := ↓s₀

initialize a tree T with an unmarked node/root (I₀, 0) //I₀ is an ideal, 0 is the level

while T contains an unmarked node c: (I, n) do
    if c has an ancestor (I', n') s.t. I' = I then mark c
    else
        if c has an ancestor c': (I', n') s.t. I' ⊂ I  ∧  n' = n
            w ← sequence of labels from c' to c
            replace c: (I, n) by (post_C^∞(I, w), n + 1)
        for a ∈ Σ do
            for J ∈ post_C(I, a)
                T := T ∪ ((I,n), a, (J,n))
        mark c
return ⋃_{(I,n) ∈ T} I
```

__Sketch of the correctness of the algorithm.__
* The algorithm terminates because we assume a finite number of acceleration levels.
* The properties of the completion implies it is computing the covering set.
* For any transfinite trace (sequence of transition that contains acceleration) and any state covered by this trace, there is a finite trace that covers the state.

The proof of correctness can be found in [Forward Analysis for WSTS, Part III: Karp-Miller Trees](https://arxiv.org/abs/1710.07258).

This algorithm terminates on "flat" systems, i.e., acceleration only on simple cycles, not nested cycles.
However, the analysis of non-flat systems is still a ongoing subject of research.
Later in this class, we will discuss about lossy channel systems and depth-bounded processes.
For both types of system, we know what the completion is (simple regular expressions, and nested graphs), but both types of systems are not flat.

#### Example

Let us look at the following transfer net:
```
   2
    ↙ |a ↖
(∙) ⇒ |b ⇒ ( )
    ↘ |c ↗
```

Here is the tree shown at each depth

```
((1 0), 0, ✗)
```

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✗)
              └c→ ((0 1), 0, ✗)
```

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✓) −a→ ((2 0), 0, ✗)
              └c→ ((0 1), 0, ✗)
```

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✓) −a→ ((2 0), 0, ✗)
              └c→ ((0 1), 0, ✓) −a→ ((2 0), 0, ✗)
```

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✓) −a→ ((2 ℕ), 1, ✓) ┬a→ ((4 ℕ), 1, ✗)
              │                                   ├b→ ((0 ℕ), 1, ✗)
              │                                   └c→ ((1 ℕ), 1, ✗)
              └c→ ((0 1), 0, ✓) −a→ ((ℕ 0), 1, ✓) ┬b→ ((0 ℕ), 1, ✗)
                                                  └c→ ((ℕ 1), 1, ✗)
```

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✓) −a→ ((2 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✗)
              │                                   │                 ├b→ ((0 ℕ), 2, ✗)
              │                                   │                 └c→ ((ℕ ℕ), 2, ✗)
              │                                   ├b→ ((0 ℕ), 1, ✓) ┬a→ ((1 ℕ), 1, ✗)
              │                                   │                 └b→ ((0 ℕ), 1, ✗)
              │                                   └c→ ((1 ℕ), 1, ✓) ┬a→ ((3 ℕ), 1, ✗)
              │                                                     ├b→ ((0 ℕ), 1, ✗)
              │                                                     └c→ ((0 ℕ), 1, ✗)
              └c→ ((0 1), 0, ✓) −a→ ((ℕ 0), 1, ✓) ┬b→ ((0 ℕ), 1, ✓) ┬a→ ((2 ℕ), 1, ✗)
                                                  │                 └b→ ((0 ℕ), 1, ✗)
                                                  └c→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✗)
                                                                    ├b→ ((0 ℕ), 2, ✗)
                                                                    └c→ ((ℕ ℕ), 2, ✗)
```
...

```
((1 0), 0, ✓) ┬b→ ((0 1), 0, ✓) −a→ ((2 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
              │                                   │                 ├b→ ((0 ℕ), 2, ✓) ┬a→ ((2 ℕ), 2, ✓)
              │                                   │                 │                 └b→ ((0 ℕ), 2, ✓)
              │                                   │                 └c→ ((ℕ ℕ), 2, ✓)
              │                                   ├b→ ((0 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
              │                                   │                 │                 ├b→ ((0 ℕ), 2, ✓)
              │                                   │                 │                 └c→ ((ℕ ℕ), 2, ✓)
              │                                   │                 └b→ ((0 ℕ), 1, ✓)
              │                                   └c→ ((1 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
              │                                                     │                 ├b→ ((0 ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 3, ✓)
              │                                                     │                 │                 └b→ ((0 ℕ), 2, ✓)
              │                                                     │                 └c→ ((ℕ ℕ), 2, ✓)
              │                                                     │b→ ((0 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
              │                                                     │                 │                 ├b→ ((0 ℕ), 2, ✓)
              │                                                     │                 │                 └c→ ((ℕ ℕ), 2, ✓)
              │                                                     │                 └b→ ((0 ℕ), 1, ✓)
              │                                                     └c→ ((0 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
              │                                                                       │                 ├b→ ((0 ℕ), 2, ✓)
              │                                                                       │                 └c→ ((ℕ ℕ), 2, ✓)
              │                                                                       └b→ ((0 ℕ), 1, ✓)
              └c→ ((0 1), 0, ✓) −a→ ((ℕ 0), 1, ✓) ┬b→ ((0 ℕ), 1, ✓) ┬a→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
                                                  │                 │                 ├b→ ((0 ℕ), 2, ✓)
                                                  │                 │                 └c→ ((ℕ ℕ), 2, ✓)
                                                  │                 └b→ ((0 ℕ), 1, ✓)
                                                  └c→ ((ℕ ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 2, ✓)
                                                                    ├b→ ((0 ℕ), 2, ✓) ┬a→ ((ℕ ℕ), 3, ✓)
                                                                    │                 └b→ ((0 ℕ), 2, ✓)
                                                                    └c→ ((ℕ ℕ), 2, ✓)
```
