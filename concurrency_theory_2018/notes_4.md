# Well-structured transition systems (WSTS)

## Ordering

### Definitions

__Notation.__
Ordering relations are defined w.r.t. a set of element, e.g., $(X,≤)$ where $X$ is elements ordered by $≤$.
For simplicity, we usually omit $X$.

A _quasiorder_ (QO) $≤$ is binary relation that is
- reflexive:      $∀ x.\ x ≤ x$
- transitive:     $∀ x y z.\ x ≤ y ∧ y ≤ z ⇒ x ≤ z$

A _partial order_ (PO) $≤$ is binary relation that is
- reflexive:      $∀ x.\ x ≤ x$
- transitive:     $∀ x y z.\ x ≤ y ∧ y ≤ z ⇒ x ≤ z$
- antisymmetric:  $∀ x y.\ x ≤ y ∧ y ≤ x ⇒ x = y$

A _linear order_ $≤$ is a binary relation that is
- reflexive:      $∀ x.\ x ≤ x$
- transitive:     $∀ x y z.\ x ≤ y ∧ y ≤ z ⇒ x ≤ z$
- antisymmetric:  $∀ x y.\ x ≤ y ∧ y ≤ x ⇒ x = y$
- total:          $∀ x y.\ x ≤ y ∨ y ≤ x$

__Remarks.__
* Orders are often called ordering relation or simply ordering. (The hyphenation may also change: quasiorder = quasi-odering.)
* Quasiorders are also called preorders.
* Linear orders are also called total orders.

A binary relation $R$ is _well-founded_ over a set $X$ iff $∀ S ⊆ X.\ S ≠ ∅ ⇒ ∃ m ∈ S.\ ∀ s ∈ S.\ ¬R(s, m)$.
($m$ is a minimal element of $S$.)

A _well-quasi-ordering_ (WQO) $≤$ is a binary relation that is a QO such that, for any infinite sequence $x₀~x₁~x₂ …$, there exists indices $i$, $j$ with $i < j$ such that $x_i ≤ x_j$.


#### Examples

* $(ℕ,≤)$ is a WQO and also a linear order.
* $<$ is not an ordering relation.
* $(ℤ,≤)$ is a linear order but not a WQO.
* $(ℚ⁺,≤)$ is a linear order but not a WQO.
* $(ℕ,|)$, where $|$ is "divides", is PO but not a WQO.
* $=$ is a PO.
* $(X,=)$ with $X$ finite is a WQO.
* Adding a finite number of elements to a WQO preserves the WQO as long as the ordering is extended to still be a QO.


### Properties of WQO

__Lemma.__
If $≤$ is a WQO then there is no infinite antichain.
(An antichain is a set of elements which are all incomparable.)

_proof._
* By contradiction, assume $X$ is an infinite antichain.
* Applying the definition of WQO on $X$ gives two elements $x_i$, and $x_j$ with $x_i ≤ x_j$.
* Therefore, $X$ is not an antichain. (Contradiction.)


__Lemma.__
If $≤$ is a WQO then any infinite sequence $x₀ x₁ x₂ …$ contains an infinite increasing subsequence: $x_{i₀} ≤ x_{i₁} ≤ x_{i₂} …$ with $i₀ < i₁ < i₂ …$.

_proof._
* Let $M = \\{ i ~|~ ∀ j > i.\ x_i ≰ x_j \\}$. $M$ is the set of indices of elements which do not have any larger successor in the chain.
* Because $≤$ is a WQO, $M$ is finite.
* Any $x_i$ such that $∀ j ∈ M.\ j < i$ can start an infinite increasing subsequence. (We can always continue the sequence, otherwise the last element's index would be in $M$.)


__Lemma.__
If $≤$ is a WQO over $X$ then $<$ is well-founded over $X$.
($x < y$ means $x ≤ y ∧ y ≰ x$.)

_proof._
* By contradiction, assume $<$ is not well-founded.
* Therefore, there is $S ≠ ∅$ such that $∀ m ∈ S. ∃ s ∈ S. s < m$. (Notice that $S$ must be an infinite set.)
* Let pick an element $s₀ ∈ S$ and construct an infinite descending chain $s₀ > s₁ > s₂ > …$. We can always find a smaller element because $S$ is not well-founded.
* Therefore, $s₀ > s₁ > s₂ > …$ does not contains any $i$ and $j$ with $i < j$ and $s_i ≤ s_j$.
* Beacsue $S ⊆ X$ and $S$ contains $s₀ > s₁ > s₂ > …$, $X$ has an infinite descending chain.
* Therefore, $≤$ is not a WQO. (Contradiction.)


__Lemma.__
Given a QO $≤$, if $<$ is well-founded and $≤$ does not have infinite antichain then $≤$ is a wqo.

_proof._
* By contradiction, assume $≤$ is not a wqo.
* Then there exists an infinite sequence $x₀ x₁ x₂ …$ where $∀ i j. i < j ⇒ x_i ≰ x_j$.
* Let $M = \\{ i ~|~ ∀ j > i.\ x_i ≱ x_j \\}$. $M$ is the set of indices of elements which do not have any smaller successors in the chain.
* Case split on whether $M$ is finite or infinite:
  - If $M$ is infinite then it forms an infinite antichain which contradicts the assumption.
  - If $M$ is finite then there is $k = max(M)$.
    That is the last element in the sequence that doesn't have a smaller successor.
    Let's observe $x_d$, $d > k$.
    There is smaller successor, $x_l$ ($l>d$), $x_l ≤ x_d$.
    From the choice of sequence $x$ (namely, the witness that $≤$ is not a WQO) we also know that $x_d ≰ x_l$.
    These two facts give us (by definition)  $x_l < x_d$.
    Since this holds for any element after $x_k$, we can build an infinite descending subsequence.
    That contradicts the assumption of well-foundedness.


### Building WQO from other WQO

#### Finite tuples

__Dickson's lemma.__
Let $(X,≤)$ be a WQO then $(X^k,≤^k)$, where $k$ is finite and $≤^k$ is the component-wise ordering, is a WQO.

_proof._
By induction on $k$:
* $k = 1$:
  - by assumption $(X¹,≤¹) = (X,≤)$ is a WQO.
* $k → k + 1$:
  1. $≤^{k+1}$ is a QO: omitted for brevity but easy to prove.
  2. let $x^{k+1}₀ x^{k+1}₁ x^{k+1}₂ …$ be an infinite sequence.
    Each element $x^{k+1}$ is of the form $(x^k, x)$.
    We need to find $x^{k+1}_i ≤^{k+1} x^{k+1}_j$.
    - By the infinite increasing subsequence lemma we can find a subsequence $y^{k+1}₀ y^{k+1}₁ y^{k+1}₂ …$ such that $y^{k}₀ ≤^k y^{k}₁ ≤^k y^{k}₂ …$.
    - Since $≤$ is a WQO we can find $y_i ≤ y_j$.
    - Finally, we get $(y^k_i, y_i) ≤^{k+1} (y^k_j, y_j)$.


#### Embeddings of finite sequences

Let $w₁$ and $w₂$ be two finite sequences.
$w₁$ is a _subsequence_ of $w₂$ if it is possible to obtain $w₁$ from by deleting some characters of $w₂$.
More formally, there is an injective mapping $f$ from $[0, |w₂|)$ to $[0, |w₁|)$ such that:
*  $∀ i j.\ i < j ⇒ f(i) < f(j)$
*  $∀ i.\ w₁[i] = w₂[f(i)]$

For instance:
* $0110$ is a subsequence of $01010101$ with the following mapping: $(0→0), (1→1), (2→3), (3→6)$.
* $0110$ is not a subsequence of $10100$.

We can generalize the subsequence relation to _embedding_ by relaxing the second condition to $≤$ instead of $=$.

Let $w₁$ and $w₂$ be two finite sequences.
$w₁$ _embeds_ in $w₂$ if there is an injective mapping $f$ from $[0, |w₂|)$ to $[0, |w₁|)$ such that:
*  $∀ i j.\ i < j ⇒ f(i) < f(j)$
*  $∀ i.\ w₁[i] ≤ w₂[f(i)]$

For instance:
* $0110$ embeds in $01234$ with the following mapping: $(0→0), (1→1), (2→2), (3→3)$.
* $0101$ does not embed in $1230$.

__Higman's lemma.__
The embedding relation over finite sequences of well-quasi-ordered elements is a WQO.

Without proof for the moment, maybe in a later lecture.

This ordering will be important when we looking at lossy channel systems.


### Closed sets

The _upward-closure_ of a set $X$ is $↑X = \\{ y ~|~ ∃ x ∈ X.\ x ≤ y \\}$.
The _downward-closure_ ($↓X$) is defined similarly.

A set $X$ is _upward-closed_ iff $X = ↑X$ and _downward-closed_ iff $X = ↓X$.

Given an upward-closed set $X$, $B$ is a _basis_ of $X$ iff $↑B = X$.


__Lemma.__
If $≤$ is a WQO then any upward-closed set has a finite basis.

_proof._
* Given an upward-closed set $X$, let $B$ be the set of minimal elements of $X$. Notice that all the elements in $B$ are incomparable.
* $B$ exists because $<$ is well-founded.
* $B$ is finite. Otherwise it would form an infinite antichain and contradicts the WQO assumption.
* $↑B = X$ because we choose $B$ that way and $X$ is upward-closed.

Concretely, this means we can represent upward-closed sets by their minimal elements.


__Lemma.__
If $≤$ is a WQO then any infinite increasing sequence of upward-closed sets $X₀ ⊆ X₁ ⊆ X₂ ⊆ …$ eventually stabilizes, i.e., there is a $k$ such that $∀ i.\ i > k ⇒ X_i = X_k$.

_proof._
* By contradiction, assume that we have $X₀ ⊆ X₁ ⊆ X₂ ⊆ …$ which does not stabilizes.
* By removing equal elements, we get an infinite subsequence $Y₀ ⊂ Y₁ ⊂ Y₂ ⊂ …$ which does not stabilizes.
* From this sequence, create an infinite sequence of elements $y₀ …$ such that $y_i ∈ Y_{i+1} ∖ Y_i$.
* Because $Y$s are upward-closed, $y₀ …$ cannot contain an infinite increasing subsequence.
* Because $≤$ is a WQO, $y₀ …$ cannot contain an infinite decreasing sequence.
* Therefore the sequence $y₀ …$ contains an infinite antichain which contradicts the WQO hypothesis.


## Transition systems (TS)

A _transition sytem_ $\mathcal{S}$ is a pair $(S,→)$ where
* $S$ is a set of states (can be infinite),
* $→ ⊆ S × S$ is a transition relation.

_Remark._
We will focus on the covering problem which is a state property and, therefore, the notion of TS is bare bone.
It does not include any kind of labelling on the transition, or any other kind of refinement.
The idea of WSTS can be generalized to TS with labelling, however it complicates the definition.


Given a TS $(S,→)$ the set of direct predecessors and successors are defined as:
* $\mathit{pre}(X) = \\{ y ~|~ ∃ x ∈ X.\ y → x \\}$
* $\mathit{post}(X) = \\{ y ~|~ ∃ x ∈ X.\ x → y \\}$

_Notation._
We often write $\mathit{pre}(s)$ instead of $\mathit{pre}(\\{s\\})$ and similarly for $\mathit{post}$.

$→⁺$ is the transitive closure of $→$ and $→^*$ is the reflexive transitive closure of $→$.

### Finitely branching TS

A TS is _finitely branching_ iff $∀ s ∈ S.\ \mathit{post}(s) \text{is finite}$.

In this class we are only dealing with finitely branching TS.


### WSTS

A _well-structured transition system_ $\mathcal{S}$ is a triple $\mathcal{S} = (S,→,≤)$ such that:
* $(S,→)$ is a TS
* $≤$ is a WQO over $S$
* compatibility: $∀ x₁ x₂ y₁.\ ∃ y₂.\ x₁ → x₂ ∧ x₁ ≤ y₁ ⇒ y₁ →^* y₂ ∧ x₂ ≤ y₂$.

#### Different kinds of compatibility/simulation

Compatibility is also called monotonicity.
We can identify a few variations:

* strict: $∀ x₁ x₂ y₁.\ ∃ y₂.\ \ x₁ → x₂ ∧ x₁ < y₁ ~⇒~ y₁ →^* y₂ ∧ x₂ < y₂$ (caveat: this does not always imply compatibility)
* strong: $∀ x₁ x₂ y₁.\ ∃ y₂.\ \ x₁ → x₂ ∧ x₁ ≤ y₁ ~⇒~ y₁ → y₂ ∧ x₂ ≤ y₂$
* stuttering: $∀ x₁ x₂ y₁.\ ∃ \text{ sequence } y₂ … y_n.\ \ x₁ → x₂ ∧ x₁ ≤ y₁  ~⇒~  y₁ → … → y_n  ∧  x₂ ≤ y_n  ∧  ∀ i < n.\ x₁ ≤ y_i$
* …

__Lemma.__
If $≤$ is a partial order then strict compatibility implies compatibility.

_proof._
As exercise.

__Lemma.__
Strong compatibility implies stuttering compatibility.

_proof._
As exercise.

#### Examples

PN is strict, strong, and even has the same transition labelling...

FA is strict, strong, and even has the same transition labelling...


## Covering problem (revisited)

Given a WSTS $\mathcal{S}$, initial state $s₀$, and a target state $t$.
$(\mathcal{S},s₀)$ can _cover_ $t$ if there is $s'$ such that $s₀ →^* s'$ and $s' ≥ t$.

The covering problem generalizes from single target state $t$ to set of states $T$ with $∃ t ∈ T.\ s' ≥ t$.

It can be rewritten as $s₀ →^* s'$ and $s' ∈ ↑T$.

Another equivalent formulation is $s₀ ∈ \mathit{pre}^*(↑T)$.

If $T=↑T$ (upward-closed) then $\mathit{pre}^*(T) = \mathit{pre}^*(↑T)$ and covering is the same as reachability.

## Set saturation algorithm

Let $\mathit{pre}^*(I)$ be the limit of the sequence $I₀ ⊆ I₁ ⊆ I₂ ⊆ …$ where $I₀ = I$ and $I_{n+1} = I_n ∪ \mathit{pre}(I_n)$.

__Lemma.__
Given a WSTS $(S,→,≤)$ and $T ⊆ S$ if $T$ is upward-closed then $\mathit{pre}^*(T)$ is upward-closed.

_proof._
* Assume that $s ∈ \mathit{pre}^*(T)$, $s→^*t$, and $t ∈ T$.
* By monotonicity (and induction if more than one transition), for any $s' ≥ s$ then we can find $t'$, $s'→^* t'$ and $t' ≥ t$.
* Because $T$ is upward-closed $t' ∈ T$.
* Therefore $s' ∈ \mathit{pre}^*(T)$ which means $\mathit{pre}^*(T)$ is upward-closed.

_Remark._
The stronger version "if $T$ is upward-closed then $\mathit{pre}(T)$ is upward-closed" is only true for WSTS with stuttering compatibility.

Before giving the algorithm we need to make some decidability assumptions.

A WSTS has an _effective pred-basis_ if there is an algorithm to compute $↑\mathit{pre}(↑s)$ for any $s$.

#### Example for Petri net

Consider the following Petri net:
```
   ↗ | ↘
( )     (∙)
   ↖ | ↙
  2
```
Let compute `↑pre(↑(0 1))`:
* if the top transition did fire then the previous state was in `↑(1 0)`
* if the bottom transition did fire then the previous state was in `↑(0 2)`

So `↑pre(↑(0 1)) = ↑(1 0) ∪ ↑(0 2)`.

```
  2
   ↗ | ↘
( )     (∙)
   ↖ | ↙
```
Let compute `↑pre(↑(0 1))`:
* if the top transition did fire then the previous state was in `↑(2 0)`
* if the bottom transition did fire then the previous state was in `↑(0 2)`

So `↑pre(↑(0 1)) = ↑(2 0) ∪ ↑(0 2)`.


### Algorithm for the covering problem

Given a WSTS $\mathcal{S}$ with an effective pred-basis, initial state $s₀$, and a set of target states $T$.

```
M = ↑T
N = ∅
while M ≠ N
    N := M
    M := M ∪ ↑pre(↑M)
return s₀ ∈ M
```

__Theorem.__
Given a WSTS with an effective pred-basis and a decidable $≤$, the covering problem is decidable.

_proof._
* The algorithm above terminates because the sequence of $M$ stabilizes (Lemma above) and all the operations are decidable.
* The algorithm solves the covering problem.
  We will need some extra propositions.
  Let $M_i$ by the value of $M$ after the $i$th iteration of the $while$ loop.
  Assume that the loop executes $m$ times.
  $M_m$ is the last value computed by the algorithm.
  We extend the sequence of $M_i$ with $M_i = M_m$ for $i ≥ m$.
  - _proposition (1)_: $M_m = ↑M_m = ⋃_{i ∈ ℕ} M_i = ⋃_{i ∈ ℕ} ↑pre^i(↑ T)$ by induction on $i$
    * $i = 0$: $M₀ = ↑T = ↑pre^0(↑ T)$ (1st line of the algorithm)
    * $i → i+1$:

      case 1: $i < m$:
      - $M_{i+1} = M_i ∪ ↑pre(↑M_i)$ (5th line of the algorithm)
      - $M_{i+1} = ⋃_{0≤j≤i} ↑pre^j(↑T) ∪ ↑pre(↑⋃_{0≤j≤i} ↑pre^j(↑T))$ (induction hypothesis)
      - $M_{i+1} = ⋃_{0≤j≤i} ↑pre^j(↑T) ∪ ⋃_{1≤j≤i+1} ↑pre^j(↑T)$ (distributing $↑pre(↑_)$ over $⋃$)
      - $M_{i+1} = ⋃_{0≤j≤i} ↑pre^j(↑T) ∪ ↑pre^{i+1}(↑T)$ ($X ∪ X = X$)

      case 2: $i ≥ m$:
      - The sequence has stabilized so $M_{i+1} = M_{i}$ and $↑pre^{i+1}(↑ T) ⊆ ⋃_{i ∈ ℕ} ↑pre^i(↑ T)$.
      - The rest follows with a bit of algebra and $X ⊆ Y ⇒ X ∪ Y = Y$.
  - _proposition (2)_: $M_m = pre*(↑T)$
    * $M_m = ⋃_{i ∈ ℕ} ↑pre^i(↑ T) = ↑pre^*(↑T)$ by proposition (1).
    * $pre^*(↑T) = ↑pre^*(↑T)$ by lemma above.
  - The algorithm returns $s₀ ∈ M_m = pre^*(↑T)$ and, therefore, solves the covering problem.


## Examples

Let consider the following Petri net:
```
     u   l
    (∙) ( )
     ↓ ⤱ ↓
lock −   − unlock
     ↑ ↘ ↑ ↘
|→  ( ) ( ) ( ) → |
     x   c   y
```
With the ordering on the places be `(u l x c y)`.

We can violate mutual exclusion if we can cover `(0 0 0 2 0)`.

Running the algorithm gives:
* `M₀ = ↑(0 0 0 2 0)`
* `M₁ = ↑(0 0 0 2 0) ∪ ↑(1 0 1 1 0)`
* `M₂ = ↑(0 0 0 2 0) ∪ ↑(1 0 0 1 0) ∪ ↑(2 0 2 0 0)`
* `M₃ = ↑(0 0 0 2 0) ∪ ↑(1 0 0 1 0) ∪ ↑(2 0 1 0 0)`
* `M₄ = ↑(0 0 0 2 0) ∪ ↑(1 0 0 1 0) ∪ ↑(2 0 0 0 0)`
* `M₅ = M₄`

Since `s₀ = (1 0 0 0 0)` and `s₀ ∉ M₅`, the net respects mutual exclusion.


## Worst case complexity

The worst case complexity for the backward algorithm is given by the longuest descending chain or the longuest antichain in the ordering.
WSTS gives decidability but no meaningful complexity bound.
For instance, let us look at ordering on trees which we will use in [notes 11](notes_11.md).

#### Embeddings of finite trees

Let $T₁$ and $T₂$ by two finite rooted tree and $(X,≤)$ be the set of nodes' labels with a WQO.
$T₁$ is inf-embeddable in $T₂$ if there is an injective mapping $f$ from the nodes of $T₁$ to the nodes of $T₂$ such that:
* For all node $n$ in $T₁$, $label(n) ≤ label(f(n))$.
* If the node $m$ is a descendent of $n$ in $T₁$ then $f(m)$ is a descendent of $f(n)$.
* If $m₁$ and $m₂$ are children of $n$ then $F(n)$ is the first common ancestor of $f(m₁)$ and $f(m₂)$.

For instance, Let us look at the following 3 trees:

$T₁$:
```
  r
 ↗
b
 ↘
  b
```

$T₂$:
```
  r
 ↗
b   r
 ↘ ↗
  g→b
```

$T₃$:
```
  r
 ↗
g   g
 ↘ ↗
  b→b
```

In the pictures above, the letter is the color from the WQO $(\\{r,g,b\\}, =)$.

We have that:
* $T₁ ≤ T₂$
* $T₁ ≰ T₃$
* $T₂ ≰ T₃$ and $T₃ ≰ T₂$

__Kruskal's theorem.__
Over the finite trees with nodes labeled by elements of a WQO, inf-embedding is a WQO.

Without proof for the moment, maybe in a later lecture.

The longuest non ascending chain in this ordering is mind-bogglingly long as explain in the following two videos about `TREE(3)`: https://www.youtube.com/watch?v=3P6DWAwwViU, https://www.youtube.com/watch?v=IihcNa9YAPk
