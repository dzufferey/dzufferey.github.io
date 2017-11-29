# Solutions to homework 4

## WQO from well-founded and no infinite antichain

__Lemma.__
Given `≤`, if `<` is well-founded and `≤` does not have infinite antichain then `≤` is a wqo.

_proof._
* By contradiction, assume `≤` is not a wqo.
* Then there exists an infinite sequence `x₀ x₁ x₂ …` where `∀ i j. i < j ⇒ x_i ≰ x_j`.
* Let `M = { i | ∀ j > i. x_i ≱ x_j }`. `M` is the set of indices of elements which do not have any smaller successors in the chain.
* Case split on whether `M` is finite or infinite:
  - If `M` is infinite then it forms an infinite antichain which contradicts the assumption.
  - If `M` is finite then there is `k = max(M)`.
    That is the last element in the sequence that doesn't have a smaller successor.
    Let's observe `x_d`, `d > k`.
    There is smaller successor, `x_l` (`l>d`), `x_l ≤ x_d`.
    From the choice of sequence `x` (namely, the witness that `≤` is not a WQO) we also know that `x_d ≰ x_l`.
    These two facts give us (by definition)  `x_l < x_d`.
    Since this holds for any element after `x_k`, we can build an infinite descending subsequence.
    That contradicts the assumption of well-foundedness.

## Upward-closed properties

### Give a proof that place k-boundedness is upward-closed.

Violation of k-boundedness is of the form `∑_{s∈S} M(s) > k`.
Set of error markings is `ERR = {M: ∑_{s∈K} M(s) > k}`.
Per definition of upward closure, `↑ERR = {M':∃ N' ∈ ERR. N' ≤ M'}`.
If `T ∈ ERR` then trivially `T ∈ ↑ERR`.
Other inclusion, if `T ∈ ↑ERR` then there is `N ∈ ERR` such that `N ≤ T` which implies `N(s) ≤ T(s), ∀ s ∈ S` which also gives us  `∑_{s∈K} T(s) ≥ ∑_{s∈K} N(s) > k` and that means `T ∈ ERR`.
Finally, we have `↑ERR = ERR`

### Give a counter-example that shows that deadlock-freedom is not upward-closed.

Consider the Petri net
```
( ) ⇄ |
```
The marking `(0)` is a deadlock but `(1)` is not and `(1)` is included in `↑(0)`.


## Compatibility

### If `≤` is a partial order then strict compatibility implies compatibility.

By antisymmetry of PO, we can prove that `x ≤ y` is `x < y ∨ x = y`. (`x ≤ y ∧ (x=y ∨ x≠y)`).

The `<` case is covered by strict compatibility and the `=` case is trivial as we can use reflexivity to claim that `x ≤ x` and then using using `x₂` as `y₂` from the definition of compatibility.

### Strong compatibility implies stuttering compatibility

Definition of strong compatibility requires that `y′` is an immediate successor of `y`.
But this is only a special case of the definition of stuttering compatibility.
With stuttering compatibility `y′` can be reach after some number of transitions and this number can as well be 1.


## Effective pred-basis

### DFA and NFA

`↑s = s`, `pre(↑s) = pre(s) = {s' : ∃ a s. t. (s',a,s) ∈ δ }`, `↑pre(↑s) = pre(↑s)`

### Petri net

Algorithm by Stephan Spengler and Johannes Freiermuth (Thanks!).

```
// P will hold the value for pre(↑s)
P = {}
for t ∈ T:
  M' = M
  for s ∈ S:
    // find any marking that is a predecessor of marking M
    M'(s) = max(0, M(s) - W(s,t) + W(t,s))
  for s ∈ S:
    // add if it is smaller than any existing element of P
    if M'(s) < min{ M(s): M ∈ P }:
      P = P ∪ {M'}
  //remove all the elements that were made obsolete by addition of a greater one
  for M" ∈ P:
    if M" > M':
      P = P\{M"}
return P
```
