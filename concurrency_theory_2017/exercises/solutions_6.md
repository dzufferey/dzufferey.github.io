# Solutions 6

## WQO and powerset

Let us look in more details at a particular type of WQO that is well behaved with respect to powerset.

Let `X` be a finite set and `≤` a quasi-order on `X`.
* Show that `(X,≤)` is a WQO
* Show that `(2^X,⊑)` is a WQO (``P ⊑ Q ⇔ ∀ q ∈ Q. ∃ p ∈ P. p ≤ q``)
* Show that `(2^X,⊆)` is a WQO

**Solution** `X` is finite and `2^X` is finite.
This means that any infinite sequence contains at least one element repeated.
Since all the suggested orderings are reflexive, we have that these are all well-quasi-ordered.

## Backward vs forward search

We saw two approaches to the coverability problem for Petri nets:
1. forward search (Kark-Miller tree)
2. backward search (covering algorithm for WSTS)

Forward and backward analysis can behave very differently on different nets.

* Can you find a small Petri net (with just a few places) such that the forward search is very efficient (stops after few iterations) and the backward search is slow (> 100 iterations)?

**Solution** Consider the following Petri net:
```
| → ( )
```
- Initial marking: `(0)`
- Target marking: `(1000)`

Forward search would immediately find `0 -> 1 -> ω`. Backward search would have to cover all the values `↑1000 -> ↑999 -> ... -> ↑0`

* Can you find a small Petri net (with just a few places) such that the backward search is very efficient (stops after few iterations) and the forward search is slow (> 100 iterations)?

**Solution**  Consider the following Petri-net
 ```
 ( ) → | → ( )
 ```
- Initial marking: `(1000 0)`
- Target marking: `(1001 0)`

The forward search would take 1000 iterations `(1000,0) -> (999,1) -> ... -> (0,1000)`. Bacward search - on the other hand - would finish much sooner by finding sequence `(1001,0) -> (1002,0) -> (ω, 0)`

## Optimizing the Karp-Miller Tree algorithm

Let us look at the ideal KM tree from [notes 5](https://github.com/dzufferey/dzufferey.github.io/blob/master/concurrency_theory_2017/notes_5.md):

```
    Input: very-WSTS 𝓢 completion-post-effective and ∞-completion-effective, initial state s₀
    Output: the covering set of 𝓢

    𝓒 := the completion of 𝓢

 1: initialize a tree T with an unmarked node (↓s₀, 0)
 2: while T contains an unmarked node c: (I, n) do
 3:     if c has an ancestor (I′, n′) s.t. I′ = I then mark c
 4:     else
 5:         if c has an ancestor c′: (I′, n′) s.t. I′ ⊂ I  ∧  n′ = n
 6:             w ← sequence of labels from c′ to c
 7:             replace c: (I, n) by (post_𝓒^∞(I, w), n + 1)
 8:         for a ∈ Σ do
 9:             for J ∈ post_𝓒(I, a)
10:                 T := T ∪ ((I,n), a, (J,n))
11:         mark c
12: return ⋃_{(I,n) ∈ T} I
```

_Remark._
When asked to justify in the following questions, we do not expect a complete proof due to the complexity of the problem ( You are welcome to try though :) ).
If you think the claim is true then you should explain your approach to showing why it is true and, maybe, try to give a proof sketch.
If you think the claim is false then you should try to give a counterexample or explain what you think breaks.

### Optimization 1

Because larger states give rise to more behaviors, we can stop the search early when we see smaller states.
On line `3` of the algorithm, let us replace `I′ = I` by `I′ ≥ I`.
Is the algorithm still solving the covering problem? Justify.

**Solution**
Yes, it would still work. All the states explored from `I` were already explored from `I'` (because we are talking about downward closed sets).

[Optional]
By looking at the paper [Forward Analysis for WSTS, Part III: Karp-Miller Trees](https://arxiv.org/abs/1710.07258).
Can you suggest are reason why the authors use `=` and not `≥`?

**Solution**
Because they were not looking only to coverability. Their setting is checking if a liveness property `f` holds. They show that it can be reduced to the problem of repeated coverability. Then it becomes important to really know which nodes are visited repeatedly (and not only which are covered once).

### Optimization 2


Using the same idea that larger states give rise to more behaviors, we can prune the search by
1. stopping the search when another branch already contains a larger state,
2. removing smaller states and their successors in other branches of the tree.
We get a new algorithm call the minimal coverability tree algorithm.

```
    Input: very-WSTS 𝓢 completion-post-effective and ∞-completion-effective, initial state s₀
    Output: the covering set of 𝓢

    𝓒 := the completion of 𝓢

 1: initialize a tree T with an unmarked node (↓s₀, 0)
 2: while T contains an unmarked node c: (I, n) do
 3:     if there is a node c′: (I′, n′) s.t. I′ = I then mark c
 ⅰ:     else if there is a node c′: (I′, n′) s.t. I ⊂ I′ then
 ⅱ:         remove from T the subtree starting at c (including c)
 5:     else if c has an ancestor c′: (I′, n′) s.t. I′ ⊂ I  ∧  n′ = n
 6:         w ← sequence of labels from c′ to c
 7:         replace c: (I, n) by (post_𝓒^∞(I, w), n + 1)
 a:         let c′: (I′, n′) be the oldest ancestor s.t. I′ ⊂ I (if it exists)
 b:             remove from T the subtree starting at c′ (but keep c′)
 c:             replace c′ by c in T
 d:         for each c′: (I′, n′) s.t. I′ ⊂ I  /*any node, not only the ancestors*/
 e:             remove from T the subtree starting at c′ (including c′)
 f:     else
 8:         for a ∈ Σ do
 9:             for J ∈ post_𝓒(I, a)
10:                 T := T ∪ ((I,n), a, (J,n))
11:         mark c
12: return ⋃_{(I,n) ∈ T} I
```

There are three main changes:
* the line `ⅰ-ⅱ` stop the search is if a larger node already exists,
* the lines `a-e` are the new code that prune the search, and
* The acceleration (`5-7`) and computation of the successors (`8-11`) occurs in different branches.
  The nodes are not marked after the acceleration and the computation of the post only occurs when there is not acceleration possible.
  A node is marked after the successors have been added.
  The acceleration does not mark the nodes.

Is the algorithm still solving the covering problem? Justify.

**Solution**
No! For a similar (but not the same) optimization, the counterexample is given in [this paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.61.9377).
For our optimization, a counterexample is given with [this Petri net](counterExampleNet.jpg)
