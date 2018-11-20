# Homework 5

_Instructions_
* Due *before* November 27 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).


## Monotonicity of Petri net extensions

In the previous exercises, we discussed (1) reset nets, (2) transfer nets, and (3) nets with inhibitory edges.

(1)-(2) are defined in the [exercises 4](viewer.html?md=concurrency_theory_2018/exercises/exercises_4.md).
(3) is defined in the [exercises 2](viewer.html?md=concurrency_theory_2018/exercises/exercises_2.md).

For each of these extension, determine what kind of monotonicity/compatibility ([lecture notes 4](viewer.html?md=concurrency_theory_2018/notes_4.md)) is respected: normal (WSTS definition), strict, strong, stuttering.
Give a short proof for the kind of property that are respected and a counterexample for the kinds that are not.



## Some more WQOs

We saw a few examples of WQO and how to build WQOs from other WQO (Dickson's lemma and Higman's lemma) in the [lecture notes 4](viewer.html?md=concurrency_theory_2018/notes_4.md).
Let us look at some more examples and determine whether or not they are WQO.

Let $(X,≤)$ be both a WQO and a PO.
For each of the following example, either give a proof that it is a WQO or give a counterexample that show it is not a WQO.

__Example 1.__

The _lexicographic order_ $(X^*,≤_{lex})$ over words in $X$ is defined as $w_1 ≤_{lex} w_2 ⇔ w_1 <_{lex} w_2 ∨ w_1 = w_2$ where

$$$
w_1 <_{lex} w_2 ⇔ ∨ \left\\{ \begin{array}{l}
    ∃ j.~ j < min(|w_1|,|w_2|) ~∧~ w_1[j] < w_2[j] ~∧~ ∀ i.~ i < j ⇒ w_1[i] = w_2[i] \\\\
    |w_1| < |w_2| ∧ ∀ i.~ i < |w_1| ⇒  w_1[i] = w_2[i]
 \end{array}\right.
$$$

($w[i]$ assumes the indexing goes from $0$ to $|w|-1$.)


__Example 2.__

The _subword order_ $(X^*,≤_{sub})$ over words in $X$ is defined as $w_1 ≤_{sub} w_2 ⇔ ∃ i.~ ∀ j ∈[0,|w_1|).~ w_1[j] ≤ w_2[i+j]$.


__Example 3.__

The embedding with groups of size $k$ $(X^*,≤_{emk})$ for a fixed $k$ is a more variation over the word embedding.

Intuitively, we group symbols by chunks of size $k$ and requires that the chunks are matched by contiguous blocks.
$≤_{em1}$ corresponds to embedding.

More formally, $w_1 ≤_{emk} w_2$ if there is an injective mapping $f$ from $[0, |w_1|)$ to $[0, |w_2|)$ such that:
* $∀ i j.\ i < j ⇒ f(i) < f(j)$ (same as embedding)
* $∀ i.\ w₁[i] ≤ w₂[f(i)]$ (same as embedding)
* $∀ i j.~ (i \mod k) = 0 ∧ j ∈ [0,k) ⇒ f(i+j) = f(i)+j$ (new condition)

__Example 4.__

A finite multiset over $X$ is a function $m: X ⇒ ℕ$ such that $support(m) = \\{ x ~|~ m(x) > 0 \\}$ is finite.

The _finite multiset embedding_ $(\mathcal{M}(X), ≤_{\mathcal{M}})$ is defeined as follow: $m_1 ≤_{\mathcal{M}} m_2$ iff there exists an injective function $f: support(m_1) → support(m_2)$ such that $∀ x.\ x ≤ f(x) ∧ m₁(x) ≤ m₂(f(x))$.
