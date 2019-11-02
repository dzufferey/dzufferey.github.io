# Homework 2

_Instructions_
* Due on November 11, Monday, at 5pm.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants in the document.
* Please submit your solutions in one readable pdf file. For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).



## Shuffle Product for Automaton

The shuffle product $⧢$ for two words over $Σ$ is inductively defined as:
* $au ~ ⧢ ~ bv = \\{ aw ~|~ w \in (u ~ ⧢ ~ bv) \\} \cup \\{ bw ~|~ w \in (au ~ ⧢ ~ v) \\}$,
* $ε ~ ⧢ ~ v = \\{v\\}$,
* $u ~ ⧢ ~ ε = \\{u\\}$

for $a,b ∈ Σ$ and $u,v ∈ Σ^\*$.

Here is an example: $ab ~ ⧢  ~ xy = \\{ abxy, ~ axby, ~ xaby, ~ axyb, ~ xayb, ~ xyab \\}$.

The shuffle product generate all the sequences that can be obtained with a single riffle shuffle.
(Special technique to mix two decks of cards.)

A finite automaton is a finite description of a (potentially infinite) set of words.

Our goal is to define a construction which correspond to the shuffle of the words accepted by two automatons.


#### Tasks
* Define a new operation which takes as input two automatons and returns an automaton which accepts a word iff this word is a shuffle of two words accepted by the automatons.
  More formally, given two automatons $A$, $B$ define a shuffle product $A ~ ⧢ ~ B$ such that:
  \\[w ∈ L(A ~ ⧢ ~ B) ⇔ ∃ u,v.\ w = u ~ ⧢ ~ v ∧ u ∈ L(A) ∧ v ∈ L(B)\\]
* Prove that your definition is correct.
* Briefly discuss the differences of between the synchronized and shuffle product.
  Try to give some examples where on product is more suitable than the other.


## Counting with an Automaton

Give an NFA that recognizes the language $L := \\{ a^i ~|~ i \neq 30 \\}$ with less than 25 states or give a proof that such automaton does not exist.


## Automata and Petri Nets

Let us discuss in more details how we can compare operations on automata with Petri Nets.

To compare both we need to extend Petri nets with a labeling function.
The labeling function has the role of the alphabet for automaton.

A _labeled Petri Net_ is a tuple $(S, T, Σ, W, L)$ where
* $S$ is a finite set of places
* $T$ is a finite set of transitions
* $Σ$ is a finite set of labels (alphabet)
* $W$ is a weight function over $(S × T) ∪ (T × S) → ℕ$
* $L$ is a labeling function $T → Σ$

Given an initial marking $M₀$ we say that a work $w ∈ Σ^*$ is accepted if there exists a sequence of transitions $t₁ t₂ … t_n$ such that $M₀ [t₁〉 M₁ [t₂〉 M₂ … [t_n〉 M$ and $w = L(t₁) L(t₂) … L(t_n)$.

For the automaton, in this exercise, we look at _prefix-closed_ automata.

An automata $A$ is prefix-closed iff every prefix of an accepted word is also accepted.
Formally:\\[ ∀ w ∈ L(A), i ∈ [0, |w|].~ w₁ … w_i ∈ L(A). \\]
Concretely, if $A$ is a DFA then all the states of $A$ are accepting except a single non-accepting sink state (all transitions from that state go back to that state).
If $A$ is an NFA then if it has more than one state, all the states are accepting.

#### Tasks
* From prefix-closed automata to labelled Petri nets
  - Give a translation from prefix-closed automata to labelled Petri nets.
  - Give a construction which take two prefix-closed automaton and returns a labelled Petri net corresponding to the synchronized product.
  - Give a construction which take two prefix-closed automaton and returns a labelled Petri net corresponding to the shuffle product.
* Product constructions for automaton like the synchronized or shuffle product are exponential.
  The product of $m$ automaton with $n$ states give an automaton with $n^m$ states.
  With labelled Petri nets we can have more compact result.
  - What is the worst case size of your constructions for the synchronized product as labelled Petri net?
  - What is the worst case size of your constructions for the shuffle product as labelled Petri net?


## Dining Philosophers

The [dining philosophers problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem) has been introduced to explain some of the challenges to resource allocation and synchronization in a concurrent system.
We want to use Spin to check a proposed solution to this problem.
We focus on the [Chandy/Misra solution](https://www.cs.utexas.edu/users/misra/scannedPdf.dir/DrinkingPhil.pdf).

#### Tasks
* Encode the dining philosophers problem in Spin without any synchronization and show there can be deadlocks.
* Implement the Chandy/Misra solution and shows that there is no deadlock anymore.

In both cases, make your solution parametric.
Then you can vary the parameter to experience what is know as the "state-space explosion" problem which is the exponential complexity of the product construction.

_Remark._
When writing paper authors focus on exlpaining the idea and often simplify the setting as much a possible.
While this makes for more readable papers, implementing the proposed solution requires bringing back some of the so-called "implementation details".
Using a tool like Spin is an intermediate step.
There are more details but it is still usually simpler than a normal implementation and Spin can help debug.
