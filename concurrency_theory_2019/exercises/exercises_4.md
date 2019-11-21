# Homework 4

_Instructions_
* Due on November 25, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


# Petri Nets with Parametric Initial Marking

Let $N$ be a Petri net and $P$ by a finite set of parameters.

A _parametric marking_ of $N$ is a function $\text{PM}: S → L[ℕ ∪ P]$ where $L[ℕ ∪ P]$ denotes linear expressions over $ℕ ∪ P$.
For instance, a place in a marking could have $3 x + 5$ tokens where $x$ is a parameter.
Note that we do not consider substraction as possible operator in linear expressions.

A valuations of the parameters $ρ: P ⇒ ℕ$ give concrete values to the parameters $P$.

### Tasks

Given a Petri net $N$, a parametric initial marking $\text{PM₀}$, a target marking $M$.
We can ask the following questions:
- _existential covering_: is there a valuation $ρ$ such that $(N,ρ(\text{PM₀}))$ can cover $M$?
- _universal covering_: Does $(N,ρ(\text{PM₀}))$ cover $M$ for all valuation $ρ$?

For each question:
- Explain how to answer the question. (Hint: reduce to normal Petri nets)
- Prove that your solution is correct.


# Karp-Miller Tree for ℤ Petri Nets

Let us look at a modification of Petri nets.

Given a Petri net $N = (S, T, W)$, a marking of $N$ is a function $M: S → ℤ$. (changing $ℕ$ to $ℤ$.)
The semantics is the same except that transitions are always enabled.

Here is the Karp-Miller tree algorithm for Petri net (week 3):
```
KarpMillerTree(S,T,W,M₀)
    F = {M₀}    // frontier
    E = {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F ← F ∖ {M}
        for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
            ancestors ←  { A | A can reach M in E } ∪ M
            M′ ← accelerate(ancestors, M′)
            E ← E ∪ { (M,M′) }
            if ∀ A ∈ ancestors. not(A ≥ M′) then
                F ← F ∪ {M′}
    return E
```

Here is the backward algorithm for WSTS (week 4):
```
M = ↑T
N = ∅
while M ≠ N
    N := M
    M := M ∪ ↑pre(↑M)
return s₀ ∈ M
```

### Questions
* Does the Karp-Miller algorithms still work on $ℤ$ Petri net? Justify
* Does the backward algorithms still work on $ℤ$ Petri net? Justify
* Can you think of a simpler algorithms for $ℤ$ Petri net? Justify


# Different Kinds of Petri Nets Properties

We discussed a number of different reachability/safety properties for Petri nets.

Let us look at the following properties:
* reaching a given marking
* covering a given marking
* deadlock freedom
* co-linear properties


We want to determine how these properties compare to each other.

### Questions
* Explain what the properties are and the algorithms that can check them (if we covered any).
* For the different properties, are there properties which are special cases of others?
  - When a property is a special case of another, try to find a reduction
  - When a property does not reduce to another, explain why not (try to find an example)
* What changes if we consider the following generalizations of the properties:
  - reaching a marking in a given set of markings
  - covering a marking in a given set of markings
  - finite union of co-linear properties


# Lossy Petri Net with Inhibitory Edges (LN)

LN are Petri nets with testing if some places have no tokens (inhibitor arc) and, furthermore, tokens may get lost before and after executing a transition (lossy).

A _Lossy Petri Net with inhibitory edges_ is a 4-tuple $N = (S, T, W, I)$ where
* $S$ is a finite set of places
* $T$ is a finite set of transitions
* $W$ is a weight function over $(S × T) ∪ (T × S) → ℕ$
* $I$ is a inhibition function over $T → (S ∪ {⊥})$

To define what $M [t〉M'$ is, we need an intermediate marking $M₁$.
An enabled transition $t$ can fire and it produce a new marking $M'$ if
\\[
\begin{array}{rccl}
M [t〉M' & \Leftrightarrow & ∃ M₁. & M ≥ M₁ ≥ W( \\_ ,t) \\\\
& & ∧ & (I(t) = ⊥ ∨ M₁(I(t)) = 0) \\\\
& & ∧ & M' ≤ M₁ - W( \\_ ,t) + W(t, \\_ )
\end{array}
\\] 

$W( \\_ ,t)$ and $W(t, \\_ )$ are the forward and backward vector for $t$.

### Questions
* Is the covering problem solvable for LN?
    If yes give an algorithm or reduction to an exisiting model where we know how to solve it.
    If no, reduce an undecidable problem to it.
* Is the reachability problem solvable for LN?
    If yes give an algorithm or reduction to an exisiting model where we know how to solve it.
    If no, reduce an undecidable problem to it.
