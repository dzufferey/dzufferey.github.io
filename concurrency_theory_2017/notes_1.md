# Finite state machines

## DFA

#### Example

word finishing with 1

#### Definition

A deterministic finite automaton M is a 5-tuple `(Q, Σ, δ, q₀, F)` where

* `Q` is a finite set of states
* `Σ` is a finite alphabet (set of input symbols)
* `δ` is the transition function (`Q × Σ → Q`)
* `q₀` is the initial state (`q₀ ∈ Q`)
* `F` is the set of accepting states (`F ⊆ Q`)

Let `w = a₁ a₂ ... a_n` be a word over the alphabet Σ.
The automaton M accepts w if there is a sequence of states, `r₀ r₁ ... r_n`, such that:
* `r₀ = q₀`
* `r_{i+1} = δ(r_i, a_{i+1})` for i = 0, ..., n−1
* `r_n ∈ F`


## NFA

#### Example

word with 1 as the 3th symbol before the end

#### Definition

A non-deterministic finite automaton M is a 5-tuple, `Q, Σ, δ, q₀, F` where

* `Q` is a finite set of states
* `Σ` is a finite alphabet (set of input symbols)
* `δ` is the transition function (`Q × Σ → 2^Q`)
* `q₀` is the initial state (`q₀ ∈ Q`)
* `F` is the set of accepting states (`F ⊆ Q`)

Let `w = a₁ a₂ ... a_n` an be a word over the alphabet Σ.
The automaton M accepts w if there is a sequence of states, `r₀ r₁ ... r_n`, such that:
* `r₀ = q₀`
* `r_{i+1} ∈ δ(r_i, a_{i+1})` for i = 0, ..., n−1
* `r_n ∈ F`

## Operation (Closure properties)

* intersection/union
* complementation
* emptiness/universality

### Synchronized Product

Given automaton M₁ and M₂, the synchronized product M₁ ⊗ M₂ be the automaton M where:

* `Q = Q₁ × Q₂` 
* `Σ = Σ₁ ∪ Σ₂`
* `δ` is the transition function 
  - `δ((q₁,q₂), a) = (δ₁(q₁, a), δ₂(q₂, a))` if `a ∈ Q₁` and `a ∈ Q₂`
  - `δ((q₁,q₂), a) = (q₁, δ₂(q₂, a))` if `a ∉ Q₁` and `a ∈ Q₂`
  - `δ((q₁,q₂), a) = (δ₁(q₁, a), q₂))` if `a ∈ Q₁` and `a ∉ Q₂`
* `q₀ = (q₀₁,q₀₂)`
* `F = F₁ × F₂`

#### Example

lock + program ...

### Determinization (Powerset construction)

Turn a NFA into a DFA ...

## Verifying Properties

### Properties

Properties of concurrent systems are broadly divided in two categories:
* _Safety_: properties that are violated by finite traces
* _Liveness_: properties that can only be violated by infinite traces

In this class we focus on _safety_ and _eventuality_.
General classes of temporal properties (LTL, CTL, μ-calculus, weak/strong fairness, ...) are out of scope.

#### Example

* Assertion
* Termination
* Deadlock-freedom

## Verification

As Paths in graphs:
- Safety is reachability: path from the initial state to an error state.
- Eventuality is nested reachability: lasso path with the stem starting at the initial state and the loop does not go to any "progress" state.

As automata construction:
- language inclusion: `A ⊆ B` reduces to `A ∩ ¬B = ∅`
- (co-)Büchi automaton ...

### State-space Exploration (Model Checking)

...

### Symmetry Reduction

### The Spin Model-Checker

http://spinroot.com/spin/whatispin.html

#### Promela

http://spinroot.com/spin/Man/Manual.html

#### Running Spin

https://github.com/tcruys/runspin
