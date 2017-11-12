# Homework 3

_Instructions_
* Due on November 15.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.

## Invariants, Siphons, and Traps

### Part 1

Consider the following net:
```
( ) → | → ( ) → | → ( )
 ↑    ↓    ↑    ↑    ↓
 | ← ( ) ← | ← ( ) ← |
```

* Give at least one non-trivial trap (not no places or all the places)
* Give at least one non-trivial siphon (not no places or all the places)
* Give at least one non-trivial invariant (`I≠0`)

### Part 2

Consider the boolean operations: intersection, union, and difference.
Are siphons or traps closed under any of these operations? Justify.

By closed under an operation, we mean that if two sets of places have a property then applying the operation preserve that property.
For instance, is the intersection of two siphons a siphon?


## Petri nets with transfer and reset edges

Let us consider two generalizations of Petri Nets:
* _transfer nets_ which have special edges that transfer the tokens from one place to another
* _reset nets_ which have special edges that consume all the tokens in a place

### Definitions

An _Extended Petri Net_ `N` is a 4-tuple `(S, T, W, R)` where
* `S` is a finite set of places
* `T` is a finite set of transitions
* `W` is a weight function over `(S × T) ∪ (T × S) → ℕ`
* `R` is a transfer/reset function over `T → (S ∪ {⊥}) × (S ∪ {⊥})`

`⊥` (bottom) is a dummy element used as placeholder for transition/places which are not connected to any reset/transfer edge.

We categorize the nets according to `R` as follow:
* If `R(t) = (⊥, ⊥)` for all `t` then the net is a normal Petri net.
* If `R(t) = (s, ⊥) ∧ s ≠ ⊥` then there is a _reset edge_ from `s` to `t` and the net is a _reset net_.
* If `R(t) = (s, s′) ∧ s ≠ ⊥ ∧ s′ ≠ ⊥` then the transition `t` is a _transfer edge_ from `s` to `s′` and the net is a _transfer net_.

Furthermore, `R` respects the following:
* `R(t) = (s, s′) ∧ s′ ≠ ⊥ ⇒ s ≠ ⊥`.
* `R(t) = (s, s′) ∧ s ≠ ⊥ ∧ s′ ≠ ⊥ ⇒ s ≠ s′`.
* On top of normal edges a net can have either transfer or reset edges but not both.

Let us explain what firing a transition means in the context of extended Petri net.

`t` is enabled at `M` iff `∀ s ∈ S. M(s) ≥ W(s,t)`.
This is similar to Petri nets.

`M [t〉 M′` is computed as follow:
1. `t` must be enabled at `M`
2. create an intermediate marking `M₁` where `M₁(s) = M(s) - W(s,t)`.
3. assume `R(t) = (s₁,s₂)` create an intermediate marking `M₂` to apply the reset/transfer:
  * if `s ≠ s₁ ∧ s ≠ s₂` then `M₂(s) = M₁(s)`
  * if `s = s₁` then `M₂(s) = 0`
  * if `s = s₂` then `M₂(s) = M₁(s) + M₁(s₁)`
4. compute the final marking: `M′(s) = M₂(s) + W(t,s)`.

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

### Questions

For reset nets and then transfer nets:
* Are these nets monotonic?
* Are these nets strictly monotonic?
* Does the `TerminationCheck` algorithm work on such nets?
* Does the `BoundednessCheck` algorithm work on such nets?

For each question: if yes give a proof, if no give a counterexample.


## Petri nets with inhibitory edges

Even though we can store some information in the places of Petri nets as tokens, it not really possible to count.
This is what makes many problems decidable for Petri nets.
Now, we will explore an extension which allows counting.

### Inhibitory edges

An _Petri Net with inhibitory edges_ `N` is a 4-tuple `(S, T, W, I)` where
* `S` is a finite set of places
* `T` is a finite set of transitions
* `W` is a weight function over `(S × T) ∪ (T × S) → ℕ`
* `I` is a inhibition function over `T → (S ∪ {⊥})`

The difference between Petri net with and without inhibitory edges is when transitions are enabled.
Inhibitory edges block a transition from firing as long as the place with the inhibitory edge contain tokens.
More formally, a transitions `t` is enabled iff `(I(t) = ⊥ ∨ M(I(t)) = 0) ∧ ∀ p ∈ S. M(s) ≥ W(s,t)`.

#### Example

Consider the following net where `⟜` represent an inhibitory edge:
```
(∙)
    ↘
(∙) ⟜ | → ( )
```
In the net above, the transition cannot fire.

In the configuration below, the transition can fire.
```
(∙)
    ↘
( ) ⟜ | → ( )
```
After firing, we get:
```
( )
    ↘
( ) ⟜ | → (∙)
```

### Minsky machines

Let us consider [Minsky machines](https://en.wikipedia.org/wiki/Counter-machine_model#1961:_Minsky.27s_model_of_a_partial_recursive_function_reduced_to_a_.22program.22_of_only_two_instructions), a simple kind of [counter machine](https://en.wikipedia.org/wiki/Counter_machine).

It has
* a finite number of labels `L` (program counter)
* a finite number of registers `R` containing integers
* each label corresponds to an instruction which can be
  - `INC(r, l): r +=1; goto l`
  - `JZDEC( r, lTrue, lFalse): if r > 0 then { r -= 1; goto lTrue } else { goto lFalse }`
  - `HALT`

A state is a pair `(l, rv)` where `l` is a label (`∈ L`) and `rv: R → ℕ` is a function that gives the value stored in each registers.

The semantics of the instructions is given in the pseudo-code above.

Minsky machines with at least 2 registers are known to be Turing-complete.
This means that the halting problem for Minsky machines is undecidable.

### From Minsky machines to Petri nets with inhibitory edges

* Give an example that shows inhibitory edges are not monotonic.
* Give a reduction from Minsky machines to Petri nets with inhibitory edges and show that the reachability problem for Petri nets with inhibitory edges is undecidable.
