# Homework 9

_Instructions_
* Due on January 17.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


## Structural congruence, definitions, and bisimulation in CCS

We saw that structural congruence (`≡`) is a bisimulation.
However, it does not say anything about definitions.

Consider the definitions:
```
A(x,y) ≝ !x.?y.A(y,x)
B(x,y) ≝ !x.?y.B(y,x)
```
They are obviously equivalent.
But we cannot show that using `≡`.

Let us discuss how we can combine bisimulations to obtain new bisimulations.
Then, we can combine `≡` with a lemma about `A` and `B`.

For this exercise, the domain of the bisimulations are CCS processes for both the left-hand-side and right-hand-side of the relations.
For instance, `≡` is one such bisimulation.

1. Given two bisimulation `R₁` and `R₂` show that the relation `R₁ ∪ R₂` is also a bisimulation.
2. If `R` is a bisimulation, show that `R⁻¹` (inverse) and `R*` (transitive closure) are also bisimulations.
3. Give a bisimulation `R` which contains `R(A(x,y), B(x,y))`.
   Explain what `R` must contain beyond `R(A(x,y), B(x,y))`.
   (Hint: after taking a step, the result must again be in `R`).
4. Use what you did above and `≡` to show that the two following processes are bisimilar:
  * `τ.(B(a, b) | (ν x) A(x, a))`
  * `(ν y z) (!y.0 | τ.A(a, b))`



## ν-free CCS

For the encoding of Minsky machines in CCS, we used definitions that include restriction (`ν`) on the right-hand-side.

The ν-free CCS is a subset of CCS which disallow `ν` in definition.
Concretely, it means that the number of name is a system is bounded by the names in the initial state/process.
Some names can become dangling (no process uses them anymore), but it is not possible to create new names.


### Petri net counter in ν-free CCS

Petri Nets can "count" but it is not possible to test for `0`.
Let call such counter a _Petri net counter_.

If we allow infinitely many definitions it can be encoded in CCS as
```
C₀ ≝ ?inc.C₁
C_n ≝ ?inc.C_{n+1} + ?dec.C_{n-1}
```

Give an encoding of Petri net counter in the ν-free CCS using _finitely many_ definitions.


### [Optional] Reducing the ν-free CCS to Petri net

Give a reduction from the ν-free CCS to Petri net.

You reduction takes as input:
* a finite set of definition of the form: `P(a) ≝ ∑_i π_i. ∏_j P_{ij}(a_{ij})` (sum of prefix followed by parallel composition).
* a configuration of the form: `(ν a₁ a₂ … a_m) P₁(…) | P₂(…) | … | P_n(…))`
* a definition name `P` to cover (the system can reach a configuration that contains `P`: `(ν a₁ a₂ … a_m) … | P(a) | …`).



## Generalized handover protocol in the π-calculus

Consider the handover example (motivating example) at the beginning of [notes 10](../notes_10.md).

Generalize to have the following
* Have the example work with a fixed number of base station `N`.
  You can use parameterized equations, e.g.,  `P_i(…) = …` where you can use `i` in the right hand side (for list of name, sum, and parallel composition).
* Instead of the base station having channels pairs (`talk`, `switch`), the `Center` should keep available channel stored in a queue, and, for each handover, it picks some available channels and forward them to the base stations when it becomes active.

