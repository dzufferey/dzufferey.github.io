# Solutions 9

## Structural congruence, definitions, and bisimulation in CCS


1. In two steps:
  - `R₁ ∪ R₂` is a simulation:
    * applying the definitions of simulation on `R₁ ∪ R₂` gives `(R₁ ∪ R₂)(x, y) ∧ →(x, a, x′) ⇒ ∃ y′. →(y, a, y′) ∧ (R₁ ∪ R₂)(x′, y′)`.
    * the rest of the proof follows by case splits on `∪`.
  - `(R₁ ∪ R₂)⁻¹` is a simulation using the same and the fact that `R₁⁻¹` and `R₂⁻¹` are simulation.
2. Let us look at the two parts:
  - `R⁻¹` is a bisimulation by applying definition of bisimulation and `(R⁻¹)⁻¹ = R`
  - For the transitive closure, we can
    * base case: the identity relation is a bisimulation therefore, `R⁰` is a bisimulation.
    * induction step: `R^{i+1} = { (x,z) | ∃ y. R^i(x,y) ∧ R(y,z) }` is a bisimulation assuming `R^i` is a bisimulation.
      ... ommitting the details ...
3. `R = {(A(x,y), B(x,y)), (?y.A(y,x), ?y.B(y,x)), (A(y,x), B(y,x)), (?x.A(x,y), ?x.B(x,y))}`
4. First we look at the first process
  * `τ.(B(a, b) | (ν x) A(x, a))`
  * `τ.(B(a, b) | (ν x) !x.?y.A(a, x))` by `≡`
  * `τ.(B(a, b) | 0)` by `≡`
  * `τ.B(a, b)` by `≡`

  Then we look at the second process
  * `(ν y z) (!y.0 | τ.A(a, b))`
  * `(ν y) (!y.0 | τ.A(a, b))` by `≡`
  * `(ν y) !y.0 | τ.A(a, b)` by `≡`
  * `τ.A(a, b)` by `≡`

  Then we combine the 2 formula
  * `τ.A(a, b) ≡ τ.B(a, b)` if
  * `A(a, b) ≡ B(a, b)` by `R`

  Here we mix `≡` and `R`, to be more accurate we should define a new relation which contains both `≡` and `R`.



## ν-free CCS

### Petri net counter in ν-free CCS

To simulate a Petri net counter, we encode the value of the counter in the number of `?dec.0` processes.
Incrementing the counter create one `?dec.0` and decrementing consume one such process.

Here is the definition:
```
counter ≝ ?inc.(counter | ?dec.0)
```

Compared to the version with infinitely many definition we have `C_n` and `(counter | ∏_n ?dec.0)` are bisimilar.

### [Optional] Reducing the ν-free CCS to Petri net

Let `𝓓` be the definitions and `𝓒` the configuration.

The reduction follows the steps:
1. collect the names in `𝓒` in a finite set `N`
2. For each definition in `𝓓` instantiate the parameters of the definition with the names in `N`.
   If the definition has `p` parameters this creates `N^p` instances of the definition.
3. Create one place in the Petri net for each instance generated in step 2.
4. For every instance, check in the definition contains `τ. ∏_j P_{i}(a_{i})` (internal transition).
   If yes, create a transition that consumes one token in the place corresponding to the instance and produces one token each place corresponding to `P_{i}(a_{i})` (with the instantiated names).
5. For every pair of instances, check by expending the definition if one (or more) synchronization can happen.
   If yes, add the resulting transition to the Petri net: (a) consumes tokens in the two places corresponding to the instances which synchronize and (b) produces tokens in the places corresponding to the suffix of the process where the synchronization happened.
6. From the configuration `𝓒` create the initial marking by putting tokens in the appropriate places.
