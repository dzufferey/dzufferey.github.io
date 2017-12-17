# Calculus of Communicating Systems (CCS)

Until now we have focused on state/automata─based models of concurrent systems.
Process calculi (CCS, CSP, π─calculus) provide an alternative approach to model concurrent system.

A key element of CCS is the distinction between _names_ and _process_.
_Names_ are channels and they are orthogonal to processes, e.g., a process can send or receive messages from _any_ name in its scope.
In the world of CSM, only a single process can receive from a channel.

You can find more information in the [notes on CCS by Emanuele D’Osualdo](https://www.tcs.cs.tu─bs.de/documents/ConcurrencyTheory_WS_20162017/ccs.pdf).

__Example.__

Let us revisit the ping─pong example and express it in CCS:
* ping:
  ```
    →  (init)
  ?Pong ↑ ↓ pong!Ping
       (wait)

  ```
  becomes `ping() ≝ !Ping.?Pong.ping()`
* pong:
  ```
       →  (init)
  ping!Pong↑ ↓ ?Ping
          (ack)
  ```
  becomes `pong() ≝ ?Ping.!Pong.pong()`

Furthermore, CCS allows us the processes to be parametric in the name they use:
```
ping(x,y) ≝ !x.?y.ping(x,y)
pong(x,y) ≝ ?x.!y.pong(x,y)
```
We have seen how to define processes.
Now we can compose them together: `ping(a, b) | pong(a,b)`.

This is equivalent to `!a.?b.ping(a, b) | ?a.!b.pong(a,b)`.

Reduction synchronizes the sends (`!`) and receive (`?`).

```
!a.?b.ping(a, b) | ?a.!b.pong(a,b)  →  ?b.ping(a, b) | !b.pong(a,b)  →  ping(a, b) | pong(a,b)  →  …
```

We can simplify the definitions even more by factoring out the common part:
```
ping(x,y) ≝ !x.pong(y,x)
pong(x,y) ≝ ?x.ping(y,x)
```


## Syntax

__Process definitions.__
A set of mutually recursive definitions of the form:
```
A(a) ≝ P
```
where
* `A` is the name of the process
* `a` is a list of _names_
* `P` is a process

__Processes.__
```
P ::= π.P       (action)
    | P + P     (choice)
    | P | P     (composition)
    | (νa) P    (restriction)
    | A(a)      (named process, a can be a list of agruments)
    | 0         (end)
```

__Actions.__
```
π ::= !a        (send)
    | ?a        (receive)
    | τ         (silent)
```

_Notations._
* `!a` and `?a` is the CSP notation.
  Most publication on CCS and the π─calculus uses `ā`(`=!a`) and `a`(`=?a`).
* Often `∥` is used instead of `|`
* The binary choice `P+Q` can be generalized to indexed sum `∑_i P_i`.
* For the labelled semantics, we write `─π→` for a transition with the label `π`.


## Free names and bound names

To discuss in more details the equivalence of processes we need to define the set of _free names_ and _bound names_.

The free names (`fn`) are the names that occurs in a processes but are not restricted:
* `fn(0) = ∅`
* `fn(τ.P) = fn(P)`
* `fn(!a.P) = fn(P) ∪ {a}`
* `fn(?a.P) = fn(P) ∪ {a}`
* `fn(P + Q) = fn(P) ∪ fn(Q)`
* `fn(P | Q) = fn(P) ∪ fn(Q)`
* `fn((νa)P) = fn(P) ∖ {a}`
* `fn(A(a)) = {a}`

The dual of free names are bound names (`bn`).
The names occurring under a restriction:
* `bn(0) = ∅`
* `bn(π.P) = bn(P)`
* `bn(P + Q) = bn(P) ∪ bn(Q)`
* `bn(P | Q) = bn(P) ∪ bn(Q)`
* `bn((νa)P) = bn(P) ∪ {a}`
* `bn(A(a)) = ∅`

_Remark._
Computing the free/bound name does not unfold the definitions.
It computes the set of bound/free names for a given formula.
Taking transitions changes the bound/free names.

__Examples.__
* In `!x.0 | ?x.0`, `x` is free and there are no bound name.
  After one step, the process becomes `0|0` which has no name at all.
* `(νx)(!x.0 | ?x.0)` has no free name and `x` is a bound name.
* `(νx)(!x.0) | ?x.0` has `x` both as free name and bound name.
  In that example, `x` represents two different names.
  A simpler way of writing the same process is `(νy)(!y.0) | ?x.0`.

Restriction defines a local scope and the name bound in that scope is not visible to the outside (like a local variable in program).
Processes are equivalent up to renaming of bound names.
Renaming bound names is called α-conversion.

_Substitution._
To rename free names in a formula, we use substitution.
Substitution never change the bound names.
`P[x ↦ y]` is the substitution of free instances of `x` by `y` in `P`.
It is often written as `P[y/x]` in the literature.

For instance, `((νx)(!x.0) | ?x.0)[x ↦ y] = (νx)(!x.0) | ?y.0)`.

__No clash assumption.__
W.l.o.g. we assume that `fn(P) ∩ nb(P) = ∅`.
This prevents the ambiguous case we saw above: `(νx)(!x.0) | ?x.0`.
Using α-conversion, we can always rename the bound names to make bound and free names different.
Is it still possible to bind the same name in parallel: `(νx)(!x.0) | (νx)(?x.0)`.


## Semantics (version 1)

* Action
  ```
  ───────────
  π.P  ─π→  P
  ```
* Choice 1 & 2
  ```
   P ─π→ P′        Q ─π→ Q′ 
  ──────────      ──────────
  P+Q ─π→ P′      P+Q ─π→ Q′
  ```
* Parallel 1 & 2
  ```
    P ─π→ P′          Q ─π→ Q′ 
  ────────────      ────────────
  P|Q ─π→ P′|Q      P|Q ─π→ P|Q′
  ```
* Communication 1 & 2
  ```
  P ─!a→ P′  Q ─?a→ Q′        P ─?a→ P′  Q ─!a→ Q′ 
  ────────────────────        ────────────────────
      P|Q ─τ→ P′|Q′               P|Q ─τ→ P′|Q′
  ```
* Restriction
  ```
  P ─π→ P′  π ≠ !a  π ≠ ?a
  ────────────────────────
      (νa)P ─π→ (νa)P′
  ```
* Definition
  ```
  A(x) ≝ P  P[x ↦ y] ─π→  P′
  ───────────────────────────
        A(x) ─π→  P′
  ```

__Example.__
To create new processes, we can use the parallel composition inside a definition:
```
spawn() ≝ P(…) | spawn()
P(…) ≝ …
```

__Example.__
Choice represents alternatives, or branches.
In the world of CSM, choice is the outgoing edges from a state.

Let us look at a vending machine example:
```
Zero() ≝ ?coin.One()
One() ≝ ?coin.Two() + !water.Zero()
Two() ≝ !coffee.Zero() + !water.One()
```

__Example.__
The silent action `τ` represents internal action, i.e., action that are not precisely observable from the outside.
`τ.0` and `(νx)(?x.0 | !x.0)` are different but from the point of view of an external observer, they behave the same.

The notion of bisimulation we have seen is called _strong_ bisimulation.
It still allows comparing the number of internal steps when comparing processes.

## Internal choice

`τ` is also useful to represent internal choice.
Let us try to have a process that models a coin flip:

```
flip() ≝  !head.0 + !tail.0
gambler() ≝ ?head.0
```

Then in the process `(νhead)(νtail)(flip() | gambler())`, the gambler always win and the process reduces to `0`.

A better model would be
```
flip() ≝  τ.!head.0 + τ.!tail.0
gambler() ≝ ?head.0
```

In that case the process `(νhead)(νtail)(flip() | gambler())` can get to `(νhead)(νtail)(!tail.0 | gambler())` and get stuck.


## Open vs closed world

The semantics above is an _open world_ semantics.
It is possible to make sens/receive steps that are not matched.

For instance, we have `?x.0 ─?x→ 0`.

Similarly, (a) `(νx)(?x.0 | !x.0)` is not the same as (b) `?x.0 | !x.0`:
* (a) only has a single possible transition: `(νx)(?x.0 | !x.0) ─τ→ (νx)(0 | 0)`
* (b) can execute 3 different sequences:
  - `?x.0 | !x.0  ─τ→  0 | 0`
  - `?x.0 | !x.0  ─?x→  0 | !x.0  ─!x→  0 | 0`
  - `?x.0 | !x.0  ─!x→  ?x.0 | 0  ─!x→  0 | 0`

A process `P` is closed if `fn(P) = ∅`.


## Synchronous and asynchronous communication

Exchanging messages is a synchronous operation.
However, it is possible to emulate asynchronous communication without changing the calculus.
In a process by using `!a.0 | Pa instead of `!a.P` we can express asynchronous communication with unbounded and unordered channels.

For instance, the asynchronous version of ping-pong is:
```
ping(x,y) ≝ !x.0 | pong(y,x)
pong(x,y) ≝ ?x.ping(y,x)
```

It is interesting to notice that in CCS, asynchronous communication is a subset of the full calculus.
(`!a` can only be followed by `0`.)


## Alternative views on definitions/recursion

Instead of using a set of mutually recursive definition, it is possible to have a _recursion_ operator.

The process definition get the additional elements:
```
P ::= …
    | μX. P     (recursion)
    | X
```
and `A(a)` is removed.

In the semantics the definition rule is replaced by:
```
P[X ↦ μX.P] ─π→  P′
────────────────
  μX.P ─π→  P′
```

The ping-pong example becomes: `μX.!Ping.?Pong.X | μY.?Ping.!Pong.Y`.


## Structural Congruence

Notice that some reduction rules are _doubled_ to deal with the binary operator and send/receive duality.
It is possible to simplify this if we can factor out simple rewritings that result in bisimilar processes.

The structural congruence relation (`≡`) help simplify the transition rules (and much more).

The congruence is an equivalence relation and, therefore, it respects:
* `P ≡ P`
* `P ≡ Q ⇒ Q ≡ P`
* `P ≡ Q ∧ Q ≡ R ⇒ P ≡ R`

Then there are rules to manipulate the operators:
* actions
  - `P ≡ Q  ⇒  π.P ≡ π.Q`
* `+`
  - `P+P ≡ P`
  - `P+0 ≡ P`
  - `P+Q ≡ Q+P`
  - `(P+Q)+R ≡ P+(Q+R)`
  - `P ≡ Q  ⇒  P+R ≡ Q+R`
* `|`
  - P|0 ≡ P
  - P|Q ≡ Q|P
  - (P|Q)|R ≡ P|(Q|R)
  - `P ≡ Q  ⇒  P|R ≡ Q|R`
* `(νa)`
  - `(νa)(νb)P ≡ (νb)(νa)P`
  - `(νa)(P+Q) ≡ (νa)P + (νa)Q`
  - `a ∉ fn(P) ⇒ (νa)P ≡ P`
  - `a ∉ fn(P) ⇒ (νa)(P|Q) ≡ P | (νa)Q` (scope extrusion)
  - `π ≠ ?a ∧ π ≠ !a ⇒ (νa)π.P ≡ π.(νa)P`
  - `π = ?a ∨ π = !a ⇒ (νa)π.P ≡ 0`
  - `b ∉ fn(P) ∧ b ∉ bn(P) ⇒ (νa)P ≡ (νb)P[a ↦ b]`
  - `P ≡ Q  ⇒  (νa)P ≡ (νa)Q`
* definition
  - `A(x) ≝ P  ⇒  A(y) ≡ P[x ↦ y]`

__Example.__
TODO ...

__Theorem.__
`≡` is a bisimulation, i.e., `P ≡ P′ ∧  P ─π→ Q  ⇒  ∃ Q′. Q ≡ Q′ ∧  P′ ─π→ Q′`.


_Proof Sketch._
...


## Semantics (version 2)

With the congruence relation we can have an alternative and sightly simpler definition of the semantics.

* Action
  ```
  ───────────
  π.P  ─π→  P
  ```
* Choice
  ```
   P ─π→ P′
  ──────────
  P+Q ─π→ P′
  ```
* Parallel
  ```
    P ─π→ P′
  ────────────
  P|Q ─π→ P′|Q
  ```
* Communication
  ```
  P ─!a→ P′  Q ─?a→ Q′
  ────────────────────
      P|Q ─τ→ P′|Q′
  ```
* Restriction
  ```
  P ─π→ P′  π ≠ !a  π ≠ ?a
  ────────────────────────
      (νa)P ─π→ (νa)P′
  ```
* Congruence
  ```
  P ≡ P′  P′ ─π→ Q  Q ≡ Q′
  ────────────────────────
          P ─π→ Q′
  ```

## TODO

Structural congruence is limited to simple rewriting.
In particular, it cannot compare `+` and `|`.
For instance, consider the following two formula: `a.b.0 + b.a.0` and `a.0 | b.0`.

strong ground equivalence
   ≡
   same commitment
   expansion

## Strong and weak bisimulation

τ.P ≡ P  but not as guard for weak simulation

coin example

vending machine with internal state.

## Counting with CCS

Encoding of counters

halting to bisimulation
