# Homework 11

_Instructions_
* Due on January 31.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


## Extending the π-calculus with guards

Let us extends the π-calculus with a new kind of actions: `[x=y]` and `[xِ≠y]`.

Intuitively, a guard allows a process to continue only if the (dis)equality is satisfied.
Otherwise, it blocks.

The semantics gets extended with the following two rules:

```
───────────────
[x=x].P  ─τ→  P
```

```
───────────────
[x≠y].P  ─τ→  P
```

Here are two an examples:
* Consider the process and reduction step: `!x(y).0 | ?x(a).[a!=x].0  →  0 | [y≠x].0  →  0 | 0`
* Consider the process and reduction step: `!x(x).0 | ?x(a).[a!=x].0  →  0 | [x≠x].0` (stuck)

Is it possible to adapt depth-bounded processes to allow guards? (does the guards preserve the monotonicity?)
If yes, explain the argument (proof sketch).
If no, give an example which breaks monotonicity.



## Types and processes


### Typing names

Let us look at two close variations of definitions with the same identifiers:
* 1st version:
  ```
  A(a, b) ≝ !a(b).A(a, b) + !b(a).A(a, b)
  B(x, y) ≝ ?x(y).B(x, y) + ?y(x).B(x, y)
  ```
* 2nd version:
  ```
  A(a, b) ≝ !a(b).A(a, b) + !b(a).A(a, b)
  B(x, y) ≝ ?x(y).B(x, y) + ?y(x).B(y, x)
  ```
  The `x`, `y` names are swapped for the 2nd call to `B`.

These definitions are used in the configuration `(ν n m)( A(n,m) | B(n,m) )`.

1. Give types and types annotations such that it is well typed using both versions of the definitions.
2. Give types and types annotations such that it is well typed using with the 1st version and does not type with the 2nd version.

For each type, you need to five the subject and object sorts.
The parts that need type annotations are `A(a:t₁, b:t₂)`, `B(a:t₃, b:t₄)`, and `(ν n:t₅ m:t₆)` (some types can by the same different names).


### Corner case for binary session types

Consider the following definition:
```
A ≝ τ.A
B ≝ ?x.0
```
and in the configuration `A | B`.

It is possible to find dual types for the processes `A` and `B`?
Is there more than one solution?
Justify

(Do you think it makes sense?)
