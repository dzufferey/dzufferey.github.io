# Solution 11


## Extending the π-calculus with guards

Yes, it is still monotonic.
We saw in [notes 11](../notes_11.md) that generating the graph rewriting rules already need to case split on whether names are equal or different.

For a transition of the form `P(x,y) ≝ [x=y].Q(x,y)` we have
```
       _________________
      /                 \
     P                   Q
 x,y │         →     x,y │
     ●                   ●
      \_________________/
```
for `P(x,y) ≝ [x≠y].Q(x,y)`:
```
        _________________
       /     ____________\______
      /  x  /             \   x \
     P─────●               Q─────●
   y │            →      y │
     ●                     ●
      \___________________/
```


## Types and processes

### Typing names

1. We can use a generic type for the monadic π-calculus.
  We use the type definition `(NAME, (NAME))` and every name has the type `NAME`.

2. Here we need a finer type distinctions.

  We can use the following type definitions:
  * `(α, (β))`
  * `(β, (α))`

  And the type annotations:
  * `A(a: α, b: β)`
  * `B(x: α, y: β)`


### Corner case for binary session types

The process `B` has type `?t;end` where `t` is the type of `x`

The process `A` can have any type and in particular it can have `!t;end`.

Does it make sense? Yes.
A non-terminating process can have any type as it never returns.
The same occurs with normal type systems, e.g., [Scala nothing type](http://www.scala-lang.org/files/archive/spec/2.12/03-types.html#conformance) for exceptions.
