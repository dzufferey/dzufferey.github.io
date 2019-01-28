# Solutions 5

## Monotonicity of Petri net extensions

Remember that Petri nets respect strong compatibility and therefore they respect stuttering compatibility.
Also they respect strict compatibility and since $\leq$ is partial order, they respect compatibility.
Therefore in the following we only consider the case when $x_1 \rightarrow x_2$ with the special edge.
Therefore suppose markings $x_1, x_2, y_1$ such that $x_1 \rightarrow x_2$ and $x_1 \leq y_1$ then we have to show that the proper marking $y_2$ exist.

#### Reset nets

A reset net respects _strong_ compatibility, because if $x_1 \rightarrow x_2$ then the marking of the place affected by reset net in $x_2$ is $0$ which is less than or equal to any possible marking of $y_2$.
As a result it respects _stuttering_ compatibility and compatibility.

However it doesn't respect _strict_ compatibility.
Consider the reset net we saw in exercise 4 (`⥇` represent the reset edge):

* $x_1$
  ```
  (∙)       ( )
      ↘   ↗
  (∙) ⥇ |
  ```

* $y_1$
  ```
  (∙)       ( )
      ↘   ↗
  (:) ⥇ |
  ```

After firing the transition on both $x_1$ and $y_1$ we get:
```
( )       (∙)
    ↘   ↗
( ) ⥇ |
```

So $x_2 = y_2$ which is not strict ($x_1 < y_1$).


#### Transfer nets

A transfer net respects _strong_ compatibility because the transfer net which cause $x_1 \rightarrow x_2$ affects two places, lets call them $p_1$ and $p_2$.
$x_2(p_1) = 0$ therefore $x_2(p_1) \leq y_2(p_1)$ for any $y_2(p_1)$.
$x_2(p_2) = x_1(p_2) + x_1(p_1)$.
Therefore, if $x_1 \leq y_1$ we have $x_2 \leq y_2$ and as a result _stuttering_ compatibility and compatibility.
And if $x_1 < y_1$ we have $x_2 < y_2$ and, as a result, _strict_ compatibility.

#### Inhibitory nets

An inhibitory net doesn't respect any kind of compatibility because of the nature of inhibitory edge which blocks a transition until the corresponding place is empty.
Therefore a transition may not be available to a larger marking.

## Some more WQOs

#### Lexicographic order

Suppose $X = (\\{0, 1 \\}, ≥)$ with $1 > 0$.

Infinite decreasing sequence: $1$, $01$, $001$, $0001$, ...


#### Sub-word order

Suppose $X = (\\{a, b, c \\}, =)$ therefore every letter is comparable with itself only.

Infinite incomparable sequence: $abc$, $abbc$, $abbbc$, $abbbbc$, ...


#### Embedding with groups of size $k$

This is not even an quasi order as it is not transitive: $12 \leq_{em2} 0120$ and $0120 \leq_{em2} 01020$ but $12 \leq_{em2} 01020$ doesn't hold.


#### Finite multiset embedding

This is a WQO.

The idea to prove is that we should map the multiset to some structure that is WQO and, therefore, show the finite multiset embedding contains a WQO.

One way to to that is first we equip the set of element with some ordering.
For instance, consider the multiset $\\{a, a, a, b, c, c \\}$.
We can fix the ordering $a>b>c$.

Now there is bijection between the mentioned multiset and the word $(a,3)(b,1)(c,2)$.
Notice that when a word embeds into an other word, the corresponding multisets also embed.

Note that we consider $(a,3)$ to be one letter.
Since the set of letters is WQO ($X$ is finite) and set of numbers is WQO then by Dickson's lemma the pairs of letter+number is a WQO.
Finally, we compare the strings by embedding which is a WQO according to Higman's Lemma.
