# Petri Nets Continued...

_Assumptions._
For this part, we assume a non-trivial connected Petri Net $N = (S,T,W,M₀)$,
$C$ is the connectivity matrix,
$n = |S| ≥ 1$, and
$m = |T| ≥ 1$.

_Non-trivial net._
A Petri net is _non-trivial_ iff there is at least one place and one transition.

_Connected net._
A Petri net is _connected_ iff the graph defined by $W$ has a single connected component.

These two assumptions are needed otherwise some elements like the connectivity matrix are ill-defined and some results do not hold.
Trivial nets are easy to analyze on their own and for the case of _not_ connected nets it is possible to analyze the connected components separately.


## Structural properties

For the structural properties of Petri nets, you can find more detailed definitions and complete explanations in the [lecture notes by Roland Meyer](https://www.tcs.cs.tu-bs.de/documents/ConcurrencyTheory_WS_20112012/lecture_notes.pdf):
* 2.2 Invariants


### Invariants

An _invariant_ is a predicate which is true for any reachable state of a Petri net.

An invariant must be preserved by all the transitions in the net.
(Assuming every transition fires at least once.)

### Structural invariants

An invariant is _structural_ iff it can be expressed as vector in $I ∈ ℚ^n$ and $I^T \cdot C = 0$ (note that here $0 \in Q^m$).

$I$ is a vector of coefficients for each place such that the transition $M [〉 M'$ preserves the number of tokens with $I$ as weights: $I^T \cdot M = I^T \cdot M' $.

#### Example

Let us consider the lock example:
```graphviz
digraph PN{
  rankdir=LR
  ranksep=0.75;
  node [shape = circle, fixedsize = true, width = 0.5, fontsize = 15];
  p1 [label="∙", xlabel="u" ];
  p2 [label="", xlabel="l" ];
  node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15, fontsize=15];  
  t1[xlabel="lock"];
  t2[xlabel="unlock"];
  p1 -> t1;
  t1 -> p2;
  edge [style = invis];
  p1 -> t2;
  t2 -> p2;
  edge [style = default, constraint = false];
  p2 -> t2;
  t2 -> p1;
}
```

With
$
C = \begin{bmatrix} -1 &  1 \\\\ 1 &-1 \end{bmatrix}
$

$I^T = \begin{bmatrix}1 \\\\ 1\end{bmatrix}$ is a structural invariant.
For any reachable $M$, we have $M(u) + M(l) = I^T \cdot M₀ = 1$.

__Theorem.__
Let $I$ be a structural invariant of $N$.
For any reachable marking $M ∈ R(M₀)$, $I^T \cdot M = I^T \cdot M₀$.

_Proof._
* Let $\pi$ be the trace from $M₀$ to $M$, i.e., $M₀ [π〉M$.
* We have that $M = M₀ + C \cdot \mathit{Parikh}(\pi)$.
* Multiplying both sides by $I^T$ gives $I^T \cdot M = I^T \cdot (M₀ + C\cdot \mathit{Parikh}(\pi))$.
* Distributing $\cdot$ over $+$ gives $I^T \cdot M = I^T \cdot M₀ + I^T \cdot C\cdot \mathit{Parikh}(\pi)$.
* By definition of $I$, we have $I^T \cdot C = 0$ and, thus, $I^T \cdot C\cdot \mathit{Parikh}(\pi) = 0$.
* This simplifies the equation to $I^T\cdot M = I^T\cdot M₀$.

__Corollary.__
If $I$ is a structural invariant of $N$, $M$ a marking of $N$, and $I^T \cdot M \neq I^T \cdot M_0$, then $M$ is not reachable.

#### Example

Let consider a sightly simplified version of our running example:
```graphviz
digraph PN {
    rankdir=LR;
    node [shape = circle, fixedsize = true, width = 0.5];
    p1 [ xlabel="U", label="∙" ];
    p2 [ xlabel="L", label="" ];
    p3 [ xlabel="0", label="" ];
    p4 [ xlabel="1", label="" ];
    p5 [ xlabel="2", label="" ];
    node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15];
    t1 [xlabel="lock" ];
    t2 [xlabel="unlock" ];
    t4 [xlabel="spawn" ];
    t5 [xlabel="exit" ];
    t4 -> p3;
    p1 -> t1 [ constraint = false ];
    p3 -> t1;
    t1 -> p2;
    t1 -> p4;
    p2 -> t2;
    p4 -> t2;
    t2 -> p1 [ constraint = false ];
    t2 -> p5;
    p5 -> t5;
    p3 -> p1 [ style = invis];
}
```

With the ordering on the places be $(U, L, 0, 1, 2)$, and the ordering on transitions $(\mathit{lock}, \mathit{unlock}, \mathit{spawn}, \mathit{exit})$, we have

$C =
\begin{bmatrix}
-1 & 1 & 0 & 0 \\\\
1 & -1 & 0 & 0 \\\\
-1 & 0 & 1 & 0 \\\\
1 & -1 & 0 & 0 \\\\
0 & 1 & 0 & -1
\end{bmatrix}$

$I^T = \begin{bmatrix}1 & 0 & 0 & 1 & 0\end{bmatrix}$ is a structural invariant and we have that $I^T\cdot M₀ = 1$.

We can use that to conclude that there is at most 1 token in place $1$ and, therefore, mutual exclusion is preserved.


## Monotonicity

Until now, we only saw sufficient but not necessary conditions to check properties of Petri nets.
We will now introduce some complete procedure for termination, boundedness, and termination.

### Ordering on markings

- $N ≥ M$ iff $∀ s.\ N(s) ≥ M(s)$
- $N > M$ iff $∀ s.\ N(s) ≥ M(s) ∧ ∃ s.\ N(s) > M(s)$

$\geq$ is not a total order.
For instance, $(0,1)$ and $(1,0)$ are not comparable.

### Definition of monotonicity

_Observation._
Consider $M [t〉 M'$ and $N \geq M$.
$t$ is also enabled at $N$ and, if we fire $t$, we get $N [t〉 N'$ with $N' ≥ M'$.

__Theorem.__
$M [t〉M'  ⇒  (M+N) [t〉 (M'+N)$


More abstractly, monotonicity is usually represented using the following illustration:
```
∀ M, M′, N.    M  ≤  N
∃ N′.          ↓     ↓
               M′ ≤  N′
```
Put differently, $\leq$ is a simulation relation.
Larger states can simulate smaller ones.
By "simulate", we mean can take the same transitions (and maybe even more).



### Finite reachability tree

Algorithm to decide if a Petri net always terminates:

```c
TerminationCheck(S,T,W,M₀)
    F := {M₀}    // frontier
    E := {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F := F ∖ {M}
        ancestors := { A | A can reach M in E }
        if ∃ A ∈ ancestors. A ≤ M
            return NON-TERMINATING
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E := E ∪ { (M,t,M′) }
                F := F ∪ M′
    return TERMINATING
```

#### Example

Consider the following net:
```graphviz
digraph PN{
  rankdir=LR
  ranksep=0.75;
  node [shape = circle, fixedsize = true, width = 0.5, fontsize = 15];
  a [label=" " ];
  b [label=" " ];
  c [label=" " ];
  d [label=" " ];
  m [label="∙" ];
  node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15, fontsize=15];
  t1 [xlabel = "t₃"];
  t2 [xlabel = "t₂"];
  t3 [xlabel = "t₅"];
  t4 [xlabel = "t₆"];
  t5 [xlabel = "t₄"];
  t6 [xlabel = "t₁"];
  a -> t1;
  t1 -> b;
  c -> t3;
  t3 -> d;
  m -> t5;
  t5 -> c;
  b -> t6 [dir=both,arrowhead=none,arrowtail=normal];
  t6 -> m [dir=both,arrowhead=none,arrowtail=normal];
  edge [style = invis];
  a -> t2;
  t2 -> b;
  c -> t4;
  t4 -> d;
  edge [style = default, constraint = false];
  b -> t2;
  t2 -> a [xlabel = "2"];
  d -> t4;
  t4 -> c;
}
```
We order the state from left to right.
For conciseness, we write vector horizontally.
For instance, the initial state is `(0 0 1 0 0)`.

Let us call the transitions:
* `t₁ = ( 0  1 -1  0  0)`
* `t₂ = ( 2 -1  0  0  0)`
* `t₃ = (-1  1  0  0  0)`
* `t₄ = ( 0  0 -1  1  0)`
* `t₅ = ( 0  0  0 -1  1)`
* `t₆ = ( 0  0  0  1 -1)`

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0) NON-TERMINATING with t₄ (t₅ t₆)*
(0 0 1 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0)
```

#### Claims

* `TerminationCheck` terminates
* When `TerminationCheck` returns `NON-TERMINATING` we can extract a lasso-shaped trace where the stem starts from `M₀` and the loop is a non-decreasing cycle.
* When `TerminationCheck` returns `TERMINATING` we can extract a finite tree which contains all the reachable states.

Let us look in more details at the first one:
* If the algorithm does not terminate we have an infinite sequence of markings $\mathcal{M}$ such that $∀ i, j.\ i ≤ j ⇒ \mathcal{M}[i] > \mathcal{M}[j] ∨ \mathcal{M}[i] ~\text{incomparable with}~ \mathcal{M}[j]$.
* This is not possible if
  1. there is no infinite decreasing chain, and
  2. there is no infinite antichain (sequence where all the elements are incomparable).
* In a decreasing chain, at each step at least one of the places must have less token. Since we have a finite number of places and we cannot have negative token, it is not possible to decrease forever.
* In an antichain, all the states are incomparable... next week when we discuss well-quasi-order this will follow easily.


### Boundedness

The Petri net are strictly monotonic:
```
∀ M, M′, N.    M  <  N
∃ N′.          ↓     ↓
               M′ <  N′
```
and we can modify the algorithm to decide boundedness.

```c
BoundednessCheck(S,T,W,M₀)
    F := {M₀}    // frontier
    E := {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F := F ∖ {M}
        ancestors := { A | A can reach M in E }
        if ∃ A ∈ ancestors. A < M
            return UNBOUNDED
        else if ∃ A ∈ ancestors. A = M
            skip
        else
            for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
                E := E ∪ { (M,t,M′) }
                F := F ∪ M′
    return BOUNDED
```

#### Example

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0)
(0 0 1 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0) → (1 1 0 0 0) UNBOUNDED with t₁ (t₂ t₃)*
```

#### Claims

* `BoundednessCheck` terminates
* When `BoundednessCheck` returns `UNBOUNDED` we can extract extract a lasso-shaped trace where the stem starts from `M₀` and an increasing cycle.

### Karp-Miller tree

Let us generalize the algorithms above to decide coverability.

We need to introduce a _limit element_ $ω$ that represent an "unbounded" number of tokens.
$ω$ has the following properties:
* $ω = ω$, $ω = ω+1$, $ω = ω-1$
* $ω > n$ for any finite $n$

We can also extend markings to _generalized markings_ which are function from $S → ℕ ∪ \\{ω\\}$.


_Acceleration._
Given $M$ and $M'$ with $M' > M$, we return $M″$ such that:
* $M″(s) = M(s)$ if $M(s) = M'(s)$
* $M″(s) = ω$ if $M'(s) > M(s)$


```c
KarpMillerTree(S,T,W,M₀)
    F := {M₀}    // frontier
    E := {}      // edges in the reachability tree
    while F ≠ ∅  do
        choose M in F
        F := F ∖ {M}
        for each t ∈ T with t enabled at M and M′ such that M [t〉 M′
            ancestors :=  { A | A can reach M in E } ∪ M
            M′ := accelerate(ancestors, M′)
            E := E ∪ { (M,M′) }
            if ∀ A ∈ ancestors. not(A ≥ M′) 
                F := F ∪ {M′}
    return E

accelerate(ancestors, M)
    while ∃ A ∈ ancestors. A < M ∧ accelerate1(A, M) ≠ M do
        M := accelerate1(A, M)
    return M

accelerate1(M₁, M₂)
    M := empty marking
    for (s ∈ S))
        if (M₁(s) < M₂(s))
            M(s) := ω
        else
            M(s) := M₂(s)
    return M
```

#### Example

Applying the algorithm gives:
```
            ↗ (0 0 0 1 0) → (0 0 0 0 1) → (0 0 0 1 0)
(0 0 1 0 0)                                           ↗ (ω ω 0 0 0) → (ω ω 0 0 0)
            ↘ (0 1 0 0 0) → (2 0 0 0 0) → (ω 1 0 0 0) → (ω ω 0 0 0) → (ω ω 0 0 0)
```

#### Claims

* The Karp-Miller tree is finite.
* The `KarpMillerTree` procedure terminates.
* For any $M$, if there is $M'$ in `KarpMillerTree(`$N$`)` with $M ≤ M'$ then $N$ can cover $M$.

#### A bounded and terminating example

```
a (∙) ( ) b
   ↓ ⤱ ↓
   −   −
   ↑ ↘ ↑ ↘
  (:) ( ) ( ) → |
   c   d   e
```

We get the following tree:
```
(1 0 2 0 0) → (0 1 1 1 0) → (1 0 1 0 1) → (0 1 0 1 1) → (1 0 0 0 2) → (1 0 0 0 1)
                                        |             ↘ (0 1 0 1 0)
                                        ↳ (1 0 1 0 0)
```


## How big can a bounded Petri net be?

### 

### Vector Addition System with States (VASS)

For the first example, we will use a sightly different notation as it makes the example easier to explain.
Instead of Petri nets, we use Vector addition system with states (VASS).
VASS are extensions of states machines with counters.

__Definition.__
A VASS $V$ is a 4-tuple $(Q, n, δ, i₀)$ where
* $Q$ is a finite set of states
* $n$ is the dimension of the VASS (number of counters)
* $δ$ is the transition relation ($Q × ℤ^n × Q$)
* $i₀$ is the initial state and value of the counters ($i₀ ∈ Q×ℕ^n$)

A transition $(q,v,q')$ can be applied to a state $(x,y)$ if $x=q$ and $v+y ≥ 0$.
It results in the new state $(q',v+y)$.
We write the transition $(q,y)→(q',v+y)$.

_Example._
Consider the following 2 dimensional VASS
```graphviz
digraph vass {
	rankdir=LR;
	node [shape = circle];
	init [shape = none, label = ""];
    init -> a;
	a -> b [ label = "(-1,1)" ];
	b -> a [ label = "(0,0)" ];
	a -> a [ label = "(1,0)" ];
}
```
and the initial state $(a, (0,1))$:
- the transition to $b$ is not possible as $(0,1) + (-1,0) = (-1,1)$ which is not $≥ 0$.
- the loop to $a$ can be taken and gives a new state $(a, (1,1))$

__Claim.__
VASS are equivalent to Petri nets.
One can be reduced to the other and vice-versa.

### Tower of exponential

Let use a VASS such that the run with the highest counter value is a tower of exponential: $\underbrace{2^{2^{\cdot^{\cdot^{\cdot^{n}}}}}}_{m}$.

First, let us build a gadget to do one expenential.
Consider the following VASS:
```graphviz
digraph vass {
	rankdir=TD;
	node [shape = circle, label = ""];
    subgraph top {
	    rank = same;
	    init_a [shape = none, label = ""];
        init_a -> a_a;
	    a_a:ne -> a_a:nw [ label = "(-1, 1, 0)" ];
	    a_a -> b_a [ label = "( 0, 0, 0)" ];
        b_a -> a_a [ label = "( 0, 0,-1)" ];
        b_a -> b_a [ label = "( 2,-1, 0)" ];
    }
}
```

If the VASS start with counter values $(1,0,n)$, it can reach the counter values $(2^n,0,0)$.

Then we can chain this gadget to apply multiple time the exponential:
```graphviz
digraph vass {
	rankdir=TD;
	node [shape = circle, label = ""];
    subgraph top {
	    rank = same;
	    init_a [shape = none, label = ""];
        init_a -> a_a;
	    a_a:ne -> a_a:nw [ label = "(-1, 1, 0)" ];
	    a_a -> b_a [ label = "( 0, 0, 0)" ];
        b_a -> a_a [ label = "( 0, 0,-1)" ];
        b_a -> b_a [ label = "( 2,-1, 0)" ];
    }
    subgraph bottom {
	    rank = same;
	    init_b [shape = none, label = ""];
        init_b -> a_b [ style=invis ];
	    a_b:nw -> a_b:sw [ label = "( 0, 1,-1)" ];
	    a_b -> b_b [ label = "( 0, 0, 0)" ];
        b_b -> a_b [ label = "(-1, 0, 0)" ];
        b_b -> b_b [ label = "( 0,-1, 2)" ];
    }
	a_a -> a_b [ label = "(0,0,1)" ];
	down [shape = none, label = "..."];
    a_b -> down [ label = "(1,0,0)" ];
}
```

Staring with $(1,0,n)$, the first stage reaches $(2^n,0,0)$, the second stage gets to $(0,0,2^{2^n})$, etc.

To compute $\underbrace{2^{2^{\cdot^{\cdot^{\cdot^{n}}}}}}_{m}$, we use $3$ counters, $2m$ control state, and $n+1$ as the value of the counter in the initial state.

In this example, we get larger values by increasing the number of state.
However, the number of counters is constant.
We can do better be increasing the number of counters as well.

Here is a version with a 4th counter:
```graphviz
digraph vass {
	rankdir=TD;
	node [shape = circle, label = ""];
    subgraph top {
	    rank = same;
	    init_a [shape = none, label = ""];
        init_a -> a_a;
	    a_a:ne -> a_a:nw [ label = "(-1, 1, 0, 0)" ];
	    a_a -> b_a [ label = "( 0, 0, 0, 0)" ];
        b_a -> a_a [ label = "( 0, 0,-1, 0)" ];
        b_a -> b_a [ label = "( 2,-1, 0, 0)" ];
    }
	a_a -> a_b [ label = "( 0, 0, 0, 0)" ];
    a_b -> a_b [ label = "(-1, 0, 1, 0)" ];
    a_b -> a_a [ label = "( 1, 0, 0,-1)" ];
}
```

Each time we consume a token in the 4th counter we can transfer the token from the 1st to the 3rd counter.
Therefore, we get $\underbrace{2^{2^{\cdot^{\cdot^{\cdot^{n}}}}}}_{m}$, starting with counter value $(1,0,n,m)$.

We can simplify that to only have one parameter and get $\underbrace{2^{2^{\cdot^{\cdot^{\cdot^{2}}}}}}_{m}$, starting with counter value $(0,0,0,m+1)$.

### Ackerman function

Let us use the previous idea to build a VASS which generate even larger values.

The goal is to "compute" [Ackerman function](https://en.wikipedia.org/wiki/Ackermann_function).

Ackermann function is defined as:

$
A(m, n) =
\left\\{
\begin{array}{ll}
  n+1 & \text{if } ~ m = 0 \\\\
  A(m-1, 1) & \text{if } ~ m > 0 ∧ n = 0 \\\\
  A(m-1, A(m, n-1)) & \text{if } ~ m > 0 ∧ n > 0
\end{array}
\right.
$

It is simple to see that unfolding the recursive definition always terminates.
Either $m$ get smaller or $m$ stays constant and $n$ decreases.
However, the value returned by the function is mindbogglingly huge!
Ackermann function belongs to the class of non-primitive recursive functions.

The idea is to use a construction similar to the one above: start with a simple operation and around to call this operation many time.
In our construction, we us a gadget for each value of $m$.
Each gadget has
* an "in" counter,
* a "start" state, and
* a "stop" state.

Furthermore there is an "out" counter shared by all the gadgets.
We write $(in_m,in_{m-1},…,in_0,out)$

The first gadget we use is for $A(0,n) = n+1$:
```graphviz
digraph vass {
	rankdir=LR;
	init [shape = none, label = ""];
    a [label = "start"];
    b [label = "stop"];
    init -> a;
	a -> a [ label = "(-1, 1)" ];
	a -> b [ label = "( 0, 1)" ];
}
```

Then, for the following gadgets we can the fact that $A(m+1,n) = \underbrace{A(m,A(m,…,A(m,}_{n+1} 1)…))$.

Using the $m$th gadget, the construction for the $m+1$th gadget is:
```graphviz
digraph vass {
	rankdir=LR;
    subgraph cluster_inner {
        color=grey;
        start_inner [label = "start'"];
        stop_inner [label = "stop'"];
	    start_inner -> stop_inner [ color=gray, style=dotted ];
    }
	init [shape = none, label = ""];
    start_outer [label = "start"];
    stop_outer [label = "stop"];
    copy [label = ""];
    init -> start_outer;
    start_outer -> start_inner [label = "(0,1,…,0)"];
    start_inner -> copy [xlabel = "(0,0,…,0)",dir=both,arrowhead=none,arrowtail=normal];
    stop_inner -> stop_outer [label = "(0,0,…,0)"];
    stop_inner -> copy [xlabel = "(-1,0,…,0)", constraint = false];
    copy -> copy [label = "(0,1,…,-1)"];
}
```

To compute $A(m,n)$ the construction uses $3m+2$ control state, $m+1$ counters, and $m$,$n$ are part of the initial counter values.


An alternative encoding purely based on Petri nets can be found in Section 1.2 of the [lecture notes by Roland Meyer](https://www.tcs.cs.tu-bs.de/documents/ConcurrencyTheory_WS_20112012/lecture_notes.pdf).
