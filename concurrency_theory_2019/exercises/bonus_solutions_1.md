# Bonus Solution 1


## Effective Predecessor Basis for LCS

> Give a procedure to compute the predecessor basis for LCS

Given an upward-closed set of state for a LCS, we need to compute the set of predecessors.
We know that upward-closed sets are effectively represented by a finite number of basis elements.
We are going to compute the predecessor of the upward-closure of each basis element.

```
pred-basis(S):
    S' = ∅
    For each (M,C) in basis(S):
        For each i:
            For each s, a, with s \stackrel{j!a}{→_i} M[i]:
                S' = S' ∪ (M[i ← s], C[j ← pred-send(C[j], a))
            For each s, a, with s \stackrel{?a}{→_i} M[i]:
                S' = S' ∪ (M[i ← s], C[i ← pred-receive(C[i], a))
    return S'

pred-send(w, a):
    if w = w'⋅a
        return w'
    else
        return w //because: w⋅a ∈ ↑w

pred-receive(w, a):
    return a⋅w
```

Notice that we never need to drop a message as it leads to a strictly greater configuration and, therefore, does not help in the overall algorithm.
(Local states are unchanged and the channel gets bigger.)

> Apply your algorithm to the following LCS ...
>   ```graphviz
>   digraph finite_state_machine {
>       rankdir=LR;
>       node [shape = circle];
>       init [shape = none, label = ""];
>       init -> X;
>       X -> Y [ label = "?a, ?b" ];
>       Y -> X [ label = "?a" ];
>       Y -> Z [ label = "?b" ];
>       X -> X [ label = "!0" ];
>       Y -> Y [ label = "!1" ];
>   }
>   ```
>   ```graphviz
>   digraph finite_state_machine {
>       rankdir=LR;
>       node [shape = circle];
>       init [shape = none, label = ""];
>       init -> A;
>       A -> B [ label = "!a" ];
>       B -> C [ label = "!a" ];
>       C -> D [ label = "!b" ];
>       B -> B [ label = "?0, ?1" ];
>       D -> D [ label = "?0, ?1" ];
>   }
>   ```
>   where we try to cover the control state `Z` in the 1st machine.

We first give the basis elements computed during the algorithm's execution and then the upward-closed set at each iteration later:

| Basis | Machines State    | Channels State |
|------:|-------------------|----------------|
|  1    | $Z$, $A$          | $ε$, $ε$       |
|  2    | $Z$, $B$          | $ε$, $ε$       |
|  3    | $Z$, $C$          | $ε$, $ε$       |
|  4    | $Z$, $D$          | $ε$, $ε$       |
|  5    | $Y$, $A$          | $b$, $ε$       |
|  6    | $Y$, $B$          | $b$, $ε$       |
|  7    | $Y$, $C$          | $b$, $ε$       |
|  8    | $Y$, $D$          | $b$, $ε$       |
|  9    | $X$, $A$          | $bb$, $ε$      |
|  10   | $X$, $B$          | $bb$, $ε$      |
|  11   | $X$, $C$          | $bb$, $ε$      |
|  12   | $X$, $D$          | $bb$, $ε$      |
|  13   | $X$, $A$          | $ab$, $ε$      |
|  14   | $X$, $B$          | $ab$, $ε$      |
|  15   | $X$, $C$          | $ab$, $ε$      |
|  16   | $X$, $D$          | $ab$, $ε$      |
|  17   | $Y$, $C$          | $ε$, $ε$       |
|  18   | $X$, $C$          | $b$, $ε$       |
|  19   | $X$, $C$          | $a$, $ε$       |
|  20   | $Y$, $B$          | $ε$, $ε$       |
|  21   | $X$, $B$          | $ε$, $ε$       |
|  22   | $X$, $A$          | $ε$, $ε$       |

Basis of the set of configuration for each loop iteration:

0. 1-4
1. 1-8
2. 1-6, 8-17
3. 1-6, 8-10, 12-14, 16-20
4. 1-6, 8-9, 12-13, 16-21
5. 1-6, 8, 12, 16-22

> Prove that your procedure is correct

__TODO ...__


## Open and Closed World with Finite State Machines

> Modify the synchronized product of automatons to mimic the parallel and communication rules of CCS.

Given automaton $M_1$ and $M_2$, the new product is the NFA $M$ where:

* $Q = Q_1 × Q_2$
* $Σ = Σ_1 ∪ Σ_2$
* $δ$ is the transition relation
  - $δ((q_1,q_2), π) ∋ (δ_1(q_1, π), q_2))$ if $π ∈ Σ_1$
  - $δ((q_1,q_2), π) ∋ (q_1, δ_2(q_2, π))$ if $π ∈ Σ_2$
  - $δ((q_1,q_2), τ) ∋ (δ_1(q_1, !a), δ_2(q_2, ?a))$ if $∃ a$ such that $!a ∈ Σ_1$ and $?a ∈ Σ_2$
  - $δ((q_1,q_2), τ) ∋ (δ_1(q_1, ?a), δ_2(q_2, !a))$ if $∃ a$ such that $!a ∈ Σ_1$ and $?a ∈ Σ_2$
* $q₀ = (q₀_1,q₀_2)$
* $F = F_1 × F_2$


> Define a new restriction operation for an automata.

The restriction of $M$ by $a$ is the NFA M' where

* $Q' = Q$
* $Σ' = Σ ∖ \\{!a, ?a\\}$
* $δ'$ is the transition relation
  - $q' ∈ δ'(q, π) ⇔ q' ∈ δ(q, π) ∧ π ≠ !a ∧ π ≠ ?a$
* $q₀' = q₀$
* $F' = F$


## Modeling the Occam with CCS

> Modify the rules for communication to allow sending and receiving data values.

__TODO ...__

> Modify the choice rule for guarded choice.
> The "normal" choice is a special case of guarded choice where all the guards are true.

__TODO ...__

> Encode the program above in this extended CCS

__TODO ...__

