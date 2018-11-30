# Equivalence of processes: simulation, symmetric simulation, and bisimulation

Until now, we have discuss properties of systems through the lens of reachability properties, e.g., can a system get to a particular state.

Other types of questions we may want to ask  are
* How does a system interact with his environment? (its input/output behaviors)
* What it means for two systems to be equivalent? or implement the same interface?

Surely, two different implementations of the same protocol can have different states, so comparing them using state-based properties is not possible.
Simulation relations for labeled systems try to answer such questions.

## Labeled Transition Systems

A _labeled transition systems_ (LTS) is a triple $(S,Σ,→)$ with:
* $S$ is a set of states (can be infinite),
* $Σ$ is a finite set of labels (the alphabet),
* $→ ⊆ S × Σ × S$ is a transition relation.

## Simulation relations

We already saw an instance of simulation with the compatibility of WSTS.
In this case, it was a particular case of simulation relation within the same process.
However, this idea is more general and applicable to different processes.

Let $A$, $B$ be two LTS with the same alphabet $Σ$.
A _simulation relation_ $R$ a relation between the states of $A$ and $B$ with the following property:
$∀ a ∈ Σ,~ s_A,t_A ∈ S_A,~ s_B ∈ S_B.~ R(s_A, s_B) ∧ s_A \stackrel{a}{→_A} t_A ⇒ ∃ t_B ∈ S_B.~ s_B \stackrel{a}{→_B} t_B ∧ R(t_A, t_B)$.

If both $R$ and its inverse $R⁻¹$ are simulation relations then $R$ is a bisimulation.

We say that $A$ simulates $B$ if there is a simulation relation between $B$ and $A$ that covers all the reachable states of $B$ and relates the initials states of $A$ and $B$.

For two systems $A$ and $B$, it is possible to have $A$ simulating $B$, $B$ simulating $A$, and $A$,$B$ are not bisimilar.

__Example.__
Let us look at the following NFAs:
* $A$:
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      init -> a;
      a -> b [ label = "a" ];
      b -> c [ label = "b" ];
      c -> b [ label = "a" ];
      a -> d [ label = "a" ];
      d -> d [ label = "a,b" ];
  }
  ```
* $B$:
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      init -> 0;
      0 -> 1 [ label = "a" ];
      1 -> 2 [ label = "b" ];
      2 -> 1 [ label = "a" ];
      0 -> 3 [ label = "a" ];
      3 -> 3 [ label = "a,b" ];
  }
  ```

$A$ simulates $B$ with the following simulation relation: ${(0,a), (1,d), (2,d), (3,d)}$.

$B$ simulates $A$ with the following simulation relation: ${(a,0), (b,3), (c,3), (d,3)}$.

However, $A$ and $B$ are not bisimilar.
