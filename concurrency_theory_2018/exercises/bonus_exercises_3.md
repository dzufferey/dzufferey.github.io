# Bonus Exercises 3

_Instructions_
* Optional.
* Due on Tuesday Feb 5.

## Subtyping as a Refinement (or as a Simulation's Inverse)

We discussed simulation relation and we are going to investigate how the subtyping for communicating system fits into that view.
In this exercise, we only look at the types and the behavior they allow.
We are considering the following model: [alternating refinement relations](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.113.1421) by Rajeev Alur, Thomas A. Henzinger, Orna Kupferman, Moshe Y. Vardi (1998). You can get the paper by clicking on the pdf icon on the right.

_Terminology._
The inverse of a simulation is called a refinement.
Given two systems R and S, "R refines S" is equivalent to "S simulates R".
'Refines' means "anything done by R can also be done by S" and 'simulates' is "S can do anything that R does".

When looking at simulation, we did not distinguish between different types of actions.
However, in communicating system what we want to model that a receiver cannot restrict what a sender is allowed to do.
This is known as an _alternating simulation_ or as "an implementation R refines a specification S without constraining the other process with which it interacts."
In this exercise, we are looking at applying this framework to binary session types.
We since the setting is much more general we will actually get a sightly weaker result.

Let us call the two processes and their respective types $P$ and $Q$.
We can think of the types are automatons describing the possible executions of $P$ and $Q$.
These automatons must be such that combining them gives an alternating transition system (ATS).

Here is the outline of what we try to acheive:
1. Encode a type (and its dual) into an ATS (see the paper for the definition of alternating transition system).
2. Show that subtyping is a refinement in terms of ATS.
3. Use results about ATS to show that subtyping preserves progress.

The 3rd step uses some heavier infrastructure such as temporal logics (ATL*) that we have not covered during the class.
Therefore, we are just doing the first two steps.
The 2nd and 3rd steps impose some restrictions on the encoding of types into an ATS, so check them before doing the reduction.


__Task 1.__

Given two processes/type $P,Q$, we want to generate an ATS $(Π,Ω,Q,q_{in},π,δ)$ satisfying the following constraint:
* $Π = \\{bad\\}$ (one proposition to tag the state when something bad happened)
* $Ω = \\{P, Q\\}$
* $δ$ perserves the non blocking properties of ATS.
  You can think of $δ$ as $P$ and $Q$ declaring their action: the message/label they choose to send or the messages/labels they can receive.
  When there is a matching send/receive the system proceed to a state $s$ where $π(s) = ∅$, if there is no matching send/receive the system move to a state $π(s) = \\{bad\\}$.
* When $P = dual(Q)$ the resulting ATS must never get into a $bad$ state.

__Task 2.__

Let $P' <: P$, $P = dual(Q)$, $S$ is the ATS obtained from $P$ and $Q$, and $R$ is the ATS obtained from $P'$ and $Q$ using the construction from task 1.
(Call $P'$ in $R$ $P$ so both ATS have the same $Ω$.)

Show that your construction respects:
1. $R ≤_P S$
2. $R ≤_P S ⇔ S ≤_Q R$ (This not true in the general case, but because we are looking at a particular case this should hold.)

__3rd Step of the proof.__
The final result is obtained by applying Theorem 6 from the paper:

* First we need to encode the property in which we are interested: refinement/subtyping preserves progress.
  To express, we use that fact that $π$ is use to tag the bad/sink state.
  Then we can use the following ATL* formula: $□«P»¬bad$ and $□«Q»¬bad$.
  The formula says that $P$, respectively $Q$, always has a move to avoid the bad state.
* Let $R$ and $S$ by two systems where in $R$ the behavior of $P$ is a subtype its behavior in $S$.
  By our encoding we have that $R ≤_P S$.
  Then using the stronger duality result from the second step: we also have $S ≤_Q R$.
* From $S ≤_Q R$ and Theorem 6, we have that if $S$ satisfies $□«Q»¬bad$ then $R$ also satisfies $□«Q»¬bad$.
  This may look at bit confusing as we switched perspective.
  The subtyping is relative to $P$ but the formula is about $Q$.
  Let us exlpain in word what this mean.
  "$S$ satisfies $□«Q»¬bad$" means that when $Q$ interact with $P$ in $S$, $Q$ has a strategy not to get to a bad state or that $P$ cannot force $Q$ into a bad state.
  When we replace $P$ by its subtype (look at $R$ instead of $S$), we preserve the property that $P$ cannot force $Q$ into a bad state.
* The previous part still rely on the assumption that "$□«Q»¬bad$" holds in $S$.
  The construction we did should guarantee that as $S$ is generated from $P = dual(Q)$.
