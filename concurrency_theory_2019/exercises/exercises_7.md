# Homework 7

_Instructions_
* Due on Dec 16, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


# Division Order for Abstract Algebra

## Definitions

A _semigroup_ $(S,⋅)$ is an algebraic structure consisting of a set $S$ of elements and an associative binary operation $⋅$.

Given a semigroup $(S,⋅)$, a set $G ⊆ S$ is called _generating set_ if every element of $S$ can be expressed as combination (under the $⋅$ operation) of finitely many elements of $G$.

A quasi-order $≤$ in a semigroup $(S,⋅)$ is a _division order_ if it satisfies:
* $∀ x, y.\ x ≤ x⋅y$,
* $∀ x, y.\ x ≤ y⋅x$,
* $∀ x, y, z.\ y⋅z ≤ y⋅x⋅z$.

We are interested in finding out the condition that makes a division order a WQO.

## Task
Let $(S,⋅)$ be a semigroup quasi-ordered by a divisibility order $≤$.
- If $S$ has a finite generating set $G$, is $(S,≤)$ a WQO?
- If $S$ has a generating set $G$ such that $(G,≤)$ is a WQO, is $(S,≤)$ a WQO?

For both tasks:
- If the answer is yes then give a proof. You can embed another WQO in this order or show that this order can be build from other WQO using Dickson's lemma, Higman's lemma, or Kruskal's tree theorem.
- If the answer is no then give a counter example (a bad sequence).


# Lossy Channel System with Initial Channel State

When analyzing LCS, we always assumed that the channels are empty in the initial state.
We are going to investigate whether this is a real restriction or not.
Recall that LCS are communicating state machines with unbounded lossy FIFO channels.

Let us look at some possibilities from simple to more difficult.

__Model 1.__
For each channel, the channel's initial state is given by a word.

__Model 2.__
For each channel, an initial channel state is allowed if it is recognized by a regular expression.

__Model 3.__
For each channel, an initial channel state stems from a given but arbitrary set.

We still look at the property of control-state reachability but in contrast to the normal LCS, 
there is a set of initial states and hence the question reads as follows:
Is there an initial state (in the set of initial states) from which we can cover a particular control-state?

## Questions
Let us look at how these extended LCS models relate to normal LCS:
- For model 1: can you either reduce it to normal LCS or find an example which cannot be modeled by an LCS?
- For model 2: can you either reduce it to normal LCS or find an example which cannot be modeled by an LCS?
- For model 3: can you find assumptions so that this model can be reduced to either LCS, model 1 or 2? 
		You may need to find different sets of assumptions for the different reductions - depending on the reductions presented before.


# Partially Lossy Channel System

In general, communicating state machines can be a Turing complete model of computation.
Therefore, we looked at less powerful models such as LCS (unbounded p2p lossy FIFO channels).

Unfortunately, lossy channels describe a model of limited use.
Since every message is potentially lost, the system may not be able to do anything at all.
Let us try to make the model more useful and more realistic.

Our channels abstract how messages are transmitted over an actual network.
Let us assume that the network is a packet switching network (internet).
Each element in the path between the sender and receiver (router, etc.) has a finite memory to process and forward packets.
As long as there are fewer packets than the capacity, the transmission is reliable.
However, when the network is overloaded it can drop packets.

Let us try to model this as a partially lossy channel system (PLCS).
Let $k$ be a constant modeling the network capacity.
Consider the following variations:
1. A PLCS is a LCS that only drop messages from a channel when there is more than $k$ messages in that channel.
2. A PLCS is a LCS that only drop messages from a channel when there is more than $k$ messages in the network (sum of all the channels).

## Questions
For the two kinds of PLCSs above:
- Explain how to modify the formalization of LCS to obtain a PLCS. 
  Ensure to address all different parts of the definition by recalling and briefly explaining their role as well as whether you need to change them.
  The goal is to give a coherent modified definition for PLCS.
- Is the control-state reachability (covering) still decidable for PLCS?
  Give a proof (find a WQO which is compatible with the new semantics) or a counterexample.
