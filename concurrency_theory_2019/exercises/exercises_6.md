# Homework 6

_Instructions_
* Due on Dec 9, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


## Affine Nets (AN)

AN generalize both Petri, reset, and transfer nets.
AN allow both normal token operation like Petri nets and whole-place operations like resets and transfers.

An _Affine Net_ $N$ is a 4-tuple $(S, T, W, R)$ where
* $S$ is a finite set of places
* $T$ is a finite set of transitions
* $W$ is a weight function over $(S × T) ∪ (T × S) → ℕ$
* $R$ is a function $T → ℕ^{|S|} × ℕ^{|S|}$

A transition is enabled as like in the Petri net case.

$M \stackrel{t}{→} M'$ is defined as: $M' = R(T)⋅(M - W( \\_ ,t)) + W(t, \\_ )$ where $W( \\_ ,t)$ and $W(t, \\_ )$ are the forward and backward vector for $t$.

### Tasks

Let us look at how we can analyze affine nets.
We are interested in:
1. reachability
2. covering
3. boundedness (same definitions as for Petri net)
4. termination


Which of these questions can we (not) solve? 
What algorithms are (not) applicable?


## Defining More Operations on Channels

In class we have seen inference rules for different types of communicating state machines.
We have covered the common operations,
However, many systems have a richer set of operations.

Let us look at the operations on channels in Spin and come up with inference rules for them.
In Spin channels are independent of processes, [here](https://spinroot.com/spin/Man/chan.html) is an explanation for the declaration of channels.
For this exercise, you can assume that each process has its own channel.

The operations we will look at are
* [send](https://spinroot.com/spin/Man/send.html)
* [receive](https://spinroot.com/spin/Man/receive.html)
* [poll](https://spinroot.com/spin/Man/poll.html)
* [full](https://spinroot.com/spin/Man/full.html)
* [empty](https://spinroot.com/spin/Man/empty.html)

### Tasks
For all the operations above and their variations, do the following:
- If we already saw an inference rule for this operation, point to the relevant rule.
- Otherwise, give an inference rule for the operation.


## Santa Claus Problem

The [Santa Claus problem](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.544.5246&rep=rep1&type=pdf) in concurrency is an exercise which is more tricky than it looks.
Over the years, [many solutions have been proposed](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.567.2962&rep=rep1&type=pdf).

As it is common, the problem is only explained in natural language.
Therefore, the first step is to formalize the problem.
Then we can try to check some of the proposed solutions.

### Tasks
* From the problem description, extract the requirements/properties that the system should satisfy.
  Give a mathematical formalization for these properties.
* Come up with a solution to the problem or take an existing solutions.
  Model this solution in Spin and try to check that it satisfies the expected properties.
  For this exercise just look at safety properties, you can ignore fairness/liveness properties.
