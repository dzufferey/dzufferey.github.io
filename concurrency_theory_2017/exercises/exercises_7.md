# Homework 7

_Instructions_
* Due on December 13.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


__Control-state reachability.__
Control-state reachability is a specific type of covering/reachability question in the case of concurrent systems.
For a systems composed of a finite number processes interacting either through shared memory or message passing, the control-state reachability asks if a distinguished process can reach a particular local state.
This question is indifferent to the state of the other processes or means of synchronization (memory, channels).


## Different channel models

We have seen different properties of channels.
It is easy to see that the p2p/mailbox distinction does not matter for the bag semantics.
Furthermore, in the synchronous case the channel order also does not matter.

This still gives the following combinations:
1.  unbounded,    FIFO,     p2p,        reliable
2.  unbounded,    FIFO,     p2p,        lossy
3.  unbounded,    FIFO,     mailbox,    reliable
4.  unbounded,    FIFO,     mailbox,    lossy
5.  unbounded,    bag,      reliable
6.  unbounded,    bag,      lossy
7.  bounded,      FIFO,     p2p,        reliable
8.  bounded,      FIFO,     p2p,        lossy
9.  bounded,      FIFO,     mailbox,    reliable
10. bounded,      FIFO,     mailbox,    lossy
11. bounded,      bag,      reliable
12. bounded,      bag,      lossy
13. synchronous,  reliable
14. synchronous,  lossy


### Differences between semantics

To distinguish two semantics, we use the control-state reachability problem, i.e., finding an example where one machine can reach a particular state with one semantics but cannot with the other semantics.

In the class, we have seen some examples that distinguishes some of them:
* the juggling example distinguishes between synchronous and unbounded
* the alternating bit protocol distinguishes between FIFO and bag
* an example that distinguishes between p2p and mailbox

Let us continue:
* Can you find an example which distinguishes between unbounded+FIFO+p2p+reliable and unbounded+FIFO+p2p+lossy
* Can you find an example which (a) cannot be distinguished by synchronous+reliable and 1-bounded+FIFO+p2p+reliable, but (b) is distinguishable with 2-bounded+FIFO+p2p+reliable?
* [Optional] show that with unbounded+bag reliable or lossy cannot be distinguished.
* [Optional] Give an example that distinguishes bounded+bag+reliable and bounded+bag+lossy (the bound is up to you)

### Synchronous and Lossy systems

To define the semantics of lossy systems, we have added an extra rule that only changed the channels.
Synchronous systems do not have channels.
Suggest a semantics for a synchronous and lossy system.
You can either change the rule for synchronous system and/or add new rules.


## Breaking the Turing machine reduction (Part 1)

Let us discuss different ways of breaking the reduction from Turing machine (TM) to communicating state machines (CSM) (see [notes 7](../notes_7.md)).

The reduction only uses only 2 machines.
Therefore, point-to-point or mailbox semantics does not make any difference.
For this exercise, we _assume the mailbox semantics_.

### CSM with bounded channels

The reduction needs an unbounded channel to encode the infinite tape of the TM.
Let us look at what happens when we bound the channels.

Let `k` be the bound on the maximal size of the channel.
From the definition of CSM we have:
* `|Σ|` different possibles messages
* `N` finite state machines
* let `m` be the maximal number of state of any if the state machines, i.e., `m = max_i |S_i|`

Since all these constants are finite, the overall system is finite.

#### CSM → NFA

* Give a reduction from CSM with bounded mailbox to non-deterministic finite state machines that preserves control-state reachability.
  By preserving control-state reachability, we mean that a machine `M_i` in the CSMs can reach a given state `s_i` iff the NFA obtained with the reduction can reach some set of states `F`.
  For a given `M_i` and `s_i` explain what `F` you get with your reduction.
  (Hint: use multiple "small" state machines to encode different aspects of the CSM and combine them using the synchronized product to obtain the complete system.)
* How many states does the NFA has as a function of `N`, `m`, `|Σ|`, and `k` ?

#### NFA → CSM

* Give a reduction from non-deterministic finite state machine to CSM with bounded mailbox that preserve control-state reachability.
  By preserving control-state reachability, we mean that the NFA can reach a state `f` iff a machine `M_j` in the CSMs can reach a given state `s_i`.
  For a given `f`, explain how you get `M_i` and `s_i` with your reduction.
* Express `N`, `m`, `|Σ|`, and `k` as a function of the number of states in the NFA.

