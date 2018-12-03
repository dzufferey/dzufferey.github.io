# Homework 7

_Instructions_
* Due *before* December 11 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).


## On Bounded Communicating State Machines

In class, we mentionned that with bounded channels, communicating state machines (CSM) can be reduced to finite state machines.
Let us explore that further.

Also, as SPIN is a verifier for finite state systems, we will use it to check bounded CSM.

### Bounded CSM State Space Size

From the definition of CSM, let
* $|Σ|$ be the number of different messages
* $N$ the number of state machines
* let $m$ be the maximal number of state of any if the state machines, i.e., $m = max_i |S_i|$.
* $k$ the bound on the channel size.

Assuming p2p channels, estimate the size of the state space of CSM in the parameters listed above ($\mathcal{O}$ notation).

### Alternating Bit Protocol in SPIN

Encode the alternating bit protocol in SPIN and check it is correct with bounded channels.

SPIN has a sightly different model of channels.
Channels are specific "variable" which are accessed by name, see the [Promela constructs for channels](https://en.wikipedia.org/wiki/Promela#Message_passing).

You do not need to precisely follow the version given in the notes (SPIN allows for a more compact encoding) but the overall principle of the protocol: add some bits to a packets and acknowledgment to confirm the proper reception.

Make your model of the protocol satisfy the following requirements / use the following assumptions:
- Make it parametric in the channel size, e.g., `#define k 5`, so you can test it with different bound on the channel size.
- Make it parametric in the message to be transmitted. You can use that value in the receiver to check the message have been properly received.
- $|Σ| ≤ 128$ (ASCII characters) so you can fit the message and an extra bit in a single `byte`. You may use structures for messages if you want to make your example more complicated.

Vary the size of the channel and length of the message to transmit to see how it affects the number of states explored by SPIN.


## Communicating State Machines with Bags (instead of FIFO)

Let us discuss different ways of breaking the reduction from Turing machine (TM) to CSM (see [notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md)).

The reduction only uses only 2 machines.
Therefore, point-to-point or mailbox semantics does not make any difference.
For this exercise, we _assume the mailbox semantics_.

The ordering in the reduction was important because the tape of the TM is an ordered sequence.
If the CSM's mailboxes are bags (multisets) instead of FIFOs, the reduction does not work.

A multiset of messages is usually modeled as map from message type to natural number.
Petri nets (PN) have a limited ability to "count" and can encode such map.

From the definition of CSM we have:
* $|Σ|$ different possibles messages
* $N$ state machines
* let $m$ be the maximal number of state of any if the state machines, i.e., $m = max_i |S_i|$.

__Control-state reachability.__
Control-state reachability is a specific type of covering/reachability question in the case of concurrent systems.
For a systems composed of a finite number processes interacting either through shared memory or message passing, the control-state reachability asks if a distinguished process can reach a particular local state.
This question is indifferent to the state of the other processes or means of synchronization (memory, channels).

### CSM to PN

* Give a reduction from CSM with bag mailbox to Petri net that preserves control-state reachability.
  By preserving control-state reachability, we mean that a machine $M_i$ in the CSMs can reach a given state $s_i$ iff the PN obtained with the reduction can cover a marking $M$.
  For a given $M_i$ and $s_i$ explain what $M$ you get with your reduction.
* How many places and transitions does the PN has as a function of $N$, $m$, and $|Σ|$ ?

### PN to CSM

* Give are reduction from Petri net to communicating state machines such that a covering question for the Petri net can be encoded as a control-state reachability question in the CSM.
  Your reduction can use the marking to cover and produce different CSM depending on that marking.



## Lossy Channel Systems with Test for Empty Channel

Let us look at an extension of LCS.
In our current model, the receive is a blocking operation.
A machine waits until it receives a message.

Let us consider the model of LCS with p2p channels and add a new $¿$ symbols for transition when the channel is empty.
Compared to the definition of [lecture notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md), the alphabet is now $(ID × ! × Σ) ∪ (? × Σ) ∪ {¿}$ and the semantics is extended with the following rule:
\\[{
M[i] \stackrel{¿}{→} s  \qquad  M' = M[i ← s]  \qquad  ∀ j.~ C[j,i] = ε
} \over {
               (M, C) → (M', C)
}
\\]

_Question._
Are LCS with test for empty channels still WSTS?
- if yes, explain how to extend the conditions of WSTS (WQO, compatibility) to the test for emptiness
- if no, explain which WSTS condition does not hold and do you think the covering problem is still decidable

