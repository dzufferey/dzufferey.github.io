# Homework 8

_Instructions_
* Due on January 10.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.
* Have nice holidays!


## Ideal KM Tree for the alternating bit protocol

To get a better feeling about LCS, let us look at a concrete example.
Here is a simplified version of the alternating bit protocol:

__sender__
```
    → (0) ⤸ receiver!Msg0, ?Ack1
?Ack1 ↑ ↓ ?Ack0
      (1) ⤸ receiver!Msg1, ?Ack0
```

__receiver__
```
    → (a) ⤸ sender!Ack1, ?Msg1
?Msg1 ↑ ↓ ?Msg0
      (b) ⤸ sender!Ack0, ?Msg0
```

* Apply the ideal KM tree algorithm to this example and give the covering set.
* [Optional] If you feel like it you can try on a more realistic version of the protocol:

__sender__
```
    → (0) ⤸ receiver!Msg0, ?Ack1
?Ack1 ↑ ↓ ?Ack0
      (1) ⤸ receiver!Msg1, ?Ack0
```

__receiver__
```
    → (a)
       ↓ ?Msg0
      (b) ←────────────┐
?Msg0 ↑ ↓ sender!Ack0  │
      (c)              │
       ↓ ?Msg1         │ ?Msg0
      (b)              │
?Msg1 ↑ ↓ sender!Ack1  │
      (d) ─────────────┘
```


   
##  Breaking the Turing machine reduction (Part 2)

Let us discuss different ways of breaking the reduction from Turing machine (TM) to communicating state machines (CSM) (see [notes 7](../notes_7.md)).

The reduction only uses only 2 machines.
Therefore, point-to-point or mailbox semantics does not make any difference.
For this exercise, we _assume the mailbox semantics_.

__Control-state reachability.__
Control-state reachability is a specific type of covering/reachability question in the case of concurrent systems.
For a systems composed of a finite number processes interacting either through shared memory or message passing, the control-state reachability asks if a distinguished process can reach a particular local state.
This question is indifferent to the state of the other processes or means of synchronization (memory, channels).


### CSM with bags (instead of FIFO)

The ordering in the reduction was important because the tape of the TM is an ordered sequence.
If the CSM's mailboxes are bags (multisets) instead of FIFOs, the reduction does not work.

A multiset of messages is usually modeled as map from message type to natural number.
Petri nets have a limited ability to "count" and can encode such map.

From the definition of CSM we have:
* `|Σ|` different possibles messages
* `N` finite state machines
* let `m` be the maximal number of state of any if the state machines, i.e., `m = max_i |S_i|`

#### CSM → PN

* Give a reduction from CSM with bag mailbox to Petri net that preserves control-state reachability.
  By preserving control-state reachability, we mean that a machine `M_i` in the CSMs can reach a given state `s_i` iff the PN obtained with the reduction can cover a marking `M`.
  For a given `M_i` and `s_i` explain what `M` you get with your reduction.
* How many places and transitions does the PN has as a function of `N`, `m`, and `|Σ|` ?

#### PN → CSM

* Give are reduction from Petri net to communicating state machines such that a covering question for the Petri net can be encoded as a control-state reachability question in the CSM.
  Your reduction can use the marking to cover and produce different CSM depending on that marking.

