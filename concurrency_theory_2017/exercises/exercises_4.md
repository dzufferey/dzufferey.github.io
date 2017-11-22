# Homework 4

_Instructions_
* Due on November 22.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


## WQO from well-founded and no infinite antichain

Prove the following theorem:

Given a quasiorder `≤`, if `<` is well-founded and `≤` does not have infinite antichain then `≤` is a wqo.

Remember that `x < y` is a shorthand for `x ≤ y ∧ y ≰ x`.


## Upward-closed properties

Let us look back a safety properties of the Petri nets.
In particular, (1) deadlock-freedom and (2) place k-boundedness.

_Deadlock-freedom_ means the Petri net cannot reach deadlock, i.e., a state without successor.

_Place k-boundedness_ means that a given place, or set of places, always contains at most `k` tokens.
In the notes' running example, mutual exclusion is an instance of place k-boundedness.

Remember that a safety property corresponds to a set of states.
To verify the property, we take the complement of this set of states, i.e., the set of error states, and asked whether it is possible to reach the error state stating from the initial state.

We say that a property is upward-closed if the set of error state is upward-closed.
(To match the naming scheme of co-linear property, we should call such property co-upward-closed, but let's keep things simple).

* Give a proof that place k-boundedness is upward-closed.
* Give a counter-example that show that deadlock-freedom is not upward-closed.


## Compatibility

Prove the following two statements:
* If `≤` is a partial order then strict compatibility implies compatibility.
* Strong compatibility implies stuttering compatibility.


## Effective pred-basis

* Give an algorithm to compute the _pred-basis_ (`↑pre(↑s)`) for DFA and NFA using `=` as WQO.
* Give an algorithm to compute the _pred-basis_ (`↑pre(↑s)`) for Petri net.
