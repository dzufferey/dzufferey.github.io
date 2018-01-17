# Homework 10

_Instructions_
* Due on January 24.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


# The π-calculus and FIFO communication

In the [notes 9](../notes_9.md) we discussed how we can encode asynchronous communication in CCS.
The same construction is straightforward to generalize to the π-calculus.
The downside of this construction is that it only simulates channels with a bag semantics, i.e., messages are free-floating processes which synchronize with the receiver.

The goal of this exercise is to encode communication channels with a reliable FIFO semantics in the π-calculus and use it to translate communicating state machines in the π-calculus.
We split the task into multiple parts.

1. Given a single communicating state machine, explain how to encode the control-flow of the machine into an equivalent CCS process.
   We will use the π-calculus later, but as communicating state machine do not send payload with the messages this part can stay within CCS (π-calculus with send/receive of arity 0).
2. Extend your encoding to also account for reliable FIFO communication channels.
   You can use the full π-calculus for this part.
   (Hint: you may need to "implement" in the π-calculus extra datastructures as part of the encoding.)
3. As an example, apply your encoding to the simplified alternating bit protocol from two weeks ago:
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
   For this exercise, we assume reliable FIFO semantics, not the lossy one from the previous weeks.


# (High-order) π-calculus

Let us look at an extension of the π-calculus where processes can also send processes as part of the message.
This is the high-order π-calculus.

It is defined with the following grammar:

__Processes (same as π-calculus).__
```
P ::= π.P       (action)
    | P + P     (choice)
    | P | P     (composition)
    | (νa) P    (restriction)
    | A(a)      (named process, a can be a list of agruments)
    | 0         (end)
```

__Actions (send/receive name or processes).__
```
π ::= !a(a)     (send/output of name)
    | ?a(a)     (receive/input of name)
    | !a(A)     (send/output of process)
    | ?a(A)     (receive/input of process)
    | τ         (silent)
```

The semantics is similar to the π-calculus with the extension that receiving a process renames the corresponding identifier in the continuation.

__Example.__
With the definitions
```
P ≝ !x(R).P′
Q ≝ ?x(A).(A | Q′)
R ≝ … 
…
```
the process `P|Q` can synchronize on `x` and become `P′ | R | Q′`.


Show how to encode the high-order π-calculus in the normal π-calculus.
Given a process and the corresponding definitions, give a translation in the calculus that has the same behaviour up to some `τ` steps and the content of messages.
Explain why your translation is correct and, as an example, apply your translation to the example.

The translated process is allowed to take step that are not visible from the outside.
Regarding the messages, the names over which the synchronization happens must be preserved but the payload of the messages can be changed.

Your translation only needs to be correct when a channel can send processes or names but not both.
For instance, in the example above, `x` always sends processes and will never be used with names.

