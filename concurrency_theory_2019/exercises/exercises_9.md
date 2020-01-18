# Homework 9

_Instructions_
* Due on Jan 27, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


## π-calculus with Test for Name Equality

Let us look at an extension of the π-calculus with test for name equality $[x=y]P$ and $[x≠y]P$.

This extension can be useful to model which programs passing names to model addresses (url or pointer) or data and acting differently depending on the value.
For instance, one can model a firewall which drops messages from a set of addresses and forward messages from the others addresses.

Formally, the grammar of processes is extended with:

$
\begin{array}{rcll}
   P & ::= & …              & \text{(same as π-calculus)}   \\\\
     &   | & [a = a]P       & \text{(test)}  \\\\
     &   | & [a ≠ a]P       & \text{(test)}
\end{array}
$

In the grammar $a$ is the rule for names, so each $a$ can be a different name.

The free and bound names are extended with:
* $fn([a = b]P) = fn([a ≠ b]P) = fn(P) ∪ \\{a, b\\}$
* $bn([a = b]P) = bn([a ≠ b]P) = bn(P)$

And the semantics has the following new rules:
* equal names: \\[{ }\over{ [a = a]P  \stackrel{τ}{→} P }\\]
* disequal names: \\[{ }\over{ [a ≠ b]P  \stackrel{τ}{→} P }\\]

### Question
As the π-calculus is a Turing complete model of computation, we looked at restricted models to obtain some decidability results.
In particular, we looked at the $ν$-free π-calculus.
Can you solve the covering problem for the $ν$-free π-calculus with test for name equality?



## Model for Mobile Ad Hoc Networks

Mobile ad hoc networks (MANET) are networks which do not depend on a static infrastructure (routers, switches, etc.) but transfer packets only using the mobiles devices currently available.
Since devices are free to move independently of each other, the communication links constantly change as they are limited by the transmission range of the devices.
Two devices which move too far away cannot communicate anymore and devices which get closer can suddenly communicate.

Let us investigate a model for a simple MANET and the decidability of control-state reachability in that context.

The model is a variation of communicating state machines incorporating the following changes:
* the communication modality is synchronous broadcast (no channel),
* instead of channels between every pair of processes we have a graph which says which node can communicates together.

Like in communicating state machines, every process is a finite state machine sending and receiving messages over a finite message alphabet.
The state of the system is a pair $(M, G)$ where $M$ maps each machine to its local state and $G$ is the communication graph.
We write $G(i)$ to get the neighbours of $i$ in $G$.

The transitions are defined by the following two rules:

_Communication_
\\[{
M[i] \stackrel{!a}{→_i} M'[i] \qquad ∀ j≠i.\ (j ∈ G(i) ⇒ M[j] \stackrel{?a}{→_j} M'[j]) ∧ (j ∉ G(i) ⇒ (M[j] = M'[j]))
} \over {
(M, G) → (M', G)
}
\\]

_Reconfiguration_
\\[ {} \over { (M, G) → (M, G') } \\]

### Questions
* For the new model above, is the control-state reachability question decidable? Justify.
* Consider a generalization of the model.
  For communicating state machines, we have a fixed number of processes.
  We want to generalize that to the parameterized verification problem.
  We still have a finite number of types of machines but there can be an arbitrary number of copies of each type of machine.
  Is the control-state reachability problem still decidable? Justify.


## On Well-formed Communication Protocols and Binary Session Types

Let us look at the following at the two processes communicating with each other.

The code is given in scala pseudo code.
Sending is `!` and `receive` returns a message which can be inspected using pattern matching.

__Process 1.__
```scala
process2!Request1(1, 2)
receive match {
  case Reply1(_) =>
    process!Exit
    exit()
}
```

__Process 2.__
```scala
while(true) {
    receive match {
      case Request1(value1, value2) =>
        process1!Reply1(value1 < value2)
      case Request2(value) =>
        process1!Reply2(-value1)
      case Exit =>
        exit()
    }
}
```

Our goal is to ensure that both programs together execute correctly.

###  Questions
* Can you find a binary session type that shows that the two processes communicate correctly?
  (hint: the subtyping rule is crucial for this example, one process' local type can be a subtype of multiple types.)
