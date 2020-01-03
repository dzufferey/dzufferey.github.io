# Homework 8

_Instructions_
* Due on Jan 13, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).

## π-calculus with Replication

Let us look at a modified version of the π-calculus.
In this version, we remove the process definitions ($≝$) and replace it by a replication operator: ${}^\*$.

_Processes._

$
\begin{array}{rcll}
   P & ::= & π.P            & \text{(action)}   \\\\
     &   | & P + P   \qquad & \text{(choice)}  \\\\
     &   | & P |~ P         & \text{(parallel composition)} \\\\
     &   | & (νa) P         & \text{(restriction)} \\\\
     &   | & P^\*           & \text{(replication)} \\\\
     &   | & 0              & \text{(end)}
\end{array}
$

_Actions._

$
\begin{array}{rcll}
   π & ::= & !a(\vec a)           & \text{(send)}   \\\\
     &   | & ?a(\vec a)  \qquad   & \text{(receive)}  \\\\
     &   | & τ                    & \text{(silent)}
\end{array}
$

Then we extend free/bound names and structural congruence as follow:
* $fn(P^\*) = fn(P)$
* $bn(P^\*) = bn(P)$
* $P^\* ≡ P^\* ~|~ P$

__Remark.__
In the literature, the replication operator is $!P$ rather than $P^\*$.
We use this modified notation to avoid confusion with sending a message.

### Tasks
* For an equivalence notion of your choice, can you find a encoding of the π-calculus version we saw during the lecture to the π-calculus with replication?
* For an equivalence notion of your choice, can you find a encoding of the π-calculus with replication to the version of the π-calculus we saw during the lecture?


## Higher Order π-calculus

Let us look at an extension of the π-calculus where processes can also send processes as part of the message.
This extension is called the higher order π-calculus by reference to high order functions in functional programming.

It is defined by extending the grammar for actions:

$
\begin{array}{rcll}
   π & ::= & !a(\vec a)           & \text{(send)}   \\\\
     &   | & ?a(\vec a)  \qquad   & \text{(receive)}  \\\\
     &   | & τ                    & \text{(silent)} \\\\
     &   | & !a(A)                & \text{(send/output of process)} \\\\
     &   | & ?a(A)                & \text{(receive/input of process)}
\end{array}
$

The semantics is similar to the π-calculus with the extension that receiving a process renames the corresponding identifier in the continuation.

_Example._
With the definitions

$
\begin{array}{rcl}
P & ≝ & !x(R).P' \\\\
Q & ≝ & ?x(A).(Q' ~|~ A) \\\\
R & ≝ & … \\\\
… & &
\end{array}
$

the process $P ~|~ Q$ can synchronize on $x$ and become $P' ~|~ Q' ~|~ R$.

This extension is not often studied in details as it does not really add to what the π-calculus can already do.
In fact, we can encode the higher order π-calculus in the normal π-calculus.

### Task
* For an equivalence notion of your choice, can you find an encoding of the higher order π-calculus to the normal π-calculus?
  Apply your translation to the example above.
  Your translation only needs to be correct when a channel can send processes or names but not both.
  For instance, in the example above, $x$ always sends processes and will never be used with names.

## $ν$-free π-calculus

The $ν$-free π-calculus prevents the use of the restriction operator ($ν$) in the body of the definitions and the process defining the initial state of the system must be closed.
Intuitively, this means that it is not possible to _create_ new names and the number of names in the system is bounded by the number of names in the initial process.
This fragment of the π-calculus is not Turing-complete and we can show that it is a WSTS.

__Normal form and ordering for the processes.__
Without loss of generality, we assume the processes can be rewritten ($≡$) to have the following form: 
$(ν \vec a) ∏_i A_i(\vec a_i)$
with $\vec a_i ⊆ \vec a$ for all $i$.

Once the initial configuration of the system is known we can fix $\vec a$ and use it to describe all the system's configuration.

We can compare the configuration as follows:
* more processes makes larger configurations: $(ν \vec a) ∏_i A_i(\vec a_i) ≤ (ν \vec a) \left(∏_i A_i(\vec a_i) ~|~ ∏_j A_j(\vec a_j) \right)$
* closing $≤$ under $≡$: $P ≡ P' ∧ Q ≡ Q' ∧ P' ≤ Q' ⇒ P ≤ Q$

### Task
* Given the ordering defined above, show that the $ν$-free π-calculus is a WSTS.
