# Solutions 9

Thanks to Oliver Markgraf, Hannes Endres, Alexander Witton, Billy Joe Franks, Kerem Kahraman, and Pascal Bergsträßer for contributing to this solution.

## Weak Bisimulation

We use the rules of structural congruence and strong ground equivalence (SGE) to show the bisimulation property:

$
\begin{array}{cl}
&(\nu c) (?a.!c.0\mid?b.!c.0\mid?c.?c.P)\\\\
\overset{\text{SGE}}\equiv &(\nu c)( ?a.(!c.0\mid?b.!c.0\mid?c.?c.P) + ?b.(?a.!c.0\mid!c.0\mid?c.?c.P)) + 0 \\\\
\overset{\text{SGE}}\equiv &(\nu c)(?a.?b.(!c.0\mid!c.0\mid?c.?c.P)+ ?a.\tau.(0\mid?b.!c.0\mid?c.P) \\\\
&+ ?b.?a.(!c.0\mid!c.0\mid?c.?c.P) + ?b.\tau.(?a.!c.0\mid0\mid?c.P))\\\\
\overset{\text{SGE*}}\equiv &(\nu c)(?a.?b.\tau.\tau.P+ ?a.\tau.?b.\tau.P \\\\
&+ ?b.?a.\tau.\tau.P + ?b.\tau.?a.\tau.P) \\\\
\overset{\text{weak sim}}\approx &(\nu c)(?a.?b.P+ ?a.?b.P + ?b.?a.P + ?b.?a.P )\\\\
\overset{c \not \in fn}\equiv & ?a.?b.P+ ?a.?b.P + ?b.?a.P + ?b.?a.P \\\\
\equiv &  ?a.?b.P + ?b.?a.P
\end{array}
$


## From ν-free Process Algebra to Petri Net

#### Task 1

TODO ...

#### Task 2

TODO ...


## Making a Model from Code

#### Choice of the Model

CSM are not suitable because we potentially have an unlimited number of actors/clients.
CSM have a fixed number of processes and we need to model process creation.

CCS can model process creation but it cannot model mobility (sending names as part of messages).
In this example, the client sends its own address as part of the request.

The π-calculus easily allows both process creation and mobility.

#### What it modeled/left out

* _About names._
  In the actor model, each process get an unique address at its creation and this cannot be changed.
  `self()` always return the same address.
  Therefore, we use $ν$ when the process gets created and the definition for actors always carries the self.
* _About different kinds of messages._
  In this example, each actor receives only one type of message (`request` for the server, `hit_count` for the client).
  Therefore, we had one name per actor.
  However, if we want to model more type of messages, we can have multiple name per processes.
  For each process, we always carries these names around in the same order and associate one type of message to each name.
* _Asynchronous message-passing._
  The actor model use asynchronous message-passing.
  Therefore, we model sending messages as creating a new process which carries the message.
* _About side effect._
  While we could model printing by creating a "stdout" process and sending message to that processm, we decided to ignore the printing and replace it by $τ$.
* _Closed world._
  In this case, the program is closed-world.
  Therefore, $\text{Main}$ does not have any name as arguement.

#### Model

With an "extension" of the calculus with integers values:

$
\begin{array}{lcl}
Server(self: name, state: int) & ≝ & ?self(return).(!return(state+1).0 | Server(self, state+1)) \\\\
Client(self: name, server: name) & ≝ & !server(self).0 | ?self(count).τ.0 \\\\
Main() & ≝ & (ν s) (Server(s, 0) | (ν c) Client(c, s))
\end{array}
$

Since CCS/π-calculus can model counters (see Turing complteness of the CCS), this is more syntactic sugar than an actual extension.
The numbers and operation can be replace by their equivalent in the process algebra.
