# Communicating State Machines

__Notations.__
* To send and receive messages, we use the CSP notations (CSP = communicating sequential processes).
  - $p!a$: sending message $a$ to $p$. The $p$ can be omitted in some models.
  - $?a$: receiving message $a$.
* For the moment we consider systems with a fixed number of processes. We use $N$ for the number of processes.

## Example

Let consider the following to state machines:

* ping
    ```graphviz
    digraph finite_state_machine {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "init"];
        B [label = "wait"];
        init -> A;
        A -> B [ label = "pong!Ping" ];
        B -> A [ label = "?Pong" ];
    }
    ```
* pong
    ```graphviz
    digraph finite_state_machine {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "init"];
        B [label = "ack"];
        init -> A;
        A -> B [ label = "?Ping" ];
        B -> A [ label = "ping!Pong" ];
    }
    ```

We get the following execution:
* `(ping: init, pong: init)` and no message in transit
* `(ping: wait, pong: init)` and message `(ping, Ping, pong)`
* `(ping: wait, pong: ack)` and  no message in transit
* `(ping: wait, pong: init)` and  messages `(pong, Pong, ping)`
* `(ping: init, pong: init)` and  no message in transit
* ...

For brevity, the messages are written as triple `(sender, symbol, receiver)`.


## Definitions

To have more compact definitions, we will have one fist part which is shared among all the variations and then we will have multiple variations.


A system of communicating state machines is a pair $(Σ, M_1 … M_N)$ where
* $Σ$ finite set of messages shared among all the machines
* each $M_i$ is a DFA/NFA $(id_i, S_i, (ID × ! × Σ) ∪ (? × Σ) , →_i, s₀_i)$ with
  - $id_i$ is an unique ID for this particular machine (the ID is used to send messages to that particular machine.)
  - $S_i$ is the set of states of machine $i$
  - the alphabet is composed of two part: (1) sending messages $(ID × ! × Σ)$ and (2) receiving messages $(? × Σ)$
  - $→_i$ is the transition relation
  - $s₀_i$ is the initial state

The model of the channel only comes when we model the state of the system.
To model channels, we can pick among the following characteristics:
* FIFO or unordered
* unbounded, bounded, synchronous
* reliable or lossy

This choice will influence how we model the state of the system and the transitions.
Picking different models can be for accuracy of the model or decidability of some problems in a given model.

The state of a system is a pair $(M,C)$ where
* $M$ is a map from $id$ to states of the corresponding machine
* $C$ represent the channels. Depending on the type of system we want to model some kinds of channel:
  - point to point: $C[i,j]$ is a FIFO buffer between each pair of processes where $i$ is the sender and $j$ the receiver
  - mailbox: $C[i]$ is a FIFO buffer, each process has a single mailbox where all the incoming messages get multiplexed
  - unordered: $C[i]$ is a bag (multisets)
  - synchronous: there are no channel


__Notations.__
* Queue:
  - append / pop back:  $w = w'·a$, sometime even simpler $w = w'a$
  - prepend / pop head: $w = a·w'$, sometime even simpler $w = aw'$
* Maps:
  - $M[i]$ returns the value associated to $i$ in $M$
  - $M' = M[i ← s]$ creating a new map with the same values except for $i$ which gets value $s$. This is a shorthand for $M'[i] = s ∧ ∀ j.~ j ≠ i ⇒ M'[j] = M[j]$.
* Inference rules are written as
  \\[
  \mathit{premise}_1 \qquad \mathit{premise}_2 \qquad … \over \mathit{conclusion}
  \\]
  They basically are the same as $\bigwedge_i \mathit{premises}_i ⇒ \mathit{conclusion}$.

We can now discuss the semantics of the model discussed above:

### Reliable p2p FIFO

Sending a message
\\[{
 M[i] \stackrel{j!a}{→_i} s \qquad   C' = C[(i,j) ← C[i,j]·a]  \\qquad  M' = M[i ← s]
} \over {
                    (M, C) → (M', C')
}
\\]

Receiving a message
\\[{
M[i] \stackrel{?a}{→_i} s   \qquad   C[j,i] = a·w   \qquad  C' = C[(j,i) ←  w]  \qquad  M' = M[i ← s]
} \over{
                        (M, C) → (M', C')
}
\\]

### Lossy p2p FIFO

Same as reliable p2p FIFO and the following rule

Dropping a message
\\[{
C(i,j) = w·a·w' \qquad   C' = C[(i,j) ←  w·w']
} \over {
            (M, C) → (M, C')
}\\]

### Reliable mailbox FIFO

Sending a message
\\[{
 M[i] \stackrel{j!a}{→_i} s \qquad   C' = C[j ← C[j]·a]  \\qquad  M' = M[i ← s]
} \over {
                    (M, C) → (M', C')
}
\\]

Receiving a message
\\[{
M[i] \stackrel{?a}{→_i} s   \qquad   C[i] = a·w   \qquad  C' = C[i ←  w]  \qquad  M' = M[i ← s]
} \over{
                        (M, C) → (M', C')
}
\\]

### Lossy mailbox FIFO

Same as reliable mailbox FIFO and the following rule

Dropping a message
\\[{
C[i] = w·a·w' \qquad   C' = C[i ←  w·w']
} \over {
            (M, C) → (M, C')
}\\]

### Reliable bag

Sending a message
\\[{
 M[i] \stackrel{j!a}{→_i} s \qquad   C' = C[j ← C[j] ∪ \\{a\\}]  \\qquad  M' = M[i ← s]
} \over {
                    (M, C) → (M', C')
}
\\]

Receiving a message
\\[{
M[i] \stackrel{?a}{→_i} s   \qquad   a ∈ C[i]   \qquad  C' = C[i ← C[i] ∖ \\{a\\}]  \qquad  M' = M[i ← s]
} \over{
                        (M, C) → (M', C')
}
\\]

### Lossy bag

Same as reliable bag and the following rule

Dropping a message
\\[{
a ∈ C[i]   \qquad  C' = C[i ← C[i] ∖ \\{a\\}]
} \over{
        (M, C) → (M, C')
}
\\]

### Synchronous

Synchronous systems are quite different in the sense that they do not have channels.
A message needs to be send and received in the same step.

Step
\\[{
M[i] \stackrel{j!a}{→_i} s \qquad  M[j] \stackrel{?a}{→_j} r \\qquad  M' = M[i ← s][j ← r]
} \over {
                    (M, ∅) → (M', ∅)
}
\\]


### Bounded

Having bounded channels just adds an extra check when sending the messages.
Sending is only possible when the channel is not full.

Let $k$ be the bound ($k ≥ 1$).
Sending a message requires the extra checks: $|C[j]| < k$ (added as an additional premise to the rule.)


## Examples

#### Synchronous ping pong

Let us go back to the ping-pong example.
Because the channels are 1-bounded, the system behaves the same way with FIFO or bag.

This example even work with a synchronous semantics.
We get the following execution:
* `(ping: init, pong: init)`
* `(ping: wait, pong: ack)` after synchronizing with `pong!Ping` and `?Ping`
* `(ping: init, pong: init)` after synchronizing with `ping!Pong` and `?Pong`
* ...

#### Juggling

Ping-pong being too easy, let us look at an example that requires channels and does not work with a synchronous semantics.

* left hand
    ```graphviz
    digraph left {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "init"];
        B [label = "full"];
        C [label = "free"];
        init -> A;
        A -> B [ label = "right!Ball" ];
        B -> C [ label = "right!Ball" ];
        C -> B [ label = "?Ball" ];
    }
    ```
* right hand
    ```graphviz
    digraph right {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "full"];
        B [label = "free"];
        init -> A;
        A -> B [ label = "left!Ball" ];
        B -> A [ label = "?Ball" ];
    }
    ```

Notice that the first action of each machine is to send a messages.
Therefore, this example would get suck in a synchronous execution.
At any point in time after the first transition, there is between 1 and 3 messages in transit.

Since there is a single type of messages, the order of the channel does not matters.

Let us look in more detail as a possible execution:
* `(left: init, right: full)` and messages: ∅
* `(left: init, right: free)` and messages: `(right, Ball, left)`
* `(left: full, right: free)` and messages: `(right, Ball, left)`, `(left, Ball, right)`
* `(left: free, right: free)` and messages: `(right, Ball, left)`, `(left, Ball, right)`, `(left, Ball, right)`
* `(left: full, right: free)` and messages: `(left, Ball, right)`, `(left, Ball, right)`
* `(left: free, right: free)` and messages: `(left, Ball, right)`, `(left, Ball, right)`, `(left, Ball, right)`
* `(left: free, right: full)` and messages: `(left, Ball, right)`, `(left, Ball, right)`
* ...


#### Difference between p2p and mailbox

Let us show a difference between p2p and mailbox with the following three machines:

* **A**
    ```graphviz
    digraph a {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "a1"];
        B [label = "a2"];
        C [label = "a3"];
        init -> A;
        A -> B [ label = "C!X" ];
        B -> C [ label = "B!Y" ];
    }
    ```
* **B**
    ```graphviz
    digraph b {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "b1"];
        B [label = "b2"];
        C [label = "b3"];
        init -> A;
        A -> B [ label = "?Y" ];
        B -> C [ label = "C!Z" ];
    }
    ```
* **C**
    ```graphviz
    digraph b {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        A [label = "c1"];
        B [label = "c2"];
        C [label = "c3"];
        D [label = "c4"];
        E [label = "c5"];
        init -> A;
        A -> B [ label = "?X" ];
        B -> C [ label = "?Z" ];
        A -> D [ label = "?Z" ];
        D -> E [ label = "?X" ];
    }
    ```

To represent the execution, we need to be more careful about the representation of the channel.
First, let us look at the mailbox semantics

__Mailbox trace.__
* initial state
  - **A**: state `a1`, messages: `ε`, **B**: state `b1`, messages: `ε`, **C**: state `c1`, messages: `ε`
* **A** sends to **C**
  - **A**: state `a2`, messages: `ε`, **B**: state `b1`, messages: `ε`, **C**: state `c1`, messages: `X`
* **A** sends to **B**
  - **A**: state `a3`, messages: `ε`, **B**: state `b1`, messages: `Y`, **C**: state `c1`, messages: `X`
* **B** receives Y
  - **A**: state `a3`, messages: `ε`, **B**: state `b2`, messages: `ε`, **C**: state `c1`, messages: `X`
* **B** sends to **C**
  - **A**: state `a3`, messages: `ε`, **B**: state `b3`, messages: `ε`, **C**: state `c1`, messages: `X·Z`
* **C** receives X
  - **A**: state `a3`, messages: `ε`, **B**: state `b3`, messages: `ε`, **C**: state `c2`, messages: `Z`
* **C** receives Z
  - **A**: state `a3`, messages: `ε`, **B**: state `b3`, messages: `ε`, **C**: state `c3`, messages: `ε`

This is not the only trace, but in all the traces of the mailbox semantics, C receives `X` before `Z`.

Now let us look at the point to point semantics.

__P2p trace.__
* initial state
  - **A**: state `a1`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b1`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c1`, messages from A: `ε`, messages from B: `ε`
* **A** sends to **C**
  - **A**: state `a2`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b1`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c1`, messages from A: `X`, messages from B: `ε`
* **A** sends to **B**
  - **A**: state `a3`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b1`, messages from A: `Y`, messages from C: `ε`
  - **C**: state `c1`, messages from A: `X`, messages from B: `ε`
* **B** receives Y
  - **A**: state `a3`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b2`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c1`, messages from A: `X`, messages from B: `ε`
* **B** sends to **C**
  - **A**: state `a3`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b3`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c1`, messages from A: `X`, messages from B: `Z`
* **C** receives Z
  - **A**: state `a3`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b3`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c4`, messages from A: `X`, messages from B: `ε`
* **C** receives X
  - **A**: state `a3`, messages from B: `ε`, messages from C: `ε`
  - **B**: state `b3`, messages from A: `ε`, messages from C: `ε`
  - **C**: state `c5`, messages from A: `ε`, messages from B: `ε`

The send/receive order of the mailbox is also possible in the p2p case.
Furthermore, the p2p case allow for more possibilities that are not possible in the mailbox case.


#### Alternating bit protocol (ABP)

Let us look at a more complex example that will help us illustrate the difference between FIFO vs bag and reliable vs lossy channels.

The ABP appends `0` or `1` to messages in alternation and expect matching acknowledgment (`Ack0`, `Ack1`).
If the sender does not receive an acknowledgment, it resends messages.
The ABP work with unreliable channels as long as they are FIFO.

In the example below, the sender process _S_ tries to transmit the sequence `ABB` to the receiver process _R_.

* sender _S_
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      init [shape = none, label = ""];
      node [shape = circle, fixedsize = true, width=0.6];
      init -> ε;
      ε -> A [ label = "R!(A,0)" ];
      A -> A [ label = "R!(A,0)" ];
      A -> Aa [ label = "?Ack0" ];
      Aa -> AB [ label = "R!(B,1)" ];
      AB -> AB [ label = "R!(B,1), ?Ack0" ];
      AB -> ABa [ label = "?Ack1" ];
      ABa -> ABB [ label = "R!(B,0)" ];
      ABB -> ABB [ label = "R!(B,0), ?Ack1" ];
      ABB -> Done [ label = "?Ack0" ];
      Done -> Done [ label = "?Ack0" ];
  }
  ```
* receiver _R_ (partial)
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      init [shape = none, label = ""];
      Bcont, AAcont [shape = none, label = "..."];
      node [shape = circle, fixedsize = true, width=0.6];
      init -> ε;
      ε -> Aa [ label = "?(A,0)" ];
      ε -> Ba [ label = "?(B,0)" ];
      Aa -> A [ label = "S!Ack0" ];
      A -> Aa [ label = "?(A,0), ?(B,0)"];
      Ba -> B [ label = "S!Ack0" ];
      B -> Ba [ label = "?(A,0), ?(B,0)"];
      B -> Bcont [ label = "..." ];
      A -> AAa [ label = "?(A,1)" ];
      A -> ABa [ label = "?(B,1)" ];
      AAa -> AA [ label = "S!Ack1" ];
      AA -> AAa [ label = "?(A,1), ?(B,1)"];
      ABa -> AB [ label = "S!Ack1" ];
      AB -> ABa [ label = "?(A,1), ?(B,1)"];
      AA -> AAcont [ label = "..." ];
      AB -> ABAa [ label = "?(A,0)" ];
      AB -> ABBa [ label = "?(B,0)" ];
      ABAa -> ABA [ label = "S!Ack0" ];
      ABA -> ABAa [ label = "?(A,0), ?(B,0)"];
      ABBa -> ABB [ label = "S!Ack0" ];
      ABB -> ABBa [ label = "?(A,0), ?(B,0)"];
  }
  ```

Let us first look at a trace with reliable FIFO channels.

__Reliable FIFO trace.__
| Action                        | Sender state  | Sender mailbox    | Receiver state    | Receiver mailbox  |
| ----------------------------- | ------------- | ----------------- | ----------------- | ----------------  |
| Initial state                 | `ε`           | `ε`               | `ε`               | `ε`               |
| Sender sending `(A,0)`        | `A`           | `ε`               | `ε`               | `(A,0)`           |
| Receiver receiving `(A,0)`    | `A`           | `ε`               | `Aa`              | `ε`               |
| Receiver sending `Ack0`       | `A`           | `Ack0`            | `A`               | `ε`               |
| Sender receiving `Ack0`       | `Aa`          | `ε`               | `A`               | `ε`               |
| Sender sending `(B,1)`        | `AB`          | `ε`               | `A`               | `(B,1)`           |
| Receiver receiving `(B,1)`    | `AB`          | `ε`               | `ABa`             | `ε`               |
| Receiver sending `Ack1`       | `AB`          | `Ack1`            | `AB`              | `ε`               |
| Sender receiving `Ack1`       | `ABa`         | `ε`               | `AB`              | `ε`               |
| Sender sending `(B,0)`        | `ABB`         | `ε`               | `AB`              | `(B,0)`           |
| Receiver receiving `(B,0)`    | `ABB`         |  `ε`              | `ABBa`            | `ε`               |
| Receiver sending `Ack0`       | `ABB`         | `Ack0`            | `ABB`             | `ε`               |
| Sender receiving `Ack0`       | `Done`        | `ε`               | `ABB`             | `ε`               |

__Lossy FIFO trace.__
| Action                        | Sender state  | Sender mailbox    | Receiver state    | Receiver mailbox  |
| ----------------------------- | ------------- | ----------------- | ----------------- | ----------------  |
| Initial state                 | `ε`           | `ε`               | `ε`               | `ε`               |
| Sender sending `(A,0)`        | `A`           | `ε`               | `ε`               | `(A,0)`           |
| Network dropping `(A,0)`      | `A`           | `ε`               | `ε`               | `ε`               |
| Sender sending `(A,0)`        | `A`           | `ε`               | `ε`               | `(A,0)`           |
| Sender sending `(A,0)`        | `A`           | `ε`               | `ε`               | `(A,0)⋅(A,0)`     |
| Receiver receiving `(A,0)`    | `A`           | `ε`               | `Aa`              | `(A,0)`           |
| Receiver sending `Ack0`       | `A`           | `Ack0`            | `A`               | `(A,0)`           |
| Receiver receiving `(A,0)`    | `A`           | `Ack0`            | `Aa`              | `ε`               |
| Receiver sending `Ack0`       | `A`           | `Ack0⋅Ack0`       | `A`               | `ε`               |
| Sender receiving `Ack0`       | `Aa`          | `Ack0`            | `A`               | `ε`               |
| Sender sending `(B,1)`        | `AB`          | `Ack0`            | `A`               | `(B,1)`           |
| Sender receiving `Ack0`       | `AB`          | `ε`               | `A`               | `ε`               |
| …                             | …             | …                 | …                 | …                 |

With retransmission, traces can get quite a bit more complicated but the protocol still works as expected

__Reliable out-of-order (bag) trace.__
| Action                        | Sender state  | Sender mailbox    | Receiver state    | Receiver mailbox  |
| ----------------------------- | ------------- | ----------------- | ----------------- | ----------------  |
| Initial state                 | `ε`           | `∅`               | `ε`               | `∅`               |
| Sender sending `(A,0)`        | `A`           | `∅`               | `ε`               | `{(A,0)}`         |
| Sender sending `(A,0)`        | `A`           | `∅`               | `ε`               | `{(A,0),(A,0)}`   |
| Receiver receiving `(A,0)`    | `A`           | `∅`               | `Aa`              | `{(A,0)}`         |
| Receiver sending `Ack0`       | `A`           | `{Ack0}`          | `A`               | `{(A,0)}`         |
| Sender receiving `Ack0`       | `Aa`          | `ε`               | `A`               | `{(A,0)}`         |
| Sender sending `(B,1)`        | `AB`          | `ε`               | `A`               | `{(A,0),(B,1)}`   |
| Receiver receiving `(B,1)`    | `AB`          | `ε`               | `ABa`             | `{(A,0)}`         |
| Receiver sending `Ack1`       | `AB`          | `{Ack1}`          | `AB`              | `{(A,0)}`         |
| Sender receiving `Ack1`       | `ABa`         | `ε`               | `AB`              | `{(A,0)}`         |
| Sender sending `(B,0)`        | `ABB`         | `ε`               | `AB`              | `{(A,0),(B,0)}`   |
| Receiver receiving `(A,0)`    | `ABB`         |  `ε`              | `ABAa`            | `{(B,0)}`         |
| Receiver sending `Ack0`       | `ABB`         | `Ack0`            | `ABA`             | `ε`               |
| Sender receiving `Ack0`       | `Done`        | `ε`               | `ABA`             | `ε`               |

In this instance, the receiver process did received `ABA` instead of `ABB`.
This shows that ABP requires FIFO channel.

## Extensions

We will now discuss two simple extensions which does not actually increase the power of the model.

### Receiving From Specific Sender

In the case of p2p communication, we can have receive of the form $(ID×?×Σ)$, e.g., `q?a` for receiving message `a` from `q`.
The receive rule can be adapted to:
\\[{
M[i] \stackrel{j?a}{→_i} s   \qquad   C[j,i] = a·w   \qquad  C' = C[(j,i) ←  w]  \qquad  M' = M[i ← s]
} \over{
                        (M, C) → (M', C')
}
\\]

The same effect can be realized in the simpler model by expanding the alphabet of messages to $(ID×Σ)$, i.e., the message carry the identity of the sender.
With this new alphabet, the sender also needs to adds it's id to the messages it sends and the receiver can distinguish be looking at the id in the message.

### CSM with Internal Actions

We can also add internal actions to the CSM, i.e., actions that modifies the state but do not change the channels.

We modify the definitions of the machine to: $(id_i, S_i, Σ_i ∪ (ID × ! × Σ) ∪ (? × Σ) , →_i, s₀_i)$ with the constraints that $∀ i j.~ i≠j ⇒ Σ_i ∩ Σ_j = ∅$. 

The corrsponding transition rule is:
\\[{
M[i] \stackrel{e}{→_i} s  \qquad  M' = M[i ← s]  \qquad (∀ a ∈ Σ.~ e ≠ ?a)  \qquad (∀ a ∈ Σ,~ j ∈ ID.~ e ≠ j!a)
} \over{
                        (M, C) → (M', C)
}
\\]

Since, these internal transition does not affect the overall system, we can replace them by ε-transition and eliminate them using the algorithms from automata theory.



## CSM with unbounded reliable FIFO channels is a Turing complete model of computation

The details of the reduction are intricate.
However, the overall idea is fairly simple.
In the following note, we will only look at the overall idea behind the proof.

### Short reminder about Turing machine

A Turing machine is composed of two elements:
* head: instructions are given by a finite state machine, can: read, write, move forward, move backward
* tape: infinite tape that start with an initial word

It has an alphabet `Σ` to store words on the tape and a _blank symbol_ (represent empty cells on the tape).
A transition is the combination of reading the character at the current position, updating the local state, writing a new character, moving forward or backward.
The state machine for the head has a special _halt_ state which has no outgoing transition.


### Structure of the encoding

We keep the head from the Turing machine and insert extra parts to simulate the infinite tape using unbounded channels.

When reducing a Turing machine to a CSM, some of the functionality of the Turing machine cannot be mapped to a single transition but to a sequence of transitions.
The substrucutres implementing these operations are usually called gadget.
In this case, they are small finite state machine with a single start state and a single end state.

The overall structure is:
```
┌───────┐
│ head  │
│-------│ ┌────┐
│buffer │⇆│echo│
└───────┘ └────┘
```

We now show how to implement each of these parts.

__Buffer.__
The buffer is the key part that interact with the channel and the head.
The tape of the Turing machine is split between the channels which stores most of the tape and small _buffer_ state machine which store the letter for the current position and whether we have past the last written symbol, i.e., we are "extending" the channel.
Compared to a tape, the buffer + channel combination can only move forward and, when it reaches the end, it loops back to the beginning of the tape.

The set of messages is between the buffer and echo are:
* `Σ` (alphabet of the Turing machine)
* blank symbol (also from Turing machine)
* end of tape symbol
* current position marker

The buffer synchronizes with the head on transitions of the form `Σ × Σ × {F/B}` where the 1st element is the read character, the 2nd is the character to write, and whether to move forward or backward.

Reading and writing just depends on the current state which is store in the state of the finite state machine.
Therefore, it is a normal transition of a NFA.
On the other hand, moving forward/backward requires interacting with the channel.

_Moving forward._
* If not past the end of tape:
  1. send the current character to echo
  2. receive the next character from the channel
  3. if the character is "end-of-tape" then remember that the buffer is beyond the last written character and store "blank" as the current character
* If beyond the last written character:
  1. send the current character to echo
  2. use "blank" as the current character 

_Moving backward._
1. send the "current position" marker to echo
2. if not yet past the end then move forward until the "end of tape" character (each time sending the read characters back to echo)
3. send "end of tape to echo"
4. move forward until the "current position" marker is found, discard the marker and keep the previous character in memory


__Echo.__
Is a simple state machine that receives any messages and sends it back.

For instances, if the set of messages is `{a,b}`, echo looks like:
```
  ( )
?a ⇅ !a
→ ( )
!b ⇅ ?b
  ( ) 
```

Notice that only one of the two channels need to be unbounded for this reduction to work.

_Example._

Let us look at the tape of a turing machine where the tape contains `abc`, the head points to the 2nd position, and make transition that read `b`, write `d`, and move backward:
```
 ↓                   ↓
abc ─(b,d,backward)⇒ adc
```

Let us look at the CSM encoding.
let `.` be the end of tape symbol and `|` by the current position marker.
The corresponding states are:
```
current: b                                current: a
echo → buffer: c.a  ─(b,d,backward)⇒ … →  echo → buffer: dc.
buffer → echo: ε                          buffer → echo: ε
```
However, this is not a one step process.
Let us look at the intermediate steps:
* update the current state:
  ```
  status: ready                             status: backward/insert_current
  current: b                                current: d
  echo → buffer: c.a  ─(b,d,backward)⇒ … →  echo → buffer: c.a
  buffer → echo: ε                          buffer → echo: ε
  ```
* inserting current position and echo:
  ```
  status: backward/insert_current           status: backward/loop               status: backward/loop
  current: b                                current: d                          current: d
  echo → buffer: c.a            →           echo → buffer: c.a          →       echo → buffer: c.a|
  buffer → echo: ε                          buffer → echo: |                    buffer → echo: ε
  ```
* finding the end of the tape and echo:
  ```
  status: backward/loop                     status: backward/loop               status: backward/loop
  current: d                                current: c                          current: c
  echo → buffer: c.a|           →           echo → buffer: .a|          →       echo → buffer: .a|d
  buffer → echo: ε                          buffer → echo: d                    buffer → echo: ε
  ```
  ```
  status: backward/loop                     status: backward/find_marker        status: backward/find_marker
  current: c                                current: .                          current: .
  echo → buffer: .a|d           →           echo → buffer: a|d          →       echo → buffer: a|dc
  buffer → echo: ε                          buffer → echo: c                    buffer → echo: ε
  ```
* finding the marker and echo:
  ```
  status: backward/find_marker              status: backward/find_marker        status: backward/find_marker
  current: .                                current: a                          current: a
  echo → buffer: a|dc           →           echo → buffer: |dc          →       echo → buffer: |dc.
  buffer → echo: ε                          buffer → echo: .                    buffer → echo: ε
  ```
  ```
  status: backward/find_marker              status: ready
  current: a                                current: a
  echo → buffer: |dc.           →           echo → buffer: dc.
  buffer → echo: ε                          buffer → echo: ε
  ```

__Initialization.__

To finish the reduction, we need to initialize the channel with the input word.
For this we can extend the buffer state machine so that it send to echo the initial word before synchronizing with transitions of the head.

_Remark._
In this reduction, we use transition which are not related to sending or receiving messages, for example we use some form of synchronous product between the head and the buffer.
Notice, that these transitions are only between finite state machines and do not change the channels.
We can remove these extra transitions by:
1. compute the synchronous product between the head and the buffer to have a single state machine
2. replace the transition not related to messages by `ε`
3. use an NFA minimization algorithm to get rid of the `ε` edges.


### Limitations of the proofs

The reductions only needs two machines and one unbounded FIFO channel (the other channel may be bounded).
On the other hand, changing the model of the channel easily breaks the reduction.

Let us look what happens if the channels are:
* bounded: ???
* bags: ???
* lossy: next week ...
* [half-duplex communication and two machines](https://www.sciencedirect.com/science/article/pii/S0890540105001082)

__Half-duplex communication.__
Half duplex systems are the communication is only one direction at the same time.
Let `P` and `Q` be two processes in a half-duplex systems.
`P` can send a messages to `Q` only if the channel from `Q` to `P` is empty.

The send rules become:
\\[{
M[i] \stackrel{j!a}{→_i} s   \qquad   C[j,i] = ε  \qquad   C' = C[(i,j) ←  C[i,j]·a]  \qquad  M' = M[i ← s]
} \over{
                        (M, C) → (M', C')
}
\\]

With only two machines, the problem becomes decidable.
Intiutively, the channels need to become empty before the dirrection of the communication changes and, therefore, it is not possible to store more information than the (finite) local state of the two machines.

The proof uses are normalization lemma.
Every execution can be transformed into an equivalent execution (w.r.t. the reachable local states) where the channels are 1-bounded.
