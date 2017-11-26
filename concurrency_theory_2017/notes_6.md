# Communicating State Machines

__Notations.__
* To send and receive messages, we use the CCS notations (CCS = communicating sequential processes).
  - `p!a`: sending message `a` to `p`. The `p` can be omitted in some models.
  - `?a`: receiving message `a`.
* For the moment we consider systems with a fixed number of processes. We use `N` for the number of processes.

## Example

Let consider the following to state machines:

* ping
    ```
      →  (init)
    ?Pong ↑ ↓ pong!Ping
         (wait)

    ```
* pong
    ```
         →  (init)
    ping!Pong↑ ↓ ?Ping
            (ack)
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

To have more compact definitions, we will one fist part which is shared among all the variations and then we will have multiple variations.


A system of communicating state machine is a pair `(Σ, ⋃_{i∈[1;N]} M_i)` where
* `Σ` finite set of messages shared among all the machines
* each `M_i` is a DFA/NFA `(id_i, S_i, (ID × ! × Σ) ∪ (? × Σ) , →, s₀_i)` with
  - `id_i` is an unique ID for this particular machine (the ID is used to send messages to that particular machine.)
  - `S_i` is the set of states of machine `i`
  - the alphabet is composed of two part: (1) sending messages `(ID × ! × Σ)` and (2) receiving messages `(? × Σ)`
  - `→` is the transition relation
  - `s₀_i` is the initial state

The model of the channel only comes when we model the state of the system.
To model channels, we can pick among the following characteristics:
* FIFO or unordered
* unbounded, bounded, synchronous
* reliable or lossy

This choice will influence how we model the state of the system and the transitions.
Picking different models can be for accuracy of the model or decidability of some problems in a given model.

The state of a system is a pair `(S,C)` where
* `M` is a map from `id` to states of the corresponding machine
* `C` represent the channels. Depending on the type of system we want to model there are kinds of channel:
  - point to point: `C(i,j)` is a FIFO buffer between each pair of processes
  - mailbox: `C(i)` is a FIFO buffer, each process has a single mailbox where all the incoming messages get multiplexed
  - unordered: `C(i)` is a bag (multisets)
  - synchronous: there are no channel


__Notations.__
* Queue:
  - append / pop back:  `w = w′·a`, sometime even simpler `w = w′a`
  - prepend / pop head: `w = a·w′`, sometime even simpler `w = aw′`
* Maps:
  - `M(i)` returns the value associated to `i` in `M`
  - `M′ = M[i → s]` creating a new map with the same values except for `i` which gets value `s`. This is a shorthand for `∀ j. (j ≠ i ∧ M′(j) = M(j)) ∨ (j = i ∧ M′(i) = s)`.
* Inferrence rules are written as
  ```
  premises
  ──────────
  conclusion
  ```
  They basically are the same as `premises ⇒ conclusion`.

We can now discuss the semantics of the model discussed above:

### Reliable p2p FIFO

Sending a message
```
→ (M(i), j!a, s)    C′ = C[(i,j) →  C(i,j)·a]    M′ = M[i → s]
──────────────────────────────────────────────────────────────
                    (M, C) → (M′, C′)
```

Receiving a message
```
→ (M(i), ?a, s)    C(j,i) = a·w    C′ = C[(j,i) →  w]    M′ = M[i → s]
──────────────────────────────────────────────────────────────────────
                        (M, C) → (M′, C′)
```

### Lossy p2p FIFO

Same as reliable p2p FIFO and the following rule

Dropping a message
```
C(i,j) = w·a·w′    C′ = C[(i,j) →  w·w′]
────────────────────────────────────────
            (M, C) → (M, C′)
```

### Reliable mailbox FIFO

Sending a message
```
→ (M(i), j!a, s)    C′ = C[j →  C(j)·a]    M′ =  M[i →  s]
──────────────────────────────────────────────────────────
                (M, C) → (M′, C′)
```

Receiving a message
```
→ (M(i), ?a, s)    C(i) = a·w    C′ = C[i →  w]    M′ = M[i → s]
────────────────────────────────────────────────────────────────
                  (M, C) → (M′, C′)
```

### Lossy mailbox FIFO

Same as reliable mailbox FIFO and the following rule

Dropping a message
```
C(i) = w·a·w′    C′(i) ← w·w′
─────────────────────────────
      (M, C) → (M, C′)
```

### Reliable bag

Sending a message
```
→ (M(i), j!a, s)    a ∈ C(j)    C′ C[j → C(j) ∪ {a}]    M′ = M[i →  s]
────────────────────────────────────────────────────────────────────
                        (M, C) → (M′, C′)
```

Receiving a message
```
→ (M(i), ?a, s)    a ∈ C(i)    C′ = C[i → C(i) ∖ {a}]    M′ = M[i → s]
──────────────────────────────────────────────────────────────────────
                        (M, C) → (M′, C′)
```

### Lossy bag

Same as reliable bag and the following rule

Dropping a message
```
a ∈ C(i)    C′ = C[i → C(i) ∖ {a}]
──────────────────────────────────
        (M, C) → (M, C′)
```

### Synchronous

Synchronous systems are quite different in the sense that they do not have channels.
A message needs to be send and received in the same step.

Step
```
→ (M(i), j!a, s)    → (M(j), ?a, r)    M′ = M[i → s]    M″ = M′[j → r]
──────────────────────────────────────────────────────────────────────
                        (M, ∅) → (M″, ∅)
```


### Bounded

Having bounded channels just add an extra check when sending the messages.
Sending is only possible when the channel is not full.

Let `k` be the bound (`k ≥ 1`).
Sending a message requires the extra checks: `|C(j)| < k` (added as an additional premise to the rule.)


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
    ```
      →  (init)
           ↓ right!Ball
         (full)
    ?Ball ↑ ↓ right!Ball
         (free)

    ```
* right hand
    ```
      →  (full)
    ?Ball ↑ ↓ left!Ball
         (free)
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

* A
    ```
    →  (a1)
        ↓ C!X
       (a2)
        ↓ B!Y
       (a3)
    ```
* B
    ```
    →  (b1)
        ↓ ?Y
       (b2)
        ↓ C!Z
       (b3)
    ```
* C
    ```
            ?Z     ?X
    →  (c1) → (c4) → (c5)
        ↓ ?X
       (c2)
        ↓ ?Z
       (c3)
    ```

To represent the execution, we need to be more careful about the representation of the channel.
First, let us look at the mailbox semantics

__Mailbox trace.__
* initial state
  - A: state `a1`, messages: `ε`
  - B: state `b1`, messages: `ε`
  - C: state `c1`, messages: `ε`
* A sends to C
  - A: state `a2`, messages: `ε`
  - B: state `b1`, messages: `ε`
  - C: state `c1`, messages: `X`
* A sends to B
  - A: state `a3`, messages: `ε`
  - B: state `b1`, messages: `Y`
  - C: state `c1`, messages: `X`
* B receives Y
  - A: state `a3`, messages: `ε`
  - B: state `b2`, messages: `ε`
  - C: state `c1`, messages: `X`
* B sends to C
  - A: state `a3`, messages: `ε`
  - B: state `b3`, messages: `ε`
  - C: state `c1`, messages: `X·Z`
* C receives X
  - A: state `a3`, messages: `ε`
  - B: state `b3`, messages: `ε`
  - C: state `c2`, messages: `Z`
* C receives Z
  - A: state `a3`, messages: `ε`
  - B: state `b3`, messages: `ε`
  - C: state `c3`, messages: `ε`

This is not the only trace, but in all the traces of the mailbox semantics, C receives `X` before `Z`.

Now let us look at the point to point semantics.

__P2p trace.__
* initial state
  - A: state `a1`, messages from B: `ε`, messages from C: `ε`
  - B: state `b1`, messages from A: `ε`, messages from C: `ε`
  - C: state `c1`, messages from A: `ε`, messages from B: `ε`
* A sends to C
  - A: state `a2`, messages from B: `ε`, messages from C: `ε`
  - B: state `b1`, messages from A: `ε`, messages from C: `ε`
  - C: state `c1`, messages from A: `X`, messages from B: `ε`
* A sends to B
  - A: state `a3`, messages from B: `ε`, messages from C: `ε`
  - B: state `b1`, messages from A: `Y`, messages from C: `ε`
  - C: state `c1`, messages from A: `X`, messages from B: `ε`
* B receives Y
  - A: state `a3`, messages from B: `ε`, messages from C: `ε`
  - B: state `b2`, messages from A: `ε`, messages from C: `ε`
  - C: state `c1`, messages from A: `X`, messages from B: `ε`
* B sends to C
  - A: state `a3`, messages from B: `ε`, messages from C: `ε`
  - B: state `b3`, messages from A: `ε`, messages from C: `ε`
  - C: state `c1`, messages from A: `X`, messages from B: `Z`
* C receives Z
  - A: state `a3`, messages from B: `ε`, messages from C: `ε`
  - B: state `b3`, messages from A: `ε`, messages from C: `ε`
  - C: state `c4`, messages from A: `X`, messages from B: `ε`
* C receives X
  - A: state `a3`, messages from B: `ε`, messages from C: `ε`
  - B: state `b3`, messages from A: `ε`, messages from C: `ε`
  - C: state `c5`, messages from A: `ε`, messages from B: `ε`

The send/receive order of the mailbox is also possible in the p2p case.
Furthermore, the p2p case allow for more possibilities that are not possible in the mailbox case.


#### Alternating bit protocol

Let us look at a more complex example that will help us illustrate the difference between FIFO vs bag and reliable vs lossy channels.

TODO explain

* sender
  ```
      →  (ε)
          ↓ receiver!(A,0)
         (A) ⤸ receiver!(A,0)
          ↓ ?Ack0
         (Aa)
          ↓ receiver!(B,1)
         (AB) ⤸ receiver!(B,1), ?Ack0
          ↓ ?Ack1
         (ABa)
          ↓ receiver!(B,0)
         (ABB) ⤸ receiver!(B,0), ?Ack1
          ↓ ?Ack0
         (Done) ⤸ ?Ack0
  ```
* receiver (partial)
  ```
                                ↙ ?(A,0), ?(B,0) ┐
             →  (ε) ─?(B,0)→ (Ba) ─sender!Ack0→ (B)  ...
                 │                               │
               ?(A,0)                          ?(A,1)
                 ↓                               ↓
                (Aa)                            (BAa) ...
                 ↑│
    ?(A,0), ?(B,0)│
                 │sender!Ack0
                 │↓ a            ↙ ?(A,1), ?(B,1) ┐                 ↙ ?(A,0), ?(B,0) ┐
                (A) −?(B,1)→ (ABa) ─sender!Ack1→ (AB) ─?(B,0)→ (ABBa) ─sender!Ack0→ (ABB)
                 │                                │
               ?(A,1)                           ?(A,0)
                 ↓                                ↓
                (AAa)                            (ABAa)
                 ↑│                               ↑│
    ?(A,1), ?(B,1)│                  ?(A,0), ?(B,0)│
                 │sender!Ack1                     │sender!Ack0
                 │↓                               │↓ 
                (AA) ─?(B,0)→ ...                (ABA)
                 │
               ?(A,0)
                 ↓
                (AAAa)
                 ↑│
    ?(A,0), ?(B,0)│
                 │sender!Ack0
                 │↓ 
                (AAA)
  ```

TODO traces
