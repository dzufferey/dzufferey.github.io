# Communicating State Machines

__Notations.__
* To send and receive messages, we use the CCS notations (CCS = communicating sequential processes).
  - `p!a`: sending message `a` to `p`. The `p` can be ommited in some models.
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


## Definitions

To have more compact definitions, we will one fist part which is shared among all the variations and then we will have multiple variations.


A system of communicating state machine is a paire `(Σ, ⋃_{i∈[1;N]} M_i)` where
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
  - peer to peer: `C(i,j)` is a FIFO buffer between each pair of processes
  - mailbox: `C(i)` is a FIFO buffer, each process has a single mailbox where all the incoming messages get multiplexed
  - unordered: `C(i)` is a bag (multisets)
  - synchronous: there are no channel


__Notations.__
* Queue:
  - append / pop back:  `w = w′·a`, sometime even simpler `w = w′a`
  - prepend / pop head: `w = a·w′`, sometime even simpler `w = aw′`
* Maps:
  - `M(i)` returns the value associated to `i` in `M`
  - `M′ = M[i → s]` creating a new map with the same values except for `i` which gets value `s`. This is a shortand for `∀ j. (j ≠ i ∧ M′(j) = M(j)) ∨ (j = i ∧ M′(i) = s)`.
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

Synchronous sytems are quite different in the sense that they do not have channels.
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
Sending a message requires the extra checks: `|C(j)| < k` (addes as an additional premise to the rule.)


## Examples

TODO ...

Alternating bit protocol (FIFO vs bag)

Difference between p2p and mailbox

Synchronous ping pong

Juggling as variation of ping pong that needs buffers
