# Solutions 7

## Different channel models

### Differences between semantics

#### An example which distinguishes between unbounded+FIFO+p2p+reliable and unbounded+FIFO+p2p+lossy

```
  →  (0)
      ↓ !a
     (1)
  ?c ↑↓ !b
     (2)
```

```
  →  (a)
  !c ↑↓ ?b
     (c)
```

With a reliable semantics, the systems get stuch after sending `a` and `b` as the second machine never receives `a`.

With a lossy semantics, it is possible to drop the message `a` and go into the `b`,`c` loop.

#### An example which (a) cannot be distinguished by synchronous+reliable and 1-bounded+FIFO+p2p+reliable, but (b) is distinguishable with 2-bounded+FIFO+p2p+reliable?

* A
    ```
         B!x   B!x   C!y
    → (0) → (1) → (2) → (3)
    ```
* B
    ```
         ?x    ?x    ?z
    → (0) → (1) → (2) → (3)
    ?z ↓  ?x   ?x    
      (3) → (4) → (5)
    ```
* C
    ```
         ?y    B!z
    → (0) → (1) → (2)
    ```

With a synchronous or 1-bounded semantics, `B` can never reach the states `(3)`, `(4)`, `(5)`.
But it can reach theses states with a bound of 2.
All the other states are reachable.

#### [Optional] show that with unbounded+bag reliable or lossy cannot be distinguished.

* `⇒` Traces of the reliable semantics are included the lossy semantics. (This is true for any version with unbounded channel.)
* `⇐` The messages sent in both version are the same (unbounded channel cannot block on send). Any recieve in the lossy semantics may also be done in the reliable semantics. Since the channel are not ordered, we can permute the channel content and move the dropped messages to the "back of the channel" and never deliver them.

#### [Optional] Give an example that distinguishes bounded+bag+reliable and bounded+bag+lossy (the bound is up to you)

With a bound of 1:

* A
    ```
         B!x   B!x
    → (0) → (1) → (2)
    ```
* B
    ```
    → (0)
    ```

With a reliable semantics, `A` gets stuck after the first message but in a lossy semantics it can send both messages.

### Synchronous and Lossy systems

The rule for the normal message exchang is the same.

Step
```
→ (M(i), j!a, s)    → (M(j), ?a, r)    M′ = M[i → s]    M″ = M′[j → r]
──────────────────────────────────────────────────────────────────────
                        (M, ∅) → (M″, ∅)
```

We add a new rule that allow unmatched send:

Drop
```
→ (M(i), j!a, s)    M′ = M[i → s]
─────────────────────────────────
        (M, ∅) → (M′, ∅)
```
