# Solutions 8

## Ideal KM Tree for the alternating bit protocol

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

We represent the state as `(0, ε, a, ε, 0)` where the elements are (in order):
1. `0` is the state of the sender
2. `ε` is the channel to the sender
3. `a` is the state of the receiver
4. `ε` is the channel to the receiver
5. `0` is the level of ideal for the ideal KM algo

For simplicitiy, we omit the transitions that do not change the state adn merge 2 branches.

```
(0, ε, a, ε, 0)     ─ (!Ack1)* →    (0, Ack1*, a, ε, 1)
      ↓ (!Msg0)*                          ↓ (!Msg0)*
(0, ε, a, Msg0*, 1) ─ (!Ack1)* →    (0, Ack1*, a, Msg0*, 2)
      ↓ ?Msg0                             ↓ ?Msg0
(0, ε, b, Msg0*, 1)                 (0, Ack1*, b, Msg0*, 2)
      ↓ (!Ack0)*                          ↓ (!Ack0)*
(0, Ack0*, b, Msg0*, 2)             (0, Ack1*Ack0*, b, Msg0*, 3)
      ↓ ?Ack0                             ↓ ?Ack0
(1, Ack0*, b, Msg0*, 2)             (1, Ack0*, b, Msg0*, 3)
      ↓ (!Msg1)*                          ↓ (!Msg1)*
(1, Ack0*, b, Msg0*Msg1*, 3)        (1, Ack0*, b, Msg0*Msg1*, 4)
      ↓ ?Msg1                             ↓ ?Msg1
(1, Ack0*, a, Msg1*, 3)             (1, Ack0*, a, Msg1*, 4)
      ↓ (!Ack1)*                          ↓ (!Ack1)*
(1, Ack0*Ack1*, a, Msg1*, 4)        (1, Ack0*Ack1*, a, Msg1*, 5)
      ↓ ?Ack1                             ↓ ?Ack1
(0, Ack1*, a, Msg1*, 4)             (0, Ack1*, a, Msg1*, 5)
      ↓ (!Msg0)*                          ↓ (!Msg0)*
(0, Ack1*, a, Msg1*Msg0*, 5)        (0, Ack1*, a, Msg1*Msg0*, 6)
      ↓ ?Msg0                             ↓ ?Msg0
(0, Ack1*, b, Msg0*, 5)             (0, Ack1*, b, Msg0*, 6)
      ↓ (!Ack0)*
(0, Ack1*Ack0*, b, Msg0*, 6)
      ↓ ?Ack0
(1, Ack0*, b, Msg0*, 6)
```

