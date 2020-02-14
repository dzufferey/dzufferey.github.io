# Bonus Solutions 2


## Litmus Tests for Weak Memory Models

> ```
> thread A    ∥   thread B   
> ------------∥------------  
> write(x, 1) ∥   write(y, 1)
> read(y, 1)  ∥   read(x, 1) 
> ```
SC, TSO, PSO


> ```
> thread A    ∥   thread B
> ------------∥------------
> write(x, 1) ∥   write(y, 1)
> read(y, 0)  ∥   read(x, 0)
> ```
TSO, PSO

> ```
> thread A    ∥   thread B   
> ------------∥------------  
> read(x, 1)  ∥   read(y, 1) 
> write(y, 1) ∥   write(x, 1)
> ```
Not possible in any model

> ```
> thread A    ∥   thread B
> ------------∥------------
> read(x, 0)  ∥   read(y, 1)
> write(y, 1) ∥   write(x, 1)
> ```
SC, TSO, PSO

> ```
> thread A    ∥   thread B  
> ------------∥------------ 
> write(x, 1) ∥   read(y, 0)
> write(y, 1) ∥   read(x, 1)
> ```
SC, TSO, PSO

> ```
> thread A    ∥   thread B
> ------------∥------------
> write(x, 1) ∥   read(y, 1)
> write(y, 1) ∥   read(x, 0)
> ```
PSO

> ```
> thread A    ∥   thread B  
> ------------∥------------ 
> write(x, 1) ∥   read(y, 2)
> fence       ∥   read(x, 0)
> write(y, 2) ∥             
> ```
Not possible in any model

> ```
> thread A    ∥   thread B
> ------------∥------------
> write(x, 1) ∥   read(y, 0)
> fence       ∥   read(x, 1)
> write(y, 2) ∥
> ```
SC, TSO, PSO


## Weak Memory Control Automaton from Code

* `peterson(0)`
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      Z [shape = doublecircle];
      init -> A;
      A -> B [ label = "write(flag[0], 1)" ];
      B -> C [ label = "write(turn, 1)" ];
      C -> D [ label = "fence" ];
      D -> D [ label = "read(turn, 1)" ];
      D -> E [ label = "read(turn, 0)" ];
      E -> D [ label = "read(flag[1], 1)" ];
      E -> F [ label = "read(flag[1], 0)" ];
      F -> G [ label = "nop" ];
      G -> Z [ label = "write(flag[0], 0)" ];
  }
  ```
* `negate(x)`
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      Z [shape = doublecircle];
      init -> A;
      A -> B0 [ label = "read(x, 0)" ];
      B0 -> C0 [ label = "arw(x, 0, 1)" ];
      B0 -> A [ label = "nop" ];
      C0 -> Z [ label = "nop" ];
      A -> B1 [ label = "read(x, 1)" ];
      B1 -> C1 [ label = "arw(x, 1, 0)" ];
      B1 -> A [ label = "nop" ];
      C1 -> Z [ label = "nop" ];
  }
  ```

## On CSM with bags

> CSM → PN

For each machine, we encode the machine's state as places.
Then for each type of messages and each machine we create a place.
These places count the number of messages in each bag.

The transitions that send messages move a token in the machine state places and put a token in the appropriate bag place.

The transitions that receive messages move a token in the machine state places and consume a token from the appropriate bag place.

A control-state objective correspond to covering a marking with one token in the place corresponding to that state.

__TODO ...__


> How many places and transitions does the PN have? Describe it as function with parameters `N`, `m`, and `|Σ|`.
This encoding the corresponding PN has $m (N + |Σ|)$ places and $m (N + |Σ|)$ transitions assuming the CSM are deterministic.


> PN → CSM

The idea is to encode the marking in the bag and have the machine simulates the PN transitions by serializing the tokens consumption and production.

For each place of the PN we create one message in the alphabet.

Then we need two machines.
One machine simulates the PN transitions and the other is an "echo" machine.

__TODO ...__

