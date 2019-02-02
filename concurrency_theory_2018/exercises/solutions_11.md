# Solutions 11

## Peterson's Algorithm and TSO semantics

TLDR:
1. incorrect.
2. correct.
3. incorrect.
4. correct.

In more details:

1. We can delay the update of `flag` so both processes can enter the critical section:
    ```
    TSO                 memory                      TSO store buffer
                        flag: [0, 0], turn: 0       0: ε, 1: ε
    write_0(flag[0], 1);
                        flag: [0, 0], turn: 0       0: (flag[0], 1), 1: ε
    write_0(turn, 1);
                        flag: [0, 0], turn: 0       0: (turn, 1)⋅(flag[0], 1), 1: ε
    write_1(flag[1], 1);                                         
                        flag: [0, 0], turn: 0       0: (turn, 1)⋅(flag[0], 1), 1: (flag[1], 1)
    write_1(turn, 0);                                            
                        flag: [0, 0], turn: 0       0: (turn, 1)⋅(flag[0], 1), 1: (turn, 0)⋅(flag[1], 1)
    read_0(turn, 1);
    read_1(turn, 0);
    read_1(flag[0], 0);
    -> ERROR both processes in the critical section
    ```

2. This is perhaps the most interesting version.
  Here is why the algorithm is correct:
  * Writing the `flag` and directly using a `fence();` make this write like a write under SC.
    So we don't need to care about the buffer here.
  * In the case of the processes both trying to enter at the same time, because of the `fence`s we have that `flag: [1, 1]` therefore the second part of the while loop condition is false.
  * The write to `turn` is always visible to the process that write (read from buffer) and that write makes the first part of the condition true.
    This bias the process toward not entering the critical section.
  * While the write to turns are in the buffer, the processes are both stuck in the while loop.
  * To make sure that the algorithm is correct, we need to check what happens when the write to `turn` get from the buffers to the memory:
    - The first process which write to `turn` get into the memory is still stuck as it does not change how `turn != id` evaluates.
    - When the 2nd write to `turn` gets into the memory the process that write is still stuck but then the other process can enter the critical section.


3. Actually, just the reordering makes the algorithm incorrect even under SC. So we can ignore the buffers.
    ```
    TSO                 memory
                        flag: [0, 0], turn: 0
    write_0(turn, 1);
                        flag: [0, 0], turn: 1
    write_1(turn, 0);
                        flag: [0, 0], turn: 0
    write_1(flag[1], 1);
                        flag: [0, 1], turn: 0
    read_1(turn, 0);
                        flag: [0, 1], turn: 0
    read_1(flag[0], 0);
                        flag: [0, 1], turn: 0
    write_0(flag[0], 1);
                        flag: [1, 1], turn: 0
    read_0(turn, 0);
                        flag: [1, 1], turn: 0
    -> ERROR both processes in the critical section
    ```

4. As we are forcing the write to happens before reading, we the algorithm behaves as the SC version.


## On the Generality of our TSO Formalization

#### Task 1

Intuitively, the processes are going to coordinate and decide what program to execute depending on the order in which they execute their first transition.
The synchronization between processes is done with an atomic-read-write to a dedicated memory location.

Let us assume that $∀ p q.\ Q_p ∩ Q_q = ∅$.

Also we associate an unique integer (process id) in $[0,|\mathbb{P}|)$ to each process $p$ in $\mathbb{P}$.

* $\mathbb{A}' = \mathbb{A} ⊎ \\{t\\}$ (we add a new memory location $t$ to decide which process executes which program.)
* $\mathbb{D}' = \mathbb{D} ∪ \\{0 … |\mathbb{P}|\\}$ (we makes sure there is more data values than processes.)
* $Q = \\{q_0\\} \cup \bigcup_{p ∈ \mathbb{P}} Q_p$ (assume $q\_0$ is a fresh state not in any $Q_p$)
* $Σ$ is determined by $\mathbb{A}'$ and $\mathbb{D}'$
* $δ = \\{ (q_0, arw(t, i, i+1), q_{0i}) ~|~ 0 ≤ i < \mathbb{P} \\} \cup \bigcup_{p ∈ \mathbb{P}} δ_p$


#### Task 2

We proceed in two steps:
1. We modify a single program to initialize the memory and all the other processes to wait until the memory is initialized.
2. We use the construction above to put these different program together.

Let us define how we can do the first step:

Also we represent memory addresses by integer in $[0,|\mathbb{A}|)$.

First we need to add new memory address and make sure there is at least two different data values:
* $\mathbb{A}' = \mathbb{A} ⊎ \\{init\\}$ (we add a new memory location $init$ as flag indicating is the memory is initialized.)
* $\mathbb{D}' = \mathbb{D} ∪ \\{0, 1\\}$


_Memory initializer._ 
Let us modify $(Q, \Sigma, δ, q_{0})$ so it initializes the memory:
* $Q' = Q ⊎ \\{ q_i' ~|~ 0 ≤ i ≤ |\mathbb{A}| \\}$
* $Σ'$ is determined by $\mathbb{A}'$ and $\mathbb{D}'$
* $δ' = \\{ (q_i', write(i, m_{init}[i]), q_{i+1}') \\} \cup \\{ (q_{\mathbb{A}}', write(init, 1), q_0) \\} \cup δ$
* $q_0'$ is the new initial state

_Rest._
Let us modify $(Q, \Sigma, δ, q_{0})$ to wait until the memory is initialized:
* $Q' = Q ∪ \\{q_0'\\}$ (assume $q\_0'$ is a fresh state not in any $Q$)
* $Σ'$ is determined by $\mathbb{A}'$ and $\mathbb{D}'$
* $δ' = \\{ (q_0', read(init, 1), q_{0}) \\} \cup δ$
* $q_0'$ is the new initial state
