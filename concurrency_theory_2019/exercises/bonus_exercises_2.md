# Bonus Homework 2

_Instructions_
* Due on Feb 10, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).
* People who submit just be themselves will get a 2x multiplier toward qualifying for the exam.


## Litmus Tests for Weak Memory Models

Let us look at the memory operations of concurrently executing programs.

We assume that initially, all the memory locations are initialized with `0`.

Consider the following traces for pairs of programs.
We do not specify the interleaving between the two programs.

_examples 1_ (writes are the same, only the reads change)
```
thread A    ∥   thread B            thread A    ∥   thread B
------------∥------------           ------------∥------------
write(x, 1) ∥   write(y, 1)         write(x, 1) ∥   write(y, 1)
read(y, 1)  ∥   read(x, 1)          read(y, 0)  ∥   read(x, 0)
```

_examples 2_ (writes are the same, only the reads changes)
```
thread A    ∥   thread B            thread A    ∥   thread B
------------∥------------           ------------∥------------
read(x, 1)  ∥   read(y, 1)          read(x, 0)  ∥   read(y, 1)
write(y, 1) ∥   write(x, 1)         write(y, 1) ∥   write(x, 1)
```

_examples 3_ (writes are the same, only the reads changes)
```
thread A    ∥   thread B            thread A    ∥   thread B
------------∥------------           ------------∥------------
write(x, 1) ∥   read(y, 0)          write(x, 1) ∥   read(y, 1)
write(y, 1) ∥   read(x, 1)          write(y, 1) ∥   read(x, 0)
```

_examples 4_ (writes are the same, only the reads changes)
```
thread A    ∥   thread B            thread A    ∥   thread B
------------∥------------           ------------∥------------
write(x, 1) ∥   read(y, 2)          write(x, 1) ∥   read(y, 0)
fence       ∥   read(x, 0)          fence       ∥   read(x, 1)
write(y, 2) ∥                       write(y, 2) ∥
```

### Questions
* For each example, try to identify if the execution is possible under any of the memory model that we saw (SC, TSO, PSO.)


## Weak Memory Control Automaton from Code

When we discussed weak memory models, we saw programs as NFAs with the following operations on the transitions:
* $nop$ (no operation)
* $read(\mathbb{A}, \mathbb{D})$
* $write(\mathbb{A}, \mathbb{D})$
* $fence$
* $arw(\mathbb{A}, \mathbb{D}, \mathbb{D})$ (atomic-read-write)

On the other hand, code looks like:
```c
bool turn;
bool flag[2] = {0, 0};

void peterson(bool id /* 0 or 1 */) {
    flag[id] = 1;
    turn = 1-id;
    fence();
    while (turn != id && flag[1-id]) { }
    // entering critical section
    ...
    // exiting critical section
    flag[id] = 0;
}

spawn(peterson(0));
spawn(peterson(1));
```

or like
```c
bool negate(bool* p) {
    bool done = false;
    bool value;
    while (!done) {
        value = *p;
        done = CAS(p, value, !value); //compare and swap operation
    }
    return !value;
}
```
where `CAS` is an atomic operation provided by the CPU which is equivalent to
```c
bool CAS(int* p, int old, int new) {
    if (*p != old) {
        return false;
    }
    *p = new;
    return true;
}
```

### Questions
* What we did in class was at the level of memory operations and we did not discuss in detail how we got these operations.
  Explain how we can extract an automaton with memory operations as transitions from code.
  Give the automaton corresponding to `peterson(0)` and `negate(x)`.



## On CSM with bags

At the end of week 6, we said that communicating state machines with bags instead of FIFO have the same expressive power as Petri nets.
However, we did not prove this claim.

__Models for bags.__
A multiset of messages is usually modeled as map from message type to natural number.
Petri nets have a limited ability to "count" and can encode such map.

__Control-state reachability.__
Control-state reachability is a specific type of covering/reachability question for the case of concurrent systems.
For a system composed of a finite number of processes interacting either through shared memory or message passing, the control-state reachability asks if a distinguished process can reach a particular local state.
This question is indifferent to the state of the other processes or means of synchronization (memory, channels).


From the definition of CSM we have:
* `|Σ|` different possibles messages
* `N` finite state machines
* let `m` be the maximal number of state of any if the state machines, i.e., `m = max_i |S_i|`

###
* CSM → PN
  - Give a reduction from CSM with bag mailbox to Petri net that preserves control-state reachability.
    By preserving control-state reachability, we mean that a machine `M_i` in the CSMs can reach a given state `s_i` iff the PN obtained with the reduction can cover a marking `M`.
    For a given `M_i` and `s_i` explain the marking `M` one gets with your reduction.
  - How many places and transitions does the PN have? Describe it as function with parameters `N`, `m`, and `|Σ|`.
* PN → CSM
  - Give a reduction from Petri net to communicating state machines such that a covering question for the Petri net can be encoded as a control-state reachability question in the CSM.
  Your reduction may use the marking to cover and produce different CSM depending on that marking.

