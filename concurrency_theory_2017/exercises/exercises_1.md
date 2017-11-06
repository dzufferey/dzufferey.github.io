# Homework 1

_Instructions_
* Due on November 2nd (after the holidays).
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format. For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


## Determinization and complexity

Recall the "1 as the 3rd symbol before the end" NFA:

```
      1     0,1    0,1
→ (a) → (b)  →  (c) →  ((d))
   ↺
   0,1
```

* Determinize this NFA and give an equivalent DFA.
* What is the complexity of the construction? (hint: try the example with "4th, 5th, ... before the end")
* [Optional] Is is possible to do better? Why?


## Correctness of the determinization construction

Complete the proof of correctness of the determinization construction.

Let `N` be a NFA and `D` be a DFA obtained from `N` using the powerset construction.
Show that any word accepted by `D` is also accepted by `N`: `w ∈ L(D) ⇒ w ∈ L(N)`.


## Encoding program as automaton

Recall the lock automaton:

```
       lock
→ ((u))  ⇄  ((l))
       unlock
```

And the increment program:
```
int balance;

void increase(int x) {
    lock();
    balance += x;
    unlock();
}
```
and the corresponding CFA:
```
→ ((0))
    ↓ lock
  ((1))
    ↓ balance += x
  ((2))
    ↓ unlock
  ((3))
```

Generalize this example with two (or more) increment program while keeping a single lock.
Make sure your solution preserves the mutual exclusion property of the lock (the correct executions are accepted, while the incorrect one are rejected).
You are allowed to change the automata (states, alphabet, transition, etc.)


## Dining philosophers in Spin

* Encode the [dining philosopher problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem) in Spin (4 philosophers).
* Show it has a deadlock.
* What happens to the running time when you increase the number of philosophers?


## [Optional] Lamport's backery

* Encode [Lamport's bakery algorithm](https://en.wikipedia.org/wiki/Lamport%27s_bakery_algorithm) in Spin.
* Can you prove it safe? (Caveat: be sure the search depth is enough to explore the full state space, you can change it with `-mN` option where `N` is the depth.)
