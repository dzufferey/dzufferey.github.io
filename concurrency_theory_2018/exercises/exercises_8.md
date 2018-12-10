# Homework 8

_Instructions_
* Due *before* December 18 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).

## Dining Philosophers in CCS

__Task.__
Encode the [dining philosopher problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem) in [CCS](viewer.html?md=concurrency_theory_2018/notes_8.md).
Design your encoding such that every philosopher and fork, respectively, use the same defining equations and only the names distinguishes each philosopher and fork, respectively.

You only need to encode the behaviour of the philosophers/forks according to the problem definition.
You do not need to design a algorithms which guarantee deadlock/starvation freedom of the system.


## Effective Pred-basis for Lossy Channel Systems

In [notes 7](viewer.html?md=concurrency_theory_2018/notes_7.md), we have shown that lossy channel systems (LCS) are WSTS and looked at the representation of the downard-closed set to apply a forward analysis.
Let us look at the application of the backward algorithms ([notes 4](viewer.html?md=concurrency_theory_2018/notes_4.md)) to LCS.
The backward covering algorithm works on upward-closed sets of configurations and compute the effect of transition in _reverse_.

__Task.__
Give an algorithms to compute the predecessor basis for LCS with FIFO mailboxes.


## CSM with Insertion Error

Let us look at a variation of communicating state machines (notes 7) with some kind of network error.
Instead of dropping messages (lossy channel) we try to model channels with noise.
We model the noise by allowing the network to insert messages in the channel.

The syntax is the same as normal CSM and the semantics with p2p channels is:

* Sending a message (*unchanged*)
  \\[{
    M[i] \stackrel{j!a}{→_i} s \qquad   C' = C[(i,j) ← C[i,j]·a]  \\qquad  M' = M[i ← s]
  } \over {
    (M, C) → (M', C')
  }
  \\]

* Receiving a message (*unchanged*)
  \\[{
    M[i] \stackrel{?a}{→_i} s   \qquad   C[j,i] = a·w   \qquad  C' = C[(j,i) ←  w]  \qquad  M' = M[i ← s]
  } \over{
    (M, C) → (M', C')
  }
  \\]

* Insertion (*new*)
  \\[{
    C[i,j] = w·w'  \qquad  C' = C[(i,j) ←  w·a·w']
  }\over{
    (M, C) → (M, C')
  }\\]

__Task.__
* We are interested in the control-state reachability question for communicating state machines with insertion error.
  Can you adapt results seen in the class to decide the control-state reachability?
  (Hint: think of $→⁻¹$)
