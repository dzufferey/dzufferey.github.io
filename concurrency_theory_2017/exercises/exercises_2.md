# Homework 2

_Instructions_
* Due on November 8th.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format. For the exercises using an LP solver / Spin give the source files as well. Place all your files in a single archive (zip or tar.gz).

#### A bit of administration ...

We have learn that a few students have other obligations that prevents them from attending the exercises.
Therefore, we are trying to find a time that could accommodate everybody.

So along with the next homework, please respond to the following poll.
Here are for possible time slot:

* Monday, 13:45 - 15:15
* Tuesday,13:45 - 15:15
* Wednesday, 11:45 - 13:15
* Thursday, 17:15 - 18:45 (current time)

Rank the time slot in order of preferences from `4` (highest) to `1` (lowest).
If you cannot make it to one of the time slot, give it a `-1` value.
If you are working in group, every member of the group should give a separate answer.

We will change the time _only if we get unanimity_ on one of the time slot (everybody can attend), then we will use the preferences if there are multiple time slots that fit everybody's schedule.

Thank you

## A new Spin on Petri net

Recall that _safe_ Petri Nets are 1-bounded (definition).

Let `A` and `B` be  _prefix-closed_ automata.
An automata is prefix-closed iff every prefix of an accepted word is also accepted.
More formally: `∀ w ∈ L(A), i ∈ [0, |w|]. prefix(w, i) ∈ L(A)` (and similarly for `B`).

More concretely, if `A` is a DFA then all the states of `A` are accepting except a single non-accepting sink state (all transitions from that state go back to that state).
If `A` is an NFA then if it has more than one state, all the states are accepting.
(same for `B`).

* From prefix-closed automaton to safe Petri net:
  - Give a reduction from `A` to a safe Petri net `(S,T,W,M₀)`.
    Show the correctness of your construction:
    * Given a word `w ∈ L(A)` show how to construction a trace `π` such that `∃ M. M₀[π〉M`
    * and the reverse direction from `π` to `w`
  - Does you construction work in the case of DFA or NFA?
    Does it make a difference?
  - Given both `A` and `B` extend your construction to return a safe Petri net that corresponds to the synchronized product of `A` and `B`.
    What is the worst case size of the automaton for the synchronized product of `A` and `B`?
    What is the worst case size of the Petri net corresponding to the synchronized product of `A` and `B`?
* From safe Petri net to prefix-closed automaton:
  - Give a reduction from a safe Petri net to a prefix-closed automaton.
    (You reduction does not need to be efficient.)
  - [Optional] Is is possible to have an efficient construction?
* Spin
  1. Encode the dining philosopher problem as a Petri net
  2. Encode this Petri net in Spin
  3. Compare the performance of the Petri net encoding compared to you solution from the first week.


## Boundedness and termination

Give an example of a Petri net which is
* bounded and terminating
* bounded and non-terminating
* unbounded and terminating
* unbounded and non-terminating

or argue why such Petri net does not exist.

A non-decreasing cycle is a sequence of transitions `π` such that if `π` is enabled at `M` then `M[π〉M′` and `M′ ≥ M`.
* In your non-terminating examples, find a non-decreasing cycle.
* Show that a non-terminating Petri net must have a non-decreasing cycle.


## On co-linear properties

When using an LP solver to verify safety properties (reachability), we saw that we can only encode co-linear properties, i.e., properties which violation satisfies `A∙M ≥ B` where `M` is a marking.

Can you find an example of safety property which is _not_ co-linear?

(hint: a safety property is a set of states, `A∙M ≥ B` is a special kind of set.)

[Optional] Can you propose a strategy to (partially) lift this limitation.


## Proving Petri nets properties using an LP solver

### LP Solver

For this exercise you are free to use any LP solver with the restriction that we can reasonably check the result.
If you are familiar with Matlab, you can use it or use [Octave](https://www.gnu.org/software/octave/).

I recommend using [GLPK](https://www.gnu.org/software/glpk/) as it has a [good documentation](https://en.wikibooks.org/wiki/GLPK) which explains how to set it up for Windows/Mac/Linux.

Additionally, you can get pre-compiled binaries for
* [Windows](http://winglpk.sourceforge.net/)
* Mac through [Homebrew](https://brew.sh/)
* Linux through the package manager of your distribution

GLPK comes with a stand-alone solver called `glpsol`.
`glpsol` read the [GMPL](https://en.wikibooks.org/wiki/GLPK/GMPL_%28MathProg%29) human readable format.

For instance, the Petri Net
```
    1   2
(∙) → | → ( )
 p₁ ↖ | ↙  p₂
```
and the reachability target `M(p₂) = 10` can be encoded as
```
# counting transitions
var x1 integer, >= 0;
var x2 integer, >= 0;
# tokens in the final marking
var p1 integer, >= 0;
var p2 integer, >= 0;
# transitions
s.t. t1: p1 +     x1 - x2 = 1;
s.t. t2: p2 - 2 * x1 + x2 = 0;
# property
s.t. prop: p2 = 10;
solve;
display x1, x2;
end;
```

### Exercise

Consider the following piece of code:
```
lock l1;
lock l2;

void do_something() {
    if (?) {
        l1.lock();
        ... //critical section 1
        l1.unlock();
    } else {
        l2.lock();
        ... //critical section 2
        l2.unlock();
    }
}

while(true) {
    spawn( do_something )
}
```

Here is a Petri net model for the (un)lock operation of a lock object:
```
    lock()
    ↗ | ↘
(∙)       ( )
    ↖ | ↙
   unlock()
```

`spawn` create a new thread executing the method given in argument.

`if (*) ... else ...` is a non-deterministic choice.

* Model this program as a Petri net.
* Encode the Petri net as an LP program and use an LP solver to prove:
  - there is a most one process in the first critical section
  - there is a most one process in the second critical section
  - there can be two processes in the critical sections (1 and 2)
* Can you find a program, the corresponding Petri net model, and a co-linear property where the LP solver fails to prove the property even though the net satisfies the property?
* [Optional] LP and termination
  - Encode the presence of non-decreasing cycles as a LP problem?
  - Is it sufficient to prove non-termination?
  - Does that change if you can pick the initial state?
