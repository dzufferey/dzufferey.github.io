# Bonus Exercises 2

_Instructions_
* Optional.
* Due on Tuesday Feb 5.

## Place-Boundedness for Transfer/Reset Nets

During the class, we have discussed Petri nets and some extensions: transfer nets and reset nets.
These models are interesting as many questions about them are decidable.
However, sometime things get a bit more subtle.
Here we will investigate further the boundedness question.

There are two type of boundedness questions:
- boundedness: if any place of the net can contain an unbounded number of token for some execution
- place-boundedness: if a give place of the net can contain an unbounded number of token for some execution

Until now we have focused on boundedness.

_Assumptions._
Let us assume the following results (given without proof):
- the covering set (set of all states that can be covered) is not computable for reset and transfer nets
- boundedness is not decidable for reset nets

**Questions.**
- Is place-boundedness is decidable for Petri nets?
- Is place-boundedness is decidable for reset nets?
- Is place-boundedness is decidable for transfer nets?
 
For each question, if the problem is decidable give an algorithm or reduce the question to a decidable problem for which we already have an algorithm.
If the problem is undecidable give a reduction from an undecidable problem to the problem considered.


## Fair Lossy Channels

Let us assume p2p, FIFO channels for communicating state machines.
We have explored the two extremes in terms of reliability.
Either the channels are reliable (*all* messages are delivered) or lossy (*any* message can be dropped).

Let us look at the intermediate model of _fair lossy channels_.
A channel is _fair lossy_ iff provided that _p_ sends a message _m_ to _q_ infinitely often, _q_ receives the message _m_ infinitely often.

_Assumptions._
It is possible to implement reliable channels on top of fair lossy channels.
While the details are non-trivial let us assume this result (think of using the alternating bit protocol).

During [week 7](viewer.html?md=concurrency_theory_2018/notes_7.md), we have briefly discussed an application of the Karp-Miller tree to fair lossy channels.
For LCS a Karp-Miller tree algorithm, when the algorithm terminates it returns the corret answer.
However, the algorithm may not terminate.
In the terminology of [week 2](viewer.html?md=concurrency_theory_2018/notes_2.md), the algorithm is sound but incomplete.

**Question.**
Is the algorithm still sound but incomplete with the extra fairness assumption?
Which part/operation of the algorithm can(not) accommodate the extra fairness assumption? If you prefer, you can explain what breaks at the level of the WSTS properties.

