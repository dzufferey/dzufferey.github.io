# Homework 10

_Instructions_
* Due *before* January 22 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).


## Binary Session Types for Definitions with Arguments

In the [lecture notes 10](viewer.html?md=concurrency_theory_2018/notes_10.md), the part about "Typing processes for two party communication" we looked at process definition without arguments.
We would like to add arguments to the definitions.
Definitions should have the form: $A(a₁, a₂, …) ≝ P$.

__Tasks.__
* What kind of extra type annotations are required, if any? (Before we just had annotation for the definition: `A: t ≝ P`)
* Which of the typing rule needs to be changed? Can you propose a new version of the rules for definitions with arguments?


## Limits of Binary Session Types

Let us look at binary session types ([lecture notes 10](viewer.html?md=concurrency_theory_2018/notes_10.md), Typing processes for two party communication).
The semantics given in notes is a synchronous semantics, but the result also holds for reliable FIFO channels.
Therefore, we can apply binary session types to the interaction of two communicating state machines with reliable FIFO channels ([lecture notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md)).
Since we look at only two machines, p2p or mailbox does not make any difference.
Questions

__Tasks.__
* Can you find a type for the ping-pong example in [lecture notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md)?
* Can you find a type for the juggling example in [lecture notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md)?
* Can you find an example which can be typed and where the channels may grow unboundedly?
