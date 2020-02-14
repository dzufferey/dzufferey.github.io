# Solutions 10

## |-free π-calculus

> Can you solve the covering problem for the $|$-free π-calculus? Justify your answer. 

In the $ν$-free π-calculus we had finitely many names and infinitely many processes.
Here it is the opposite, finitely many processes and infinitely many names.

We can use the same order but we need to argue why it is still a WQO.
In the $ν$-free case we argued that there was finitely many kind of procees because there was finitely many process definitions and finitely many names.

For the $|$-free case, we need that there is finitely many processes (not definitions, actual processes).
Because each process has fintely many names at any given point there are only finitely many active names at one point.
If we generate more name then it replaces another name.
The names which are not referenced can be removed using the structural congruence rules ($≡$).

## On the Two Threads Reduction in Bulk Synchronization

> Is a single thread reduction is possible for the control-state reachability problem for LCS?
> Discuss what made the two threads reduction possible and, if possible, what would be the equivalent for the control-state reachability.

In the bulk synchronous model, we applied some abstraction over the memory.
A similar abstraction for LCS would allow a machine to send and receive any messages.

This abstraction worked in the case of GPU as the control-flow is typically independent of the data values.
It may depend on the size of the data/arrays but not so much on the values inside the data structures.
On the other hand, in LCS the type of messages is important and such abstraction is rather useless.


> Same question but for a fixed number of tokens and covering in Petri Nets.

There can be transitions that consume more tokens than they produce.
Therefore, to get to the marking to be covered we may need more tokens than there are in that marking.

Bounding the number of tokens only works for a specific class of nets; the nets where transitions produce more tokens than they consume.


## Model for Monitors (Synchronization Primitives)

> Among the models for concurrency we discussed in class.
> Which model would you use for the code above?
> Justify and show what the program in this model looks like.

__TODO ...__
