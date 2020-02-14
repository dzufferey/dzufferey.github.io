# Solutions 9

## π-calculus with Test for Name Equality

We need to update the result from exercise 8.

__TODO ...__


## Model for Mobile Ad Hoc Networks

> For the new model above, is the control-state reachability question decidable? Justify.

Yes, the semantics is roughly broadcast so there is not communication channels.
Therefore, the entire system can be encoded as some NFA.


> Consider a generalization of the model.
> For communicating state machines, we have a fixed number of processes.
> We want to generalize that to the parameterized verification problem.
> We still have a finite number of types of machines but there can be an arbitrary number of copies of each type of machine.
> Is the control-state reachability problem still decidable? Justify.

Control-state reachability is still decidable but we need to a more complicated algorithm.
We can show this model is a WSTS.

We can use the same order as in the case of the $ν$-free π-calculus.
We need to update the proof that the ordering in compatible.

Given $∏_i A_i ≤ \left(∏_i A_i ~|~ ∏_j A_j \right)$,

If $∏_i A_i$ can make a step then $\left(∏_i A_i ~|~ ∏_j A_j \right)$ can make the same transition.
We can apply _Reconfiguration_ steps until all the $A_j$ are not in $G$ and then the transition will affect only the $A_i$.


## On Well-formed Communication Protocols and Binary Session Types

First, we need to identify which element in the code corresponds to the element of binary session types.

| Code | Type |
|------|------|
|  !   |  !   |
| receive match | & |
| Request1, Request2, Reply1, Reply2, Exit | labels |

For the payload of the scala cases classes, we can serialize the operation.

`!Request2(1)` is first sending the label `Request2` followed by sending an int: `⊕Request2.!Int`.


Then, we can proceed with the typing itself.

The type for process 1 and 2 are 
```
TypeProcess1 ≝ ⊕Request1.!Int.!Int.&Reply1.?Bool.⊕!Exit.end

                 ⎧ Request1.?Int.?Int.⊕Reply1.!Bool.TypeProcess2
TypeProcess2 ≝ & ⎨ Request2.?Int.⊕Reply2.!Int.TypeProcess2
                 ⎩ Exit.end
```

Now we need to show type both processes together.
In this case, we will compute `dual(TypeProcess1)` and show that `TypeProcess2` is a subtype of that.

```
dual(TypeProcess1) ≝ &Request1.?Int.?Int.⊕Reply1.!Bool.&?Exit.end
```

For the subtyping, we need to apply the sutyping rule twice:

```
                 ⎧ Request1.?Int.?Int.⊕Reply1.!Bool.TypeProcess2
TypeProcess2 ≝ & ⎨ Request2.?Int.⊕Reply2.!Int.TypeProcess2
                 ⎩ Exit.end
```
is a subtype of `&?Exit.end`.
We just select the last option and ignore the rest.

Then we can look at `&Request1.?Int.?Int.⊕Reply1.!Bool.&?Exit.end`
For the part above, we know that `&Request1.?Int.?Int.⊕Reply1.!Bool.TypeProcess2` is a subtype.
Applying the subtyping rule one more time on the external choice.

