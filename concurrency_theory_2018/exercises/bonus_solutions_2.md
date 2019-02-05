# Bonus Solutions 2

## Place-Boundedness for Transfer/Reset Nets

#### Is place-boundedness is decidable for Petri nets?

Yes, we can use the Karp-Miller tree and check which place has a marking with $ω$.

#### Is place-boundedness is decidable for reset nets?

No, we can reduce boundedness for reset nets to $|S|$ place-boundedness queries.
For each place, ask it is is unbounded.
If the net can contain any unbounded place then it is unbounded.

#### Is place-boundedness is decidable for transfer nets?

No, we can reduce the boundedness for reset nets to place-boundedness in transfer net.
We turn the reset net into a transfer net by adding a new "dump" place which to which every resets transfer the token.
Then, if any place other than the dump is unbounded the reset net is unbounded.


## Fair Lossy Channels

In WSTS terms, acceleration and monotonicity becomes a problem.
In some sense, accelerating a sequence of transition is, in some sense, executing some transitions infinitely often.
Therefore, acceleration potentially explores unfair behaviors.
So the algorithm is exploring behaviors that are not there in the system.

For safety properties, the algorithm is still sound but incomplete.
Soundness means no false negative.
Since, the algorithm explore more behaviors it will find all the errors.

On the other hand, exploring more behaviors can introduce more false positive.
Since the algorithm was already incomplete, the characterization does not change.
How the incompleteness shows is different.
Without fairness, the incompleteness means that the algorithm does not terminate.
With fairness constraints, the algorithm may still not terminate but it can now also terminate with a false positive.
