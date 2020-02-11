# Solutions 7

## Division Order for Abstract Algebra

> Let $(S,⋅)$ be a semigroup quasi-ordered by a divisibility order $≤$.
> - If $S$ has a finite generating set $G$, is $(S,≤)$ a WQO?
> - If $S$ has a generating set $G$ such that $(G,≤)$ is a WQO, is $(S,≤)$ a WQO?

Higman's lemma is actually called [Ordering by divisibility in abstract algebras](https://doi.org/10.1112%2Fplms%2Fs3-2.1.326).
The difficulty is to maps the definitions of division order to the embedding we know.

| Division Order    | Embedding |
|-------------------|-----------|
| $S$               | $Σ^\*$    |
| $G$               | $Σ$       |
| $⋅$               | concatenation |

Then we can show that the three rule corresponds to embeddings:
1. $f$ maps $x$ to $x$ and nothing to $y$
2. $f$ maps $x$ to $x$ and nothing to $y$
3. $f$ maps $y$ to $y$, nothing to $x$, and $z$ to $z$

Applying multiple rules corresponds to composing the mappings which preserves embedding.

Then the two claims directly follow from Higman's lemma.


## Lossy Channel System with Initial Channel State

> For model 1: can you either reduce it to normal LCS or find an example which cannot be modeled by an LCS?

Model 1 is a special case of model 2 so we consider model 2 only.


> For model 2: can you either reduce it to normal LCS or find an example which cannot be modeled by an LCS?

For each machine and each outgoing channel, we create an automaton which sends the messages corresponding to the initial state.
Then, we concatenate these automaton to generate the overall initial state, and at the end, hand over the control to that original machine.


> For model 3: can you find assumptions so that this model can be reduced to LCS, model 1 or 2? 
>   	You may need to find different sets of assumptions for the different reductions - depending on the reductions presented before.

For model 3, as we are dealing with LCS we know that the downward-closure of any set of finite words is regular (model 2).
We only need to assume that we have an effective way of computing the automaton corresponding to that set.


> Let us change the channel model from p2p to mailbox.
> * Are mailbox LCS still WSTS?

Yes. Nothing in the proof that LCS are WSTS relies on p2p.
The same proof can be adapted to mailboxes.

> * Consider the mailbox variation of models 1-3 and the questions above.
>   Are the reductions from mailbox models 1-3 to mailbox LCS possible?

Only the 2nd case change as the other two reduce to it.

It is not possible to use the idea we used before: fill the channels and then continue as normal.
The problem is that we do not control the scheduler and processes can interfere as the channels get filled.

We need a different approach.
The idea is to simulate what the initial state does to each machine and then continue as normal.
For each machine:
* Create an automaton which "receive" the initial content of the channel.
* Create one copy of the machine and take the synchronized product (week 1) with the automaton for the initial channel state.
  Erase the message reception from that automaton.
  This automaton now simulates what the original machine does (change of local state, sending message) when it receives the initial content of the channel.
* Connect the product "initial × machine" to the normal machine.
  When we reach a state $(q_b,q_M)$ where $q_b$ is accepting state of the initial buffer state,
  we add an $ε$-transition to $q_M$ of the normal machine.


## Partially Lossy Channel System

> 1. A PLCS is a LCS that only drop messages from a channel when there is more than $k$ messages in that channel.
> 2. A PLCS is a LCS that only drop messages from a channel when there is more than $k$ messages in the network (sum of all the channels).

> Explain how to modify the formalization of LCS to obtain a PLCS. 

We need to update the rule corresponding to dropping message

1. per channel:
    \\[{
    C(i,j) = w·a·w' \qquad  C' = C[(i,j) ←  w·w'] \qquad |C(i,j)| > k
    } \over {
                (M, C) → (M, C')
    }\\]
2. the network:
    \\[{
    C(i,j) = w·a·w' \qquad  C' = C[(i,j) ←  w·w'] \qquad ∑_{m,n} |C(m,n)| > k
    } \over {
                (M, C) → (M, C')
    }\\]


> Is the control-state reachability (covering) still decidable for PLCS?

Yes, we need to modify the order such that it is a WQO and compatible.

The idea is similar to the order used to DTSO (week 12).
Pick $k$ elements which should be kept reliably and interleave them with normal words.
This forms a $2k+1$ tuple where each element is a WQO (finite set or subsequence).

__TODO ...__
