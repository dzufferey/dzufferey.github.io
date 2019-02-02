# Solutions 8

## Dining Philosophers in CCS

There are many different way of modeling the problem.
Here is a simple one:

$
\begin{array}{lcl}
    philo(l,r) & ≝ & !l.!r.τ.?l.?r.philo(l,r) \\\\
    fork(x) & ≝ & ?x.!x.fork(x)
\end{array}
$

Where the initial configuration is:

$
(ν_{0 ≤ i < n} i) ∏_{0 ≤ i , n} (philo(i, i+1 \mod n) ~|~ fork(i))
$

Each fork has its own name.
Acquiring a fork is sending a message to that name and releasing a fork is receiving a message from that name.
The philosopher eating is modeled by a silent action ($τ$).

## Effective Pred-basis for Lossy Channel Systems

Given an upward-closed set of state for a LCS, we need to compute the set of predecessors.
We know that upward-closed sets are effectively represented by a finite number of basis elements.
We are going to compute the predecessor of the upward-closure of each basis element.

```
pred-basis(S):
    S' = ∅
    For each (M,C) in basis(S):
        For each i:
            For each s, a, with s \stackrel{j!a}{→_i} M[i]:
                S' = S' ∪ (M[i ← s], C[j ← pred-send(C[j], a))
            For each s, a, with s \stackrel{?a}{→_i} M[i]:
                S' = S' ∪ (M[i ← s], C[i ← pred-receive(C[i], a))
    return S'

pred-send(w, a):
    if w = w'⋅a
        return w'
    else
        return w //because: w⋅a ∈ ↑w

pred-receive(w, a):
    return a⋅w
```

Notice that we never need to drop a message as it leads to a strictly greater configuration and, therefore, does not help in the overall algorithm.
(Local states are unchanged and the channel gets bigger.)


## CSM with Insertion Error

We are going to see two different solutions for this problem.

#### Version 1: direct approach

Instead of relying on WSTS, we can observe that inserting messages into the channels effectively decouple the machines and we don't even need to look at the communication.

Machines have two kinds of operations: send and receive.
* Sending is always possible, independently of whether the messages will be received.
* Receiving is not always possible because it consumes a message from the channel.
  However, we can combine the reception with insertion.
  Before each receive, we insert the appropriate message in from of the channel.
  Therefore, every receive transition can be taken.

This means that both send and receive can ignore the channels!

To solve the control-state reachability, we treat each machine as an NFA and if there is a path from the initial state to the target state, then we can reach the state.

At an high level, the algorithm is:
```
For each i
    if there is a path from q_{0i} to q_target in M[i]
        return REACHABLE
return UNREACHABLE
```

#### Version 2: using WSTS

If we look at the inverse of the transition relation: $→⁻¹$.
We can observe that is exactly corresponds to the transition of a lossy channel system.

Therefore, the general backward algorithm for WSTS is a forward algorithm for CSM with insertion error.
The difference is that this algorithm is not solving the covering problem anymore but the _sub-covering_ problem, i.e., can we get to a state covered (instead of covering) the target state.

To turn the control-state reachability problem into a covering problem we used $ε$ for the channel content.
To turn the control-state reachability problem into a sub-covering problem we use $Σ^\*$ for the channel content.

CSM with Insertion Error are an instance of Downward-WSTS.
(See Section 5 and 9.2 of the paper Well-Structured Transition Systems Everywhere! by Alain Finkel and Philippe Schnoebelen, 1998)
