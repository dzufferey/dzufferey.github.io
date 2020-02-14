# Solutions 6

## Affine Nets (AN)

> Explain how transfer and reset nets can be encoded as AN. (hint: $R(t)$)

For each $t$ we need to build a $R(t)$.

$R(t)[i,j]$ is
* $1$ if $i$ is the target of a tranfer and $j$ the source of the tranfer
* $1$ if $i=j$ and the place is not connected to any reset of transfer edge.
* $0$ otherwise

> Let us look at how we can analyze affine nets.
> * reachability

No.
Since we can simulate reset and transfer edges, reachability is undecidable.

> * covering

Yes.
Affine nets are monotonic.
This follows from the fact that $R$ contains only natural numbers.

We need to use the backward algorithms for WSTS.
Computing acceleration is not possible, and therefore, we cannot use the Karp-Miller tree.

> * boundedness (same definitions as for Petri net)

No.
[Boundedness is undecidable for reset nets.](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=5D752C1BB71C332AE6A54F60195C0D80?doi=10.1.1.57.3693&rep=rep1&type=pdf)

> * termination

We an use the algorithm we saw in week 3 which extends the finite reachability tree to decide termination.
This algorithm works on any WSTS.



## Defining More Operations on Channels

> [send](https://spinroot.com/spin/Man/send.html)

\\[{
 M[i] \stackrel{j!a}{→_i} q \qquad   C' = C[j ← C[j]·a]  \\qquad  M' = M[i ← q]
} \over {
                    (M, C) → (M', C')
}
\\]

\\[{
 M[i] \stackrel{j!!a}{→_i} q \qquad   C' = C[j ← a·C[j]]  \\qquad  M' = M[i ← q]
} \over {
                    (M, C) → (M', C')
}
\\]

> [receive](https://spinroot.com/spin/Man/receive.html)

\\[{
M[i] \stackrel{?a}{→_i} q   \qquad   C[i] = a·w   \qquad  C' = C[i ←  w]  \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C')
}
\\]

\\[{
M[i] \stackrel{??a}{→_i} q   \qquad   C[i] = w·a·w' \qquad ∀x ∈ w. x≠a   \qquad  C' = C[i ←  w·w']  \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C')
}
\\]

> [poll](https://spinroot.com/spin/Man/poll.html)

\\[{
M[i] \stackrel{?[a]}{→_i} q   \qquad   C[i] = a·w  \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C)
}
\\]

\\[{
M[i] \stackrel{??[a]}{→_i} q   \qquad   C[i] = w·a·w'  \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C)
}
\\]

> [full](https://spinroot.com/spin/Man/full.html)

If the channel has a bound of $k$:

\\[{
M[i] \stackrel{full}{→_i} q   \qquad   |C[i]| = k   \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C)
}
\\]

> [empty](https://spinroot.com/spin/Man/empty.html)

\\[{
M[i] \stackrel{empty}{→_i} q   \qquad   |C[i]| = 0   \qquad  M' = M[i ← q]
} \over{
                        (M, C) → (M', C)
}
\\]

## Santa Claus Problem

__TODO ...__

