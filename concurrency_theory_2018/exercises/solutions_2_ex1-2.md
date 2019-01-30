# Solutions 2

## Synchronized Product for DFAs/NFAs with Different Alphabets

#### Task 1

TODO ...

#### Task 2

TODO ...

## Petri nets

#### Task 1

The modification is quite straightforward: just add 1 more token in the place $U$ in the initial marking.
  
```graphviz
digraph PN {
    rankdir=LR;
    node [shape = circle, fixedsize = true, width = 0.5];
    p1 [ xlabel="U", label=":" ];
    p2 [ xlabel="L", label="" ];
    p3 [ xlabel="0", label="" ];
    p4 [ xlabel="1", label="" ];
    p5 [ xlabel="2", label="" ];
    p6 [ xlabel="3", label="" ];
    node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15];
    t1 [xlabel="lock" ];
    t2 [xlabel="unlock" ];
    t3 [xlabel="balance += x" ];
    t4 [xlabel="spawn" ];
    t4 -> p3;
    p1 -> t1 [ constraint = false ];
    p3 -> t1;
    t1 -> p2;
    t1 -> p4;
    p4 -> t3;
    t3 -> p5;
    p2 -> t2;
    p5 -> t2;
    t2 -> p1 [ constraint = false ];
    t2 -> p6;
    p3 -> p1 [ style = invis];
}
```

To show that the number of permit is preserved, we can use a structural invariant.

With the ordering on the places be $(U, L, 0, 1, 2, 3)$, and the ordering on transitions $(\mathit{lock}, \mathit{balance += x}, \mathit{unlock}, \mathit{spawn})$, the connectivity matrix is

$C =
\begin{bmatrix}
-1 &  0 &  1 & 0 \\\\
 1 &  0 & -1 & 0 \\\\
-1 &  0 &  0 & 1 \\\\
 1 & -1 &  0 & 0 \\\\
 0 &  1 & -1 & 0 \\\\
 0 &  0 &  1 & 0
\end{bmatrix}$

$I^T = \begin{bmatrix}1 & 1 & 0 & 0 & 0\end{bmatrix}$ is a structural invariant and we have that $I^T\cdot M₀ = 2$ (2 permits initially).


#### Task 2

There are more than one way to do that.
Here is one solution.
The challenge is that only the process which has the lock is allowed to relock it.
Therefore, we need to be able to distinguish between different processes.
To do that, we need to introduce as many lock/unlock transitions as there are processes.

Here is the example with two processes:

```graphviz
digraph PN {
	rankdir=LR;
    node [shape = circle, fixedsize = true, width = 0.5];
    p1 [ label="∙", xlabel = "unlocked" ];
    p2 [ label="", xlabel = "locked by P₁" ];
    p3 [ label="", xlabel = "locked by P₂" ];
    p4 [ label="", xlabel = "unlocking by P₁" ];
    p5 [ label="", xlabel = "unlocking by P₂" ];
    node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15];
    t1 [ xlabel = "lock P₁", fillcolor = blue ];
    t2 [ xlabel = "lock P₁", fillcolor = blue ];
    t3a [ xlabel = "unlock P₁", fillcolor = red ];
    t3b [fillcolor = green];
    t3c [fillcolor = green];
    t4 [ xlabel = "lock P₂", fillcolor = blue ];
    t5 [ xlabel = "lock P₂", fillcolor = blue ];
    t6a [ xlabel = "unlock P₂", fillcolor = red ];
    t6b [fillcolor = green];
    t6c [fillcolor = green];
    p1 -> t1;
    t1 -> p2;
    p2 -> t2;
    t2 -> p2 [ label = 2];
    p2 -> t3a;
    t3a -> p4;
    p4 -> t3a [ arrowhead = odot ];
    p4 -> t3b
    p2 -> t3b [ arrowhead = odot ];
    t3b -> p1;
    p4 -> t3c;
    p2 -> t3c;
    t3c -> p2;
    p1 -> t4;
    t4 -> p3;
    p3 -> t5;
    t5 -> p3 [ label = 2];
    p3 -> t6a;
    t6a -> p5;
    p5 -> t6a [ arrowhead = odot ];
    p5 -> t6b
    p3 -> t6b [ arrowhead = odot ];
    t6b -> p1;
    p5 -> t6c;
    p3 -> t6c;
    t6c -> p3;
}
```
The colors mean:
* blue: transition for locking
* red: transition for unlocking
* green: internal transition for unlocking

For each process there is two lock transitions depending on whether the process already has the lock or not.

The unlock is a bit more complex.
First it consumes a "locked" token and goes to an intermediate place.
There can be at most one unlock at the time (enforced by an inhibitory edge).
From the intermediate place, depending whether there are more locked token a token may be put back in the unlocked place.
