# Solutions 3

Thanks to Billy Joe Franks, Kerem Kahraman, and Pascal Bergsträßer for contributing to this solution.

## Petri Net, Termination, and Linear Programming

#### Task 1

We can encode the presence of non-decreasing cycles in a linear program as follows:
\\[
\begin{array}{ll}
\text{Variables:}   & X \\\\
\text{Subject to:}  & X > 0 \\\\
                    & C \cdot X ≥ 0 
\end{array}
\\]
Here, $C$ is the connectivity matrix and $X$ is a vector that represent the number of times each transition fires.
We require that $X$ contains at least one transition.
(Otherwise, $X=0$ trivially satisfies the last contraint.)
Finally, $C \cdot X$ is the net result of firing $X$ and we require it to be non-negative, i.e., a non-decreasing cycle.

Notice that the constraints do not talk about the initial marking.

In the example we have

$
C = \begin{bmatrix}
-1 & -1 & 0 & 0 \\\\
0 & 1 & -1 & 2 \\\\
0 & 0 & 2 & -3 \\\\
\end{bmatrix}
$

Solving the constraint above give, for instance, $X = [0 ~ 0 ~ 2 ~ 1]^T$.

We have: $C \cdot X = [0 ~ 0 ~ 1]^T ≥ [0 ~ 0 ~ 0]^T$.


#### Task 2

* No. Consider the net:
  ```graphviz
  digraph PN{
    rankdir=LR
    ranksep=0.75;
    node [shape = circle, fixedsize = true, width = 0.5, fontsize = 15];
    c [label=" " ];
    d [label=" " ];
    node [shape = box, label = "", style = filled, fillcolor = black, fixedsize = true, width = 0.15, fontsize=15]; 
    c -> t3;
    t3 -> d;
    d -> t5;
    t5 -> c;
  }
  ```
  It has terminated (no transition can fire).
  But it cannot be proved using the linear program.
* The analysis is sound but not complete.
* The incompleteness of the analysis stems from the fact that the LP can have a negative number of tocken during the firing of the non-decreasing cycle.
  The LP only relates the start and end marking.
  It does not say anything about the intermediate marking.
  If we are allowed to pick then the analysis is also complete.
  We can always pick an initial marking with enough tokens such that every transition in the non-decreasing cycle can be fired.



## Vector Addition System with States

#### Task 1

__PN → VASS.__

Given a Petri net $N$ we can encode an equivalent Vass $V$ as:

$V=(\\{0\\} \cup T,|S|,\delta,i_0)$

and w.o.l.g. assume $S=\\{1,\dots,m\\}$ let

$\delta=\\{(0,v_t,t) ~|~ \forall i \in S : v_t[i]=-W(i,t)\\} \cup \\{(t,v_t,0) ~|~ \forall i \in S : v_t[i]=W(t,i)\\}$

i.e. for every transition $t$ in $T$ add a loop to the VASS that encodes this $t$.

Lastly let $i_0=(1,(M_0[1],\dots,M_0[m]))$


__VASS → PN.__

Given a VASS $V$, w.l.o.g $Q=\{1,\dots,l\}$ we can encode an equivalent Petri net $N$ as:

$N=(\\{1_V,\dots,n_V \\} \cup \\{1_Q,\dots,l_Q\\},\delta,W,M_0)$

$\forall\ d=(q,v,q') \in \delta, \forall\ i \in \\{1_V,\dots,n_V\\}:$

$\qquad W(q,d)=1$

$\qquad W(d,q)=1$

$\qquad W(i,d)=
	\begin{cases}
      -v[i] & \text{if}~ v[i]<0\\\\
      0 & \text{otherwise}
	\end{cases}$

$\qquad W(d,i)=
	\begin{cases}
      0 & \text{if}~ v[i]<0\\\\
      v[i] & \text{otherwise}
	\end{cases}$

Lastly w.l.o.g. $i_0=(x,(y_1,\dots,y_n))$,
$M_0[x]=1$, and
$M_0[i_V]=y_i$.

#### Task 2

__PN → VASS.__

Let $V$ be obtained from $N$ by the above construction.
Then a marking $M$ can be transformed to a state for $V$ as follows: $\alpha(M)=(0,(M[1],\dots,M[m]))$

Assume we are in some marking $M$ and transition $t$ is enabled, such that $M[t>M'$,
then for $\alpha(M)$ the transitions $(0,v_t,t)$ and $(t,v_t,0)$ from the construction are usable, because the markings are positive and our construction encodes the change in markings, thus $\alpha(M)\rightarrow \alpha(M')$.
This generalizes to an inductive argument.

Assume we are in some marking $M$ and transition $t$ is not enabled, then this marking is not enabled, because one state $s\in S$ in $N$ does not have enough tokens for the transition to fire.
However this means $M[s]-W(s,t)<0$ and since $v_t[s]=-W(s,t)$ $\alpha(M)$ cannot fire transition $(0,v_t,t)$.
Because we have not added any elements to $\delta$ other than elements from $t\ in T$.
This generalizes to an inductive argument.

__VASS → PN.__

Let $N$ be obtained from $V$ by the above construction. Then a state for $V$ can be transformed to a marking $M$ as follows: $\beta((x,(y_1,\dots,y_n)))=M$ where
$M[i]=
	\begin{cases}
      1 & \text{if}~ i=x \\\\
      y_j &  \text{if}~ i=j_V \\\\
      0 & \text{otherwise}
	\end{cases}$.

Assume from state $i=(x,(y_1,\dots,y_n))$ we can reach $i'=(x',(y'_1,\dots,y'_n))$ with transition $d=(x,v,x') \in \delta$.
Since $(y_1,\dots,y_n)+v=(y'_1,\dots,y'_n) \geq 0$ the equivalently named transition $d$ in $N$ is enabled and $\beta(i)[d>\beta(i')$.
This generalizes to an inductive argument.

Assume from state $i=(x,(y_1,\dots,y_n))$ transition $d=(x,v,x') \in \delta$ cannot be used. Then this is because $\exists j:y_j+v[j]<0$, however this would be $\beta(i)[j]<W(j,d)$ and thus $d$ is not enabled.
This generalizes to an inductive argument.


