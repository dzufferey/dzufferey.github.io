# Solutions 8


## π-calculus with Replication

> For an equivalence notion of your choice, can you find an encoding of the π-calculus version we saw during the lecture to the π-calculus with replication?

We use weak bisimulation.

* For each definition $X ≝ P$, we introduce a new "guard" $g_X$ and a replicated process $(?g_X.P)^\*$.
* Each occurrance of $X$ is replaced by $!g_X$.
* We restrict $g_X$ in the state so that synchronization on $g_X$ appears as $τ$ from the outside.

> For an equivalence notion of your choice, can you find an encoding of the π-calculus with replication to the version of the π-calculus we saw during the lecture?

We use strong bisimulation.

For each $P^\*$ we add the definition $X_P ≝ P | X_P$ and add $X_P$ to the state.



## Higher Order π-calculus

> For an equivalence notion of your choice, can you find an encoding of the higher order π-calculus to the normal π-calculus?

We use weak bisimulation.

The idea is to use name as pointer to processes.
For each process, we introduce a "trigger" process that we can synchronize with to get a copy of that process.
For each trigger we introduce a new restricted name.

> Apply your translation to the example above.

$
\begin{array}{rcl}
P   & ≝ & !x(r).P' \\\\
Q   & ≝ & ?x(a).(Q' ~|~ !a) \\\\
R   & ≝ & … \\\\
T_R & ≝ & ?r.(R | T_R) \\\\
…   &   &
\end{array}
$

the process $P ~|~ Q$ becomes $(ν r) P ~|~ Q ~|~ T_R$.
it can synchronize on $x$ and become $(ν r) P' ~|~ Q' ~|~ !r ~|~ T_R$.
Then we can synchronize on $r$ to get $(ν r) P' ~|~ Q' ~|~ R ~|~ T_R$.
The synchronization on $r$ appears as $τ$ as $r$ is restricted.

## $ν$-free π-calculus

> Given the ordering defined above, show that the $ν$-free π-calculus is a WSTS and make sure to address all subclaims properly.

We need to show that
1. the ordering is a WQO
2. the ordering is compatible w.r.t. the transition relation
3. an effective pred basis to apply the backward algorithm

For (1), we need to show that there is there is a *finite number of kinds of processes* where a kind is a process ID and specific a arguments.
* Because we are working with the $ν$-free π-calculus, the number of names is set by the initial configuration.
* Because there are a finite number of processes ID, each has a finite set of parameters with a finite range, it is all finite.
* The order is equivalent to enumerate all the kinds of process and counting them.
  Assume we have $m$ kinds of processes.
  Then order is equivalent to the pointwise ordering of $ℕ^m$ which is a WQO.

For (2), the key element is the parallel rule.
\\[{
  P  \stackrel{π}{→}  P'
}\over{
  P|Q  \stackrel{π}{→}  P'|Q
}\\]
Given two comparable state $(ν \vec a) ∏_i A_i(\vec a_i) ≤ (ν \vec a) \left(∏_i A_i(\vec a_i) ~|~ ∏_j A_j(\vec a_j) \right)$, we can write them as $(ν \vec a) P ≤ (ν \vec a) P ~|~ Q \right)$.
If we have a step of the $P$ then using the parallel rule, $P|Q$ can do the same.

(3) is the tedious part.
We need to
* Case split on the $A_i(\vec a_i)$ in $(ν \vec a) ∏_i A_i(\vec a_i)$
* Case split on the transitions which result in $A_i(\vec a_i)$
* For transition which need more than one process (send/receive) find all the processes to execute the transition backwards.
  If such processes do not exist, just add them.
  Remember we are working with the upward-closed sets.
* Apply the transition backwards.

__TODO ...__
