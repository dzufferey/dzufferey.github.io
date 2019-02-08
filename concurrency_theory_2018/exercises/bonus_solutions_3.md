# Bonus Solutions 3

## Subtyping as a Refinement (or as a Simulation's Inverse)


#### Task 1

We start with two processes/type $P,Q$ such that $dual(P)=dual(Q)$, the construction is sightly simpler.

The key part is choice.
All the other actions are deterministic (have a single outcome).
What we need to look at how to define $δ$.

$
\begin{array}{lcl}
p & ≝ & ⊕_{i ∈ [1;n]} l_i;p_i' \\\\
q & ≝ & \\&\_{i ∈ [1;n]} l_i;q_i'
\end{array}
$

We want to capture the fact that $P$ is "making" the choice and $Q$ is "accepting" the outcome.

Let $(p,q)$ be the state then we have:
* $δ((p,q), P) = \\{ \\{ (p_i',q_i') \\} ~|~ 1 ≤ i ≤ n \\}$
* $δ((p,q), Q) = \\{ \\{ (p_i',q_i') ~|~ 1 ≤ i ≤ n \\} \\}$

$P$'s transition are singleton sets, i.e., $P$ is choosing the exact action.
On the other hand $Q$'s transitions a single set of all the message it can receive.

Since, we start with $dual(P)=dual(Q)$, $δ$ is well-formed $\left\(∀ s.\ ∀ s_P ∈ δ(s, P).\ ∀ s_Q ∈ δ(s, Q).\ |s_P ∩ s_Q| = 1\right\)$.

Otherwise, we need to do a more detailed case split in the transitions.
For the messages that are sent but cannot be received we go to an $bad$ state.

#### Task 2

Then, we modify the system for $P',Q$ with $P'<:P$.

__Case 1: $P$ sends__

$
\begin{array}{lcl}
p & ≝ & ⊕_{i ∈ [1;m]} l_i;p_i' \\\\
q & ≝ & \\&\_{i ∈ [1;n]} l_i;q_i'
\end{array}
$
with $m ≤ n$

In the new ATS, we have 
* $δ_R((p,q), P) = \\{ \\{ (p_i',q_i') \\} ~|~ 1 ≤ i ≤ m \\}$
* $δ_R((p,q), Q) = \\{ \\{ (p_i',q_i') ~|~ 1 ≤ i ≤ n \\} \\}$

__Case 2: $P$ receives__

$
\begin{array}{lcl}
p & ≝ & \\&\_{i ∈ [1;m]} l_i;p_i' \\\\
q & ≝ & ⊕_{i ∈ [1;n]} l_i;q_i'
\end{array}
$
with $n ≤ m$

In the new ATS, we have 
* $δ_R((p,q), P) = \\{ \\{ (p_i',q_i') ~|~ 1 ≤ i ≤ n \\} \cup \\{ (p_i',⊥) ~|~ n < i ≤ m \\}\\}$
* $δ_R((p,q), Q) = \\{ \\{ (p_i',q_i') \\} ~|~ 1 ≤ i ≤ n \\}$

__R refines S from $P$'s perspective.__

Let $H$ be the $P$-simulation from $R$ to $S$.
$H$ is the identity function restricted to the common states.

The definitions of $R ≤_P S$ expands to:

$∀ T_R ∈ δ_R(s, P).\ ∃ T_S ∈ δ_S(s, P).\ ∀ R_S ∈ δ_S(s, Q).\ ∃ R_R ∈ δ_R(s, P).\ (T_S ∩ R_S) × (T_R ∩ R_R) ∈ H$

because $Q$ did not change  ($R_S = R_R$) and $H$ is the identity, the formula simplifies to:

$∀ T_R ∈ δ_R(s, P).\ ∃ T_S ∈ δ_S(s, P).\ ∀ R_S ∈ δ_S(s, Q). \ (T_S ∩ R_S) = (T_R ∩ R_S)$

because of our definition we have $δ_R(s, P) ⊆ δ_S(s, P)$.
Therefore, we can pick $T_R = T_S$.
Then we have

$∀ T_R ∈ δ_R(s, P). \ ∀ R_S ∈ δ_S(s, Q). \ (T_R ∩ R_S) = (T_R ∩ R_S)$

This is further simplifies to true.

_R refines S from $P$'s perspective._


__Symmetric case $S ≤_Q R$.__
This follows the same proof strategy.

__Remark.__
For the sub/super type of values, we need to generalize the construction to expand the send/receive of types as a choice between every values of the corresponding type.
For instance, we expand $int$ to a choice between $… ~ -1 ~ 0 ~ 1 ~ 2 ~ …$
