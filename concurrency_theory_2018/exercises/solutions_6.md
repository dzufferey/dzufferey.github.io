# Solutions 6

Thanks to Ann-Sophie Steinert, Matthias Kremer, and Florian Wirschem for contributing to this solution.


## Event-Driven Asynchronous Programs

To show that asynchronous programs are a WSTS we need to find a WQO and prove it is compatible.

For this let $S$ be the system states:

* $(S, \rightarrow)$ is a TS.
* As WQO $(S, \leq)$ we use the following order: $(d_1, T_1) \leq (d_2, T_2)$ iff $d_1 = d_2$ and $T_1 \leq T_2$, with $T_1 ≤ T_2$ is finite multiset embedding.
  So $T_2$ contains every task-id of $T_1$ and at least the same number of times.
  Since there are finitely many data values $(\mathcal{D}, =)$ is a WQO and we have seen that embedding of finite multiset $((ID × S → ℕ), ≤)$ is also a WQO.
* compatibility: for $x_1 \rightarrow^t x_2$ with transition t being either a memory access or a post. Then $y_1$ has the same tasks in at least the same count as $x_1$ and also the same shared variables, thus we can use the same transition (or more posts) to reach $y_2 \geq x_2$. This is basically the same argument as compatibility for Petri net.

## Comparing Models of Communicating State Machines

### Unordered Channels (Bags)

#### Task 1

* Rule for sending:
\\[{
    M[i] \overset{j!a}{\rightarrow}_{i} s \qquad C'=C[(i,j)\leftarrow C[i,j]\cup \lbrace a\rbrace] \qquad M'=M[i \leftarrow s]
}\over{
    (M,C) ⇒ (M',C')
}\\]

* Rule for receiving
\\[{
    M[i]\overset{?a}{\rightarrow}_{i} s \qquad C[j,i]\in a C'=C[(j,i)\leftarrow C[j,i] \backslash \lbrace a\rbrace] \qquad M'=M[i \leftarrow s]
}\over{
    (M,C) → (M',C')
}\\]

#### Task 2

bag+p2p and bag+mailbox are equivalent.
A process's mailbox is the union of all its incoming channels.

### FIFO Mailbox with Lookahead

#### Task 3

The transitions of FIFO+mailbox are strictly included in the transitions of FIFO+mailbox+lookahead.

* FIFO+mailbox → FIFO+mailbox+lookahead:

  Consider the rule with lookahead (the only change):
  \\[{
  M[i] \stackrel{?a}{→_i} s   \qquad   C[i] = w·a·w'   \qquad  C' = C[i ←  w·w']  \qquad  M' = M[i ← s]  \\qquad ∀ a' ∈ w.\ s' ∈ S_i.\ (M[i], ?a', s') ∉ →_i 
  } \over{
                          (M, C) → (M', C')
  }
  \\]
  replacing $w$ by $ε$ and simplfying give the rule without lookahead.
  So FIFO+mailbox is a special case of FIFO+mailbox+lookahead.

* FIFO+mailbox+lookahead → FIFO+mailbox:

  Consider the two machines:

  __A__
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      A [label = ""];
      B [label = ""];
      C [label = ""];
      init -> A;
      A -> B [ label = "B!a" ];
      B -> C [ label = "B!b" ];
  }
  ```
  __B__
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      A [label = ""];
      B [label = ""];
      C [label = ""];
      init -> A;
      A -> B [ label = "?b" ];
      B -> C [ label = "?a" ];
  }
  ```
  The lookahead make it possible to receive the messages while no lookahead gets stuck.

#### Task 4

The transitions of FIFO+mailbox+lookahead are strictly included in the transitions of mailbox+bag.
Intuitively, the bag allow more reordering than the lookahead.

* FIFO+mailbox+lookahead → mailbox+bag:
  We have that $∀ i.\ C_{bag}[i] = \\{ a ~|~ ∃ w,w'.\ C_{FIFO}[i] = w·a·w' \\}$.
  We can use this as basis for an induction proofs over the traces of both FIFO and bag.
  Showing at each step that bag can do all the FIFO+mailbox transitions and preserve the equality above.

* mailbox+bag → FIFO+mailbox+lookahead
  Consider the two machines:

  __A__
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      A [label = ""];
      B [label = ""];
      C [label = ""];
      init -> A;
      A -> B [ label = "B!a" ];
      B -> C [ label = "B!b" ];
  }
  ```
  __B__
  ```graphviz
  digraph finite_state_machine {
      rankdir=LR;
      node [shape = circle];
      init [shape = none, label = ""];
      A [label = "b₀"];
      B [label = "b₁"];
      C [label = "b₂"];
      init -> A;
      A -> B [ label = "?a" ];
      A -> C [ label = "?b" ];
  }
  ```
  With bag, B can get to $b₁$ and $b₂$.
  With lookahead, B only get to $b₁$.
