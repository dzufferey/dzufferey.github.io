# Analyzing π-calculus processes

## Examples for the graph interpretation of the π calculus

### Ping-pong

Let us a look at the ping-pong example:

```
ping(x,y) ≝ !x.pong(y,x)
pong(x,y) ≝ ?x.ping(y,x)
```
With the initial configuration: `(ν x y)(ping(x, y) | pong(x,y))`

For these definitions there are 5 rewrite rules.
For the synchronization to happens the `x` name must be the same for the two processes.
However, for `y` it may or may not be the same.
In this example, it is the same, but when generating the rules this might be unknown.
Also, we need to consider the case where `x=y`.

With `y` being the same for `ping` and `pong`:
```
        _____________________________
       /          ___________________\_________
      /  x       /                    \   y    \
    ping───────●                     pong───────●
   y │         │ x       →          x │         │ y
     ● ───────pong                    ● ───────ping
      \    y    \____________________/_______x_/
       \____________________________/
```

With `y` being the different for `ping` and `pong`:
```
        _____________________________
       /          ___________________\_________
      /  x       /                    \   y    \
    ping───────●                     pong───────●
   y │         │ x       →          x │         │ y
     ●     ●──pong                    ●        ping──●
      \     \y  \____________________/________x_/   /
       \     \______________________/______________/
        \__________________________/
```

With `x=y` for `ping`:
```
        _____________________________
       /          ___________________\_________
      /  x,y     /                    \  x,y   \
    ping───────●                     pong───────●
               │ x       →                      │ y
         ● ───pong                            ping──●
          \ y   \____________________________x_/   /
           \______________________________________/
```

With `x=y` for `pong`:
```
        _____________________________
       /          ___________________\_________
      /  x       /                    \   y    \
    ping───────●                     pong───────●
   y │         │ x,y     →          x │         │ x,y
     ●        pong                    ●        ping
      \         \____________________/_______ _/
       \____________________________/
```


With `x=y` for `ping` and `pong`:
```
      _____________________________
     /          ___________________\_________
    /  x,y     /                    \ x,y    \
  ping───────●                     pong───────●
             │ x,y     →                      │ x,y
            pong                             ping
              \______________________________/
```


The configuration `(ν x y)(ping(x,y) | pong(x,y))` corresponds to the graph:
```
       x
  ping───────●
 y │         │ x
   ● ───────pong
          y
```

Only the first rule matches.
After applying the rule we get:
```
       y
  pong───────●
 x │         │ y
   ●────────ping
           x
```

This graph is isomorphic to the previous one as expected.



### Client-Server

```
Server(s) ≝ ?s(c).(Server(s) | Reply(c))
Client0(s) ≝ τ.((νc) Request(s,c) | Client1(s,c))
Client1(s, c) ≝ ?c.Client0(s)
Request(s, c) ≝ !s(c).0
Reply(c) ≝  !c.0
```

From the equations above, we can extract 5 rules:

`Client0` making an internal step (sending a request):
```
       _________________________________
      /         ________________________\__________
     /     s   /                         \      s  \
  Client0─────●         →               Client1─────●
                                        c │     c   │ s
                                          ● ──────Request
```

`Server` receiving a `Request` with `sِ≠c`:
```
       ________________________________
      /        ________________________\__________
     /    s   /                         \      s  \
  Server─────●         →               Server─────●
             │ s                              c
    ● ────Request                        ● ──────Reply
     \  c                               /
      \________________________________/
```

`Server` receiving a `Request` with `sِ=c`:
```
       ________________________________
      /        ________________________\__________
     /    s   /                         \      s  \
  Server─────●         →               Server─────●
             │ s,c                                | c
          Request                                Reply
```


`Client1` receiving a `Reply` with `s≠c`:
```
       _________________________________
      /         ________________________\__________
     /     s   /                         \      s  \
  Client1─────●         →               Client0─────●
  c │    c
    ● ──────Reply                       ●
     \_________________________________/
```

`Client1` receiving a `Reply` with `s=c`:
```
       _________________________________
      /         ________________________\__________
     /   s,c   /                         \      s  \
  Client1─────●         →               Client0─────●
              │ c
            Reply
```

_Remark._
We don't need to consider the synchronization between prefixes of different arity (`!s(c)` and `?c`) as the synchronization cannot happen.


Let us look at a transition on the configuration `(ν s) Server(s) | Client0(s) | Client0(s)`:
```
   Server
      │ s
  ┌───●───┐
s │       │ s
Client0  Client0
```
The only rule that applies is `Client0` sending a request.
Furthermore, there is two possible way of matching the rule.

Here is the rule matching the left `Client0`:
```
       _________________________________
      /         ________________________\__________
     /     s   /                         \      s  \
  Client0─────●            →            Client1─────●
   |          |                         c │     c   │ s
   |          |                           ● ──────Request
   |          |
   |          |
   |          |
   |          |
   |          /
   |   Server/
   |    s │ /
   |  ┌───●───┐
   \  │ s     │ s
    Client0  Client0
```

When we apply the rule we get:
```
       _________________________________
      /         ________________________\__________
     /     s   /                         \      s  \
  Client0─────●            →            Client1─────●
   |          |                        /c │    c  s │ \
   |          |                       /   ● ────Request\
   |          |                       |  /          |   \
   |          |                       |  |          |___|__
   |          |                      _|__|              |  \
   |          |                     / |                 /   \
   |          /                     | \                /     \
   |   Server/                      |  \        Server/      |
   |    s │ /                       \   \        s │ /       |
   |  ┌───●───┐                      \   \   ┌─────●───┐     |
   \  │ s     │ s                     \   \  │ s   │   │ s   |
    Client0  Client0       →           \   Client1 │ Client0 |
                                        \    │     │         /
                                         \ c │     │s       /
                                          \__●───Request___/
                                                c
```
The final morphism from the starting and ending configuration is omitted.



## Depth-bounded processes: a well-structured fragment of the π-calculus

This part is roughly based on [this paper](http://dzufferey.github.io/files/2010_Forward_Analysis_of_Depth-Bounded_Processes.pdf) and [the corresponding slides](http://dzufferey.github.io/files/FoSSaCS10-DepthBounded_processes_slides.pdf).

Following the graphical interpretation we saw earlier, we are going to find a fragment of the π-calculus which can be analyzed, i.e., a fragment which is not Turing complete.
We will try to keep all the feature of the π-calculus, e.g., mobility.
To achieve this, we identify a well-structured fragment.
Therefore, we need to find a compatible WQO on processes configurations.

The "natural" ordering is the subgraph isomorphism.
As we saw previously, it is suitable to encode properties such as covering.
Also, compatibility/monotonicity is straightforward with subgraph isomorphism.
Adding more vertices in a graph preserves the subgraphs.
On the other hand, subgraph isomorphism is not a WQO for all graphs.

The fragment of the π-calculus we look at is called _depth-bounded processes_, or depth-bounded systems.
The idea is to bound the "longest chain of processes" by limiting the nesting depth of restrictions (`ν`),

### Compatibility/monotonicity

To show compatibility of depth-bounded processes we use the graph interpretation.
Below is a proof sketch.

In the graph interpretation, we use subgraph isomorphism for both
* testing whether transitions are applicable: the LHS of the rule is a subgraph of the graph to rewrite
* ordering of configurations: a configurations is smaller if it is a subgraph of another configuration.

We need to prove:
```
∀ M, M′, N.    M  ≤  N
∃ N′.          ↓     ↓
               M′ ≤  N′
```

* Assume we that for `M → M′` we applied the rule `r: L ⇀ R`.
  Therefore, we know that `L ≤ M`.
* By assumption `M  ≤  N` and because `≤` is transitive, we have that `L ≤ N`.
  Therefore, we can also apply the rule to `N`.
* Because the rule does not change the part that is not matched, we get `M′ ≤  N′`.
  More precisely,
  - From `L ≤ M` we have a partial morphism `m₁` from `L` to `M`,
    from `M ≤ N` we have a partial morphism `m₂` from `M` to `N`,
    `m₂∘m₁` is a partial morphism from `L` to `N`.
  - The rewriting from `M` to `M′` is a mapping `m₁∘r′` applied to `L` and extending it to `m₂∘m₁∘r′` give `N′`.
  - Roughly we have `M′ = m₁∘r′(L)` and `N′ = m₂∘m₁∘r′(L) = m₂(M′)`.
    Therefore, `M′ ≤ N′`.


### Nesting depth

A _configuration_ is the subset of the π-calculus given by:
```
C ::= 0         (empty)
    | C | C     (composition)
    | (νa) C    (restriction)
    | A(x)      (named process, a can be a list of arguments)
```

The _nesting level_ of a configuration is defined as:
* `nesting(0) = 0`
* `nesting(A(x)) = 0`
* `nesting((νa) P) = nesting(P) + |a|`
* `nesting(P | Q) = max(nesting(P), nesting(Q))`

The _Nesting depth_ is the minimal nesting level for a configuration: `depth(P) = min { nesting(Q) | P ≡ Q }`.

We say that a system is _depth-bounded_ if there is a bound `k` such that the depth of all reachable configurations is less or equal to `k`.

__Remark.__
The characterization of depth-bounded processes is a _semantic characterization_ (not a syntactic one).
It depends on what the system does (the reachable configurations) and it is not something we can check easily.
More on that later.

#### Graphical interpretation of the nesting depth
In the graph interpretation of the π-calculus, a system is depth-bounded it means we have a bound on the longest acyclic path in any reachable configuration/graph.

For instance, `(ν a b c) P(a) | Q(a,b) | Q(a,c)` has depth 2 because it is structurally congruent to `(ν a) P(a) | ((ν b) Q(a,b)) | ((ν c) Q(a,c))`.

The corresponding graph is
```
  P──●──Q──●
  │
  └──●──Q──●
```
The longest acyclic path has length 6.

The bound on the longest acyclic path in the graph is _roughly_ four time the nesting depth.
The difference comes from the arity of the definitions.

For instance, looking at π-calculus processes, we have:
* `depth( (ν a) P₁(a) ) = 1`
* `depth( (ν a b) P₂(a, b) ) = 2`
* `depth( (ν a b c) P₃(a, b, c) ) = 3`

But when looking at the corresponding graphs, the bound is always 2:
```
                          ┌───●
  P₁──●       P₂──●       P₃──●
              └───●       └───●
```

A different, but equivalent, characterization of graphs which is closer to the nesting depth is the _tree-depth_ of a graph (roughly twice the nesting depth and half the length of the longest acyclic path).
This already has the idea that we can embed our graph in trees and use ordering on trees to show that we have a WQO if the depth is bounded.

__Tree-depth.__
* A _tree_ is a fully connected acyclic graph.
* A _rooted tree_ is a tree with a dedicated root vertex.
* A _rooted forest_ is a disjoint union of rooted trees.
* The _height of a vertex_ `v` in a rooted forest `F`, denoted `height(F, v)`, is the number of vertices on the path from the root of the tree to which `v` belongs to `v`.
* The _height_ of `F` is the maximal height of the vertices in `F`.
* Let `v`, `w` be vertices of `F` and let `T` be the tree in `F` to which `w` belongs.
  The vertex `v` is an _ancestor_ of vertex `w` in `F` (`v ≼ w`), if `v` belongs to the path connecting `w` and the root of `T`.
* The _closure_ `clos(F)` of a rooted forest `F` is the graph consisting of the vertices of F and the edge set `{ (v, w) | v ≼ w, v ≠ w }`.
* The _tree-depth_ `td(G)` of a graph `G` is the minimum height of all rooted forests `F` such that `G ⊆ clos(F)`.

[The slides](http://dzufferey.github.io/files/FoSSaCS10-DepthBounded_processes_slides.pdf) have figures that show the closure and tree-depth.

__Proposition.__
A set of configurations is depth-bounded iff the corresponding graphs have bounded tree-depth.

__Proposition.__
A set of graphs `G` has bounded tree-depth if there is a bound on the longest acyclic path in any graph of `G`.


### Tree encoding

Arbitrary graph are not well-ordered by subgraph isomorphism.
On the other hand, finite trees are well ordered by inf-embedding (Kruskal's tree theorem, see [notes 4](notes_4.md)).
Laver even extended that theorem to get a BQO as long as the labels on the nodes are labeled by a BQO.
However, these theorems use inf-embedding rather than subgraph isomorphism and have labels only on the vertices, not the edges.
Therefore, we need to find an encoding of graphs with bounded tree-depth and labeled on nodes and edges into tree with labels on the nodes such that subgraph-isomorphism corresponds to inf-embedding.

Here are the main elements we need to pay attentions to in the encoding:
1. from forest to tree
2. edge labels
3. edges in the closures but not in the tree
4. inf-embedding vs isomorphism

__Forests and trees.__
The definition of tree-depth allows graph with unconnected components.
On the other hand, the target ordering works on trees.
Given a rooted forest `F`, we can add a new global root and connect the root of each tree in `F` to the new node.
The result is a rooted tree with tree-depth `depth(F) + 1`.

__Edge labels.__
We can encode labels on the edges by inserting new nodes in the middle of the edge to represent the label.
For instance, the graph
```
           s
  Client0─────●
```
can be transformed in
```
  Client0──s──●
```

To avoid introducing unwanted match, we need to make sure the labels on the edges are disjoint from the labels on the nodes.
(Rename if it is not the case.)

This step preserves the graph structure, but doubles the depth.

__Edges in the closure.__
In the closure, a node may be connected to more than its parent.
It can be connected to any ancestor.
We need to remove these extra edges.

Assume the tree-depth is `k`, there is at most `k-2` ancestor (excluding the parent) to which a node may be connected.
Therefore, using `2^{k-2}` new labels it is possible to precisely tell to which ancestors a node is connected.
The new label is the product of the old label an this new "ancestry" label.

__Inf-embedding vs isomorphism.__
Finally, inf-embedding makes is possible to "skip" some parents as long as the ancestor ordering is kept.
However, isomorphism preserves every nodes along paths.

To avoid this, we can encode the height of a node as part of its label.
A node a height `h` with label `l` get a new label `(l,h)`.


In the steps above we generated more labels for the nodes.
While the number depends on the depth, since the depth is finite, the total number of labels is finite.
Therefore, the set of labels is a BQO with `=`.

__Remark.__
The reduction above may yield a finite number of different graphs.
To show that isomorphism is preserved in the sense that, given two graphs with one being a subgraph of the other, it is possible to encode them as trees such one tree is embedded in the other.
This reduction is not defined to be efficient (or implemented) but only to show the order is a BQO.

The details of the tree encoding can be found in [the paper](http://dzufferey.github.io/files/2010_Forward_Analysis_of_Depth-Bounded_Processes.pdf).

__Theorem.__ Depth-bounded processes are an instance of WSTS.

Also, the details can be found in [the paper](http://dzufferey.github.io/files/2010_Forward_Analysis_of_Depth-Bounded_Processes.pdf) or an earlier [paper by Roland Meyer](http://dl.ifip.org/db/conf/ifipTCS/ifipTCS2008/Meyer08.pdf).

### Forward vs backward analysis for depth-bounded processes

Let us discuss some of the downside of the definition of depth-bounded processes and the implications for forward/backward analysis of WSTS.

The depth-boundedness restriction is a semantics restriction, i.e., it depends on the reachable states.
The main problem is that it is actually undecidable to know a priori if a process is depth-bounded.

__Theorem.__ Determining if a system is depth-bounded is undecidable.

_Proof sketch._
By reduction of the halting problem of Minsky machine to depth-boundedness.
Recall the encoding of Minsky machines in CCS of [notes 9](notes_9.md), it also works in the π-calculus.
If a Minsky machine that halts it the values of the counter are bounded by some `k` and, therefore, the corresponding CCS process is depth-bounded.


The second problem is specific to the backward analysis.
Let us assume we are dealing with a process which is depth-bounded but we don't know the value of the bound.
(The exact value is not needed as the definition existentially quantify over it.)
The system is guarantee to be depth-bounded on the (forward) reachable states.
When going backward, the `pre` operator can generate unreachable state, for instance if the target is not coverable.
These unreachable state may not respect the bound...

One solution, is to look at `k`-bounded processes, i.e., processes with a known bound.
another approach is to use a forward analysis on depth-bounded processes.


### Ideal for depth-bounded processes

In the case of lossy channel system we were able to represent ideal using simple regular expression (finite state automaton).
Here we will use a similar idea.
However, we are working with trees instead of sequences and, therefore, we will use tree automaton.


__Notation.__
In the notes, we use the CSP notation to send/receive messages (`!a`,`?a`).
The paper and slides uses the CCS notation (`ā`,`a`).
Unfortunately, the π-calculus also has a `!` operator for replication.
Here we will use `*`.

| Operator      | CCS    | This document |
|---------------|--------|---------------|
| send/output   | `ā(b)` | `!a(b)`       |
| receive/input | `a(b)` | `?a(b)`       |
| replication   | `!P`   | `P*`          |

__Replication.__
The replication operator `P*` was introduced in π-calculus as an alternative to recursive definitions.
Here we will repurpose this operator to represent infinite sets of processes.
The meaning of the replication is given by a single congruence rule:
```
P* ≡ P | P*
```

#### Limit configurations in the π-calculus

To represent ideals, we will use limit elements, i.e., similar to the extended markings of Petri nets.
An ideal is the downward-closure of the limit element.

A _limit configuration_ is the subset of the π-calculus given by:
```
C ::= 0         (empty)
    | C | C     (composition)
    | (νa) C    (restriction)
    | A(x)      (named process, a can be a list of arguments)
    | C*        (replication)
```
Compared to configurations, we just add the replication operator.

The nesting depth is extended with `nesting(C*) = nesting(C)`.

__Lemma.__
Ideals are the downward-closure of limit configurations.

_Proof sketch._
The proof uses the same principle to the proofs the product are ideals for SRE ([notes 8](notes_8.md)).
What makes the construction more complicated is that it works on tree automata instead of normal automaton.
Given two configuration included in a limit configuration, we can unfold the replicated terms until it covers both configuration (pumping argument).


#### Limit configurations as graph

The graphical interpretation is something we used when we tried to implement the analysis described above.
It corresponds to the visual representation found in the [slides](http://dzufferey.github.io/files/FoSSaCS10-DepthBounded_processes_slides.pdf) (graph with subgraph marked with `*`).
We call them nested graphs.

You can find a formal definition in Section 5 of [this paper](http://dzufferey.github.io/files/2013_structural_counter_abstraction.pdf).
Here, we give an high-level view.

A _nested graph_ is a 4-tuple `(V,E,l,n)` where `(V,E,l)` is a labeled graphs and `n: V→ℕ` is the replication depth.
Intuitively, the replication depth in the number of `*` which enclose a node.
Normal nodes have replication depth `0`.

The meaning of nested graphs is given in terms of _unfolding_.
It is possible to unfold (copy) regions of the graph with depth `> 0`.
The fresh nodes from the copy get their depth reduced by `1`.

Inclusion between nested graph can be tested by generalizing subgraph isomorphism.
The difference is that the mapping is not necessarily injective for nodes with depth `>0`.
Also the mapping must respect the inequalities of depth across edges.
