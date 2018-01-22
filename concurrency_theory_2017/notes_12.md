# Communicating systems: further analysis, extensions, and types

To finish on the subject of communicating systems and process calculi, we are going to get an overview of a few things related to this topics.

## Building further analysis on top of the covering set for depth-bounded processes

Here is a recipe to build more analysis, e.g., termination, on top of the covering set (reachability analysis):

1. Compute the covering set (finite union of ideals)
2. Apply the transitions to the ideals in the cover and keep track of which ideal is mapped to which, use this to build an automaton.
   This automaton contains all the behavior of the systems once it is "saturated".
3. Analyze the automaton further …

The idea is to use the cover and the graph structure in the ideal as a first step to "resolve" the mobility and then use other analysis which cannot deal with the mobility.

Here is an example to build termination analysis for the 3rd step:
- Each replicated node in the ideals are associated to a counter variable.
- For all the transition, keep track of the mappings between nodes to generate update of the variables, i.e., `x′ = x + 1` is one new node of the type corresponding to `x` is created.
  The result is a multi-transfer net, an extension of transfer Petri net where multiple transfer edges are allowed.
- Use an analysis on the net to show termination.

Here are some [slides](http://dzufferey.github.io/files/2013_structural_counter_abstraction_slides.svg) (best viewed in a browser as the SVG includes some javascript) that shows visually this process.
Here is the [paper](http://dzufferey.github.io/files/2013_structural_counter_abstraction.pdf) if you are curious.


## Variations of the π-calculus

Over the years, many variations of the π-calculus, aimed at simplifying the modeling of particular systems has been developed.
Here we list a few and describe one of them in more details.

* The [Spi-calculus](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.63.2305) which add cryptographic primitive like what was presented in [week 6](slides_6.pdf).
* The [stochastic π-calculus](https://academic.oup.com/comjnl/article/38/7/578/400773) adds rate to the transition and has been used to model biological systems. It semantics is give an by a continuous time Markov chain.
* The [ambient calculus](http://lucacardelli.name/Papers/MobileAmbients.A4.pdf) adds ambient which models the "physical" location where the computation happens.

### Broadcast π-calculus

The broadcast π-calculus models broadcast communication, i.e., when messages is broadcast and all the processes that can receive the message do so.
The syntax is the same as the π-calculus, only the semantics is different.

We will need the notion of that we can _observe_ `α` in a process `P` if `?α(b).A` occurs unguarded in `P` for some `A` and some `b`.
It is written `P↓_α`.
It is a variation of the commitments we discussed in [week 9](notes_9.md).

__Semantics.__
* Silent action
  ```
  ───────────
  τ.P  ─τ→  P
  ```
* Send action
  ```
  ───────────────────
  !a(b).P  ─!a(b)→  P
  ```
* Receive action
  ```
  ──────────────────────────
  ?a(b).P  ─?a(c)→  P[b ↦ c]
  ```
* Receive skip
  ```
     ¬P↓_α
  ─────────────
  P  ─?a(b)→  P
  ```
* Parallel internal
  ```
    P ─τ→ P′
  ────────────
  P|Q ─τ→ P′|Q
  ```
* Parallel send
  ```
  P ─!a(b)→ P′  Q ─?a(b)→ Q′
  ──────────────────────────
        P|Q ─!a(b)→ P′|Q′
  ```
* Parallel receive
  ```
  P ─?a(b)→ P′  Q ─?a(b)→ Q′
  ──────────────────────────
       P|Q ─?a(b)→ P′|Q
  ```
* Choice internal
  ```
   P ─τ→ P′
  ──────────
  P+Q ─τ→ P′
  ```
* Choice send
  ```
   P ─!a(b)→ P′
  ──────────────
  P+Q ─!a(b)→ P′
  ```
* Choice receive
  ```
  P ─?a(b)→ P′  P↓_α
  ──────────────────
    P+Q ─!a(b)→ P′
  ```
* Choice skip
  ```
   ¬P↓_α   ¬Q↓_α
  ───────────────
  P+Q ─?a(b)→ P+Q
  ```
* Restriction 1
  ```
  P ─π→ P′  π ≠ !a(_)  π ≠ ?a(_)  π ≠ !_(a)  π ≠ ?_(a)
  ────────────────────────────────────────────────────
                  (νa)P ─π→ (νa)P′
  ```
* Restriction 2
  ```
     P ─!a(c)→ P′
  ────────────────
  (νa)P ─τ→ (νa)P′
  ```
* Congruence
  ```
  P ≡ P′  P′ ─π→ Q  Q ≡ Q′
  ────────────────────────
          P ─π→ Q′
  ```

__Example.__
Here is a simple publisher-subscriber model:
```
publisher(topic) ≝ !topic.publisher(topic)
subscriber(topic) ≝ ?topic.processing(topic)
processing(topic) ≝ τ.subscriber(topic)
```
Let us look at one possible execution with the configuration `(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | subscriber(t₁) | subscriber(t₂) )`:
* initial: `(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | subscriber(t₁) | subscriber(t₂) )`
* `!t₁`: `(ν t₁ t₂)( publisher(t₁) | processing(t₁) | processing(t₁) | subscriber(t₂) )`
* `τ` at subscriber: `(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | processing(t₁) | subscriber(t₂) )`
* `!t₁`: `(ν t₁ t₂)( publisher(t₁) | processing(t₁) | processing(t₁) | subscriber(t₂) )`
* ...

Notice that the first message is received by two subscribers while the second message is only received by one subscriber.

__Monotonicity of the Broadcast semantics.__
In this broadcast semantics, sending is non-blocking and only the processes that listen on the channel when a message is sent receive the message.
Intuitively, this means that is it also possible to define an WSTS for some class of depth-bounded processes.

Compared to what we saw about depth-bounded processes, we can reuse the ordering (subgraph isomorphism) and the "bounded acyclic path" condition.
However, to compute transitions and acceleration/widening cannot reuse the same approach based on graph rewriting.
It is not possible a priori how many processes are changed by a single transition.


## Types for the π-calculus

Until now, we have always assumed that names are used in a "correct" way, e.g., if two arguments are send in a message then the receiver expects two arguments.
However, we just assumed this and did not check it.
Orthogonal to the question of reachability/covering that are the focus of this lecture, there is an area of research dedicated to typing processes/channels to make sure the communication happens properly, e.g., messages have the right type, deadlock-freedom.
Here we will just scratch the surface of this topic.

### Typing names

The first tentative to type the π-calculus is to give types to the names.
The type of name is its the type of the names it carries when exchanging messages.

#### Types
Let `S` by a set of sort identifier.
Each type is a pair in `(s, o) ∈ S × S*` where
* `s` is the subject sort, i.e., name of the type.
* `o` is the object sort, i.e., the list of sort names that are sent as payload with the subject name.

Then in each definition and restriction, we need to add a type for the names.

__Example.__
Let us look a back at the handover example.
We have the following types:
* `(ALERT, ())`
* `(GIVE, (TALK,SWITCH))`
* `(SWITCH, (TALK,SWITCH))`
* `(TALK, ())`

And the definitions annotated with types are:
```
Car(talk: TALK, switch: SWITCH) ≝
      ?talk.Car(talk, switch)
    + !talk.Car(talk, switch)
    + ?switch(talk′, switch′).Car(talk′, switch′)
Base(talk: TALK, switch: SWITCH, give: GIVE, alert: ALERT) ≝
      ?talk.Base(talk, switch, give, alert)
    + !talk.Base(talk, switch, give, alert)
    + ?give(t, s).!switch(t, s).IdleBase(talk, switch, give, alert)
IdleBase(talk, switch, give, alert) ≝
    ?alert.Base(talk, switch, give, alert)
Center(t₁: TALK, t₂: TALK, s₁: SWITCH, s₂: SWITCH, g₁: GIVE, g₂: GIVE, a₁: ALERT, a₂: ALERT) ≝
    !g₁(t₂, s₂).!a₂.Center(t₂, t₁, s₂, s₁, g₂, g₁, a₂, a₁)
```

#### Typing rules
A typing environment `Γ` is a map from names to types and definitions to tuples of types.

The initial `Γ` maps the definitions names to the tuple of type which correspond to the arguments.
Then we can use the following rules to check the definitions' bodies.

__Notation.__
We use the following notation: `a|_i` is the projection of the `i`th element of the tuple `a`.
Given a type identifier `N`, we use `ob(N)` to get the object sort of `N`, e.g., `ob(GIVE) = (TALK,SWITCH)`.

```
Γ + (a,s) + … ⊢ P
──────────────────
Γ ⊢ A(a: s, …) ≝ P
```

```
─────
Γ ⊢ 0
```

```
Γ ⊢ P  Γ ⊢ Q
────────────
 Γ ⊢ P + Q
```

```
Γ ⊢ P  Γ ⊢ Q
────────────
 Γ ⊢ P | Q
```

```
Γ + (a,s) ⊢ P
──────────────
Γ ⊢ (ν a: s) P
```

```
 Γ ⊢ P
───────
Γ ⊢ τ.P
```

```
|ob(Γ(a))| = n    Γ + (b₁,ob(Γ(a))|₁) + … + (b_n,ob(Γ(a))|_n) ⊢ P
─────────────────────────────────────────────────────────────────────
                        Γ ⊢ ?a(b₁ … b_n).P
```

```
|ob(Γ(a))| = n    ob(Γ(A))|₁ = Γ(b₁)  …  ob(Γ(A))|_n = Γ(b_n)
─────────────────────────────────────────────────────────────
                    Γ ⊢ !a(b₁ … b_n).P
```

```
|Γ(A)| = n    Γ(A)|₁ = Γ(b₁)  …  Γ(A)|_n = Γ(b_n)
─────────────────────────────────────────────────
                Γ ⊢ A(b₁ … b_n)
```


__Remark.__
The typing systems focuses on the arity of names but by giving differently named types to names with the same artiy, it can do some finer checks.
For instance, in the example above `ALERT` and `TALK` are used in the same way (no payload) but since their type is named differently, it is not possible to put an `ALERT` name instead of a `TALK` name.

This make is possible to have different granularity when typing names.
At one extreme, we can just keep track of the arity for instance, we can type CCS processes using only the type `(NAME, ())` and the monadic π-calculus with `(NAME, (NAME))`.
Or as with the example, give a finer distinctions by give naming differently what essentially is the same type.

#### Limitations

By only looking at names, the typing systems does not meet the typical requirements for a type system: progress and preservation.
While preservation holds, progress does not.

Consider the example below:
```
A(a: NAME) ≝ ?a.A(a)
```
and the initial state `(ν a: NAME) (A(a) | A(a))`
where name is the type `(NAME, ())`.

While this process is well typed it is stuck while being not `0`.
(The usual characterisation of progress is either can take a step or is `0`.)


Another limitation is that names needs to be used uniformly.
For instance, the encoding of polyadic π-calculus into monadic π-calculus is not possible with typed processes.
Assume we have `a: FOO` with `(FOO, (INT, STRING))`,
sending a message `!a(i s)` becomes `(ν arg: ???)!a(arg).!arg(i).!arg(s)`.
It is not possible to type `arg` as it is first used to send an `INT` and then a `STRING`.

To solve these limitations, another possibility is to type processes instead of names.


### Typing processes for two party communication

Channels carries bits, the type is used to give meaning to this bits.
At different time point, a channel can carry different types.

Rather than using the π-calculus, we will use a model which is closer to an actual systems.
In some sense, communicating state machines are what we need but we use a notation inspired from the process calculus as it is more compact.
Compared to the π-calculus:
- Processes and messages are different.
- Each process comes with a unique address/channel (synchronous or asynchronous+FIFO).
- Only primitive types, no high-order types

First, we look at the case of having only **two** processes.
In this setting, we can exploit a duality property for two party communication.
For instance, send is the dual or receive.

__Notation.__
Since we work with two processes, we implicitly assume that they are called `P` and `Q` and omit the addresses when sending/receiving.
To avoid confusion between integer and `0` as the "terminated process", we use `end` for termination.


#### Send/receive duality

__Example: straight line communication__

By straight line, we mean no control-flow (choice or recursion).

Let us look at this example:
```
P ≝ !1.!2.?comparison.end
Q ≝ ?a.?b.!(a ≥ b).end
```

Here the type of `P` is `!int;!int;?bool;end` and for `Q` we have `?int;?int;!bool;end`.

For such straight line type, we can define the duality as:
* `dual(?t) = !t`
* `dual(!t) = ?t`
* `dual(t₁;t₂) = dual(t₁); dual(t₂)`
* `dual(end) = end`

Then `(P: t₁) | (Q: t₂)` is well typed if `t₁ = dual(t₂)`

__Remark.__
It is easy to see that the `dual` relation is also its inverse: `dual(dual(t)) = t`.


#### Internal vs external choice duality

Straight line code is not that common and branching/choice is needed.
To properly deal with choice, we will need to make the distinction between internal and external choice.

__Example: badly structured choice__
First, let us look at an example of badly structured communication.
```
P ≝ !42.end + ?result.end
Q ≝ ?result.end + !42.end
```
While this could execute correctly in a synchronous system, it could lead to deadlock in an asynchronous system.
Even in an synchronous system, this example is trick as the choice in `P` and `Q` is coupled.

__Internal and external choice.__
Ideally, we want that each choice can be tracked to a single process (internal choice) while the other process learn about it (external choice).
Internal choice is implicitly linked to sending messages and external choice to receiving messages:
* internal choice is denoted as `l₁.P₁ ⊕ l₂.P₂` where `l₁` and `l₂` are _labels_.
* external choice is denoted as `l₁.P₁ & l₂.P₂` where `l₁` and `l₂` are labels.
The labels indicates which branch has been selected and the two processes synchronize on that label.
Here we present the choice as binary but it is straightforward to generalize to n-ary (`⊕_i l_i.P_i` and `&_i l_i.P_i`).

Our duality relations get extended with:
* `dual(l₁.P₁ ⊕ l₂.P₂) = l₁.dual(P₁) & l₂.dual(P₂)`
* `dual(l₁.P₁ & l₂.P₂) = l₁.dual(P₁) ⊕ l₂.dual(P₂)`

__Example.__
```
P ≝ add.!1.!2.?res.end ⊕ geq.!1.!2.?comparison.end
Q ≝ add.?a.?b.!(a + b).end & geq.?a.?b.!(a ≥ b).end
```
where
* `P` has type `add;!int;!int;?int;end ⊕ geq;!int;!int;?bool;end` and
* `Q` has type `add;?int;?int;!int;end & geq;?int;?int;!bool;end`.


#### Recursion

...

#### Types and Processes

Congruence 

#### Typing rules

...

#### Subtyping

Until now, the types directly reflect the processes and there is a direct syntacic match between them

works only on choice:
- fewer internal choice
- more external choice


#### properties: deadlock free, no message left in the channels

preservation and progress


#### What we did not cover

* internal steps
* higher-order types, scope restriction, and mobility
* process creation and parallel composition in general
* ...


### Multiparty session types.

Generalization to multiparty types work with a global type which is then projected on the different processes.
...
