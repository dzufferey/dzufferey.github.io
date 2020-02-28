# Typing System for Communication

When we look at processes, we have always assumed that names are used in a "correct" way, e.g., if two arguments are sent in a message then the receiver expects two arguments.
However, we just assumed this and did not check it.
Orthogonal to the question of reachability/covering that are the focus of this lecture, there is an area of research dedicated to typing processes/channels to make sure the communication happens properly, e.g., messages have the right type, deadlock-freedom, when process terminates there is no pending messages.
Here we will just scratch the surface of this topic.

#### Properties of Type Systems

The main properties of a type system are:
* preservation: A well-typed process is still well-typed after taking a step.
* progress: either the program has finished or it it possible to take a step.

Notice that progress, in this context, is a very local condition and it is weaker than termination.
For instance, a process stuck in an infinite loop without message ($A ≝ τ.A$) can make progress.
Actually, we will see that $A ≝ τ.A$ can have any type.

However, progress is strong enough to imply the absence of deadlocks.
And it is not possible to have all the processes stuck on send/receive operations.

## Typing Names in the π-calculus

The first tentative to type the π-calculus is to give types to names.
The type of a name is the type of the names it carries when exchanging messages.

#### Types
Let $S$ be a set of sort identifier.
Each type is a pair in $(s, o) ∈ S × S^\*$ where
* $s$ is the subject sort, i.e., name of the type.
* $o$ is the object sort, i.e., the list of sort names that are sent as payload with the subject name.

Then in each definition and restriction, we need to add a type for the names.

__Example.__
Let us look a back at the handover example.
We have the following types:
* `(ALERT, ())`
* `(GIVE, (TALK,SWITCH))`
* `(SWITCH, (TALK,SWITCH))`
* `(TALK, ())`

And the definitions' annotated with types are:
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
A typing environment $Γ$ is a map from names to types and definitions to tuples of types.

The initial $Γ$ maps the definitions names to the tuple of type which correspond to the arguments.
Then we can use the following rules to check the definitions' bodies.

__Notation.__
We use the following notation: $a|_i$ is the projection of the $i$th element of the tuple $a$.
Given a type identifier $N$, we use $ob(N)$ to get the object sort of $N$, e.g., `ob(GIVE) = (TALK,SWITCH)`.

\\[{
  Γ + (a,s) + … ⊢ P
}\over{
  Γ ⊢ A(a: s, …) ≝ P
}\\]

\\[{
}\over{
  Γ ⊢ 0
}\\]

\\[{
  Γ ⊢ P \qquad Γ ⊢ Q
}\over{
  Γ ⊢ P + Q
}\\]

\\[{
  Γ ⊢ P \qquad Γ ⊢ Q
}\over{
  Γ ⊢ P | Q
}\\]

\\[{
  Γ + (a,s) ⊢ P
}\over{
  Γ ⊢ (ν a: s) P
}\\]

\\[{
  Γ ⊢ P
}\over{
  Γ ⊢ τ.P
}\\]

\\[{
  |ob(Γ(a))| = n  \qquad  Γ + (b₁,ob(Γ(a))|₁) + … + (b_n,ob(Γ(a))|_n) ⊢ P
}\over{
  Γ ⊢ ?a(b₁ … b_n).P
}\\]

\\[{
  |ob(Γ(a))| = n  \qquad  ob(Γ(a))|₁ = Γ(b₁)  \qquad … \qquad ob(Γ(a))|_n = Γ(b_n)
}\over{
  Γ ⊢ !a(b₁ … b_n).P
}\\]

\\[{
  |Γ(A)| = n  \qquad  Γ(A)|₁ = Γ(b₁)  \qquad  … \qquad  Γ(A)|_n = Γ(b_n)
}\over{
  Γ ⊢ A(b₁ … b_n)
}\\]


__Remark.__
The typing systems focuses on the arity of names but by giving differently named types to names with the same artiy, it can do some finer checks.
For instance, in the example above `ALERT` and `TALK` are used in the same way (no payload) but since their type is named differently, it is not possible to put an `ALERT` name instead of a `TALK` name.

This makes it possible to have different granularity when typing names.
At one extreme, we can just keep track of the arity for instance, we can type CCS processes using only the type `(NAME, ())` and the monadic π-calculus with `(NAME, (NAME))`.
Or as with the example, give a finer distinctions by give naming differently what essentially is the same type.

#### Limitations

By only looking at names, the typing systems does not meet the typical requirements for a type system: progress and preservation.
While preservation holds, progress does not.

Consider the example below:

$
\begin{array}{lcl}
A(a: \mathit{NAME}) & ≝ & ?a.A(a)
\end{array}
$

and the initial state $(ν a: \mathit{NAME}) (A(a) ~|~ A(a))$
where name is the type $(\mathit{NAME}, ())$.

While this process is well typed it is stuck while being not $0$.
(The usual characterization of progress is either can take a step or is $0$.)


Another limitation is that names needs to be used uniformly.
For instance, the encoding of polyadic π-calculus into monadic π-calculus is not possible with typed processes.
Assume we have $a: \mathit{FOO}$ with $(\mathit{FOO}, (\mathit{INT}, \mathit{STRING}))$,
sending a message $!a(i, s)$ becomes $(ν arg: ???)!a(arg).!arg(i).!arg(s)$.
It is not possible to type $arg$ as it is first used to send an $\mathit{INT}$ and then a $\mathit{STRING}$.

To solve these limitations, another possibility is to type processes instead of names.


## Typing Processes for Two Party Communication (Binary Session Types)

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
Since we work with two processes, we implicitly assume that they are called $P$ and $Q$ and omit the addresses when sending/receiving.
To avoid confusion between integer and $0$ as the "terminated process", we use $end$ for termination.

### Model

__System.__
A list of definitions of the 

$
\begin{array}{rcll}
System & ::= & A | A & \text{with}~ (A ≝ P)^\*
\end{array}
$

where
* $A$ are identifier of definitions
* $P$ is a process

__Processes.__

$
\begin{array}{rcll}
   P & ::= & π.P            & \text{(action)}   \\\\
     &   | & P + P   \qquad & \text{(choice)}  \\\\
     &   | & A              & \text{(named process)} \\\\
     &   | & end            & \text{(end)}
\end{array}
$

__Actions.__

$
\begin{array}{rcll}
   π & ::= & !expr          & \text{(send)}   \\\\
     &   | & ?a    \qquad   & \text{(receive)}  \\\\
     &   | & τ              & \text{(silent)}
\end{array}
$

__Expression.__

$
\begin{array}{rcll}
expr & ::= & a              & \text{(variable)} \\\\
     &  | & 0 | 1 | …       & \text{(integer literal)} \\\\
     &  | & true | false    & \text{(boolean literal)} \\\\
     &  | & ``∖w^\*"        & \text{(string literal)} \\\\
     &  | & …               &
\end{array}
$

Compared to the π-calculus the definition do not have parameters, process do not have parallel composition and restriction.
Messages do not carry name but values: integer, boolean, string, etc.

This model inherits the applicable $≡$ rules.

__Semantics.__
The semantics is a mix between π-calculus (process algebra notation) and communicating state machines (fixed number of participant).

* Silent action
  \\[ {}\over{τ.P | Q ~ → ~ P|Q} \\]
  \\[ {}\over{P | τ.Q ~ → ~ P|Q} \\]
* Choice
  \\[ {}\over{(P+P')|Q ~ → ~ P|Q} \\]
  \\[ {}\over{(P+P')|Q ~ → ~ P'|Q} \\]
  \\[ {}\over{P|(Q+Q') ~ → ~ P|Q} \\]
  \\[ {}\over{P|(Q+Q') ~ → ~ P|Q'} \\]
* Communication
  \\[ {}\over{!a.P|?b.Q ~ → ~ P|Q[a/b]} \\]
  \\[ {}\over{?b.P|!a.Q ~ → ~ P[a/b]|Q} \\]
* Congruence
  \\[{
  P ≡ P' \quad Q ≡ Q' \quad P'|Q' ~→~ P″|Q″ \quad P″ ≡ P‴ \quad Q″ ≡ Q‴
  }\over{
  P|Q ~→~ P‴|Q‴
  }\\]


__Remark.__
Here we present a version with synchronous communication but the principle is more general and also works with asynchronous+reliable+FIFO communication channels as defined for communicating state machines.

### Send/Receive Duality

__Example: straight line communication__

By straight line, we mean no control-flow (choice or recursion).

Let us look at this example:

$
\begin{array}{lcl}
P & ≝ & !1.!2.?comparison.end \\\\
Q & ≝ & ?a.?b.!(a ≥ b).end
\end{array}
$

Here the type of $P$ is $!int;!int;?bool;end$ and for $Q$ we have $?int;?int;!bool;end$.

For such straight line type, we can define the duality as:
* $dual(?t) = !t$
* $dual(!t) = ?t$
* $dual(t₁;t₂) = dual(t₁); dual(t₂)$
* $dual(end) = end$

Then $(P: t₁) | (Q: t₂)$ is well typed if $t₁ = dual(t₂)$.

__Remark.__
It is easy to see that the $dual$ relation is also its inverse: $dual(dual(t)) = t$.


### Internal/External Choice Duality

Straight line code is not that common and branching/choice is needed.
To properly deal with choice, we will need to make the distinction between internal and external choice.

__Example: badly structured choice__
First, let us look at an example of badly structured communication.

$
\begin{array}{lcl}
P & ≝ & !42.end + ?result.end \\\\
Q & ≝ & ?result.end + !42.end
\end{array}
$

While this could execute correctly in a synchronous system, it could lead to deadlock in an asynchronous system.
Even in an synchronous system, this example is tricky as the choice in $P$ and $Q$ is coupled.

__Internal and external choice.__
Ideally, we want that each choice can be tracked to a single process (internal choice) while the other process learn about it (external choice).
Internal choice is implicitly linked to sending messages and external choice to receiving messages:
* internal choice is denoted as $l₁.P₁ ⊕ l₂.P₂$ where $l₁$ and $l₂$ are _labels_.
* external choice is denoted as $l₁.P₁ \\& l₂.P₂$ where $l₁$ and $l₂$ are labels.

The labels indicates which branch has been selected and the two processes synchronize on that label.
Here we present the choice as binary but it is straightforward to generalize to n-ary ($⊕_i l_i.P_i$ and $\\&_i l_i.P_i$).
Furthermore, we assume that all the labels in a choice are different.
We use internal/external choice both in the processes and as part of the types.

The choice rules are now
\\[{}\over{l₁.P₁ ⊕ l₂.P₂ ~|~ l₁.Q₁ \\& l₂.Q₂  ~~ → ~~ P₁~|~Q₁}\\]
\\[{}\over{l₁.P₁ ⊕ l₂.P₂ ~|~ l₁.Q₁ \\& l₂.Q₂  ~~ → ~~ P₂~|~Q₂}\\]
\\[{}\over{l₁.P₁ \\& l₂.P₂ ~|~ l₁.Q₁ ⊕ l₂.Q₂  ~~ → ~~ P₁~|~Q₁}\\]
\\[{}\over{l₁.P₁ \\& l₂.P₂ ~|~ l₁.Q₁ ⊕ l₂.Q₂  ~~ → ~~ P₂~|~Q₂}\\]

Our duality relations get extended with:
* $dual(l₁.t₁ ⊕ l₂.t₂) = l₁.dual(t₁) \\& l₂.dual(t₂)$
* $dual(l₁.t₁ \\& l₂.t₂) = l₁.dual(t₁) ⊕ l₂.dual(t₂)$

__Example.__

$
\begin{array}{lcl}
P & ≝ & add.!1.!2.?res.end ~⊕~ geq.!1.!2.?comparison.end \\\\
Q & ≝ & add.?a.?b.!(a + b).end ~\\&~ geq.?a.?b.!(a ≥ b).end
\end{array}
$

where
* $P$ has type $add;!int;!int;?int;end ~⊕~ geq;!int;!int;?bool;end$ and
* $Q$ has type $add;?int;?int;!int;end ~\\&~ geq;?int;?int;!bool;end$.


### Recursion

As with the other constructs, we can add type identifiers with mutually recursive definitions.

__Example.__

$
\begin{array}{lcl}
P: t₁ & ≝ & !1.!2.?res.P \\\\
Q: t₂ & ≝ & ?a.?b.!(a + b).Q
\end{array}
$

with the types:
* $t₁ ≝ ~ !int;!int;?int;t₁$
* $t₂ ≝ ~ ?int;?int;!int;t₂$

Computing the dual of a type is still easy:
* $dual(ID ≝ t) = ``dual(ID)" ≝ dual(t)$
* $dual(ID) = `dual(ID)" $

For each identifier, we introduce a dual identifier and then proceed to take the dual of the body.
In the definition above we use $``dual(ID)"$ as placeholder for the dual identifier.

But computing type equality it is more tricky as it is required to compute equality up to renaming of definitions.
Unification is needed.

Also type inference is harder.
In the scope of this lecture we avoid type inference and relies on type annotations.


__Remark.__
Most publications uses the least fixed point notation ($μX.P$) which only create simple recursion rather than definition which are more flexible and creates mutually recursive definitions.


### Typing and Processes

The types directly reflect the processes and there is a direct syntactic match between them.
In the simple version, this is what the typing rules do.

We omit the typing rules for literals ($1:int$, $``foo":string$, …) and focus on the rule for communication.

A _typing environment_ $Γ$ is a map from names and definitions to types.
The _initial environment_ $Γ$ maps the definitions identifiers to their type.
This is needed to deal with recursion.
For instance, if there is a definition $A: t ≝ P$ then $Γ$ contains $(A, t)$.

\\[{
  Γ ⊢ P: t
}\over{
Γ ⊢ A: t ≝ P
}\\]

\\[{
Γ(id) = t
}\over{
Γ ⊢ id: t
}\\]

where $id$ is the identifier of either a definition or a name bound when receiving a message.

\\[{}\over{
Γ ⊢ end: end
}\\]

\\[{
  Γ ⊢ P: t
}\over{
Γ ⊢ (τ.P): t
}\\]

\\[{
    Γ ⊢ P: t₁  \qquad  Γ ⊢ Q: t₂
}\over{
Γ ⊢ (l₁.P ⊕ l₂.Q): (l₁;t₁ ⊕ l₂;t₂)
}\\]

\\[{
    Γ ⊢ P: t₁  \qquad  Γ ⊢ Q: t₂
}\over{
Γ ⊢ (l₁.P \\& l₂.Q): (l₁;t₁ \\& l₂;t₂)
}\\]

\\[{
Γ + (a,t) ⊢ P: t'
}\over{
 Γ ⊢ ?a.P: ~ ?t;t'
}\\]

\\[{
Γ ⊢ a: t  \qquad  Γ ⊢ P: t'
}\over{
  Γ ⊢ !a.P: ~ !t;t'
}\\]

Here we give very simple rules.
There can be many extensions that will allow to type more programs, e.g., commutativity of choice.


Then the composition $P:t₁ ~|~ Q:t₂$ is well typed iff $t₁=dual(t₂)$.
Since we work with binary session types, this works **only** for two processes.
The only tricky part is to deal with recursion and guessing which identifiers are dual.
The simplest would be to used an [unification algorithm](https://en.wikipedia.org/wiki/Unification_(computer_science)).

Here is a rules that ties everything together:
\\[{
∀i,j.~ i≠j ⇒ A_i ≠ A_j \qquad
Γ = \bigcup_i (A_i, t_i) \qquad
∀ i.~ Γ ⊢ A_i: t_i ≝ P_i \qquad
Γ(P) = dual(Γ(Q))
}\over{
P | Q ~~ \text{with} ~~ \bigcup_i A_i: t_i ≝ P_i
}\\]


### Subtyping

Until now, the types and processes precisely mirror each other.
However, we can extend the typing with a subtype relations.
We write $t₁$ being a subtype of $t₂$ as $t₁ <: t₂$.

We assume that we are given a subtype relation for the primitive (message payload) types.
For instance, $int <: real$.

Here is how the subtype relation works for send and receive:

\\[{
 t₁ <: t₂
}\over{
!t₁ <: !t₂
}\\]

\\[{
 t₂ <: t₁
}\over{
?t₁ <: ?t₂
}\\]


For the subtyping of choice it is simpler to work with the n-ary version of the operators:

\\[{
1 ≤ n ≤ m \qquad
∃ f~ \text{injective function from} ~ [1;n] ~\text{to} ~ [1;m].~ ∀ i ∈ [1;n].~ l_i = l_{f(i)}' ∧ t_i <: t_{f(i)}'
}\over{
⊕_{i ∈ [1;n]} l_i;t_i ~ <: ~ ⊕_{j ∈ [1;m]} l'_j;t'_j
}\\]

\\[{
1 ≤ m ≤ n \qquad
∃ f~ \text{injective function from} ~ [1;m] ~\text{to} ~ [1;n].~ ∀ i ∈ [1;m].~ l_i = l_{f(i)}' ∧ t_i <: t_{f(i)}'
}\over{
\\&\_{i ∈ [1;n]} l_i;t_i ~ <: ~ \\&\_{j ∈ [1;m]} l_j';t_j'
}\\]

Intuitively, subtypes can do fewer internal choices and allow more external choices.


### Progress and Preservation 

Progress and Preservation is proven by induction on the syntax of the processes and types.
Here we give a sketch of how to prove it.

Given well-typed $(P: t₁) ~|~ (Q: t₂)$ with $t₁ = dual(t₂)$ we need to case split on the structure of the processes.
* Case $P:t₁$ is $?a.P': ~ ?t;t'$:
  - by assumption $Q$ has type $dual(?t;t') = !t;dual(t')$
  - therefore, $Q$ is of the form $!b.Q'$ with $b:t$ and $Q':dual(t')$
  - $?a.P' ~|~ !b.Q'$ can make a communication step and we get $(P':t') ~|~ (Q[b/a]:dual(t'))$
  - finally, we apply to induction hypothesis to get that progress also holds for $(P':t') ~|~ (Q[b/a]:dual(t'))$
* Case ...


### FIFO Communication

We have seen the case of synchronous interaction.
This is based on the work of Kohei Honda: [Types for Dyadic Interaction](http://citeseer.ist.psu.edu/viewdoc/summary?doi=10.1.1.45.1355), 1993.
Similar results also hold when FIFO communication is used.
The earliest work I found is by Matthias Neubauer and Peter Thiemann: [Session Types for Asynchronous Communication](http://www2.informatik.uni-freiburg.de/~thiemann/papers/stac.ps.gz), 2004.
Even though this work is cited very often, this is an unpublished manuscript.
Regarding published results, there is the work on [linear type theory for asynchronous session types](https://doi.org/10.1017/S0956796809990268) by Simon J. Gay and Vasco T. Vasconcelos, 2009.
The setting and results are more general (and also more complicated).


### What we did not cover

* more than 2 participants
* higher-order types, scope restriction, and mobility
* process creation and parallel composition in general
* ...
