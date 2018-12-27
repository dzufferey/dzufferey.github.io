# Analysis of π-calculus Processes

CCS and the π-calculus are Turing-complete models.
Therefore, we can only hope to analyze a subset of the calculus.

## $ν$-free π-calculus

The $ν$-free π-calculus prevents the use of the restriction operator ($ν$) in the body of the definitions and the process defining the initial state of the system must be closed.
Intuitively, this means that it is not possible to _create_ new names and the number of names in the system is bounded by the number of names in the initial process.
This fragment of the π-calculus is not Turing-complete and we can show that it is a WSTS.

__Normal form and ordering for the processes.__
Without loss of generality, we assume the processes can be rewritten ($≡$) to have the following form: 
$(ν \vec a) ∏_i A_i(\vec a_i)$
with $\vec a_i ⊆ \vec a$ for all $i$.

Once the initial configuration of the system is known we can fix $\vec a$ and use it to describe all the system's configuration.

We can compare the configuration as follows:
* more processes makes larger configurations: $(ν \vec a) ∏_i A_i(\vec a_i) ≤ (ν \vec a) \left(∏_i A_i(\vec a_i) ~|~ ∏_j A_j(\vec a_j) \right)$
* closing $≤$ under $≡$: $P ≡ P' ∧ Q ≡ Q' ∧ P' ≤ Q' ⇒ P ≤ Q$

This ordering is a WQO as:
* __QO__:
  - _reflexive_: with $∏_j A_j(\vec a_j)$ empty in the ordering definition
  - _transitive_: this roughly corresponds to building a derivation of the form $P ≤ P | Q ≤ P | Q | R$
* __Well__:
  We can show that the ordering contains a WQO.
  We associate an index to unique named process $A_i(\vec a_i)$ and we associate to a configuration a tuple of ℕ where we count how many named process there are for a given index.
  Tuples of natural numbers with point-wise ordering is a WQO.

  _Example._
  For the definitions

  $
  \begin{array}{rcl}
      ping(x,y) & ≝ & !x.pong(y,x) \\\\
      pong(x,y) & ≝ & ?x.ping(y,x)
  \end{array}
  $

  and initial process $(ν a b) (ping(a, b) | pong(a, b))$.
  We have the following unique name processes:
  1. $ping(a,a)$,
  2. $ping(a,b)$,
  3. $ping(b,a)$,
  4. $ping(b,b)$,
  5. $pong(a,a)$,
  6. $pong(a,b)$,
  7. $pong(b,a)$, and
  8. $pong(b,b)$.

  The configuration $(ν a b) (ping(a, b) | pong(a, b))$ corresponds to the tuple $(0 ~ 1 ~ 0 ~ 0 ~ 0 ~ 1 ~ 0 ~ 0)$.

__Monotonicity.__
As we assume the system is closed, we can use the closed world semantics covered in [notes 9](viewer.html?md=concurrency_theory_2018/notes_9.md).
For the ordering, we need to look at the two part of the definition:

_Case 1:_ $(ν \vec a) ∏_i A_i(\vec a_i) ≤ (ν \vec a) \left(∏_i A_i(\vec a_i) ~|~ ∏_j A_j(\vec a_j) \right)$

For the sake of simplicity we can write this as $(ν \vec a) P ≤ (ν \vec a) (P | Q)$ and the smaller process taking a step is $(ν \vec a) P → (ν \vec a) P'$.

From $(ν \vec a) P → (ν \vec a) P'$, we can deduce that $P → P'$ as the restriction rule is the only one that can be applied.

Then, using the parallel and restriction rules, we can build the following derivation:
\\[{
    {
      P  →  P'
    }\over{
      P|Q  →  P'|Q
    }
}\over{
(ν \vec a) (P|Q) → (ν \vec a) (P'|Q)
}\\]

Furthermore, we have $(ν \vec a) P' ≤ (ν \vec a) (P'|Q)$ by definition of $≤$.

_Case 2: $P ≡ P' ∧ Q ≡ Q' ∧ P' ≤ Q' ⇒ P ≤ Q$

This correspond to an induction proof where the previous case is the base case that gets instantiated over $P' ≤ Q'$ and the proof is completed using the congruence rule:
\\[{
  P ≡ P' \qquad P' → Q' \qquad Q' ≡ Q
}\over{
  P → Q
}\\]


## More Examples of π-calculus Fragments with Decidable Properties:

* [On the Decidability of Fragments of the Asynchronous Pi-Calculus](https://core.ac.uk/download/pdf/52472189.pdf) by Roberto M. Amadio and Charles Meyssonnier, 2002.
* [On Boundedness in Depth in the π-Calculus](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.672.5898) by Roland Meyer, 2008.


# Variations and Extensions of the π-calculus

Over the years, many variations of the π-calculus, aimed at simplifying the modeling of particular systems has been developed.
Here we list a few and describe one of them in more details.

* The [Spi-calculus](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.63.2305) which add cryptographic primitive like public-key cryptography in order to model security protocols.
* The [stochastic π-calculus](https://academic.oup.com/comjnl/article/38/7/578/400773) adds rates to the transition and has been used to model biological systems.
  It semantics is given as a continuous time Markov chain.
* The [ambient calculus](http://lucacardelli.name/Papers/MobileAmbients.A4.pdf) adds ambient which models the "physical" location where the computation happens.

## Broadcast π-calculus

The broadcast π-calculus models broadcast communication, i.e., when messages is broadcast and all the processes that can receive the message do so.
The syntax is the same as the π-calculus, only the semantics is different.

We will need the notion of that we can _observe_ $α$ in a process $P$ if $?α(\vec b).A$ occurs unguarded in $P$ for some $A$ and some $\vec b$.
It is written $P↓_α$.
It is a variation of the commitments we discussed in [week 9](notes_9.md).

__Semantics.__
* Silent action
  \\[{
  }\over{
    τ.P  \stackrel{τ}{→}  P
  }\\]
* Send action
  \\[{
  }\over{
    !a(\vec b).P  \stackrel{!a(\vec b)}{→}  P
  }\\]
* Receive action
  \\[{
    \\{\vec c\\} ∩ bn(P) = ∅
  }\over{
    ?a(\vec b).P  \stackrel{?a(\vec c)}{→}  P[c/b]
  }\\]
* Receive skip
  \\[{
     ¬P↓_a
  }\over{
    P \stackrel{?a(\vec b)}{→} P
  }\\]
* Parallel internal
  \\[{
    P  \stackrel{τ}{→}  P'
  }\over{
    P|Q  \stackrel{τ}{→}  P'|Q
  }\\]
* Parallel send
  \\[{
    P  \stackrel{!a(\vec b)}{→}  P' \qquad
    Q  \stackrel{?a(\vec b)}{→}  Q'
  }\over{
    P|Q  \stackrel{!a(\vec b)}{→}  P'|Q'
  }\\]
* Parallel receive
  \\[{
    P  \stackrel{?a(\vec b)}{→}  P' \qquad
    Q  \stackrel{?a(\vec b)}{→}  Q'
  }\over{
    P|Q  \stackrel{?a(\vec b)}{→}  P'|Q'
  }\\]
* Choice internal
  \\[{
    P  \stackrel{τ}{→}  P'
  }\over{
    P+Q  \stackrel{τ}{→}  P'
  }\\]
* Choice send
  \\[{
    P  \stackrel{!a(\vec b)}{→}  P'
  }\over{
    P+Q  \stackrel{!a(\vec b)}{→}  P'
  }\\]
* Choice receive
  \\[{
    P  \stackrel{?a(\vec b)}{→}  P' \qquad P↓_a
  }\over{
    P+Q  \stackrel{?a(\vec b)}{→}  P'
  }\\]
* Choice skip
  \\[{
    ¬P↓_a \qquad ¬Q↓_a
  }\over{
    P+Q  \stackrel{?a(\vec b)}{→}  P+Q
  }\\]
* Restriction 1
  \\[{
    P  \stackrel{π}{→}  P' \qquad π ≠ !a(␣) \qquad π ≠ ?a(␣) \qquad π ≠ !␣(… a …) \qquad π ≠ ?␣(… a …)
  }\over{
    (νa)P  \stackrel{π}{→}  (νa)P'
  }\\]
* Restriction 2
  \\[{
    P  \stackrel{!a(\vec b)}{→}  P'
  }\over{
    (νa)P  \stackrel{τ}{→}  (νa)P'
  }\\]
* Congruence
  \\[{
    P ≡ P' \qquad P' \stackrel{π}{→} Q' \qquad Q' ≡ Q
  }\over{
    P \stackrel{π}{→} Q
  }\\]

__Example.__
Here is a simple publisher-subscriber model:

$
\begin{array}{lcl}
publisher(topic)  & ≝ & !topic.publisher(topic) \\\\
subscriber(topic) & ≝ & ?topic.processing(topic) \\\\
processing(topic) & ≝ & τ.subscriber(topic)
\end{array}
$

Let us look at one possible execution with the configuration $(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | subscriber(t₁) | subscriber(t₂) )$:
* initial: $(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | subscriber(t₁) | subscriber(t₂) )$
* $!t₁$: $(ν t₁ t₂)( publisher(t₁) | processing(t₁) | processing(t₁) | subscriber(t₂) )$
* $τ$ at subscriber: $(ν t₁ t₂)( publisher(t₁) | subscriber(t₁) | processing(t₁) | subscriber(t₂) )$
* $!t₁$: $(ν t₁ t₂)( publisher(t₁) | processing(t₁) | processing(t₁) | subscriber(t₂) )$
* ...

Notice that the first message is received by two subscribers while the second message is only received by one subscriber.

__Monotonicity of the Broadcast semantics.__
In this broadcast semantics, sending is non-blocking and only the processes that listen on the channel when a message is sent receive the message.
Intuitively, this means that it is also possible to define an WSTS for fragments of the broadcast calculus.


# Typing System for the π-calculus

When we look at processes, we have always assumed that names are used in a "correct" way, e.g., if two arguments are send in a message then the receiver expects two arguments.
However, we just assumed this and did not check it.
Orthogonal to the question of reachability/covering that are the focus of this lecture, there is an area of research dedicated to typing processes/channels to make sure the communication happens properly, e.g., messages have the right type, deadlock-freedom.
Here we will just scratch the surface of this topic.

## Typing Names

The first tentative to type the π-calculus is to give types to the names.
The type of name is the type of the names it carries when exchanging messages.

#### Types
Let $S$ by a set of sort identifier.
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

This make is possible to have different granularity when typing names.
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


## Typing Processes for Two Party Communication

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

### Model (version 1)

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

The model will be refined later.

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
⊕_{i ∈ [1;n]} l_i;t_i  <:  ⊕_{j ∈ [1;m]} l'_j;t'_j
}\\]

\\[{
1 ≤ m ≤ n \qquad
∃ f~ \text{injective function from} ~ [1;m] ~\text{to} ~ [1;n].~ ∀ i ∈ [1;m].~ l_i = l_{f(i)}' ∧ t_i <: t_{f(i)}'
}\over{
\\&_{i ∈ [1;n]} l_i;t_i  <:  \\&_{j ∈ [1;m]} l_j';t_j'
}\\]

Intuitively, subtypes can do fewer internal choices and allow more external choices.


### Properties of the Type System

The main properties of type system are:
* preservation: An evaluation step does not change the type
* progress: either the program has finished or it it possible to take a step

Progress and Preservation is proven by induction on the syntax of the processes and types.
Here we give a sketch of how to prove it.

Given well-typed $(P: t₁) ~|~ (Q: t₂)$ with $t₁ = dual(t₂)$ we need to case split on the structure of the processes.
* Case $P:t₁$ is $?a.P': ~ ?t;t'$:
  - by assumption $Q$ has type $dual(?t;t') = !t;dual(t')$
  - therefore, $Q$ is of the form $!b.Q'$ with $b:t$ and $Q':dual(t')$
  - $?a.P' ~|~ !b.Q'$ can make a communication step and we get $(P':t') ~|~ (Q[b/a]:dual(t'))$
  - finally, we apply to induction hypothesis to get that progress also holds for $(P':t') ~|~ (Q[b/a]:dual(t'))$
* Case ...

If we add some extra checks for the absence of loops with only τ steps, then progress also implies deadlock-freedom.


### What we did not cover

* more than 2 participants
* higher-order types, scope restriction, and mobility
* process creation and parallel composition in general
* ...
