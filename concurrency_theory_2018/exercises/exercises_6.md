# Homework 6

_Instructions_
* Due *before* December 4 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).

## Event-Driven Asynchronous Programs

Let us look some class of event-driven asynchronous programs.
Intuitively, these are programs that can _post_ tasks that will be executed in the future.
These programs are called _asynchronous_ as posting a task returns immediately and does not wait for the result of the task.
Here we assume that the tasks are simple functions (no recursive call, only post) and multiple tasks can execute concurrently.

Here is an example of an asynchronous programs:
```
global bit = 0;

h1() {
    if (bit == 0) {
        post h1();
        post h2();
    }
}

h2() {
    bit = 1;
}

Initially:
    h1();
```

__Syntax.__

We model asynchronous program by a tuple $(\mathcal{D}, \mathcal{T}, d₀, t₀)$ where
* $\mathcal{D}$ is a finite set of data values for the global state
* $\mathcal{T}$ is a finite set of tasks where each tasks is a finite state machine of the form $(id, S, \mathcal{D} × (ID ∪ \mathcal{D}), →, s₀)$ with
  - $id$ is an unique identifier for each type of task ($ID$ is the set of all the identifiers)
  - $S$ is a finite set of state
  - $\mathcal{D} × (ID ∪ \mathcal{D})$ is the alphabet
  - $→ ~ ⊆ ~ S × \mathcal{D} × (ID ∪ \mathcal{D}) × S$ is the transition relation
  - $s₀$ is the initial state
* $d₀ ∈ \mathcal{D}$ is the initial data value
* $t₀ ∈ ID$ is the initial task

The state of a system is a pair $(d,T)$ where:
* $d ∈ \mathcal{D}$ is the value of the shared variables
* $T ∈ (ID × S → ℕ)$ is a multiset of task ids and the local state of the corresponding task

__Semantics.__

_Notation._
We use the following notation:
* $→_i$ for the transition relation corresponding to the task with id $i$;
* $\mathcal{T}[i].s₀$ stands for the initial state of the task corresponding to id $i$.


The initial state of an asynchronous program is $(\mathcal{D}, \mathcal{T}, d₀, t₀)$ is $(d₀,\\{t₀, \mathcal{T}[t₀].s₀\\})$. 


The transitions follows the rules:
- memory access:
  \\[{
    (i,s₁) ∈ T₁ \qquad s₁ \stackrel{(d₁,d₂)}{→_i} s₂ \qquad T₂ = (T₁ ∖ \\{(i,s₁)\\}) ∪ \\{(i,s₂)\\}
  } \over {
    (d₁,T₁) → (d₂,T₂)
  }\\]
- post:
  \\[{
    (i,s₁) ∈ T₁ \qquad s₁ \stackrel{(d₁,t)}{→_i} s₂ \qquad T₂ = (T₁ ∖ \\{(i,s₁)\\}) ∪ \\{(i,s₂), (t,\mathcal{T}[t].s₀)\\}
  } \over {
    (d,T₁) → (d,T₂)
  } \\]


__Task.__

Show that asynchronous programs are WSTS.


## Comparing Models of Communicating State Machines

In this exercise, we only consider reliable channels.

__A Labelled semantics.__
In class we have seen a semantics for communicating state machines (CSM) that only look at states at the global level.
We can generalize the rules to carry over the labels of the local transition to labels of the global transitions.

At the global level, the labels are of the form $(ID, (ID × ! × Σ) ∪ (? × Σ))$ where the first element of the pair is the id of the machine making a transition and the second part is the label of the local transition of the machine.

The rules in [lecture notes 6](viewer.html?md=concurrency_theory_2018/notes_6.md) are extending following the pattern:
\\[{
M[i] \stackrel{x}{→_i} s   \qquad   …
} \over{
(M, C) \stackrel{(i,x)}{→} …
}
\\]


__Comparing CSM by traces.__
In this exercise, we will compare CSM by keeping the same CSM but execuing them under different channel semantics.
We are interested in executions traces (sequences of labels) the CSM can do starting from the initial state of all the machines and empty channels.

### Unordered Channels (Bags)

For channels as bags, we did not make the distinction between point-to-point (p2p) communication and mailbox.
Let us look at this in more details.

__Task 1.__
Give the transition rules that corresponds to point-to-point communication with bags.
(The lecture notes only have the mailbox version.)

__Task 2.__
Compare the two models:
* bag+p2p → bag+mailbox:
  - either give an example of CSM having traces with bag+p2p that are not possible with bag+mailbox
  - or show that for any CMS every bag+p2p trace is also a bag+mailbox trace
* bag+mailbox → bag+p2p:
  - either give an example of CSM having traces with bag+mailbox that are not possible with bag+p2p
  - or show that for any CSM every bag+mailbox trace is also a bag+trace trace

### FIFO Mailbox with Lookahead

For this part, we are looking at a common extension of FIFO channels and mailbox semantics: lookahead.
Intuitively, when a machine does not have transitions defined for the message at the head of its message queue it is allowed to skip messages until there is a message for which a transition is defined.

We acheive this by modifying the receive rule and keeping the same send rule.
The new receive rule is:
\\[{
M[i] \stackrel{?a}{→_i} s   \qquad   C[i] = w·a·w'   \qquad  C' = C[i ←  w·w']  \qquad  M' = M[i ← s]  \\qquad ∀ a' ∈ w.\ s' ∈ S_i.\ (M[i], ?a', s') ∉ →_i 
} \over{
                        (M, C) → (M', C')
}
\\]

__Task 3.__

Compare FIFO with mailbox with and without lookahead:
* FIFO+mailbox → FIFO+mailbox+lookahead
  - either give an example of CSM having traces with FIFO+mailbox that are not possible with FIFO+mailbox+lookahead
  - or show that for any CMS every FIFO+mailbox trace is also a FIFO+mailbox+lookahead trace
* FIFO+mailbox+lookahead → FIFO+mailbox
  - either give an example of CSM having traces with FIFO+mailbox+lookahead that are not possible with FIFO+mailbox
  - or show that for any CMS every FIFO+mailbox+lookahead trace is also a FIFO+mailbox trace

__Task 4.__

Compare FIFO with mailbox and lookahead against the bag semantics:
* FIFO+mailbox+lookahead → FIFO+bag
  - either give an example of CSM having traces with FIFO+mailbox+lookahead that are not possible with FIFO+bag
  - or show that for any CMS every FIFO+mailbox+lookahead trace is also a FIFO+bag trace
* FIFO+bag → FIFO+mailbox+lookahead
  - either give an example of CSM having traces with FIFO+bag that are not possible with FIFO+mailbox+lookahead
  - or show that for any CMS every FIFO+bag trace is also a FIFO+mailbox+lookahead trace


