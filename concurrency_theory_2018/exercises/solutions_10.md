# Solutions 10

## Binary Session Types for Definitions with Arguments

The first part is that we have need type annotations for the arguments: $A(a₁: t₁, a₂: t₂, …) ≝ P$.

Also the type of definition gets a bit more complicated.
It is like a function type: $(\vec t, t)$ where $\vec t$ are the types of the arguments and $t$ is the "return" type.

When we type check the body of a definition, we need to add all the arguments in the type environment:
\\[{
Γ + (a_1, t_1) + (a_2, t_2) + … ⊢ P: t
}\over{
Γ ⊢ A(a₁: t₁, a₂: t₂, …): t ≝ P
}\\]

Previously, we have one single rule for identifiers.
Now this rule is only for variables/arguments:
\\[{
Γ(id) = t
}\over{
Γ ⊢ id: t
}\\]

We need to introduce a rule for using a definition:
\\[{
Γ(A) = (\vec t, t) \qquad ∀ i.\ Γ ⊢ \vec a[i]: \vec t[i] 
}\over{
Γ ⊢ A(\vec a): t
}\\]

The remaining rules are the same.

The final change is how we build the initial type environment: $Γ$.
For each $A(a₁: t₁, a₂: t₂, …): t ≝ P$, we add $(A, ((t₁, t₂, …), t))$ to $Γ$.


## Limits of Binary Session Types

#### Type for ping-pong

Since, we just discusses typing arguments we can use that feature

$
\begin{array}{lcl}
    \text{Ping}(x: ping, y: pong): ~ !ping;?pong;\text{Ping} & ≝ & !x.?y.\text{Ping}(x,y) \\\\
    \text{Pong}(x: ping, y: pong): ~ ?pong;!ping;\text{Pong} & ≝ & ?x.!y.\text{Pong}(x,y)
\end{array}
$

and we get that $\text{Ping} = dual(\text{Pong})$.

#### Type for juggling

Unfortunately, it is not possible to type this example.
Our type system describes sequences of messages (and choice) but it cannot express independent events.

Except for internal actions, the type describe all the actions of a process.
Then it needs to be matched by the other process.

Since both processes send as their first action, the duality breaks.
This program works because the channels allow messages to cross while "in flight".

This is an example of a program that executes correctly (with buffer size $> 0$) but cannot be typed.



#### Type for for a system with unbounded channels

There are some simple example if we consider processes of the form: $A ≝ τ.A$ and another process sending.

But we can also have more reasonable example:

$
\begin{array}{rcl}
P & ≝ & l₁.P ⊕ l₂.end \\\\
Q & ≝ & l₁.Q ~\\&~ l₂.end
\end{array}
$

Where $P$ adnd $Q$ are their own respective types.

In this example $P$ sends some number of $l₁$ and then finishes by $l₂$.
In an execution, we can perform all the send operations ($P$'s transitions) first and then all the receive ($Q$'s transitions) later.
The buffer needs to be as large as the number of sends which is unbounded.
