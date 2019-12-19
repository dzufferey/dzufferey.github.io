# Bonus Homework 1

_Instructions_
* Due on Jan 6, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


## Effective Predecessor Basis for LCS

To apply the backward algorithm for WSTS on LCS we need a procedure to compute the predecessor basis of an upward-closed set of states.

### Tasks
* Give a procedure to compute the predecessor basis for LCS
* Apply your algorithm to the following LCS
    ```graphviz
    digraph finite_state_machine {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        init -> X;
        X -> Y [ label = "?a, ?b" ];
        Y -> X [ label = "?a" ];
        Y -> Z [ label = "?b" ];
        X -> X [ label = "!0" ];
        Y -> Y [ label = "!1" ];
    }
    ```
    ```graphviz
    digraph finite_state_machine {
        rankdir=LR;
        node [shape = circle];
        init [shape = none, label = ""];
        init -> A;
        A -> B [ label = "!a" ];
        B -> C [ label = "!a" ];
        C -> D [ label = "!b" ];
        B -> B [ label = "?0, ?1" ];
        D -> D [ label = "?0, ?1" ];
    }
    ```
    where we try to cover the control state `Z` in the 1st machine.
* Prove that your procedure is correct


## Open and Closed World with Finite State Machines

When we discussed CCS (week 8), we looked at the difference between a closed-world and an open-world modelling assumption.
Process algebras are the first model we discussed that could accommodate both (with the help of the $ν$ operator).

Most models we discussed are operating under a closed-world assumption.
Let us revisit finite-state machines and try to define a product operation and a new restriction operation which can simulate the open and closed world (CCS-like semantics).
We look at the labelled semantics of CCS and the labels correspond to letters in the alphabet of the automaton.

Let us assume that the alphabet $Σ$ of the automaton always contains a special letter $τ$ which corresponds to the silent action in CCS.

### Tasks
* Modify the synchronized product of automatons to mimic the parallel and communication rules of CCS.
* Define a new restriction operation for an automata.
  The operation takes as argument an automaton $M$ and a letter $a$ in $Σ$ the alphabet of $M$.
  The operation returns an automaton $M'$ over the alphabet $Σ ∖ \\{!a, ?a\\}$.
  $M'$ accepts exactly the words accepted by $M$ containing neither $!a$ nor $?a$.


## Modeling the Occam with CCS

[Occam](https://en.wikipedia.org/wiki/Occam_(programming_language)) is a programming language which was originally designed for the _transputer_, a family of processors designed in the 1980s for parallel computing.

Occam has the following constructs:
* input (`?`) and output (`!`) over rendezvous channels
* `SEQ` for expressions which are evaluated sequentially
* `PAR` for expressions which are evaluated in parallel
* `ALT` for an alternative of guarded commands (guards can be a combination of boolean and input expressions

Here is an example occam program which merges two streams (up to 100 elements per stream)
```occam
WHILE TRUE
    ALT
       count1 < 100 & c1 ? data
         PAR
           count1 := count1 + 1
           merged ! data
       count2 < 100 & c2 ? data
         PAR
           count2 := count2 + 1
           merged ! data
       status ? request
         SEQ
           out ! count1
           out ! count2
```

For this exercise, assuming that:
- channel names in occam program are global and identified by their name.
- CCS is extended with
  + integers (operations $+$,$-$,$>$,$≥$) and boolean (operations $∧$,$∨$,$¬$) expressions
  + guarded choice $[G]P + [G]P$ where $G$ is a boolean expression and $P$ a CCS process
  + it is possible to send values with messages. The actions are

    $
    \begin{array}{rcll}
       π & ::= & !a(e)           & \text{(send)}   \\\\
         &   | & ?a(v)  \qquad   & \text{(receive)}  \\\\
         &   | & τ               & \text{(silent)}
    \end{array}
    $

    where $e$ is an expression and $v$ a variable.
    Let us assume that names and variables have different identifiers to avoid any confusion.
    Variable names can be used as parameters in definitions.

### Tasks
First, let us try to give a formalization for the new elements of the calculus.
* Modify the rules for communication to allow sending and receiving data values.
* Modify the choice rule for guarded choice.
  The "normal" choice is a special case of guarded choice where all the guards are true.
* Encode the program above in this extended CCS

-----

description and code modified from https://en.wikipedia.org/wiki/Occam_(programming_language) under CC-BY-SA license
