# The Spin Model-Checker

You can download spin at: http://spinroot.com/

To run spin, we recommend using the following script: https://github.com/tcruys/runspin

## Promela

You can find more explanation in the [manual](http://spinroot.com/spin/Man/Manual.html) or even [Wikipedia](https://en.wikipedia.org/wiki/Promela).

The input language for Spin is _Promela_ (Process/Protocol Meta Language).

_Primitive Types:_
* `bool`
* `byte` (unsigned: 0 to 255)
* `short` (16-bits signed integer)
* `int` (32-bits signed integer)

It is possible to have arrays.
`bool ready[2] = false;` is an array of size 2 containing boolean values that are initialized to false.

_Statements:_
* assignments: `x = 1;`
* test: `x == 1;` (also `!=`, `<`, `>`, `<=`, `>=`)
* `(condition -> valueTrue : valueFalse)`
* if-blocks
    ```
    if
    :: condition_1 -> body_1
    :: condition_2 -> body_2
    ...
    :: condition_n -> body_n
    :: else -> ...
    fi;
    ```
    If multiple alternatives are enabled, spin will explore all of them.
    `else` is optional.
    `else` is enabled only if no other condition is enabled.
* do-loops
    ```
    do
    :: condition_1 -> body_1
    :: condition_2 -> body_2
    ...
    :: condition_n -> body_n
    :: else -> ...
    od;
    ```
    Like `if` in a `while(true)`.
    The `break` statement is the only way to exit a loop.
* assertions: `assert(condition);`
* atomic blocs:
    ```
    atomic {
        ...
    }
    ```
    executes all the statement in the block as a single step (no interleaving).
* `printf` as in C.
* `skip` doesn't do anything.

`;` and `->` are separators.
In particular, `;` is not needed after the last statement.

Tests are normal statement that executes only when they are true and block otherwise.
`x != 0` simulates `while (x == 0) {}`.

Each statement executes atomically;

_Processes:_
* processes
  ```
  proctype name(args){
      ...
  }
  ```
  Processes are started with `run name(values)`.

  Alternatively it is possible to mark processes as active:
  ```
  active [2] proctype client(){
      ...
  }
  ```
  `[2]` is an optional parameter that starts 2 processes.

  The `_pid` variable is a special integer variable which as unique for each process.
* `init { ... }` block is like the `main` in C but without arguments.
  If there are active processes, `init` is not needed.
  
* if there are multiple active processes, Spin builds a product automaton and traverses it using a specified strategy (BFS or DFS)

## Examples

You can find examples of spin programs [here](https://github.com/dzufferey/dzufferey.github.io/tree/master/concurrency_theory_2017/spin_examples).

Here are the particularity of the examples
* `ex01.pml`: simple while loop. Notice that the number of states explored by Spin is propotional to the sizes of the data.
* `ex02.pml`: same as 1 but without a way of exiting the loop. Spin report a deadlock as the program get stuck.
* `ex03.pml`: same as 2 but with printing. It is possible to replay the error trace with `spin -t ex03.pml`.
* `ex04.pml`: infinite loop. Even though the loop is infinite, the analysis terminates because it has a finite number of states.
* `ex05.pml`: if statement
* `ex06.pml`: unsafe if statement. All the enabled branches are explored, not only the first one.
* `ex07.pml`: more data, more states
* `ex08.pml`: even more data and even more states. To explore all the state, we need to increase the depth of the search (`-mN` option).
* `peterson.pml`: an encoding of [Peterson's mutual exclusion protocol](https://en.wikipedia.org/wiki/Peterson%27s_algorithm) in Spin
* `peterson2.pml`: also Peterson's protocol but a more compact version which uses more advanced features

