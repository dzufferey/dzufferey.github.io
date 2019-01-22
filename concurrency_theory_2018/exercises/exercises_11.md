# Homework 11

_Instructions_
* Due *before* January 29 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).


__About the Exam.__
We are trying to group the exams during the following two weeks: (1) Feb 25 - Mar 1 and (2) Mar 25 - Mar 29.
If you have not already done so, please send the week you would like to participate in the exam to Damien.
If these dates are not possible for you let us know and we will try to find a solution.



## Peterson's Algorithm and TSO semantics

When presenting the Spin in the first week, we saw Peterson's algorithm to implement a critical section.
We were able to show the algorithm correct.
However, Spin memory model is sequential consistency (instantaneous read and write).

Let us investigate what happens if we try to run Peterson's algorithm under TSO.
Here are 4 versions of the algorithm in pseudo code.
The first version is the original version and the others have been modified by reordering some instructions and/or adding a memory fence.

* Version 1:
    ```c
    bool turn;
    bool flag[2] = {0, 0};

    void peterson(bool id /* 0 or 1 */) {
        flag[id] = 1;
        turn = 1-id;
        while (turn != id && flag[1-id]) { }
        // entering critical section
        ...
        // exiting critical section
        flag[id] = 0;
    }

    spawn(peterson(0));
    spawn(peterson(1));
    ```
* Version 2:
    ```c
    bool turn;
    bool flag[2] = {0, 0};

    void peterson(bool id /* 0 or 1 */) {
        flag[id] = 1;
        fence();
        turn = 1-id;
        while (turn != id && flag[1-id]) { }
        // entering critical section
        ...
        // exiting critical section
        flag[id] = 0;
    }

    spawn(peterson(0));
    spawn(peterson(1));
    ```
* Version 3:
    ```c
    bool turn;
    bool flag[2] = {0, 0};

    void peterson(bool id /* 0 or 1 */) {
        turn = 1-id;
        fence();
        flag[id] = 1;
        while (turn != id && flag[1-id]) { }
        // entering critical section
        ...
        // exiting critical section
        flag[id] = 0;
    }

    spawn(peterson(0));
    spawn(peterson(1));
    ```
* Version 4:
    ```c
    bool turn;
    bool flag[2] = {0, 0};

    void peterson(bool id /* 0 or 1 */) {
        flag[id] = 1;
        turn = 1-id;
        fence();
        while (turn != id && flag[1-id]) { }
        // entering critical section
        ...
        // exiting critical section
        flag[id] = 0;
    }

    spawn(peterson(0));
    spawn(peterson(1));
    ```

__Question.__
For each version of the algorithm, is algorithm is correct? (at most on process in the critical section)
If no, give an execution that violates mutual exclusion. Include the state of the memory and buffers in your execution.
If yes, show that the algorithm is correct. Consider the sequences of read/write/fence that could lead to an error and show these cannot happen.


## On the Generality of our TSO Formalization

To make our formalization of TSO easier, we assumed that
1. all the processes are described by the same NFA (execute the same program)
2. the memory starts will every addresses having a default value.

In this exercise, we will show that these are not really restrictions.

As usual, we are looking at the control state reachability problem and throughout this exercise, any transformation of the program(s) must preserve control state reachability.
You are allowed to modify $\mathbb{A}$ and $\mathbb{D}$.

__Task 1.__

Assume that we want to model a system where every process executes a different program: $∏_{p∈\mathbb{P}} (Q_p, \Sigma_p, δ_p, q_{0p})$.

Give a construction that encode the multiple programs into a single one to so it fits our formalization ($∏_{p∈\mathbb{P}} (Q, \Sigma, δ, q_{0})$).

__Task 2.__

We want to model the case where the memory, instead of the default value, has a specific configuration $m_{init}: \mathbb{A} → \mathbb{D}$.

Given a program $(Q, \Sigma, δ, q_0)$ and a memory configuration $m_{init}$, construct a new program that results in the same control-state being reached but starts with the default memory configuration.

