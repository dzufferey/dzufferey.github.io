# Homework 9

_Instructions_
* Due *before* January 15 (you can send them until Monday night).
* Send your solution by email to Simin Oraee.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* For the proofs, please try to be precise. When possible, try to copy the style in the lecture notes: sequences of facts and how you derived them.
* You can submit your solution in pdf or text format and any other source file.
  If you have more than one file place all your files in a single archive (zip or tar.gz).

## Weak Bisimulation

In the [lecture notes 9](viewer.html?md=concurrency_theory_2018/notes_9.md) we introduced strong and weak bisimulations.
Using the techniques we have seen in class to show that
\\[
(ν c) (?a.!c.0 | ?b.!c.0 | ?c.?c.P)  ~ ≈ ~ ?a.?b.P + ?b.?a.P   \qquad \text{assuming} ~ c ∉ fn(P)
\\]

## From ν-free Process Algebra to Petri Net

In the [lecture notes 10](viewer.html?md=concurrency_theory_2018/notes_10.md) we show that the ν-free π-calculus is a WSTS.
The proof that the ordering is a WQO hints at a possible reduction to Petri net.
We are going to explore this further in this exercise.

__Task 1.__
Give a reduction from the ν-free π-calculus to Petri net that preserve the covering problem, i.e., a $(ν \vec a) ∏_i A_i(\vec a_i)$ is coverable iff a marking in the corresponding Petri net is coverable.

__Task 2.__
In class, we showed that the ν-free broadcast calculus is also a WSTS.
Give a reduction from the ν-free broadcast calculus to monotonic extension of Petri nets (reset or transfer net).
Your reduction must preserve the covering problem.

## Making a Model from Code

Consider the following example of an Erlang program (simplified from https://www.it.uu.se/edu/course/homepage/distsys/vt11/lab/lab.pdf).

```erlang
server(State) ->
    receive
        {request,Return_PID} ->
            io:format("SERVER ~w: Client request received from ~w~n", [self(), Return_PID]),
            NewState = State + 1,
            Return_PID ! {hit_count,NewState},
            server(NewState)
    end.

client(Server_Address) ->
    Server_Address ! {request, self()},
    receive
        {hit_count,Number} ->
            io:format("CLIENT ~w: Hit count was ~w~n",[self(), Number])
    end.

main() ->
    Server_PID = spawn(server,[0]),
    spawn(client,[Server_PID])
```

A possible output of such program is
```
SERVER <0.27.0>: Client request received from <0.29.0>
CLIENT <0.29.0>: Hit count was 1
```
where `0.27.0` and `0.29.0` are the respective addresses of the server and client.

Erlang implements the actor model which is a type of message passing concurrency.

Actors execute concurrently, have their own unordered mailbox, and send messages to each other. We have:
- `spawn` creates a new actor and returns the address of the actor.
- `!` send a message
- `receive` receive messages and match them against a pattern.
- Erlang implement FIFO mailboxes but the actor model does not require message ordering (bags are good enough).

**Task.**
From the models for message-passing concurrency that we have seen which is the most suitable to encode this example?
Encode this example in the model of your choice and explain what parts of the code is accurately captured by your model and which parts you had to leave out.

