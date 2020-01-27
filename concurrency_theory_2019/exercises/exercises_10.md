# Homework 10

_Instructions_
* Please remember to fill the poll if you intend to take the exam: [https://terminplaner4.dfn.de/CT19-Exams](https://terminplaner4.dfn.de/CT19-Exams).
* Due on Feb 3, Monday, at 8am.
* Send your solution by email to Felix Stutz. Please prefix your email subject with `[CT19-SUB]`.
* We expect you to work in groups of 3 to 4 people, be sure to include the names of all the participants **and your group number** in the document.
* Please submit your solutions in one readable pdf file. Based on the experiences for the first exercise sheet, we require you to **typeset your solutions** as announced in the tutorial.
  We exclude automata, petri nets etc. from this requirement for now but please ensure that they are legible and scanned (no photos).
  For the exercises using Spin give the promela source file as well. Place all your files in a single archive (zip or tar.gz).


## |-free π-calculus

Similar to the $ν$-free π-calculus that we have seen in exercise 8, let us look at another fragment of the π-calculus.

The $|$-free π-calculus prevents the use of the parallel operator ($|$) in the body of the definitions.
Only the initial configuration can use $|$.

This means that the maximum number of processes is bounded by the number of processes in the initial configuration.

### Questions
* Can you solve the covering problem for the $|$-free π-calculus? Justify your answer. 


## On the Two Threads Reduction in Bulk Synchronization

When we discussed the analysis techniques for the bulk synchronous model, we used a reduction of an arbitrary number of threads to only two threads.
The reduction used the arguments that we are interested in a special class of properties which can be violated with only two threads.

On the other hand, we discussed the control-state reachability problem for communicating state machine or having a token in a specific place in a Petri net.
This property depended only on a single process or a fixed number of token.
Why did we not do a reduction to finite systems?

### Questions
* Do you think a single thread reduction is possible for the control-state reachability problem is LCS?
  Discuss what made the two threads reduction possible and, if possible, what would be the equivalent for the control-state reachability.
* Same question but for a fixed number of tokens and covering in Petri Nets.


## Model for Monitors (Synchronization Primitives)

In class, we discussed different ways for concurrent shared memory programs to synchronize threads.
Let us examine a new one: _monitor_ (also known as _condition variable_).
Here is a short description and code sample.

> In concurrent programming, a monitor is a synchronization construct that allows threads to have both mutual exclusion and the ability to wait (block) for a certain condition to become true.
> Monitors also have a mechanism for signaling other threads that their condition has been met.
> A monitor consists of a mutex (lock) object and condition variables.
> A condition variable is basically a container of threads that are waiting for a certain condition.
> Monitors provide a mechanism for threads to temporarily give up exclusive access in order to wait for some condition to be met, before regaining exclusive access and resuming their task.

```c
RingBuffer queue; // A thread-unsafe ring-buffer of tasks.
Lock queueLock;   // A mutex for the buffer of tasks.
CV queueFullOrEmptyCV; // A condition variable for when the queue is empty or full
                       // Its associated lock is "queueLock".

public method producer(){
    while(true){
        task myTask = ...; // Producer makes some new task to be added.
        queueLock.acquire();
        while(queue.isFull()){
            // atomically release queueLock, enqueue this thread onto the CV, and sleep this thread.
            wait(queueLock, queueFullOrEmptyCV);
            // "wait" automatically re-acquires "queueLock" when the thread awakes
        }
        queue.enqueue(myTask); // Critical section: add the task to the queue.
        notifyAll(queueFullOrEmptyCV); // the queue is non-empty, wake-up all blocked threads
        queueLock.release();
    }
}

public method consumer(){
    while(true){
        queueLock.acquire();
        while (queue.isEmpty()){
            // atomically release queueLock, enqueue this thread onto the CV, and sleep this thread.
            wait(queueLock, queueFullOrEmptyCV);
            // "wait" automatically re-acquires "queueLock" when the thread awakes
        }
        myTask=queue.dequeue(); //Critical Section take a task off of the queue.
        notifyAll(queueFullOrEmptyCV); // the queue is non-full, wait-up all blocked threads
        queueLock.release();
        doStuff(myTask);
    }
}
```

### Questions
* Among the models for concurrency we discussed in class.
  Which model would you use for the code above?
  Justify and show what the program in this model looks like.

-----

description and code modified from https://en.wikipedia.org/wiki/Monitor_(synchronization) under CC-BY-SA license
