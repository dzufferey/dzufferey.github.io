# Concurrency theory motivation

## What it is:

The class is about studying mathematical models for concurrent systems and trying to find "good" models.

> "All models are wrong, but some are useful."

The main focus of the class when looking at models is to answer the question: Can we reason algorithmically about the model?
In particular, we study the decidability of reachability questions: Given a system, can the system reach a particular state?

This question is fundamental as many other questions can be reduced to reachability.
For instance, can a program deadlock is a reachability question.

In the exploration of models, we will look at trade-off between expressive power of models and tractability of analysis.
In this process, we will discover some interesting mathematical bits.

## What it isn't:

Concurrency theory is obviously linked to concurrent programming but this class is _not about programming_.

Concurrency theory and concurrent programming influence each other but evolve concurrently.
For instance:
* Weak memory models came due to choice in processor architecture that predate multi-core CPU and became an important research question much later.
* The communication model of the GO programming language is inspired from work on process algebra, in particular CSP.



## Example of topics covered

### Proving properties of infinite state systems

__Example.__ parametric lock-and-increment

Consider the following program in pseudo-code
```c
ℕ balance;

void increase() {
    lock();
    balance += 1;
    unlock();
}

void main() {
    assume(N >= 0);
    threads[N];
    for (i in [1;N])
        thread_create(threads[i], increase);
    for (i in [1;N])
        thread_join(threads[i]);
    assert(balance == N);
}
```

We will give algorithm that can show this program works for any value of `N`.


### Building (decidable) models to explain concurrent programs

__Example.__ weak memory models

```c
#include <pthread.h>
#include <stdio.h>

int x = 0;
int y = 0;

void *thread1(void* args)
{
    x = 1;
    printf("y: %d\n", y);
}

void *thread2(void* args)
{
    y = 1;
    printf("x: %d\n", x);
}

void main() {
    pthread_t threads[2];
    pthread_create(&threads[0], NULL, thread1, NULL);
    pthread_create(&threads[1], NULL, thread2, NULL);
    void* retval;
    pthread_join(threads[0], &retval);
    pthread_join(threads[1], &retval);
}
```

On multicore CPU, the program *can* result in:
```
x: 0
y: 0
```

We will discuss why this can happen and how to check for such behavior.


### Some nice bit of mathematics

__Example.__ Application of ordering theory

* Reachability communicating state machines with unbounded FIFO channels is undecidable.
* If we make the channel lossy the problem becomes decidable.

This result will use Higman's lemma: "The embedding relation over finite sequences of well-quasi-ordered elements is a well-quasi-order."

Don't worry about the obscure terminology, it will come clear during the class. :)

## Other information

* _Vague exercise questions._
  At times exercises may looks underspecified.
  These exercises do not have a single solution as there may be multiple approaches to solve them.
  Don't worry though.
  Our goal is not to setup traps to make you fail but to develop a different skill set.
  Often questioning the task itself is a crucial part in finding a solution.
* _Oral exam._
  An oral exam require you to both solve some problem and explain you solution.
  Being able to clearly explain yourself is a very valuable skill but, unfortunately, not trained enough in CS.
  The exam will have the following form:
  * Questions: You will pick three questions at random from a pool and keep two.
  * Preparation: You will have half an hour to think about the question and prepare. You will have access to the course material during that time.
  * Examination: The examination will last half an hour in which you will discuss the question and we will ask further questions/clarifications.
