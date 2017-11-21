# Homework 5

_Instructions_
* Due on November 29.
* Send your solution by email to Ivan Gavran.
* You can work in groups up to 3 people, be sure to include the names of all the participants.
* You can submit your solution in pdf, markdown, or text format.


## Coin game (How large can finite Petri net get?)

Consider the following game:

### State

The game is played with 6 buckets numbered from 1 to 6.
At the start, each bucket contains a single coin.

Visually:
```
 │1│ │1│ │1│ │1│ │1│ │1│
 └─┘ └─┘ └─┘ └─┘ └─┘ └─┘
  1   2   3   4   5   6
```
The number below the bucket is the bucket ID and the number inside is the number of coins.


### Actions

There are 2 kinds of actions:
1. take 1 coin from bucket `i` and put 2 coins in bucket `i+1` (`i ∈ [1;5]`)
2. for `i<j<k` take 1 coin from bucket `i` and swap the content buckets `j` and `k`


Visually:
```
 │1│ │1│ │1│ │1│ │1│ │1│
 └─┘ └─┘ └─┘ └─┘ └─┘ └─┘
  1   2   3   4   5   6

   ↓  action 1 on bucket 3

 │1│ │1│ │0│ │3│ │1│ │1│
 └─┘ └─┘ └─┘ └─┘ └─┘ └─┘
  1   2   3   4   5   6
```


```
 │1│ │1│ │0│ │3│ │1│ │1│
 └─┘ └─┘ └─┘ └─┘ └─┘ └─┘
  1   2   3   4   5   6

   ↓  action 2 on bucket 1, 3, and 4

 │0│ │1│ │3│ │0│ │1│ │1│
 └─┘ └─┘ └─┘ └─┘ └─┘ └─┘
  1   2   3   4   5   6
```

### Goal

The goal is to maximise the total number of coins by playing any number of actions.


### Questions

- show that lexicographic ordering on words of length 6 where each letter is in ℕ is a WQO.
- use this to show that the game terminate (hint: what type of sequence in this ordering is a trace of the game)
- let `≼` be the lexicographic ordering on ℕ⁶ and `≤` by the componentwise ordering (tuple ordering). Show that `≤` is compatible with the game but `≼` is not.
- show that the game can be encoded as a Petri net with a number of places polynomial in the number of buckets (hint: instead of swapping the content of the buckets you can swap their names)

We can generalize the game to work with `N` buckets.

- [Optional and fun] Let's try to get rich. Assume each coin is worth 1 standard monetary unit (SMU) and that the richest human has a fortune `< 2⁴⁰` SMU.
  * Can you get richer than by playing the game once with 6 buckets?
  * Can you do better? What is the minimal `N` that will make you the richest person?
- [Optional and mind-blowing] What is the maximum number of coins as a function of `N` ?


### Some more examples

Let us look at the version with 2 buckets.
Each line is the state of the game after a move.
```
1 1
0 3
```

Let us look at the version with 3 buckets:
```
1 1 1
1 0 3
0 3 0
0 2 2
0 1 4
0 0 6
```

Let us look at the version with 4 buckets:
```
1 1 1   1
1 1 0   3
1 0 3   0
...
1 0 0   6
0 6 0   0
0 5 2   0
0 5 1   2
0 5 0   4
0 4 4   0
...
0 4 0   8
...
0 3 0  16
...
0 2 0  32
...
0 1 0  64
...
0 0 0 128
```
