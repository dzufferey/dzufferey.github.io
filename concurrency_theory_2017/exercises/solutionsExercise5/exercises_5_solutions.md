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
The ordering is reflexive (`x≼x`). It is also transitive: assume `x≼y, y≼z`.
  - if `x = y`: `y ≼ z` implies `x ≼ z`
  - if `x < y`: there is `i≤6` such that `x_i < y_i` and `∀j < i: x_j=y_j`. Then `x_j≼z_j` and `x_i≼z_i`. Therefore, `x≼z`
From that we can infer that `≼` is a well-quasi-ordering: it is a quasiorder, it is well founded (the same way natural numbers are well-founded) and it is total (hence, there is for sure no infinite antichain). Now using the lemma from the exercise 4 we get it is a well-quasi-ordering.
- use this to show that the game terminate (hint: what type of sequence in this ordering is a trace of the game)
Any trace of the game is a strictly decreasing sequence (the next element's most significant bits are either equal or 1 smaller)
- let `≼` be the lexicographic ordering on ℕ⁶ and `≤` be the componentwise ordering (tuple ordering). Show that `≤` is compatible with the game but `≼` is not.
Consider `x = (1,1,2,3,4,5)` and `y = (1,1,3,1,4,5)`. Let the applied transition be the second move on positions 1, 3 and 4. This results in successors `x' = (0,1,3,2,4,5)` and `y' = (0,1,1,3,4,5)`. While `x≼y` it is not the case that `x'≼y'`. Therefore, `≼` is not compatible with the game. For the componentwise ordering, let's assume `x≤y` and consider both possible actions
  - action one on position `i`: `x_i' = x_i - 1`, `x_(i+1)' = x_(i+1)'+2 `, `y_i' = y_i - 1`, `y_(i+1)' = y_(i+1)'+2 `. From there we can see that `x_j' < y_j', j = 1,...,6` (the values are either unchanged, or increased/decreased by the same amount)
  - action two on positions `i, j, k`: `x_i' = x_i-1, x_j' = x_k, x_k'=x_j` and `y_i' = y_i-1, y_j' = y_k, y_k'=y_j`. Again, the values are either unchanged, decreased by the same number or keeping the same value but chaning positions (which doesn't influence componentwise ordering)

  In both case we can conclude `x'≤y'`

- show that the game can be encoded as a Petri net with a number of places polynomial in the number of buckets (hint: instead of swapping the content of the buckets you can swap their names)
<br />
We can encode the game as a Petri net with `n^2+n` places. Namely, let `S = S_roles ∪ S_values`. Further, `S_values = {pos(i): i ≤ n}` and `S_roles = {pos(i)role(j): i, j ≤ n}`. The idea is that `S_values` stores the number of coins in each bucket. (if there are 7 coins in bucket 2, we want that place `pos(2)` contains 7 tokens). However, to support the move number two (exchanging the coins between two buckets) we are using positions from `S_roles`: they say which `pos(i)` plays the role of which bucket. So, for example, if `pos(1)role(2)` contains a token, then `pos(1)` should be treated as bucket number 2. Therefore, we have to  change the description of `S_values`: namely, if there are 7 coins in bucket 2, we want that place `k` that plays the role of bucket 2 (determined by `pos(k)role(2)` containing a token) contains 7 tokens.<br />The transitions are defined as `T = T_move1 ∪ T_move2`. `T_move1 = {t[1, i, p(i), p(i+1)]: i, p(i), p(i+1) ≤ n, p(i) ≠ p(i+1) }`. Transition `t[1, i, p(i), p(i+1)]` denotes first move applied to bucket `i` given that `p(i)` plays the role of `i` and `p(i+1)` plays the role of `i+1`. The weights are defined as follows `W(pos(p(i)), t[1, i, p(i), p(i+1)]) = W(pos(i)role(p(i)), t[1, i, p(i), p(i+1)]) = W(pos(i+1)role(p(i+1)), t[1, i, p(i), p(i+1)]) = W(t[1, i, p(i), p(i+1)], pos(i+1)role(p(i+1))) = W(t[1, i, p(i), p(i+1)], pos(i)role(p(i))) = 1` and `W(t[1, i, p(i), p(i+1)], pos(p(i+1))) = 2`. The transitions corresponding to move 2 are defined as `T_move2 = { t[2,i,j,k,p(i), p(j), p(k)]: i,j,k,p(i), p(j), p(k) ≤ n, i < j < k, p(i) ≠ p(j) ≠ p(k)}`. The weights are defined as `W(pos(i)role(p(i)), t[2,i,j,k,p(i), p(j), p(k)]) = W(pos(j)role(p(j)), t[2,i,j,k,p(i), p(j), p(k)]) = W(pos(k)role(p(k)), t[2,i,j,k,p(i), p(j), p(k)]) = W(pos(p(i)), t[2,i,j,k,p(i), p(j), p(k)]) = W(t[2,i,j,k,p(i), p(j), p(k)], pos(j)role(p(k))) = W(t[2,i,j,k,p(i), p(j), p(k)], pos(k)role(p(k))) = 1`

We can generalize the game to work with `N` buckets.

- [Optional and fun] Let's try to get rich. Assume each coin is worth 1 standard monetary unit (SMU) and that the richest human has a fortune `< 2⁴⁰` SMU.
  * Can you get richer than by playing the game once with 6 buckets?
  * Can you do better? What is the minimal `N` that will make you the richest person?

 We will need few helper sequences: `(a,0,0) → (a-1, 2, 0)→*(a-1,0,4)→(a-2,4,0)→*(0,2^a, 0)=(0,2↑a,0)`. What happens if we consider four buckets? `(a,0,0,0)→(a-1,2,0,0)→*(a-1,0,2^2,0)→(a-2,2^2,0,0)→*(a-2, 0, 2^2^2,0)→(a-3, 2^2^2,0)→*(0, 2↑↑a,0,0)`.  Now, starting from `(1,1,1,1,1,1)` we get `(1,1,1,1,1,1)→*(1,1,0,0,0,128)→(1,0,128,0,0,0)→*(1,0,0,2↑↑128,0,0)` and the number of tokens is already greater than `2^40`. It is clear that one can do it already with 5 tokens.
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
