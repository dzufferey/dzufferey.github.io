#define N 4
byte flag[N];
byte turn[N];
byte mutex;

// Basically we try to stage N-1 round of Peterson's protocol to revolve all the conflicts
// a good explanation in https://cs.nyu.edu/wies/teaching/ppc-14/material/lecture02.pdf

inline lock() {
    byte i = 1 //start with at stage 1, 0 means not interested
    do
    ::  i < N ->
        flag[_pid] = i; // wants to enter the i-th stage
        turn[i] = _pid; // gives the priority to not _pid
        byte j = 0;
        do
        :: j < N ->
            turn[i] != _pid || // given priority by someone else
            j == _pid || // skip self
            flag[j] < i; // process j not in stage i or higher
            j = j + 1
        :: j == N ->
            break // nobody at a same or higher stage
        od;
        i = i + 1; // go to the next stage
    ::  else ->
        break
    od
}

inline unlock() {
    flag[_pid] = 0 // not interested in any stage
}

active [N] proctype P()
{
    do
    ::  lock();
        mutex++;
        /* critical section */ 
        assert(mutex == 1);
        mutex--;
        unlock()
    od;
}
