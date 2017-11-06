/* runspinsafe: %spin -a        %gcc -o pan -DSAFETY pan.c %./pan -m100000000   % */

#define N 2
// declaration and initial values of global variables
bool entering[N] = false;
short number[N] = 0;
byte ncrit = 0;

active [N] proctype client()
{
    do
    ::  entering[_pid] = true;
        byte i = 0;
        short max = number[_pid];
        do
        :: i < N ->
            max = (number[i] > max -> number[i] : max);
            i = i + 1;
        :: i >= N ->
            i = 0;
            break;
        od;
        number[_pid] = 1 + max;
        entering[_pid] = false;
        do
        :: i < N ->
            if
            :: !entering[i] && (number[i] == 0 || number[i] > number[_pid] || (number[i] == number[_pid] && i >= _pid)) -> skip;
            fi;
            i = i + 1;
        :: i >= N ->
            i = 0;
            break;
        od;
        ncrit = ncrit + 1;
        //critical section
        assert(ncrit <= 1)
        ncrit = ncrit -1;
        number[_pid] = 0;
    od;
}

