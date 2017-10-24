/* Peterson's algorithm */

bool flag0;
bool flag1;
bool turn;
byte mutex;

active proctype P0() {
    do
    ::  flag0=true; 
        turn=0;
        !flag1 || (turn == 1);
        mutex++;
        /* critical section */ 
        assert(mutex == 1);
        mutex--;
        flag0=false;
    od;
}


active proctype P1() {
    do
    ::  flag1=true; 
        turn=1;
        !flag0 || (turn == 0);
        mutex++;
        /* critical section */ 
        assert(mutex == 1);
        mutex--;
        flag1=false;
    od;
}
