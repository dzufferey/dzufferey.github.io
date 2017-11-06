#define N 10
#define FREE 255

byte fork[N] = FREE;

active [N] proctype philosopher() {
    do
    :: // get left fork
       atomic {
           fork[_pid] == FREE;
           fork[_pid] = _pid;
       };
       // get right fork
       atomic {
           fork[(_pid+1)%N] == FREE;
           fork[(_pid+1)%N] = _pid;
       };
       // eat
       // put back forks
       fork[_pid] = FREE;
       fork[(_pid+1)%N] = FREE
    od;
}

