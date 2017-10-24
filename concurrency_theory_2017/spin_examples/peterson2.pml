bool flag[2];
bool turn;
byte mutex;

active [2] proctype P()
{
    do
    ::  flag[_pid] = true;
        turn = _pid;
        !flag[1-_pid] || turn == 1-_pid;
        mutex++;
        /* critical section */ 
        assert(mutex == 1);
        mutex--;
        flag[_pid] = false
    od;
}
