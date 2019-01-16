//a not quite correct version using a dedicated processes to model the lock
//spin complaints that there is an error as L gets stuck when all the incr processes are done

//the message type
mtype = { lock, unlock }
chan event = [0] of { mtype } //unbuffered mtype events 

active proctype L() {
    bool locked = false;
    do
    :: event?lock  //receive an event
       event?unlock
    od
}

int balance = 0
int critical = 0

active [6] proctype incr() {
  event!lock //send an event
  critical = critical + 1
  assert(critical == 1) //check only one process in the critical section
  balance = balance + 1
  critical = critical - 1
  event!unlock
}
