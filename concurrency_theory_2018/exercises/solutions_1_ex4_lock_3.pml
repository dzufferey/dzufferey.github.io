//fixes lock_2 by keeping track of the running incr processes and terminates the lock when there are no more incr

mtype = { lock, unlock }
chan event = [0] of { mtype }

int running = 6;

active proctype L() {
    bool locked = false;
    do
    :: event?lock
       event?unlock
    :: running == 0
       break
    od
}

int balance = 0
int critical = 0

active [6] proctype incr() {
  event!lock
  critical = critical + 1
  assert(critical == 1)
  balance = balance + 1
  critical = critical - 1
  event!unlock
  running = running - 1
}
