//version using shared memory to encode the lock

//status of the lock
mtype = { locked, unlocked }
mtype lock_status = unlocked

//macro to (un)lock
//notice that we have to check the status and set the new status atomically! (it is funny the we require atomic operation to implent a lock)
inline lock() {
    atomic{
        lock_status == unlocked;
        lock_status = locked
    }
}
inline unlock() {
    atomic{
        lock_status == locked;
        lock_status = unlocked
    }
}

int balance = 0
int critical = 0

active [6] proctype incr() {
  lock()
  critical = critical + 1
  assert(critical == 1) //check only one process in the critical section
  balance = balance + 1
  critical = critical - 1
  unlock()
}
