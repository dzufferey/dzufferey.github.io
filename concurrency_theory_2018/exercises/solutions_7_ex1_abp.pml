// constants to vary
#define channelSize 5
#define maxMsgValue 4
#define nbrMsg 3

// to check the transmission is fine
byte sent[nbrMsg];
byte received[nbrMsg];

//
chan a2b = [channelSize] of { byte };
chan b2a = [channelSize] of { byte };

//to check the bit in the messages
#define set_bit(msg, bt) (bt -> (msg | 128) : msg)
#define check_bit(msg, bt) (bt -> (msg & 128) != 0 : (msg & 128) == 0)

active proctype sender() {
    byte i = 0;
    byte msg = 0;
    do
    :: i < nbrMsg ->
        //generate new message
        atomic {
            do
            :: sent[i] < maxMsgValue -> sent[i] = sent[i] + 1
            :: break
            od
        }
        a2b!set_bit(sent[i], i % 2);
        do
        :: b2a?msg ->
            atomic {
                printf("sender: i = %d, msg = %d\n", i, msg);
                if
                :: msg == i % 2 -> // good to go
                    printf("ack ok\n");
                    msg = 0;
                    break
                :: else -> //wrong ack
                    printf("wrong ack\n");
                    msg = 0;
                    //a2b!set_bit(sent[i], i % 2); ignore, the outer loop will resend
                fi
            }
        :: nfull(a2b) -> //model timeout by non-determinism, resend the message as long as there is space in the channel
            a2b!set_bit(sent[i], i % 2);
        od;
        i = i + 1
    :: else ->
        break
    od
}

active proctype receiver() {
    byte i = 0;
    byte msg = 0;
    do
    :: i < nbrMsg ->
        do
        :: a2b?msg ->
            atomic{
                printf("receiver: i = %d, msg = %d\n", i, msg);
                if
                :: check_bit(msg, i % 2) -> // good to go
                    b2a!(i % 2);
                      received[i] = msg & 127;
                      msg = 0;
                      i = i + 1;
                    break
                :: else -> //wrong message, resend previous ack
                    b2a!((i-1) % 2)
                fi
            };
        od
    :: else ->
        break
    od;
    atomic {
        i = 0;
        do
        :: i < nbrMsg ->
            assert(sent[i] == received[i]);
            i = i + 1
        :: else ->
            break
    od;
    }
}
