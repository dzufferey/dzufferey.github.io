# counting transitions
var spawn     integer, >= 0;
var if_true   integer, >= 0;
var if_false  integer, >= 0;
var lock_1    integer, >= 0;
var crit_1    integer, >= 0;
var unlock_1  integer, >= 0;
var lock_2    integer, >= 0;
var crit_2    integer, >= 0;
var unlock_2  integer, >= 0;
# tokens in the final marking
var u_1   integer, >= 0;
var l_1   integer, >= 0;
var u_2   integer, >= 0;
var l_2   integer, >= 0;
var pc0   integer, >= 0; #before if
var pc1_1 integer, >= 0; #before lock
var pc1_2 integer, >= 0;
var pc2_1 integer, >= 0; #entering critical section
var pc2_2 integer, >= 0;
var pc3_1 integer, >= 0; #before unlock
var pc3_2 integer, >= 0;
var pc4   integer, >= 0; #done
# transitions
# s.t. t??: XXX   + spawn + if_true + if_false + lock_1 + crit_1 + unlock_1 + lock_2 + crit_2 + unlock_2 = 0;
s.t. t00: u_1                                + lock_1          - unlock_1                              = 1;
s.t. t01: l_1                                - lock_1          + unlock_1                              = 0;
s.t. t02: u_2                                                             + lock_2          - unlock_2 = 1;
s.t. t03: l_2                                                             - lock_2          + unlock_2 = 0;
s.t. t04: pc0   - spawn + if_true + if_false                                                           = 1;
s.t. t05: pc1_1         - if_true            + lock_1                                                  = 0;
s.t. t06: pc2_1                              - lock_1 + crit_1                                         = 0;
s.t. t07: pc3_1                                       - crit_1 + unlock_1                              = 0;
s.t. t08: pc1_2                   - if_false                              + lock_2                     = 0;
s.t. t09: pc2_2                                                           - lock_2 + crit_2            = 0;
s.t. t10: pc3_2                                                                    - crit_2 + unlock_2 = 0;
s.t. t11: pc4                                                  - unlock_1                   - unlock_2 = 0;
# property
# s.t. prop: pc2_1 + pc3_1 >= 2;
# s.t. prop: pc2_2 + pc3_2 >= 2;
# s.t. prop: pc2_1 + pc3_1 + pc2_2 + pc3_2 >= 2;
s.t. prop: pc2_1 + pc3_1 + pc2_2 + pc3_2 >= 3;
solve;
display spawn, if_true, if_false, lock_1, lock_2, crit_1, crit_2, unlock_1, unlock_2;
display u_1, l_1, u_2, l_2, pc0, pc1_1, pc2_1, pc3_1, pc1_2, pc2_2, pc3_2, pc4;
end;
