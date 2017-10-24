/* runspin_dfs: %spin -a        %gcc -o pan -DSAFETY pan.c %./pan -m100000000 -w25      % */
/* runspin_bfs: %spin -a        %gcc -o pan -DSAFETY -DBFS pan.c %./pan -m10000000 -w25      % */
short b0;
byte b1;
init{
    do
    :: b0 = b0 + 1
    :: b1 = b1 + 1
    od
}
