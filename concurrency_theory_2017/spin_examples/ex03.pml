byte b = 0;
init{
    do
    :: b < 128 ->
       b = b + 1;
       printf("%d\n", b)
    od
}
