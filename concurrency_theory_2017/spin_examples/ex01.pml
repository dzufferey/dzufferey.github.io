byte b = 0;
init{
    do
    :: b < 128 -> b = b + 1
    :: else -> break
    od
}
