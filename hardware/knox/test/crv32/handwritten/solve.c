// inspired by 6.858 lab 3 exercise 1

// can we solve for the x that returns 1234 ?
int f(int x) {
    if (x == 7)
        return 100;
    if (x*2 == x+1)
        return 70;
    if (x > 2000)
        return 80;
    if (x*2 == 1000)
        return 30000;
    if (x < 500)
        return 33;
    if (x / 123 == 7)
        return 1234;
    return 40;
}
