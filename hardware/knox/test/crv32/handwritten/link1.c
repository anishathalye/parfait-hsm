static int x = 3;
int y = 4;

int f2(int);
static int f(int);
extern int w;

int f1(int z) {
    return f(1) + f(w) + x + f2(y) + z;
}

static int f(int x) {
    return x;
}
