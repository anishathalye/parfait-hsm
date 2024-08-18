static int x = 5;
int w = 6;

int f1(int);
static int f(int);

int f2(int z) {
    return x + w + z;
}

static int f(int x) {
    return x + 1;
}

// main(41) -> 79
int main(int z) {
    return f(f1(f2(f(z))));
}
