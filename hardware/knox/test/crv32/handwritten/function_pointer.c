int f(int x) {
    return x * 2 + 1;
}

int g(int x) {
    return x * x + 6;
}

int (*fp)(int x);

void go(int x) {
    if (x == 0) {
        fp = g;
    } else {
        fp = f;
    }
}

int main() {
    go(0);
    int r = fp(7);
    return r + 1;
}
