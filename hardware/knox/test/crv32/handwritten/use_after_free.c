void use(int *x) {

}

int *f(int *y) {
    int x = 7;
    use(&x);
    // dummy use of argument, so it's saved on stack, to match stack layout of g
    if (*y == 0) {
        return 0;
    }
    return &x;
}

// this will have the same stack layout/position as f
//
// if we don't catch use-after-free bugs, this program will run fine and return 7
int g(int *x) {
    int y = 44;
    use(&y); // make it store it to the stack
    return *x;
}

int main() {
    int y = 394;
    int *x = f(&y);
    // note: can't `return g(x)` because it's tail-call-optimized
    int r = g(x);
    return r + 10001; // prevent tail call optimization
}
