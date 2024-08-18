// this program branches on a symbolic, and in one branch, calls a function
// (but doesn't do so in the other branch); because the CompCert semantics
// don't garbage collect stack frames from the memory representation, the shape
// of the memory in the two branches will be different, which complicates
// merging

void f(void);

int main(int a0, int a1) {
    if (a0 || a1) {
        return 1;
    }
    f();
    return 2;
}

void f(void) {
    return;
}
