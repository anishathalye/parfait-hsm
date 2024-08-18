void f(int *x) {
    *x = *x + 1;
}
int main() {
    int x = 3;
    f(&x);
    return x + 10;
}
