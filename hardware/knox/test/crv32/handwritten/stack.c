int mul2_slow(int n);

int main() {
    return mul2_slow(999);
}

int mul2_slow(int n) {
    if (n == 1) {
        return 2;
    }
    // deliberately set up so it's not tail recursive
    return 2 + mul2_slow(n-1);
}
