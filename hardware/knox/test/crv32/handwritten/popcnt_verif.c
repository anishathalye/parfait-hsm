int popcnt_ref(unsigned x) {
    int count = 0;
    // purposefully set up so we're not branching on a symbolic variable
    for (int i = 0; i < 32; i++) {
        count += x & 1;
        x = x >> 1;
    }
    return count;
}

int popcnt_opt(unsigned x) {
    x = (x & 0x55555555) + ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x & 0x0F0F0F0F) + ((x >> 4) & 0x0F0F0F0F);
    x = (x & 0x00FF00FF) + ((x >> 8) & 0x00FF00FF);
    x = (x & 0x0000FFFF) + ((x >>16) & 0x0000FFFF);
    return x;
}

int verify(unsigned x) {
    return popcnt_ref(x) == popcnt_opt(x);
}

// in main, we manually test this on a couple cases
//
// when we want to verify, we'll call verify directly
int main() {
    int ok = 1;
    ok &= verify(0);
    ok &= verify(1);
    ok &= verify(8);
    ok &= verify(1337);
    ok &= verify(28934);
    ok &= verify(99999999);
    ok &= verify(847347374);
    return !ok; // return 0 on success
}
