#include <stdint.h>

uint64_t a = 0x8758a8495b472343;
uint64_t b = 0x0037f8375e83cd3f;

int popcnt(uint64_t x) {
    int c = 0;
    while (x > 0) {
        c += x & 1;
        x = x >> 1;
    }
    return c;
}

int main() {
    // use all the builtins: addl, subl, negl, mull
    uint64_t res = (a * (-b)) - b + a;
    return popcnt(res);
}
