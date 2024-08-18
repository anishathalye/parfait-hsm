#include <stdint.h>

uint64_t a = 0x8758a8495b472343;
uint64_t b = 0x0037f8375e83cd3f;

int main() {
    uint64_t res = a + b;
    int r = (res >> 35);
    return r;
}
