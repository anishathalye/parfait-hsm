#include <stdint.h>

// misc stuff to help with instruction coverage

#define assert(b) do { if (!(b)) return 1; } while (0)

// See compcert.backend.SelectDiv.divu_mul / divu_mul_params
uint32_t emit_mulhu(uint32_t x) {
    return x / 3ul;
}

uint32_t emit_ori(uint32_t x) {
    return x | 0xff;
}

int emit_sub(int a, int b) {
    return a - b;
}

char data[] = {'a', 'b', 'c', 'd'};
int16_t data2[8];

int f() {
    return data[0];
}

int emit_xor(int a, int b) {
    return a ^ b;
}

int main() {
    assert(emit_mulhu(13ul) == 4ul);
    assert(emit_ori(0x30000) == 0x300ff);
    assert(emit_sub(3, 15) == -12);
    assert(data[1] == 'b');
    data2[4] = -1;
    f(); // prevent next line from being optimized out
    assert(((uint16_t *) data2)[4] == 0xffff);
    assert(emit_xor(0xf83, 0xf41) == 0x0c2);
    return 0;
}
