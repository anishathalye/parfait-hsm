#include <stdint.h>

int add_acc(int, int);

int x = 12;
uint32_t v = 17;
uint32_t *vptr = &v;
const int magic = 1337;

int8_t blank[16];

int16_t foo[] = {1, 3, 3, 7};

int main() {
    add_acc(1, 2);
    return add_acc(1, 2);
}

int add_acc(int a, int b) {
    (*vptr)++;
    blank[x++]++;
    return a + b + v + foo[1] + blank[13];
}

