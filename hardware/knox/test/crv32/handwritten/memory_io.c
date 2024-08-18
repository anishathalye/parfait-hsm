#include <stdint.h>

void dot(int *a, int *b, size_t len, int *res) {
    int sum = 0;
    for (int i = 0; i < len; i++) {
        sum += a[i] * b[i];
    }
    *res = sum;
}
