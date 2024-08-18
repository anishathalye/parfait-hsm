#include <stdint.h>

uint32_t x = 0xffff3375ul;
uint32_t d1 = 2ul;
uint32_t d2 = 48583ul;
uint32_t d3 = 0xffff0000ul;

int32_t y = 76;
int32_t d4 = 67;
int32_t d5 = 3;
int32_t d6 = -6;
int32_t d7 = 2;

int32_t z = -332;
int32_t d8 = 65;

#define check_equal(a, b) if ((a) != (b)) return 1;

int main() {
    // we need variables for d1 d2 etc., because if we inline the numbers,
    // the compiler can substitute multiplication for division
    check_equal(x / d1, 2147457466ul);
    check_equal(x / d2, 88403ul);
    check_equal(x % d1, 1ul);
    check_equal(x % d3, 0x3375ul);

    check_equal(y / d4, 1);
    check_equal(y / d5, 25);
    check_equal(y / d6, -12);
    check_equal(y % d7, 0);
    check_equal(y % d5, 1);
    check_equal(y % d6, 4);

    check_equal(z / d8, -5);
    check_equal(z % d8, -7);
    check_equal(z / d6, 55);
    check_equal(z % d6, -2);
}
