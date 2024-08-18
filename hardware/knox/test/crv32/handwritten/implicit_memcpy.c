#include <stdint.h>

struct uint128_t {
    uint64_t low;
    uint64_t high;
};

struct uint128_t add(struct uint128_t x, struct uint128_t y);

int main() {
    struct uint128_t x = {
        .low = 3,
        .high = 4,
    };
    // compiler uses memcpy intrinsic for the following:
    struct uint128_t y = x;
    y.low = 4;
    struct uint128_t sum = add(x, y);
    return sum.high;
}

struct uint128_t add(struct uint128_t x, struct uint128_t y) {
    struct uint128_t res;
    res.low = x.low + y.low;
    res.high = x.high + y.high;
    if (res.low < x.low) {
        res.high += 1;
    }
    return res;
}
