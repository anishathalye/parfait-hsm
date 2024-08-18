#include "sha256.h"

int main(unsigned char *msg, size_t len, unsigned char *out, int count) {
    // loop for benchmarking purposes
    for (int i = 0; i < count; i++) {
        SHA256_CTX ctx;
        sha256_init(&ctx);
        sha256_update(&ctx, msg, len);
        sha256_final(&ctx, out);
    }
    return 0;
}

void *memset(void *b, int c, size_t len) {
    unsigned char *d = b;
    unsigned char v = c;
    for (size_t i = 0; i < len; i++) {
        d[i] = v;
    }
    return b;
}
