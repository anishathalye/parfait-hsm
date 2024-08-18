int src[5] = {42, 38, 8473843, 3999399, 111};
int dst[5];

#define NELEM(arr) (sizeof(arr) / sizeof(*arr))

int main() {
    int *sptr = src;
    int *dptr = dst;
    int *end = src + NELEM(src);
    while (sptr != end) {
        *(dptr++) = *(sptr++);
    }
    int sum = 0;
    for (int i = 0; i < NELEM(dst); i++) {
        sum += dst[i];
    }
    return sum;
}
