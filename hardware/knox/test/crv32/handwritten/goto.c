int x = 1;

int main() {
    x++;
    if (x) {
        goto skip;
    }
    x++;
skip:
    x++;
    return x;
}
