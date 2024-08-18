#include <stdint.h>

// volatile to prevent constant folding
uint32_t u1, u2, u3;
int32_t s1, s2, s3;

#define assert_equal(a, b) do { if ((a) != (b)) return 1; } while (0)
#define check_op_unsigned_imm(a, op, b, expected) do { u1 = (a); g(); u3 = u1 op (b); assert_equal(u3, expected); } while (0)
#define check_op_unsigned_reg(a, op, b, expected) do { u1 = (a); u2 = (b); g(); u3 = u1 op u2; assert_equal(u3, expected); } while (0)
#define check_op_unsigned(a, op, b, expected) do { check_op_unsigned_imm(a, op, b, expected); check_op_unsigned_reg(a, op, b, expected); } while (0)
#define check_op_signed_imm(a, op, b, expected) do { s1 = (a); g(); s3 = s1 op (b); assert_equal(s3, expected); } while (0)
#define check_op_signed_reg(a, op, b, expected) do { s1 = (a); s2 = (b); g(); s3 = s1 op s2; assert_equal(s3, expected); } while (0)
#define check_op_signed(a, op, b, expected) do { check_op_signed_imm(a, op, b, expected); check_op_signed_reg(a, op, b, expected); } while (0)

// called after setting globals, to prevent constant folding
void g() {
    // nop
}

char buf[4];

int main() {
    // unsigned, left shift
    check_op_unsigned(4, <<, 3, 32);
    check_op_unsigned(4, <<, 31, 0);
    check_op_unsigned(4, <<, 0, 4);
    check_op_unsigned(1234, <<, 12, 5054464);
    check_op_unsigned(0x5739fad3, <<, 8, 0x39fad300);

    // signed, left shift, positive
    check_op_signed(4, <<, 3, 32);
    check_op_signed(4, <<, 31, 0);
    check_op_signed(4, <<, 0, 4);
    check_op_signed(1234, <<, 12, 5054464);
    check_op_signed(0x5739fad3, <<, 1, 0xae73f5a6); // shifting this left 8 bits would be UB

    // left shifting a negative number is UB

    // unsigned, right shift
    check_op_unsigned(174, >>, 3, 21);
    check_op_unsigned(12345, >>, 5, 385);

    // signed, right shift, positive
    check_op_signed(174, >>, 3, 21);
    check_op_signed(12345, >>, 5, 385);

    // signed, right shift, negative
    //
    // right shifting a negative number is implementation-defined: CompCert
    // does an arithmetic right shift
    check_op_signed(-174, >>, 1, -87);
    check_op_signed(-174, >>, 3, -22);
    check_op_signed(-12345, >>, 5, -386);

    // unsigned, less than
    check_op_unsigned(1234, <, 1235, 1);
    check_op_unsigned(1234, <, 1234, 0);
    check_op_unsigned(0, <, 0, 0);
    check_op_unsigned(0, <, UINT32_MAX, 1);

    // signed, less than
    check_op_signed(-5, <, 5, 1);
    check_op_signed(5, <, -5, 0);
    check_op_signed(0, <, 6, 1);
    check_op_signed(6, <, 0, 0);
    check_op_signed(0, >, INT32_MIN, 1);
    check_op_signed(0, <, INT32_MAX, 1);
    check_op_signed(INT32_MIN, <, INT32_MAX, 1);
    check_op_signed(-1, <, 0, 1);

    // unsigned, not equal
    check_op_unsigned(5, !=, 5, 0);
    check_op_unsigned(5, !=, 6, 1);
    if ((buf != NULL) != 1) {
        return 1;
    }

    // unsigned, equal
    check_op_unsigned(5, ==, 5, 1);
    check_op_unsigned(5, ==, 6, 0);
    if ((buf == NULL) != 0) {
        return 1;
    }

    return 0;
}
