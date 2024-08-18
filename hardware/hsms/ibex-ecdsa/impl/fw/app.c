#include "drivers.h"
#include "K2.h"
#include <stddef.h>
#include <stdint.h>

void *memcpy(void *dest, const void *src, size_t sz);

#define DIVISOR 2
#define STATE_LEN 56
#define CMD_LEN 49
#define RESP_LEN 65

// to keep things simpler, we read max-length commands from the host
//
// (otherwise, would have to do more symbolic execution to explore each
// possible command length)

// could K2 auto-generate this scaffolding code?

struct pmem {
    uint32_t active;
    uint8_t _pad[4];
    uint8_t state0[STATE_LEN];
    uint8_t state1[STATE_LEN];
} *pmem = (struct pmem *) FRAM_BASE;

// proofs make use of knowledge of pmem layout
typedef char assert_pmem_packed[(sizeof(struct pmem)==(STATE_LEN*2+4+4))*2-1];

__attribute__((aligned(4))) uint8_t state_buf[STATE_LEN];
__attribute__((aligned(4))) uint8_t command_buf[CMD_LEN];
__attribute__((aligned(4))) uint8_t response_buf[RESP_LEN];

void read_command();
void read_state();
void compute();
void write_state();
void write_response();

int main() {
    uart_init(UART1, DIVISOR);

    read_command();

    read_state();

    compute();

    write_state();

    write_response();

    poweroff(); // done, don't interact with world any more until next reset

    return 0; // unreachable; to silence compcert warning
}

void read_command() {
    for (size_t i = 0; i < CMD_LEN; i++) {
        command_buf[i] = uart_read(UART1);
    }
}

void read_state() {
    uint8_t *base = (uint8_t *) &pmem->state0;
    uint32_t zlt = 0 < pmem->active;
    zlt = zlt * STATE_LEN;
    uint8_t *active = base + zlt;
    memcpy(&state_buf, active, STATE_LEN);
}

void compute() {
    K2_Ecdsa_Impl_main(state_buf, command_buf, response_buf);
}

void write_state() {
    uint8_t *base = (uint8_t *) &pmem->state0;
    uint32_t zlt = 0 < pmem->active;
    zlt = 1 - zlt;
    zlt = STATE_LEN * zlt;
    uint8_t *inactive = base + zlt;
    memcpy(inactive, &state_buf, STATE_LEN);
    // the following line is written this way on purpose, rather than reusing
    // the zlt and setting pmem->active to something like `1 - zlt`; we
    // concretize zlt earlier, but we _don't_ want to concretize this, so that
    // we end up with exactly the same symbolic expression in both case splits,
    // so the merge is easier
    pmem->active = !pmem->active; // commit point
}

void write_response() {
    for (size_t i = 0; i < RESP_LEN; i++) {
        uart_write(UART1, response_buf[i]);
    }
}
