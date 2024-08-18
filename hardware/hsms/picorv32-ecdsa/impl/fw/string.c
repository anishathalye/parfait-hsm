#include "string.h"

void *memcpy(void *dst, const void *src, size_t n) {
  char *d = dst;
  const char *s = src;
  while (n--) {
    *(d++) = *(s++);
  }
  return dst;
}

void *memmove(void *dst, const void *src, size_t n) {
  char *d = dst;
  const char *s = src;
  if (s == d) {
    return dst;
  } else if (d < s) {
    // copy in forward direction
    while (n--) {
      *(d++) = *(s++);
    }
  } else {
    // copy in reverse direction
    d = d + n - 1;
    s = s + n - 1;
    while (n--) {
      *(d--) = *(s--);
    }
  }
  return dst;
}

size_t strlen(const char *str) {
  size_t n;
  for (n = 0; *str; str++) {
    n++;
  }
  return n;
}

char *strchr(const char *str, int c) {
  for (; *str; str++) {
    if (*str == c) {
      return (char *) str;
    }
  }
  return NULL;
}

void *memset(void *ptr, int value, size_t num) {
  char *p = ptr;
  while (num--) {
    *(p++) = value;
  }
  return ptr;
}
