extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_4-1.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
unsigned int x;

void decr(){x-=2;}

int main(void) {
  x = 0x0ffffff1;

  while (x > 1) decr();

  __VERIFIER_assert(!(x % 2));
}
