extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_2-2.c", 3, "reach_error"); }
extern unsigned int __VERIFIER_nondet_uint(void);

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

unsigned int x;

void incr() {x= x+1;}

int main(void) {
 x = __VERIFIER_nondet_uint();

 while (x < 0x0fffffff) incr();

  __VERIFIER_assert(x > 0x0fffffff);
}
