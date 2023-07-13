int f(int a, int b) {
  if (a > 23) return 0;
  if (b < 9) return 0;
  return 123;
}

int main() {
  int b=__VERIFIER_nondet_int();
  if (b >= 9 || b <= 3) return 0;
  int a=__VERIFIER_nondet_int();
  if (a<=23 || a >= 110) return 0;
  int r = f(a,b);
  assert(r!=123);
  return 0;
}
