
int f(int a) {
  return a + 9;
}

int main() {
  int a = __VERIFIER_nondet_int();
  int b = f(a);
  assert(b==0);
}
