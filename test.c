

int f(int a) {
  if (a == 3)
    return 9;
  else 
    return f(a- 1);
}

int main() {
  int s = __VERIFIER_nondet_int();
  if (s>7||s<7)return 0;
  int r = f(s);
  __VERIFIER_assert(r!=9);
}

