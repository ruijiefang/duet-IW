void assert(int r){
  if (r==0){
        ERROR: {reach_error();abort();}
  }
}

int f(int a, int b) {
  if (a <0) return 0;
  if (b <0) return f(a-1,b);
  return f(a,b-1)+3;
}

int main() {
  int a = __VERIFIER_nondet_int();
  if (a < 3 || a > 9) return 0;
  int b = __VERIFIER_nondet_int();
  if (b < 5 || b > 13) return 0;
  int r = f(a,b);
  assert(r > 0);
  return 0;
}

