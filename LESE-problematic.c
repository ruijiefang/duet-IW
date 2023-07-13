
void client(int N) {
  int i = 0, max = 0;
  while(i<N){i++;max++;}
  if (!(max<8)) {
    return;
  } // else max<8 
  assert(0);
}

int main() {
  int N = __VERIFIER_nondet_int();
  client();
  return 0;
}
