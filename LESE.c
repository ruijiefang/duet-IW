
void client(int N) {
  int i = 0, max = 0;
  while(i<N){i++;max++;}
  if (max<8) {
    return 0;
  } else return 1;
}

int main() {
  int N = __VERIFIER_nondet_int();
  int r = client();
  
  assert(r==0);

  return 0;
}
