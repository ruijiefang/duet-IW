

// returns 3
int w(int y) {
  while (__VERIFIER_nondet_int()) {
    y++;
  }
  return 3 - y + y;
}

// returns 3
int p(int x) {
  int i = 12;//0;
  while(i < 10) i+= x;
  int j = w(i);
  //while (j < 10) j += x;
  return 3;
}

int main() {
  int a = 2;
  a = a + 1; // calling p with argument a=3
  int v = p(a); // gets 3
  assert (v > 10);//unsafe
  return 0;
}

