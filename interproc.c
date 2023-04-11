
int p(int x) {
  int i = 0;
  while(i < 10) i+= x;
  return i;
}

int main() {
  int a = 2;
  a = a + 1;
  int v = p(a);
  assert (v < 10);
  return 0;
}

