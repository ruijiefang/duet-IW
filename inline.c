int f(int a) {

  a = a + 9;
  int b = a + 3;
  if (a==9+9) {
    int c = b + 1;
    return c;} else 
    {
      return b;}
}

int main() {
  int j = 9;
  int k = 0;
  if (k==0)
    k = f(j);
  assert(k==0);
  return 0;
}
