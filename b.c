
int main() {
  int a = 9,  b = 7;
  
  int c = a + b * 2;
  if (c > 3) {
    int d = a + 8;
    if (d < 9 && c > 5) {
      assert(b>1);
    }
    d = c - 1;
  }
  c--;
  return c - a + b;
}
