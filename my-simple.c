int f(int oo) {
  if (oo==0) return 0;
  else {
    int a = f(oo-1);
    int b = f(oo-1);
    return a+b;
  }
}

int main() {

  int a = f(2);
  assert(a!=0);
  return 0;
}
