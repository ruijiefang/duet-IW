int f(int oo, int bar) {
  if (oo==0) return 0;
  else {
    int r= f(oo-1,bar-1) + bar-1;
    return r;
  }
}

int main() {
  int a = f(5,3);
  assert(a<0);
  return 0;
}
