
int r(int x, int y) {
  if (__VERIFIER_nondet_int()) {
    return r(x + y, y + 1);
  } else {
    return x;
  }
}

int main(){
      int x,y = 1;
      x = 0;
      y = r(x, y);
      assert (x<=y);
     return 0;
}

