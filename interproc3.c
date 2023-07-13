int id(int x) {
  return x;
}

// returns x + 1
int p(int x) {
  return id(x) + 1;
}

int main() {
  int x = 9;
  int y = p(x); // y = x + 1 = 9 + 1
  assert(y < 0);// asserting 9+1<0; bug!
}

