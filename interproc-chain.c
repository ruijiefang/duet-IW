// returns 3
int r(int y) {
  while (y < 3) { y++; }
  while (y > 3) { y--; }
  return y;
}

// returns 3
int q(int x) {
  return r(x);
}

// returns 3 + 1
int p(int x) {
  return q(x) + 1;
}

int main() {
  int x = 9;
  int y = p(x);
  assert(y > 0);//not fail
}

