int foo(int x) {

  return x + 1;
}

int bar(int y) {
  return y + 2;
}

int main() {

  int a = 3;

  int x = foo(a);

  int y = bar(x);

  assert(y == 1);
}
