int foo(int x) {
  int choice = __VERIFIER_nondet_int();
  if (choice) {
    return x + 1;
  } else {
    return x + 2;
  }
}

int main()
{
  int x = 0;
  x = foo(x);
  x = foo(x);
  assert(x<4);
  return 0;
}
