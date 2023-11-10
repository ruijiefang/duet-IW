

int main()
{
  int i = 1, j = 0;
  while(__VERIFIER_nondet_int()) i = 2 * i;
  while(i>0){j++;i--;}
  assert(j!=32);
  return 0;
}
