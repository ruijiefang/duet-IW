

int main()
{
  int i = 1; //int j = 0;
  while(__VERIFIER_nondet_int()) i = 2 * i;
  int j = 0;
  while(i>0){j++;i--;}
  assert(j!=3);
  return 0;
}
