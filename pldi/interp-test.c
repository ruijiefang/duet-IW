

int main()
{
  int i = 1; //int j = 0;
  while(__VERIFIER_nondet_int()) i = 2 * i;
  int j = 0;
  while(i>0){j++;i--;}
  assert(j!=131);
  return 0;
}
