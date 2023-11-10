

int main()
{
  int i = 1; 
  int havoc = __VERIFIER_nondet_int();
  if (havoc<0) havoc = -havoc;
  while(havoc>0){ i = 2 * i; havoc--; }
  int j = 0;
  while(i>0){j++;i--;}
  assert(j!=131);
  return 0;
}
