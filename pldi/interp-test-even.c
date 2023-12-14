

int main()
{
  int i = 1;  
  int havoc = __VERIFIER_nondet_int();
  while(havoc>0){ i = 2 * i; havoc--; }
  int j = 0;
  while(i>0){j++;i--;}
  assert(j!=130);
  return 0;
}
