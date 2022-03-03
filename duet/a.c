
int main()
{
  int a = 0;
  int d = a + 9;
  if (d != 0) { 
    a=d + 3;  
    d = a + 9;
} else {
    a = 10;
  }
  d = a - 1;
  a = d ;
  assert(a==0);
  return 1;
}

