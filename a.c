void b() {
  return ;
}

int main()
{
  int a = 0;
  if (a != 0) { 
    b();
  } else {
    a = 3 + 7;
  }
  assert(a==0);
  return 1;
}
