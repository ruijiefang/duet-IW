int main()
{
int a = 0;
while (a < 10) {
 if (a == 0)
  a += 1;
 else a += 2;
}
assert(0); // fail
return 0;
}
