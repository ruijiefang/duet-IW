int main()
{
int a = 0;
int b = __VERIFIER_nondet_int();
while (a < b) {
 if (a == 0)
  a += 1;
 else a += 2;
}
assert(!(a<b)); // safe
return 0;
}
