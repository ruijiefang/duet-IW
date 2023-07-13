
int restrict_range(int x, int ub, int lb) {
  if (x>ub) return ub;
  if (x<lb) return restrict_range(-x,ub,lb);
  return x;
}

int low(int x, int y, int z) {
  if (x< y && x < z) return x;
  if (z < y && z < x) return z;
  return y;
}

int poshigh(int x, int y, int z) {
  return -low(-x,-y,-z);
}

int abs(int x) {
  return restrict_range(x, 0, x);
}

int main() {
  int x = abs(__VERIFIER_nondet_int()), z = abs(__VERIFIER_nondet_int());
  int y=0, w=0;
  while(x--) y++;
  while(z--) w++;
  int h=poshigh(x,y,z);
  assert(h>=y&&h>=w);
  return 0;
}


