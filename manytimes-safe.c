int abs(int x) {if (x<0)return -x; else return x;}

int main() {
  int x = nd();
  // absincr start
  int xx = abs(x);
  int y=0, z=0;
  while(xx-- > 0){z++;y+=2;}
  while(z-- > 0){xx++;y--;}
  // absincr end
  assert(abs(x) + 1 == y+1);//safe
  return 0;
}

