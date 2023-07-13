
int abs(int x) {if (x<0)return -x; else return x;}

int p(int x) {
  int y = 0;
  while (x--){
    if (x<-0xfff){return 7;}
    y++;}
  return y + 1;
}

int main() {
  int x = nd(), z=nd();
  x = abs(x);
  z = abs(z);

  int y = 0;
  while(x>0){x--;y=p(x)+p(z);}
  // p(0)==1, so y=1+(z+1)=z+2
  assert(y+1==z);//safe
//  assert(p(x)==x+1);
  return 0;
}

