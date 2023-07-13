int abs(int x) {if (x<0)return -x; else return x;}

int cnd(int y) {
  int z=0;
  while(y>0) {
    y--;
    z++;
  }
  while (1) {
   int x = nd();
   if (x==z+1)return x;
   else {
     return cnd(z);
   }
  }
}

int main(){
 int x = 0;
 int y = 0;
 int m = abs(nd());
  int n = abs(nd());
  int p = n;
 while (x<m) x++;
 while (y < m){y=cnd(y); }
 while (m > 0) {m--;n++;}
 assert(x==y&&x==n-p);//safe
return 0;
}

