int abs(int x) {if (x<0)return -x; else return x;}

int incr(int y) {
  int z=0;
  while(y>0) {
    y--;
    z++;
  }
  while (1) {
   int x = nd();
   if (x==z+1)return x;
   else {
     return incr(z);
   }
  }
}

int main(){
 int m = abs(nd());
  int n = abs(nd());
  int p = n, q=m;
 while (m > 0) {m--;n=incr(n);}
 assert(n==p+q);
return 0;
}


