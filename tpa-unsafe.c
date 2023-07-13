
int main (){
 int N = 500;
 int x =0; int y = N;
 while(x < 2* N){
  x = x + 1;
  if(x > N)
   y = y + 1;
 }
 assert( y != 2 * N );
 return 0;
}


