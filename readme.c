// SeaHorn v0.1.0 README 
int main(){
      int x,y;
      x=1; y=0;
      while (__VERIFIER_nondet_int())
      {
        x=x+y;
        y++;
      }
      assert (x>=y);
     return 0;
}


