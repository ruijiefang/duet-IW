extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }

int main (){
 int N = 1000;
int x  = 0;
 while(__VERIFIER_nondet_int()){
  x++;
 }
 assert( x < N );
 return 0;
}
