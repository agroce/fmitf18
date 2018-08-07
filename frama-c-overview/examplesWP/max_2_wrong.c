/*@ ensures \result >= a && \result >= b ;
    ensures \result == a || \result == b ; */
int max(int a, int b);

extern int v ;
   
int main(){
  v = 3;
  int r = max(4,2);
  //@ assert v == 3 ;
}
