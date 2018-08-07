/* 1. frama-c-gui div2.c -val -main=f */
/* 2. frama-c-gui div2.c -val -main=f -slevel=2 */

int f ( int a ) {
  int x, y;
  int sum, result;  
  if(a == 0){ 
    x = 0; y = 5;
  }else{
    x = 5; y = 0;
  } 
  sum = x + y;  // sum cannot be 0
  result = 10/sum; // no div. by 0
  return result;
}
