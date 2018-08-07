/* 1. frama-c-gui div1.c -val -main=f */
/* 2. frama-c-gui div1.c -val -main=f -slevel=2 */

int f ( int a ) {
  int x, y;
  int sum, result;  
  if(a == 0){ 
    x = 0; //y = 5; 
  }else{
    x = 5; y = 0;
  } 
  sum = x + y;  // y can be non-initialized
  result = 10/sum; 
  return result;
}
