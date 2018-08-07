/* frama-c-gui div1.c -val -main=f */

int f ( int a ) {
  int x, y;
  int sum, result;  
  if(a == 0){ 
    x = 0; y = 0;
  }else{
    x = 5; y = 5;
  } 
  sum = x + y;     // sum can be 0
  result = 10/sum; // risk of division by 0
  return result;
}
            
