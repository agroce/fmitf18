int f ( int a ) {
  int x, y;
  int sum, result;  
  if(a == 0){ 
    x = 0; y = 0;
  }else{
    x = 5; y = 5;
  } 
  sum = x + y;        
  //@ assert sum != 0;
  result = 10 / sum;  
  return result;
}
