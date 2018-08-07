int f ( int a ) {
  int x, y;
  int sum, result;  
  if(a == 0){ 
    x = 0; y = 5;
  }else{
    x = 5; // y = 0;
  } 
  //@ assert \initialized(&y);
  sum = x + y;  // y can be non-initialized
  //@ assert sum != 0;
  result = 10 / sum; // risk of division by 0
  return result;
}
            
int main(void){
  f(42);
  f(0);
  return 0;
}
