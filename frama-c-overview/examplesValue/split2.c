int gcd(int x, int y) {
  int a = x, b = y;
  /*@ assert b < 0 || b == 0 || b > 0; */
  while(b!=0) {
    int tmp = a % b;
    a = b; b = tmp;
    /*@ assert b < 0 || b == 0 || b > 0; */
  }
  return a;
}
