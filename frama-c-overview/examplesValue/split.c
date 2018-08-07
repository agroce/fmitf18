int gcd(int x, int y) {
  int a = x, b = y;
  while(b!=0) {
    int tmp = a % b;
    a = b; b = tmp;
  }
  return a;
}
