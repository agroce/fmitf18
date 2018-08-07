/*@ ensures (x >= 0 ==> \result == x) && 
      (x < 0 ==> \result == -x);
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}
