/*@ ensures \result >= a && \result >= b;
    ensures \result == a || \result == b;
    assigns \nothing;
*/
int max ( int a, int b ) {
  if ( a >= b )
    return a ;
  return b ;
}
