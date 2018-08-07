#include<limits.h>
/*@ requires x > INT_MIN;
    behavior pos: 
      assumes x >= 0;
      ensures \result == x;
    behavior neg:
      assumes x < 0;
      ensures \result == -x;
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}
