/* 1. frama-c-gui sqrt.c -val */
/* 2. frama-c-gui sqrt.c -val -slevel=8 */

#include "__fc_builtin.h"
int A, B;
int root(int N){
  int R = 0;
  while(((R+1)*(R+1)) <= N) {
    R = R + 1;
  }
  return R;
}

void main(void)
{
  A = Frama_C_interval(0,64);
  B = root(A);
}
