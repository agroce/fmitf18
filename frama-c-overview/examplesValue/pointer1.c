/* 1. frama-c-gui pointer1.c -val */

#include "stdlib.h"

int main(void){
  int *p;
  if( p )
    *p = 10;
  return 0;
}
