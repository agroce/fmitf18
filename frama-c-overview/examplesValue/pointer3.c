/* 1. frama-c-gui pointer3.c -val */

#include "stdlib.h"

int main(void){
  int * p = (int*)malloc(sizeof(int));
  if( p )
    *p = 10;
  return 0;
}
