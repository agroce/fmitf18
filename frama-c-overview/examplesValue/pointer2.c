/* 1. frama-c-gui pointer2.c -val */

#include "stdlib.h"

int main(void){
  int * p = (int*)malloc(sizeof(int));
  *p = 10;
  return 0;
}
