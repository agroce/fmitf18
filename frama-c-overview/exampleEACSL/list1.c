#include "stdlib.h"

struct list {
  struct list *next;
  int value;
};

/*@ 
  requires \valid(list); 
  assigns *list; 
*/
void list_init(struct list ** list) {
  *list = NULL;
}

int main(void){
  struct list ** l = malloc(sizeof(void *));
  list_init(l);
  free(l);
  list_init(l);
}
