
int main(void){
  struct list node;
  node.value = 1;
  node.next  = &node;

  struct list * l = &node;

  l = list_chop(&l);
}
