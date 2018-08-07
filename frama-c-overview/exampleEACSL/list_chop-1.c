struct list
{
  struct list *next;
  int value;
};

/*@ 
  requires \valid(list); 
  requires 0 <= length(*list);
*/
struct list * list_chop(struct list ** list){
  // removes the last element of the list
}
