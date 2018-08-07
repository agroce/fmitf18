/*@ ensures \result == length(list); 
  @ assigns \nothing; */
int length(struct list * list){
  int len = 0;
  struct list * l = list;
  
  while(l != NULL && len < INT_MAX){
    l = l->next;
    len ++;
  }
  if(l!=NULL){
    return -1;
  }
  else
    return len;
}

