/*@ ensures \result == length_aux(l, n); 
  @ assigns \nothing; */
int length_aux(struct list * l, int n){
  if (n < 0)
    return -1;
  else if (l == NULL)
    return n;
  else if (n < INT_MAX)
    return length_aux(l->next, n+1);
  else
    return -1;
}
/*@ ensures \result == length(l); 
  @ assigns \nothing; */
int length(struct list * l){
  return length_aux(l, 0);
}
