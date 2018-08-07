/*@ 
  logic int length_aux{L}(struct list * l, 
                          int n)=
    n < (int)0 ? ((int)-1) :
      l == NULL ? n : 
        n < INT_MAX ? 
	  length_aux(l->next, (int)(1+n)) :
          ((int)-1);
     
  logic int length{L}(struct list * l) = 
    length_aux(l, (int)0);
*/

