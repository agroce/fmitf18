// returns a non-zero value iff all elements
// in a given array t of n integers are zeros
int all_zeros(int t[], int n) {
  int k;
  for(k = 0; k < n; k++) 
    if (t[k] != 0) 
      return 0;
  return 1;
}
