// sorts given array a of size length > 0
void sort (int* a, int length) {
  int current;
  for (current = 0; current < length - 1; current++) {
    int min_idx = current;
    int min = a[current];
    for (int i = current + 1; i < length; i++) {
      if (a[i] < min) {
	min = a[i];
	min_idx = i;
      }
    }
    if (min_idx != current){ 
      L: a[min_idx]=a[current];
      a[current]=min;
    }
  }  
}
