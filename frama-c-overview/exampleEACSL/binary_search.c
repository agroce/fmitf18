/*@ requires \forall integer i; 0 <= i < length ==> \valid(a+i);
    requires \forall integer i; 0 <= i < length-1 ==> a[i]<=a[i+1];
    requires length >=0;

    behavior exists:
      assumes \exists integer i; 0<=i<length && a[i] == key;
      ensures 0<=\result<length && a[\result] == key;

    behavior not_exists:
      assumes \forall integer i; 0<=i<length ==> a[i] != key;
      ensures \result == -1;
*/
int binary_search(int* a, int length, int key) {
  int low = 0, high = length - 1;
  /* /\*@ loop invariant 0<=low<=high+1; */
  /*     loop invariant high<length; */
  /*     loop invariant \forall integer k; 0<=k<low ==> a[k] < key; */
  /*     loop invariant \forall integer k; high<k<length ==> a[k] > key; */
  /* *\/ */
  while (low<=high) {
    int mid = low+(high-low)/2;
    if (a[mid] == key) return mid;
    if (a[mid] < key) { low = mid+1; }
    else { high = mid - 1; }
  }
  return -1;
}

int main(void) {
  int t[10] = { -29, -10, 0, 12, 42, 42, 43, 54, 102, 123 };
  int res = binary_search(t, 10, 102);
  /*@ assert res == 8; */
  return 0;
}
