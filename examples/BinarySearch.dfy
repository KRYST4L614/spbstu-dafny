// Задача 2: бинарный поиск в отсортированном массиве.
method BinarySearch(a: array<int>, key: int) returns (idx: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= idx ==> idx < a.Length && a[idx] == key
  ensures idx < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall k :: 0 <= k < lo ==> a[k] < key
    invariant forall k :: hi <= k < a.Length ==> a[k] > key
  {
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

method Main() {
  var a := new int[] [1, 3, 5, 7, 9, 11];
  var i := BinarySearch(a, 7);
  print "BinarySearch([1, 3, 5, 7, 9, 11], 7) = ", i, "\n";
  var j := BinarySearch(a, 4);
  print "BinarySearch([1, 3, 5, 7, 9, 11], 4) = ", j, "\n";
}
