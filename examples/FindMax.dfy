// Задача 1: индекс максимального элемента массива.
method FindMax(a: array<int>) returns (idx: int)
  requires a.Length > 0
  ensures 0 <= idx < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[idx]
{
  idx := 0;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= idx < i
    invariant forall k :: 0 <= k < i ==> a[k] <= a[idx]
  {
    if a[i] > a[idx] {
      idx := i;
    }
    i := i + 1;
  }
}

method Main() {
  var a := new int[] [3, 7, 2, 5];
  var i := FindMax(a);
  print "FindMax([3, 7, 2, 5]) = ", i, " (a[", i, "] = ", a[i], ")\n";
}
