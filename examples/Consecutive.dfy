// Пример, который Dafny не может верифицировать.
// Произведение двух соседних целых чисел всегда чётно,
// но Z3 не справляется с нелинейной арифметикой и остатком от деления.
method Consecutive(x: int) returns (y: int)
  ensures y % 2 == 0
{
  y := x * (x + 1);
}

method Main() {
  var x := -3;
  while x <= 3 {
    var y := Consecutive(x);
    print x, " * ", x + 1, " = ", y, ", y % 2 = ", y % 2, "\n";
    x := x + 1;
  }
}
