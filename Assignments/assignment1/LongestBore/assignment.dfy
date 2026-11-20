module Predef {}

abstract module Assignment refines Predef {
  predicate isBoring(a: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |a|
  {
    forall i, j :: start <= i < j < end ==> a[i] == a[j]
  }

  method LongestBoringSubsequence(a: seq<int>) returns (start: int, len: int)
    ensures 0 <= start <= start + len <= |a|
    ensures isBoring(a, start, start+len)
    ensures forall i, j :: 0 <= i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len
} 