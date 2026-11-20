module Predef {
    // No contents for this question
}

abstract module Assignment refines Predef {
  predicate prime(n: int) {
    n > 1 &&
    (forall d :: 1 < d < n ==> n % d != 0)
  }

  method IsPrime(n: int) returns (b: bool)
    requires n > 0
    ensures b <==> prime(n)
} 