// Please, before you do anything else, add your names here:
// Group:    25
// Member 1: Niels van den Heuvel : 2146940
// Member 2: Lorant Kutnyanszky : 2171562

include "assignment.dfy"
 
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method IsPrime(n: int) returns (b: bool)
      ensures b <==> prime(n) // repeated for your convenience
    {

      // base case, 1 and lower isn't prime
      if (n <= 1) {return false;}

      // 2 is prime
      if (n == 2) {return true;}

      // otherwise if divisble by 2 return false.
      if (n % 2 == 0) {return false;}

      // our number is odd and greater than 2
      assert n > 2;
      assert n%2 != 0;

      var i:=1;

      // for now the number is prime.
      b := true;

      // as long as we don't touch n
      while i < (n-2)
        decreases n - i        
        invariant i%2 == 1
        invariant forall k | 2 <= k <= i :: n%k != 0
      {
        // asserting invariant properties for the sake of it.
        assert i%2 == 1;
        assert forall k | 2 <= k <= i :: n%k != 0;

        // prime detection
        if (n % (i + 2) == 0) {
          // prime detected what the fuck
          b := false;
          
          assert i+2 < n;
          assert n % (i+2) == 0;
          
          // trivially this number isn't prime
          assert !prime(n);

          // prime false, b false, so it holds
          assert b <==> prime(n);
         
          return b;
        }

        
        assert n % (i + 2) != 0;       
    
        assert (i + 1) % 2 == 0;

        assert n%2 != 0;
        
        IHateEvenNumbers(n);

        assert forall i :: (i >= 1 && i%2 == 0) ==> n%i != 0;
        assert (i+1) >= 1;
        assert ((i+1)%2 == 0);

        // untill and including i 
        assert forall k | 2 <= k < i :: n%k != 0;
        // i + 1
        assert n%(i+1) != 0;
        // i + 2
        assert n%(i+2) != 0;

        // new bounds aquired
        assert forall k | 2 <= k <= i+2 :: n%k != 0;
        
        // maintain invariant by updating i
        i := i + 2;

        // confirm invariant is maintained.
        assert i % 2 == 1;
        assert forall k | 2 <= k <= i :: n%k != 0;      
      }     

      assert b;
      assert prime(n);
      
      assert b <==> prime(n);
    }


  lemma IHateEvenNumbers(n: int) 
    requires n%2 == 1
    ensures forall i :: (i >= 1 && i%2 == 0) ==> n%i != 0
  {
    assert n%2 == 1;
    
    if exists x :: x > 2 && x%2 == 0 && n%x == 0 {

      var x :| x > 0 && x%2 == 0 && n%x == 0;
      assert n%x == 0;
      assert x%2 == 0;

      var a := n/x;
      assert a * x == n;      


      var b := x/2;
      assert b*2 == x;
    
      var c := a * b;

      assert c * 2 == n;
      assert n%2 == 0;
      
      assert false;
      
    } 

    assert !exists x :: x > 0 && x%2 == 0 && n%x == 0;    
  }

  lemma OddPlusEvenIsOdd(n: int) 
    requires n%2==1
    ensures forall i :: (i > 0 &&  i%2 == 0) ==> (n+i)%2 == 1
  {
  }
  

  lemma IHateOtherNumbersToo(n: int, d: int) 
    requires n > 2
    requires d > 1
    requires d < n
    ensures n % d == 0 ==> !prime(n) 
  {
    if (n%d == 0) {
      var k := n/d;
      assert k * d == n;

      assert n > 1;
      
      assert n % d != 1;

      assert !prime(n);

      assert n % d == 0 ==> !prime(n);
    }
    assert n % d == 0 ==> !prime(n);

  }

}