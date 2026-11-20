method DerivationProof_1_1(P: bool, Q: bool, R: bool)
{
    if (P && Q) {
        if (R) {
            assert Q;
            assert Q && R;
        }
        assert R ==> Q && R;
    }
    assert (P && Q) ==> (R ==> Q && R);
}

method DerivationProof_1_1alt(P: bool, Q: bool, R: bool)
{
    assert (P && Q) ==> (R ==> Q && R);
}

method Handout_1_6<T>(P: T->bool, Q: T-> bool, R: T-> bool)
ensures ((forall x::P(x) ==> Q(x)) && (forall y::Q(y) ==> R(y))) ==> (forall z::P(z) ==>R(z))
{
    // assume
    if (forall x::P(x) ==> Q(x)) && (forall y::Q(y) ==> R(y)) {
        // intro variable z
        forall z | P(z) ensures R(z) {
            // assume
            if (P(z)) {
                // and elim
                assert forall x::P(x) ==> Q(x);
                // forall elim
                assert P(z) ==> Q(z);
                // impl elim
                assert Q(z);
                // and elim
                assert forall y::Q(y) ==> R(y);
                // forall elim
                assert Q(z) ==> R(z);
                // impl elim
                assert R(z);
            }
            // impl intro
            assert P(z) ==> R(z);
        }
        // forall intro
        assert (forall z::P(z) ==> R(z));
    }
    // impl intro
    assert ((forall x::P(x) ==> Q(x)) && (forall y::Q(y) ==> R(y))) ==> (forall z::P(z) ==>R(z));
}

method Triple(x: int) returns (r: int)
{
  var y := 2 * x;
  r := x + y;
//   return x + y; this also works
  assert r == 3 * x; // making this 3 * x + 1 means it cant be proven
}


method Triple_again(x: int) returns (r: int)
  requires x % 2 == 0 // commenting this out means the postcondition doesn't always hold
  requires x % 4 == 0
  requires x == 4
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}