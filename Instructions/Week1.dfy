method Triple(x: int) returns (r: int)
{
  var y := 2 * x;
  r := x + y;
  assert r == 3 * x + 1;
  // this fucking annoys me ngl
}


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
    // your proof goes here
}