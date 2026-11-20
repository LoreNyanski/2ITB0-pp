include "submission.dfy"

abstract module Tests {
    import Submission

    @TimeLimit(60)
    method PrimeTest0() {
        var p := Submission.IsPrime(1);
        assert !p;
    }

    method PrimeTest1() {
        var p := Submission.IsPrime(4);
        assert 4 % 2 == 0;
        assert !p;
    }

    method PrimeTest2() {
        var p := Submission.IsPrime(7919);
        assert p;
    }

    method PrimeTest3() {
        var p := Submission.IsPrime(361);
        assert 361 % 19 == 0;
        assert !p;
    }

    method PrimeTest4() {
        var p := Submission.IsPrime(2);
        assert p;
    }

    method PrimeTest5() {
        var p := Submission.IsPrime(7);
        assert p;
    }
}
