include "submission.dfy"

abstract module Tests {
    import Submission

    @TimeLimit(60)
    method LongestBoreTest0() {
        // Test on empty input (start lower bounded by 0, but length is 0 because empty.)
        var a: seq<int> := [];
        var start: int;
        var length: int;
        start, length := Submission.LongestBoringSubsequence(a);
        assert start == 0;
        assert length == 0;
    }

    method LongestBoreTest1() {
        var a := [1];
        var start, length;
        start, length := Submission.LongestBoringSubsequence(a);
        assert Submission.isBoring(a, 0, 1);
        assert start == 0;
        assert length == 1;
    }

    method LongestBoreTest2() {
        var a := [1, 1];
        var start, length := Submission.LongestBoringSubsequence(a);
        assert Submission.isBoring(a, 0, 2);
        assert start == 0;
        assert length == 2;
    }

    method LongestBoreTest3() {
        var a := [1, 1, 2];
        var start, length := Submission.LongestBoringSubsequence(a);
        assert Submission.isBoring(a, 0, 2);
        assert a[1] != a[2];
        assert ! Submission.isBoring(a, 1, 3);
        assert start == 0;
        assert length == 2;
    }
}
