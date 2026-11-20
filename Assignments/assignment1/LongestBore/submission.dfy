// Please, before you do anything else, add your names here:
// Group:    25
// Member 1: Niels van den Heuvel: 2146940
// Member 2: Lorant Kutnyanszky: 2171562

include "assignment.dfy"

/**
    Make sure this file and the file tests.dfy verify.
    Verification of tests.dfy is only dependent on the contract of this method, 
    not on its implementation. 
 */
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method LongestBoringSubsequence(a: seq<int>) returns (start: int, len: int)
        // postcondition repeated for your convenience  
        ensures 0 <= start <= start + len <= |a|
        ensures isBoring(a, start, start+len)
        ensures forall i, j :: 0 <= i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len // Boring subsequence may not be longer than sequence.
    {

        start := 0; // current best start
        len := 0; // current best length

        for n := 0 to |a|+1 // potential starting positions
            invariant 0 <= start <= start + len <= |a|
            invariant isBoring(a, start, start+len)
            // for all previous starting positions: every boring subsequence that starts there is no longer than the current best length
            invariant forall i, j | 0 <= i < n :: i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len
        {
            for m := n to |a|+1 // potential ending positions
                invariant 0 <= start <= start + len <= |a|
                invariant isBoring(a, start, start+len)
                // for all previous ending positions: if the sequence that ends here is boring it is no longer than the current best length
                invariant forall j :: n <= j < m && isBoring(a, n, j) ==> j - n <= len
            {
                // check if the sequence is boring
                var flag := true;
                for index := n to m
                    invariant flag <==> isBoring(a, n, index)
                {
                    if a[index] != a[n]
                    {
                        flag := false;
                    }
                }
                assert flag <==> isBoring(a, n, m);

                // if its boring and longer than the current best, update current best.
                if flag && (m - n > len)
                {
                    start := n;
                    len := m - n;
                }

                // invariant holds for this iteration
                assert isBoring(a, n, m) ==> m - n <= len;
            }
            // result of loop: every boring subsequence that starts at n is no longer than the current best length
            assume forall j :: n <= j <= |a| && isBoring(a, n, j) ==> j - n <= len;
        }
        assert forall i, j :: 0 <= i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len;


        // start := 0;
        // len := 0;
        // for n := 0 to |a|
        // {
        //     for m := n to |a| 
        //     {
        //         if ((m - n > len) && (isBoring(a, n, m))) 
        //         {
        //             start := n;
        //             len := m - n;
        //         }
        //     }
        //     assert forall j :: n <= j <= |a| && isBoring(a, n, j) ==> j - n <= len;
        // }


        // lööp over all indecies (except last)
            // lööp over all indeces from prev lööp var until last
                // is it longer than the previous one?
                    // is it boring?
                        // make it new longest sequence
    }

}
