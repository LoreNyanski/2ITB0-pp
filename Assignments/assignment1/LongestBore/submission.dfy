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

        for n := 0 to |a|+1 // n can be at most |a|
            invariant 0 <= start <= start + len <= |a|
            invariant isBoring(a, start, start+len)
            invariant forall i, j | 0 <= i < n :: i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len // for all previous starting positions: len is the best length
        {
            var newLen := findLongestBoringAt(a, n); // find the best possible boring sequence length at this start
            
            // if its better than our current one, update the current one
            if newLen > len
            {
                start := n;
                len := newLen;
            }

            assert forall j :: n <= j <= |a| && isBoring(a, n, j) ==> j - n <= len; // invariant holds for this iteration
        }
    }

    // helper method that finds the length of the longest possible boring subsequence starting at the index "start"
    method findLongestBoringAt(a: seq<int>, start: int) returns (len: int)
        requires 0 <= start <= |a|
        ensures start <= start + len <= |a|
        ensures isBoring(a, start, start + len)
        ensures forall j :: start <= j <= |a| && isBoring(a, start, j) ==> j - start <= len
    {
        len := 0; // current best length

        for m := start to |a|+1 // m can be at most |a|
            invariant 0 <= start <= start + len <= |a|
            invariant isBoring(a, start, start+len)
            invariant forall j :: start <= j < m && isBoring(a, start, j) ==> j - start <= len // for all previous ending positions: len is the best length
        {
            // apparently isBoring() would also work here, but predicate feels like a specification language thing, not a programming language thing
            var flag := checkBoring(a, start, m); // check if the sequence is boring

            // if its boring and longer than the current best, update current best.
            if flag && (m - start > len) 
            { 
                len := m - start; 
            }

            assert isBoring(a, start, m) ==> m - start <= len; // invariant holds for this iteration
        }
    }

    // helper method that returns true if an only if the subsequence is boring
    method checkBoring(a: seq<int>, start: int, end: int) returns (flag: bool)
        requires 0 <= start <= end <= |a|
        ensures flag <==> isBoring(a, start, end)
    {
        flag := true;
        for index := start to end
            invariant flag <==> isBoring(a, start, index)
        {
            if a[index] != a[start]
            {
                flag := false;
            }
        }
    }
}
