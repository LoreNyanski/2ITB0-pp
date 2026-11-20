// Please, before you do anything else, add your names here:
// Group:    <Group number>
// Member 1: <Full name 1>: <Student number 1>
// Member 2: <Full name 2>: <Student number 2>

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
       // TODO 
    }

}