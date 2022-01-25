import Mathlib.Tactic.Ring

/- # Proving challenge -/

/- My summing function -/
def sum : Nat → Nat
  | 0     => 0
  | n + 1 => n + 1 + sum n

/- Auxiliary proofs -/
theorem natSuccEqPlusOne {a : Nat} : Nat.succ a = a + 1 := rfl
theorem mulDist {a b c : Nat} : a * (b + c) = a * b + a * c := by ring
theorem squareOfSum {a b : Nat} :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring
theorem auxPermutation {n : Nat} :
  n * n + 2 * n + 1 + n + 1 = n * n + n + 2 * n + 2 := by ring

/- The actual proof -/
theorem twoTimesSumEqTimesSucc {n : Nat} : 2 * sum n = n * (n + 1) := by
  induction n with
    | zero => rfl
    | succ n hi =>
      simp only [sum]
      iterate 3 rw [mulDist]
      rw [hi, mulDist, natSuccEqPlusOne, squareOfSum, add_comm]
      simp [←add_assoc, auxPermutation]

/-! # Programming challenge -/

/-
A helper function for the programming challenge.

It carries over two variables for the computation happening on the current streak:
`currStreak` and `currSum`. `currStreak` is the length of the current consecutive
ascending sequence and `currSum` is the sum of that sequence.

It also carries over two variables for the best solution until this point:
`currMaxStreak` and `currMaxSum`, whose names indicate analogous utilities to the
other two.
-/
def longestConsecutiveSumAux : List Nat → Nat → Nat → Nat → Nat → Nat
  | a::b::t, currStreak, currSum, currMaxStreak, currMaxSum =>
    if a + 1 ≠ b then -- breaking the streak
      longestConsecutiveSumAux (b::t) 0 0 currMaxStreak currMaxSum
    else
      if currMaxStreak < currStreak + 1 then -- update highest values
        longestConsecutiveSumAux (b::t) (currStreak + 1) (a + currSum) 
          (currStreak + 1) (a + b + currSum)
      else
        longestConsecutiveSumAux (b::t) (currStreak + 1) (a + currSum)
          currMaxStreak currMaxSum
  | _, _, _, _, currMaxSum => currMaxSum

/- Final function for the challenge -/
def longestConsecutiveSum (l : List Nat) : Nat := longestConsecutiveSumAux l 0 0 0 0

#eval longestConsecutiveSum [1, 2, 3, 100, 7, 8, 9, 10] -- 34 = 7 + 8 + 9 + 10

/- # Extra -/

/- This function extracts the greatest sum instead of the sum of the longest sequence -/
def greatestConsecutiveSumAux : List Nat → Nat → Nat → Nat
  | a::b::t, currSum, currMaxSum =>
    if a + 1 ≠ b then -- breaking the streak
      greatestConsecutiveSumAux (b::t) 0 currMaxSum
    else
      greatestConsecutiveSumAux (b::t) (a + currSum)
        (max (a + b + currSum) currMaxSum)
  | _, _, currMax => currMax

def greatestConsecutiveSum (l : List Nat) : Nat := greatestConsecutiveSumAux l 0 0

#eval greatestConsecutiveSum [1, 2, 3, 100, 7, 8] -- 15 = 7 + 8
