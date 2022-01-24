/- My summing function -/
def sum : Nat → Nat
  | 0     => 0
  | n + 1 => n + 1 + sum n

/- Mathlib stuff -/
theorem addComm {a b : Nat} : a + b = b + a := sorry
theorem addDist {a b c : Nat} : a + (b + c) = a + b + c := sorry
theorem mulDist {a b c : Nat} : a * (b + c) = a * b + a * c := sorry
theorem squareOfSum {a b : Nat} :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b := sorry
theorem introSumLeft {a b c : Nat} (h : b = c) : a + b = a + c := sorry
theorem sumPerm {a b c d : Nat} : a + b + c + d = c + a + b + d := sorry
theorem natSuccEqPlusOne {a : Nat} : Nat.succ a = a + 1 := rfl

/- This is amazingly ugly! -/
theorem auxTheorem {n : Nat} :
    n * n + 2 * n + 1 + n + 1 = n * n + n + 2 * n + 2 := by
  have a := n * n
  have b := 2 * n + 1 + n + 1
  have c := n + 2 * n + 2
  have aux' : 2 * n + 1 + n + 1 = n + 2 * n + 2 := by rw [sumPerm] rfl
  have introLeft := @introSumLeft (n * n) (2 * n + 1 + n + 1)
    (n + 2 * n + 2) (aux')
  simp [addDist] at introLeft
  exact introLeft

/- The actual proof -/
theorem twoTimesSumEqTimesSucc {n : Nat} : 2 * sum n = n * (n + 1) := by
  induction n with
    | zero => simp
    | succ n hi =>
      simp only [sum]
      rw [mulDist, hi, mulDist, mulDist, mulDist,
        natSuccEqPlusOne, squareOfSum, addComm]
      simp [addDist, auxTheorem]

def greatestConsecutiveSumAux : List Nat → Nat → Nat → Nat
  | a::b::t, currSum, currMaxSum =>
    if a + 1 ≠ b then
      greatestConsecutiveSumAux (b::t) 0 currMaxSum
    else
      greatestConsecutiveSumAux (b::t) (a + currSum)
        (max (a + b + currSum) currMaxSum)
  | _, _, currMax => currMax

def greatestConsecutiveSum (l : List Nat) : Nat := greatestConsecutiveSumAux l 0 0

def longestConsecutiveSumAux : List Nat → Nat → Nat → Nat → Nat → Nat
  | a::b::t, currStreak, currSum, currMaxStreak, currMaxSum =>
    if a + 1 ≠ b then
      longestConsecutiveSumAux (b::t) 0 0 currMaxStreak currMaxSum
    else
      if currMaxStreak < currStreak + 1 then
        longestConsecutiveSumAux (b::t) (currStreak + 1) (a + currSum) 
          (currStreak + 1) (a + b + currSum)
      else
        longestConsecutiveSumAux (b::t) (currStreak + 1) (a + currSum)
          currMaxStreak currMaxSum
  | _, _, _, _, currMaxSum => currMaxSum

/- This is the actual programming challenge -/
def longestConsecutiveSum (l : List Nat) : Nat := longestConsecutiveSumAux l 0 0 0 0

#eval greatestConsecutiveSum [1, 2, 3, 100, 7, 8] -- 15
#eval longestConsecutiveSum [1, 2, 3, 4, 100, 7, 8, 9, 10, 2, 3, 4, 5, 6] -- 20
