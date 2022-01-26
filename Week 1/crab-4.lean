/- Function for the programming question. -/
def sumOfLongestSublistAux : List Nat → Nat → Nat → Nat → Nat → Nat 
    | [], _, _, _, totalSum => totalSum
    | [x], currLen, maxLen, currSum, totalSum => sumOfLongestSublistAux [] 0 0 0 (currSum+x)
    | x::y::xs, currLen, maxLen, currSum, totalSum =>
        if y=x+1 then
          sumOfLongestSublistAux (y::xs) (currLen+1) maxLen (currSum+x) totalSum
        else
          sumOfLongestSublistAux (y::xs) 0 (max currLen maxLen) 0 (if currLen < maxLen then totalSum else currSum)

def sumOfLongestSublist (list: List Nat) : Nat := 
      sumOfLongestSublistAux list 0 0 0 0

#eval sumOfLongestSublist [1,2,3,100,7,8,9,10] /- 34 -/
