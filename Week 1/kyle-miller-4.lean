/- Proving question -/

def sum_to : Nat → Nat
| 0 => 0
| n + 1 => sum_to n + n + 1

theorem sum_to_eq (n : Nat) : 2 * sum_to n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 2 * (sum_to n + n + 1) = _
    simp [Nat.mul_add, ih]
    simp [Nat.succ_mul, Nat.add_succ, Nat.mul_succ, Nat.succ_add, Nat.add_assoc]

/- Programming question -/

structure Run where
  max : Nat
  len : Nat
  sum : Nat
  best_len : Nat
  best_sum : Nat

def Run.init : Run where
  max := 0
  len := 0
  sum := 0
  best_len := 0
  best_sum := 0

def Run.commit (r : Run) : Run :=
  if r.len ≥ 2 && r.len > r.best_len then
    { r with best_len := r.len, best_sum := r.sum }
  else
    r

def Run.push (r : Run) (n : Nat) : Run :=
  if r.max + 1 == n then
    { r with
      max := n,
      len := r.len + 1,
      sum := r.sum + n }
  else
    { r.commit with
      max := n
      len := 1
      sum := n }

def Run.extract (r : Run) : Nat := r.commit.best_sum

def longest_consec_sublist_sum (l : List Nat) : Nat := (l.foldl Run.push Run.init).extract

#eval longest_consec_sublist_sum [1, 2, 3, 100, 7, 8] -- 6
#eval longest_consec_sublist_sum [1, 2, 3, 4, 100, 7, 8, 9, 10, 2, 3, 4, 5, 6] -- 20
