macro_rules
  | `(ℕ) => `(Nat)

section ProvingQuestion

open Nat

@[reducible] def natsum : Nat → Nat
  | zero => zero
  | succ n => succ n + natsum n

theorem nat_sum_closed_form : ∀ n : ℕ, (succ (succ zero)) * (natsum n) = n * (succ n) := by
  intro n
  induction n with
    | zero => rfl
    | succ _ ih => rw [Nat.mul_add, ih, ← Nat.add_mul, Nat.mul_comm, Nat.succ_add, Nat.succ_add, Nat.zero_add]

end ProvingQuestion


section ProgrammingQuestion

variable {α : Type _} [LE α] [∀ a b : α, Decidable (a ≤ b)]

@[reducible] def List.isIncreasing : List α → Bool
  | [] => true
  | a :: [] => true
  | a :: b :: tail =>
    if h : a ≤ b then
      isIncreasing (b :: tail)
    else
      false

abbrev IncreasingList (α : Type _) [LE α] [∀ a b : α, Decidable (a ≤ b)] := { l : List α // List.isIncreasing l }

-- splits a list `ℓ` into an initial increasing stretch (possibly empty) and the rest of the list
def firstIncreasingStretch : (ℓ : List α) → {listpair : IncreasingList α × List α // ℓ = listpair.fst ++ listpair.snd}
  | [] => { val := (⟨[], rfl⟩ , []), property := rfl }
  | a :: [] => { val := (⟨[a], rfl⟩, []), property := rfl }
  | a :: b :: tail =>
    if h : a ≤ b then
      match firstIncreasingStretch (b :: tail) with
        | ⟨(⟨lInc, incPrf⟩, lTail), prf⟩ =>
          { val := (⟨a :: lInc, by admit⟩, lTail), property := by simp [prf] }
    else
      { val := (⟨[], rfl⟩, (a :: b :: tail)), property := rfl }

-- iteratively fetches maximal increasing stretches
partial def maximalIncreasingStretches : List α → List (IncreasingList α)
  | [] => []
  | a :: [] => []
  | a :: b :: tail =>
    if a ≤ b then
      match firstIncreasingStretch (a :: b :: tail) with
        | ⟨(lInc, lTail), _⟩ =>
          lInc :: (maximalIncreasingStretches lTail)
    else
      maximalIncreasingStretches (b :: tail)
-- termination_by

section Misc

def IncreasingList.LE (l₁ l₂ : IncreasingList α) := l₁.val.length ≤ l₂.val.length

instance inclLE : LE (IncreasingList α) := ⟨IncreasingList.LE⟩

instance [listDec : ∀ ℓ₁ ℓ₂ : List α, Decidable (ℓ₁.length ≤ ℓ₂.length)]
: ∀ l₁ l₂ : IncreasingList α, Decidable (l₁ ≤ l₂) := λ l₁ l₂ => by apply listDec

class Zero (α : Type _) where
  zero : α

instance : Zero Nat := ⟨Nat.zero⟩

instance : Zero Int := ⟨(0 : Int)⟩

def List.sum {α : Type _} [Add α] [Zero α] : List α → α :=
  List.foldl Add.add Zero.zero

prefix:100 "[∑]" => List.sum

class Min (α : Type _) where
  min : α

instance {α : Type _} : Min (List α) := ⟨List.nil⟩

instance : Min (IncreasingList α) := ⟨⟨[], rfl⟩⟩

def List.min {α : Type _} [LE α] [∀ a b : α, Decidable (a ≤ b)] [Min α] : List α → α :=
  List.foldl (λ a b => if a ≤ b then a else b) Min.min

def List.max {α : Type _} [LE α] [∀ a b : α, Decidable (a ≤ b)] [Min α] : List α → α :=
  List.foldl (λ a b => if b ≤ a then a else b) Min.min

end Misc

def ConsecutiveIncreasing : List Nat → Bool
  | [] => false
  | [a] => false
  | [a, b] => a ≤ b
  | a :: b :: tail =>
    if (b = Nat.succ a) then
      ConsecutiveIncreasing (b :: tail)
    else
      false


def LongestIncreasingStretchSum : List Nat → Nat :=
  λ l =>
  List.sum $ Subtype.val $ List.max $ (List.filter (ConsecutiveIncreasing ∘ Subtype.val) $ maximalIncreasingStretches l)


end ProgrammingQuestion
