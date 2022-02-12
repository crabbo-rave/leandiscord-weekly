/-
The definition of a totally ordered set.
-/
class TotalOrder (α : Type _) [LE α] [DecidableRel $ @LE.le α _] where
  (reflLE : ∀ a : α, a ≤ a)
  (antisymmLE : ∀ {a b : α}, a ≤ b → b ≤ a → a = b)
  (transLE : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
  (totalLE : ∀ a b : α, a ≤ b ∨ b ≤ a)

namespace TotalOrder

def max {α : Type _} [LE α] [DecidableRel $ @LE.le α _] : α → α → α
  | a, b =>
    if a ≤ b then
      b
    else
      a

def min {α : Type _} [LE α] [DecidableRel $ @LE.le α _] : α → α → α
  | a, b =>
    if a ≤ b then
      a
    else
      b

variable {α : Type} [LE α] [DecidableRel $ @LE.le α _] [TotalOrder α]
variable {a b x : α}

theorem notLE : ¬(a ≤ b) → b ≤ a :=
  λ h : ¬(a ≤ b) =>
    match TotalOrder.totalLE a b with
      | Or.inl h' => False.elim (h h')
      | Or.inr h' => h'

theorem max_symm : max a b = max b a := by
  byCases h:(a ≤ b) <;> byCases h':(b ≤ a) <;> simp [max, h, h']
  · apply TotalOrder.antisymmLE <;> assumption
  · apply TotalOrder.antisymmLE <;> (apply notLE ; assumption)

@[simp] theorem max_left_le : TotalOrder.max a b ≤ x → a ≤ x :=
  if h:(a ≤ b) then by
    simp [max, h]
    intro h'
    apply TotalOrder.transLE h h'
  else by
    simp [max, h]
    exact id

@[simp] theorem max_right_le : max a b ≤ x → b ≤ x := by
  byCases h:(a ≤ b) <;> simp [max, h]
  · exact id
  · intro h'
    apply TotalOrder.transLE (notLE h) h'

theorem min_symm : min a b = min b a := by
 byCases h:(a ≤ b) <;> byCases h':(b ≤ a) <;> simp [min, h, h']
  · apply TotalOrder.antisymmLE <;> assumption
  · apply TotalOrder.antisymmLE <;> (apply notLE ; assumption)

@[simp] theorem min_le_left : x ≤ min a b → x ≤ a := by
  byCases h:(a ≤ b) <;> simp [min, h]
  · exact id
  · intro h'
    apply TotalOrder.transLE
    · assumption
    · apply notLE ; assumption

@[simp] theorem min_le_right : x ≤ min a b → x ≤ b := by
  byCases h:(a ≤ b) <;> simp [min, h]
  · intro h'
    exact TotalOrder.transLE h' h
  · exact id

theorem both_le_max_le : a ≤ x → b ≤ x → (max a b) ≤ x := by
  intro ; intro ; byCases h:(a ≤ b) <;> simp [max, h] <;> assumption

theorem le_both_le_min : x ≤ a → x ≤ b → x ≤ (min a b) := by
  intro ; intro ; byCases h:(a ≤ b) <;> simp [min, h] <;> assumption

end TotalOrder
