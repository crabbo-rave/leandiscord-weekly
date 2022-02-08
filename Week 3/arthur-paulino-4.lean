import Mathlib.Logic.Basic

variable {α : Type} [LT α] [LE α] [DecidableRel $ @LT.lt α _] [DecidableRel $ @LE.le α _]

-- mathlib3 stuff (not ported yet)
theorem not_le {a b : α} : ¬ a ≤ b ↔ b < a := sorry
theorem lt_min_iff {a b c : α} : a < min b c ↔ (a < b ∧ a < c) := sorry
theorem max_lt_iff {a b c : α} : max a b < c ↔ (a < c ∧ b < c) := sorry

theorem leOfLes {a₁ a₁' a₂ a₂' : α}
    (h : ¬(a₂ ≤ a₁' ∨ a₂' ≤ a₁))
    (hle  : (a₁, a₂).1 < (a₁, a₂).2)
    (hle' : (a₁', a₂').1 < (a₁', a₂').2) :
    (max a₁ a₁', min a₂ a₂').fst < (max a₁ a₁', min a₂ a₂').snd := by
  rw [not_or_distrib] at h
  simp only [not_le] at h
  simp only [lt_min_iff, max_lt_iff]
  cases h
  constructor
  all_goals (constructor assumption assumption)

/- This structure characterizes my open interval -/
structure Interval (α : Type) [LT α] where
  i  : α × α
  le : i.1 < i.2

/- A set is a list of intervals -/
abbrev Set α [LT α] := List (Interval α)

namespace Set

/- Whether a set contains a cetain element -/
def hasMem : Set α → α → Prop 
  | ⟨(a₁, a₂), _⟩ :: is, a => (a₁ < a ∧ a < a₂) ∨ hasMem is a
  | []                 , _ => False

theorem hasMemOfAppendRight {S S' : Set α} (h : hasMem S a) :
    hasMem (S' ++ S) a := by
  induction S' with
    | nil         => exact h
    | cons _ _ hi => exact Or.inr hi

theorem hasMemOfAppendLeft {S S' : Set α} (h : hasMem S a) :
    hasMem (S ++ S') a := by
  induction S with
    | nil          => simp only [hasMem] at *
    | cons i ss hi =>
      cases h
      refine Or.inl $ by assumption
      refine Or.inr $ hi $ by assumption

theorem hasMemOrOfAppend {S S' : Set α} (h : hasMem (S ++ S') a) :
    hasMem S a ∨ hasMem S' a := by
  induction S with
    | nil =>
      simp [hasMem] at *
      exact h
    | cons i ss hi =>
      cases h
      refine Or.inl $ Or.inl (by assumption)
      have hor : hasMem ss a ∨ hasMem S' a := by refine hi $ by assumption
      cases hor
      refine Or.inl $ Or.inr (by assumption)
      refine Or.inr $ by assumption

/- Removes parts of a set that are outside of a certain interval -/
def prune : Set α → Interval α → Set α
  | ⟨(a₁, a₂), hle⟩ :: Ss, ⟨(a₁', a₂'), hle'⟩ =>
    if h : a₂ ≤ a₁' ∨ a₂' ≤ a₁ then
      -- throwing current interval away
      prune Ss ⟨(a₁', a₂'), hle'⟩
    else
      -- pruning cutting current interval
      ⟨(max a₁ a₁', min a₂ a₂'), leOfLes h hle hle'⟩ :: (prune Ss ⟨(a₁', a₂'), hle'⟩)
  | [], _ => []

theorem hasMemOfPrune {S : Set α} {i : Interval α} {a : α} (h : (S.prune i).hasMem a) :
    S.hasMem a := sorry

theorem hasMemOfPruneWith {S : Set α} {i : Interval α} {a : α}
    (h : S.hasMem a) (hi : i.i.1 < a ∧ a < i.i.2) :
    (S.prune i).hasMem a := sorry

theorem inLimitsOfHasMemPrune {S : Set α} {i : Interval α}
    (h : hasMem (prune S i) a) :
    i.1.1 < a ∧ a < i.1.2 := sorry

/- (A₁ ∪ A₂ ∪ ⋯) ∩ (B₁ ∪ B₂ ∪ ⋯) = ((A₁ ∪ A₂ ∪ ⋯) ∩ B₁) ∪ ((A₁ ∪ A₂ ∪ ⋯) ∩ B₂) ∪ ⋯ -/
def intersec : Set α → Set α → Set α
  | Ss, i :: Ss' => (Ss.prune i) ++ Ss.intersec Ss'
  | _, _         => []

theorem intersecIsCorrectMP {S₁ S₂ : Set α} {a : α}
    (h : S₁.hasMem a ∧ S₂.hasMem a) :
    (S₁.intersec S₂).hasMem a := by
  induction S₂ with
    | nil => simp [hasMem] at *
    | cons i ss hi =>
      have h₁ := h.1
      have h₂ := h.2
      cases h₂
      refine hasMemOfAppendLeft $ by refine hasMemOfPruneWith h₁ (by assumption)
      refine hasMemOfAppendRight $ hi $ And.intro h₁ (by assumption)

theorem intersecIsCorrectMPR {S₁ S₂ : Set α} {a : α}
    (h : (S₁.intersec S₂).hasMem a) : S₁.hasMem a ∧ S₂.hasMem a := by
  constructor
  induction S₂ with
    | nil          => simp [hasMem] at *
    | cons i ss hi =>
      cases hasMemOrOfAppend h
      refine hasMemOfPrune $ by assumption
      refine hi $ by assumption
  induction S₂ with
    | nil         => simp [hasMem] at *
    | cons _ _ hi =>
      cases hasMemOrOfAppend h
      refine Or.inl $ inLimitsOfHasMemPrune $ by assumption
      refine Or.inr $ hi $ by assumption

theorem intersecIsCorrect {S₁ S₂ : Set α} {a : α} :
    S₁.hasMem a ∧ S₂.hasMem a ↔ (S₁.intersec S₂).hasMem a :=
  Iff.intro intersecIsCorrectMP intersecIsCorrectMPR

end Set
