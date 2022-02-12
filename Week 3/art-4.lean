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

section Logic

theorem Or.assoc {a b c : Prop} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := Iff.intro
  (Or.rec (Or.rec Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr))
  (Or.rec (Or.inl ∘ Or.inl) (Or.rec (Or.inl ∘ Or.inr) Or.inr))

theorem And.assoc {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := Iff.intro
  (λ ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩)
  (λ ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩)

theorem And.right_distrib_or {a b c : Prop} : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := Iff.intro
  (λ ⟨hab, hc⟩ => Or.elim hab (λ ha => Or.inl ⟨ha, hc⟩) (λ hb => Or.inr ⟨hb, hc⟩))
  (Or.rec (λ ⟨ha, hc⟩ => ⟨Or.inl ha, hc⟩) (λ ⟨hb, hc⟩ => ⟨Or.inr hb, hc⟩))

theorem And.left_distrib_or {a b c : Prop} : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := Iff.intro
  (λ ⟨ha, hbc⟩ => Or.elim hbc (λ hb => Or.inl ⟨ha, hb⟩) (λ hc => Or.inr ⟨ha, hc⟩))
  (Or.rec (λ ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩) (λ ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩))

end Logic

variable {α : Type} [LE α] [DecidableRel $ @LE.le α _] [TotalOrder α]

/-
An inductive definition of a set (built up from intervals)
-/
inductive Set (α : Type _) [LE α] [DecidableRel $ @LE.le α _] [TotalOrder α]
  | null : Set α
  | interval : α × α → Set α
  | union : Set α → Set α → Set α
  | intersection : Set α → Set α → Set α
  deriving Repr, DecidableEq

def Set.mem (x : α) : Set α → Prop
  | Set.null  => False
  | Set.interval (a, b) => a ≤ x ∧ x ≤ b
  | Set.union u v => mem x u ∨ mem x v
  | Set.intersection u v => mem x u ∧ mem x v

def Set.ext : Set α → Set α → Prop
  | u, v =>
    ∀ a : α, Set.mem a u ↔ Set.mem a v

infix:20 " ≃ " => Set.ext

def Set.ext.refl (A : Set α) : A ≃ A := λ _ => ⟨id, id⟩
def Set.ext.symm {A B : Set α} : (A ≃ B) → (B ≃ A) := λ hAB => (λ _ => Iff.symm (hAB _))
def Set.ext.trans {A B C : Set α} : (A ≃ B) → (B ≃ C) → (A ≃ C) := λ hAB hBC => λ _ => (Iff.trans (hAB _) (hBC _))

instance Set.ext.Equivalence : Equivalence (@Set.ext α _ _ _) where
    refl  := Set.ext.refl
    symm  := Set.ext.symm
    trans := Set.ext.trans

instance ExtSetoid : Setoid (Set α) := ⟨@Set.ext α _ _ _, Set.ext.Equivalence⟩

def ExtSet (α : Type _) [LE α] [DecidableRel $ @LE.le α _] [TotalOrder α] :=
  Quotient (@ExtSetoid α _ _ _)

theorem Set.union.sound {a₁ b₁ a₂ b₂ : Set α} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
  Set.union a₁ b₁ ≃ Set.union a₂ b₂ := by
    simp [Set.ext, Set.mem] at *
    intro; rw [ha _, hb _]
    exact Iff.rfl

theorem Set.intersection.sound {a₁ b₁ a₂ b₂ : Set α} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
  Set.intersection a₁ b₁ ≃ Set.intersection a₂ b₂ := by
    simp [Set.ext, Set.mem] at *
    intro; rw [ha _, hb _]
    exact Iff.rfl

namespace ExtSet

def null : ExtSet α := Quotient.mk' Set.null

notation "⊘" => null

def interval : α × α → ExtSet α := λ i => Quotient.mk' (Set.interval i)

notation "["a"|"b"]" => interval (a, b)

def union : ExtSet α → ExtSet α → ExtSet α :=
  λ eu ev =>
  Quotient.lift₂
  (λ u v : Set α => Quotient.mk ExtSetoid (Set.union u v))
  (λ _ _ _ _ ha hb => Quotient.sound $ Set.union.sound ha hb)
  eu ev

infix:100 " ∪ " => union

def intersection : ExtSet α → ExtSet α → ExtSet α :=
  λ eu ev =>
  Quotient.lift₂
  (λ u v : Set α => Quotient.mk ExtSetoid (Set.intersection u v))
  (λ _ _ _ _ ha hb => Quotient.sound $ Set.intersection.sound ha hb)
  eu ev

infix:100 " ∩ " => intersection

def mem (a : α) : ExtSet α → Prop :=
  Quotient.lift (Set.mem a) (λ _ _ h => propext (h _))

infix:180 " ∈ " => mem

def ext {eu ev : ExtSet α} : (∀ a : α, a ∈ eu ↔ a ∈ ev) → eu = ev := by
  let ⟨u, hu⟩ := Quotient.exists_rep eu
  let ⟨v, hv⟩ := Quotient.exists_rep ev
  rw [← hu, ← hv]
  show (∀ a : α, Set.mem a u ↔ Set.mem a v) → (Quotient.mk ExtSetoid u = Quotient.mk ExtSetoid v)
  intro
  apply Quot.sound
  assumption

def mem.empty : ∀ a : α, (a ∈ ⊘) ↔ False := λ _ => Iff.rfl

def mem.interval {a b : α} : ∀ x : α, x ∈ [a|b] ↔ a ≤ x ∧ x ≤ b := λ _ => Iff.rfl

def mem.union {eu ev : ExtSet α} {a : α} : a ∈ (eu ∪ ev) ↔ (a ∈ eu) ∨ (a ∈ ev) := by
  let ⟨u, hu⟩ := Quotient.exists_rep eu
  let ⟨v, hv⟩ := Quotient.exists_rep ev
  rw [← hu, ← hv]
  exact Iff.rfl

 def mem.intersection {eu ev : ExtSet α} {a : α} : a ∈ (eu ∩ ev) ↔ (a ∈ eu) ∧ (a ∈ ev) := by
  let ⟨u, hu⟩ := Quotient.exists_rep eu
  let ⟨v, hv⟩ := Quotient.exists_rep ev
  rw [← hu, ← hv]
  exact Iff.rfl


theorem intersection.left_distrib_union {A B C : ExtSet α} : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ExtSet.ext; intro; simp [mem.union, mem.intersection, And.left_distrib_or]
theorem intersection.right_distrib_union {A B C : ExtSet α} : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
  apply ExtSet.ext; intro; simp [mem.union, mem.intersection, And.right_distrib_or]

theorem union.assoc {A B C : ExtSet α} : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply ExtSet.ext; intro; simp [mem.union, Or.assoc]

theorem inter.assoc {A B C : ExtSet α} : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply ExtSet.ext; intro; simp [mem.intersection, And.assoc]

theorem empty.left_inter {A : ExtSet α} : ⊘ ∩ A = ⊘ := by
  apply ExtSet.ext; intro; simp [mem.intersection, mem.empty]

theorem empty.right_inter {A : ExtSet α} : A ∩ ⊘ = ⊘ := by
  apply ExtSet.ext; intro; simp [mem.intersection, mem.empty]

theorem empty.left_union {A : ExtSet α} : ⊘ ∪ A = A := by
  apply ExtSet.ext; intro; simp [mem.union, mem.empty]

theorem empty.right_union {A : ExtSet α} : A ∪ ⊘ = A := by
  apply ExtSet.ext; intro; simp [mem.union, mem.empty]

end ExtSet


abbrev Interval α := α × α

def Interval.toSet : Interval α → ExtSet α :=
  λ ⟨a, b⟩ => [a|b]

instance : Coe (Interval α) (ExtSet α) := ⟨Interval.toSet⟩

def Interval.intersect : Interval α → Interval α → Interval α
  | (a, b), (c, d) => (TotalOrder.max a c, TotalOrder.min b d)

theorem Interval.intersect.correct : ∀ (i₁ i₂ : Interval α),
  (Interval.intersect i₁ i₂).toSet = (i₁.toSet ∩ i₂.toSet) := by
    intro (a, b)
    intro (c, d)
    simp [Interval.intersect, Interval.toSet]
    apply ExtSet.ext
    intro x
    apply Iff.intro
    · intro ⟨x_l, x_r⟩
      apply And.intro
      apply And.intro
      · apply TotalOrder.max_left_le x_l
      · apply TotalOrder.min_le_left x_r
      apply And.intro
      · apply TotalOrder.max_right_le x_l
      · apply TotalOrder.min_le_right x_r
    · intro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      apply And.intro
      · apply TotalOrder.both_le_max_le h₁ h₃
      · apply TotalOrder.le_both_le_min h₂ h₄


abbrev Intervals α := List (Interval α)

def Intervals.union : List (Interval α) → ExtSet α
  | []      => ⊘
  | i :: is => i.toSet ∪ (union is)
--  List.foldl (Set.union) ⊘ ∘ List.map (Interval.toSet)

prefix:250 "⋃ " => Intervals.union

theorem Intervals.unionAppend {li₁ li₂ : List (Interval α)} : ⋃ (li₁ ++ li₂) = ⋃ li₁ ∪ ⋃ li₂ := by
  induction li₁ with
    | nil => simp [List.append, Intervals.union, ExtSet.empty.left_union]
    | cons li lis ih => simp [Intervals.union]; rw [ExtSet.union.assoc, ← ih];  rfl

def Intervals.intersectInterval : Intervals α → Interval α → Intervals α
  |   []   , _ => []
  | i :: is, ι  => (Interval.intersect i ι) :: (intersectInterval is ι)

theorem Intervals.intersectInterval.correct {I : Intervals α} (ι : Interval α) : ⋃(I.intersectInterval ι) = (⋃I ∩ ι.toSet) := by
  induction I with
    | nil =>
      simp [Intervals.intersectInterval, Intervals.union, ExtSet.empty.left_inter]
    | cons i is ih =>
      simp [Intervals.intersectInterval, Intervals.union]
      rw [ExtSet.intersection.right_distrib_union, ← ih, Interval.intersect.correct]

def Intervals.intersect : Intervals α → Intervals α → Intervals α
  | is, []    => []
  | is, ι :: ιs => (intersectInterval is ι) ++ intersect is ιs

theorem Intervals.intersect.correct {I₁ I₂ : Intervals α} : ⋃(Intervals.intersect I₁ I₂) = ⋃I₁ ∩ ⋃I₂ := by
  induction I₂ with
    | nil =>
      simp [Intervals.intersect, Intervals.union, ExtSet.empty.right_inter]
    | cons ι ιs ih =>
      simp [Intervals.union]
      rw [ExtSet.intersection.left_distrib_union, ← ih, ← Intervals.intersectInterval.correct]
      simp [Intervals.intersect, Intervals.unionAppend]
