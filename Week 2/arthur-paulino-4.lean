@[simp] def List.pop : List α → List α × Option α
  | a :: t => (t, a)
  | _      => ([], none)

@[simp] def List.push : List α → Option α → List α
  | l, some a => (a :: l)
  | l, none   => l

@[simp] def List.ascending {α : Type} [LT α] : List α → Prop
  | a :: b :: t => a < b ∧ ascending (b :: t)
  | _           => True

theorem List.nonEmptyIff {l : List α} : l ≠ [] ↔ 0 ≠ l.length := sorry

theorem Nat.zeroNeSumOne {a : Nat} : 0 ≠ a + 1 := by
  simp [Ne.symm, succ_ne_zero a]

inductive Tower | L | M | R

open Tower

instance : ToString Tower where
  toString := fun t => match t with
    | L => "L" | M => "M" | R => "R"

abbrev Move := Tower × Tower

structure Hanoi where
  (l : List Nat) (m : List Nat) (r : List Nat)

namespace Hanoi

def new (n : Nat) : Hanoi :=
  ⟨List.range n, [], []⟩

def solve' : Tower × Tower × Tower → Nat → List Move → List Move
  | _ ,           0,     m => m
  | ⟨t₁, t₂, t₃⟩, n + 1, m =>
    solve' ⟨t₂, t₁, t₃⟩ n ((t₁, t₃) :: (solve' ⟨t₁, t₃, t₂⟩ n m))

def solve (n : Nat) : List Move :=
  solve' ⟨L, M, R⟩ n [] |>.reverse

def apply : Hanoi → Move → Hanoi
  | han, (L, M) => let pop := han.l.pop; ⟨pop.fst, han.m.push pop.snd, han.r⟩
  | han, (L, R) => let pop := han.l.pop; ⟨pop.fst, han.m, han.r.push pop.snd⟩
  | han, (M, L) => let pop := han.m.pop; ⟨han.l.push pop.snd, pop.fst, han.r⟩
  | han, (M, R) => let pop := han.m.pop; ⟨han.l, pop.fst, han.r.push pop.snd⟩
  | han, (R, L) => let pop := han.r.pop; ⟨han.l.push pop.snd, han.m, pop.fst⟩
  | han, (R, M) => let pop := han.r.pop; ⟨han.l, han.m.push pop.snd, pop.fst⟩
  | han, _      => han

def applyMoves' : List Hanoi → List Move → List Hanoi
  | han :: hans, m :: ms => (han.apply m) :: (applyMoves' (han :: hans) ms)
  | hans, [] => hans
  | [], _ => []

def applyMoves (han : Hanoi) (ms : List Move) : List Hanoi :=
  applyMoves' [han] ms

@[simp] def isStart (han : Hanoi) : Prop :=
  han.l.ascending ∧ han.m = [] ∧ han.r = []

@[simp] def isSolved (han : Hanoi) : Prop :=
  han.l = [] ∧ han.m = [] ∧ han.r.ascending

@[simp] def isValid (han : Hanoi) : Prop :=
  han.l.ascending ∧ han.m.ascending ∧ han.r.ascending

def areValid : List (Hanoi) → Prop
  | han :: hans => han.isValid ∧ areValid hans
  | []          => True

@[simp] def solutionOf (n : Nat) : List Hanoi :=
  (Hanoi.new n).applyMoves (solve n)

theorem validOfStart {han : Hanoi} (h : han.isStart) :
  han.isValid := by simp at h; simp [h]

theorem validOfSolved {han : Hanoi} (h : han.isSolved) :
  han.isValid := by simp at h; simp [h]

theorem sizeOfSolutionSucc {n : Nat} :
    (solutionOf (n + 1)).length = 2 * (solutionOf n).length + 1 := sorry

theorem solutionNotEmpty {n : Nat} : solutionOf n ≠ [] := by
  cases n with
    | zero => simp [applyMoves, applyMoves']
    | succ m =>
      -- relying on `sizeOfSolutionSucc`, really?! this should be much weaker!
      rw [List.nonEmptyIff, sizeOfSolutionSucc]
      simp [Nat.zeroNeSumOne]

theorem solvedForAll {n : Nat} :
  (solutionOf n).head solutionNotEmpty |>.isSolved := sorry

theorem validForAll {n : Nat} : areValid (solutionOf n) := sorry

end Hanoi
