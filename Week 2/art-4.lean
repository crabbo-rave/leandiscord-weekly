/-
An exhaustive description of all possible moves in the game.

Moves of the form `move__nil` are to towers that are empty, while moves of the form
`move__cons` are to towers having at least one disc. The condition of the larger discs being below the
smaller ones is enforced in the latter case.
-/
inductive TowersOfHanoi (n : Nat) : List Nat → List Nat → List Nat → Type _

  | move₁₂nil {a : Nat} {as cs : List Nat} :
    TowersOfHanoi n (a :: as) [] cs → TowersOfHanoi n as [a] cs

  | move₁₂cons {a b : Nat} {as bs cs : List Nat} :
    (a < b) → TowersOfHanoi n (a :: as) (b :: bs) cs → TowersOfHanoi n as (a :: b :: bs) cs

  | move₁₃nil {a : Nat} {as bs : List Nat} :
    TowersOfHanoi n (a :: as) bs [] → TowersOfHanoi n as bs [a]

  | move₁₃cons {a b : Nat} {as bs cs : List Nat} :
    (a < c) → TowersOfHanoi n (a :: as) bs (c :: cs) → TowersOfHanoi n as bs (a :: c :: cs)

  | move₂₃nil {b : Nat} {as bs : List Nat} :
    TowersOfHanoi n as (b :: bs) [] → TowersOfHanoi n as bs [b]

  | move₂₃cons {b c : Nat} {as bs cs : List Nat} :
    (b < c) → TowersOfHanoi n as (b :: bs) cs → TowersOfHanoi n as bs (b :: c :: cs)

  | move₃₂nil {c : Nat} {as cs : List Nat} :
    TowersOfHanoi n as [] (c :: cs) → TowersOfHanoi n as [c] cs

  | move₃₂cons {b c : Nat} {as bs cs : List Nat} :
    (c < b) → TowersOfHanoi n as (b :: bs) (c :: cs) → TowersOfHanoi n as (c :: b :: bs) cs

  | move₂₁nil {b : Nat} {bs cs : List Nat} :
    TowersOfHanoi n [] (b :: bs) cs → TowersOfHanoi n [b] bs cs

  | move₂₁cons {a b : Nat} {as bs cs : List Nat} :
    (b < a) → TowersOfHanoi n (a :: as) (b :: bs) cs → TowersOfHanoi n (b :: a :: as) bs cs

  | move₃₁nil {c : Nat} {bs cs : List Nat} :
    TowersOfHanoi n [] bs (c :: cs) → TowersOfHanoi n [c] bs cs

  | move₃₁cons {a c : Nat} {as bs cs : List Nat} :
    (c < a) → TowersOfHanoi n (a :: as) bs  (c :: cs) → TowersOfHanoi n (c :: a :: as) bs cs


open TowersOfHanoi

/-
Custom tactics for playing the game.

The `moveXY` tactic invokes the built-in `apply` tactic
which uses a function `f : α → β` to convert a goal `⊢ β` to `⊢ α`.

This is the reason the constructors of the form `moveYX`` are applied.
-/

section movetactics

macro "moveAB" : tactic => `(first
                               | apply move₂₁cons ; simp
                               | apply move₂₁nil)

macro "moveAC" : tactic => `(first
                               | apply move₃₁cons ; simp
                               | apply move₃₁nil)

macro "moveBA" : tactic => `(first
                               | apply move₁₂cons ; simp
                               | apply move₁₂nil)

macro "moveBC" : tactic => `(first
                               | apply move₃₂cons ; simp
                               | apply move₃₂nil)

macro "moveCA" : tactic => `(first
                               | apply move₁₃cons ; simp
                               | apply move₁₃nil)

macro "moveCB" : tactic => `(first
                               | apply move₂₃cons ; simp
                               | apply move₂₃nil)

macro "done" : tactic => `(assumption)

end movetactics


-- an example of the game in action
example (goal : TowersOfHanoi 2 [] [] [0, 1]) : TowersOfHanoi 2 [0, 1] [] [] := by
  moveAC
  moveAB
  moveCA
  moveBC
  moveAC
  done

theorem moveStack {n : Nat} {as bs cs as' bs' cs' : List Nat} (αs βs γs : List Nat)
  (init : TowersOfHanoi n as bs cs) (final : TowersOfHanoi n as' bs' cs') :
  (TowersOfHanoi n (as ++ αs) (bs ++ βs) (cs ++ γs)) → (TowersOfHanoi n (as' ++ αs) (bs' ++ βs) (cs' ++ γs)) := by
  intro moves
  sorry
