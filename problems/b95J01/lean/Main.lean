import Mathlib

/-! # APM b95J01: powers landing in a finite-index subgroup

## Statement repairs

None.
-/

noncomputable section

/-- The standard non-normal index-three subgroup of `S₃`. -/
def b95j01CounterexampleSubgroup : Subgroup (Equiv.Perm (Fin 3)) :=
  Subgroup.zpowers (Equiv.swap 0 1)

/-- The involution used in the counterexample. -/
def b95j01CounterexampleElement : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- Existence and divisibility of the least positive exponent, its stronger
normal-subgroup divisibility property, and the requested explicit counterexample. -/
theorem apm_b95j01
    (G : Type*) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    (∀ g : G, ∃ k : ℕ,
      0 < k ∧ g ^ k ∈ H ∧
      (∀ l : ℕ, 0 < l → g ^ l ∈ H → k ≤ l) ∧
      (∀ m : ℤ, g ^ m ∈ H → (k : ℤ) ∣ m) ∧
      (H.Normal → k ∣ H.index)) ∧
    (¬ b95j01CounterexampleSubgroup.Normal ∧
      b95j01CounterexampleSubgroup.index = 3 ∧
      b95j01CounterexampleElement ∉ b95j01CounterexampleSubgroup ∧
      b95j01CounterexampleElement ^ 2 ∈ b95j01CounterexampleSubgroup ∧
      ¬ 2 ∣ b95j01CounterexampleSubgroup.index) := by
  sorry
