import Mathlib

open Matrix

noncomputable section

def apmIntegralMatrix {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, A i j = z

noncomputable def apmReduction (n : Type*) [Fintype n] [DecidableEq n]
    (p m : ℕ) (h : p ^ (m - 1) ∣ p ^ m) :
    Matrix.GeneralLinearGroup n (ZMod (p ^ m)) →*
      Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom h _)

theorem apm_b96a01 :
    (∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι))) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹)) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ) := by
  sorry
