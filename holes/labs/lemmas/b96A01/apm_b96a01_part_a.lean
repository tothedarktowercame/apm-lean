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

-- BEGIN SEAT AREA
theorem apm_b96a01_part_a :
    ∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι)) := by
  sorry
-- END SEAT AREA

theorem apm_b96a01_part_b :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) := by
  sorry

theorem apm_b96a01_part_c :
    ∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a := by
  sorry

theorem apm_b96a01_part_d_nonabelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → ¬(∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  sorry

theorem apm_b96a01_part_d_abelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → (∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  sorry

theorem apm_b96a01_part_d :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  intro n _ _ G hG hs p hp hex
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · exact apm_b96a01_part_d_abelian n G hG hs hcomm p hp hex
  · exact apm_b96a01_part_d_nonabelian n G hG hs hcomm p hp

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
  exact ⟨apm_b96a01_part_a, apm_b96a01_part_b,
    apm_b96a01_part_c, apm_b96a01_part_d⟩

#print axioms apm_b96a01
