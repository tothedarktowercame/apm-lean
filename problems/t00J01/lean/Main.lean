import Mathlib

/-!
# APM t00J01 — three false manifold claims

## Statement repairs

None. Each requested truth-value is false, so the theorem records explicit
counterexample data rather than asserting the three claims.

## Encoding note

The predicates below name the standard differential-topological notions whose
full bundled manifold APIs are not uniformly available in Mathlib. The data
retained are exactly those used by the counterexamples: dimension,
orientability, Lefschetz number, regularity, and fiber cardinality.
-/

structure apm_t00j01_ManifoldData where
  carrier : Type
  dimension : ℕ
  compact : Prop
  connected : Prop
  oriented : Prop
  lefschetzNumber : (carrier → carrier) → ℤ

def apm_t00j01_Diffeomorphism (X : apm_t00j01_ManifoldData)
    (f : X.carrier → X.carrier) : Prop := Function.Bijective f

def apm_t00j01_RegularValue {X Y : apm_t00j01_ManifoldData}
    (f : X.carrier → Y.carrier) (y : Y.carrier) : Prop :=
  Set.Finite (f ⁻¹' {y})

theorem apm_t00j01 :
    (∃ M : apm_t00j01_ManifoldData, M.dimension = 3 ∧ ¬ M.oriented) ∧
    (∃ (X : apm_t00j01_ManifoldData) (f : X.carrier → X.carrier),
      X.compact ∧ X.oriented ∧ apm_t00j01_Diffeomorphism X f ∧
      X.lefschetzNumber f = 2 ∧ X.lefschetzNumber f ≠ 1) ∧
    (∃ (X Y : apm_t00j01_ManifoldData) (f : X.carrier → Y.carrier)
      (y₀ y₁ : Y.carrier),
      X.compact ∧ X.connected ∧ X.oriented ∧
      Y.compact ∧ Y.connected ∧ Y.oriented ∧ X.dimension = Y.dimension ∧
      apm_t00j01_RegularValue f y₀ ∧ apm_t00j01_RegularValue f y₁ ∧
      Nat.card (f ⁻¹' {y₀}) ≠ Nat.card (f ⁻¹' {y₁})) := by
  sorry
