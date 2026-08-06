import Mathlib

/-!
# APM m02A01: Weak and strong convergence

## Statement repairs

None.

## Encoding questions

None. Weak convergence uses Mathlib's genuine weak topology, and the strict
counterexample is the standard unit-vector sequence in the actual Banach space
`ℓ²(ℕ, ℝ)`.
-/

open Filter

noncomputable section

def apm_m02A01_weaklyConverges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : ℕ → X) (a : X) : Prop :=
  Tendsto (fun n ↦ toWeakSpace ℝ X (x n)) atTop
    (nhds (toWeakSpace ℝ X a))

abbrev apm_m02A01_l2 := lp (fun _ : ℕ ↦ ℝ) 2

def apm_m02A01_basisVector (n : ℕ) : apm_m02A01_l2 :=
  lp.single 2 n 1

theorem apm_m02a01 :
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a b : X),
      apm_m02A01_weaklyConverges x a →
      apm_m02A01_weaklyConverges x b → a = b) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a : X),
      Tendsto x atTop (nhds a) → apm_m02A01_weaklyConverges x a) ∧
    (apm_m02A01_weaklyConverges apm_m02A01_basisVector 0 ∧
      ¬Tendsto apm_m02A01_basisVector atTop (nhds 0)) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        [FiniteDimensional ℝ X] (x : ℕ → X) (a : X),
      apm_m02A01_weaklyConverges x a ↔ Tendsto x atTop (nhds a)) := by
  sorry
