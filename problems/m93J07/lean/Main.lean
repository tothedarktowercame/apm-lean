import Mathlib
import Mathlib.Topology.Bases

open MeasureTheory

/-!
# APM m93J07 — a Banach-space and `Lᵖ` example zoo

## Statement repairs

None.  The two impossible requests are represented as nonexistence claims.

## Encoding note

Banach spaces are bundled below so separability and surjectivity of the
canonical map into the continuous bidual can be stated without assuming the
very properties whose examples the problem asks us to distinguish.
-/

structure apm_m93j07_Banach where
  carrier : Type
  normedAddCommGroup : NormedAddCommGroup carrier
  normedSpace : NormedSpace ℝ carrier
  completeSpace : CompleteSpace carrier

attribute [instance] apm_m93j07_Banach.normedAddCommGroup
  apm_m93j07_Banach.normedSpace apm_m93j07_Banach.completeSpace

def apm_m93j07_Reflexive (X : apm_m93j07_Banach) : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X.carrier)

def apm_m93j07_Separable (X : apm_m93j07_Banach) : Prop :=
  Nonempty (TopologicalSpace.SeparableSpace X.carrier)

def apm_m93j07_DualSeparable (X : apm_m93j07_Banach) : Prop :=
  Nonempty (TopologicalSpace.SeparableSpace (StrongDual ℝ X.carrier))

theorem apm_m93j07 :
    (∃ X : apm_m93j07_Banach, ¬ apm_m93j07_Separable X) ∧
    (∃ X : apm_m93j07_Banach,
      apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
    (∃ X : apm_m93j07_Banach,
      apm_m93j07_Separable X ∧ ¬ apm_m93j07_DualSeparable X) ∧
    (¬ ∃ X : apm_m93j07_Banach,
      ¬ apm_m93j07_Separable X ∧ apm_m93j07_DualSeparable X) ∧
    (let H := Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1));
      (∃ Φ : H →ₗ[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ) ∧
      (∃ Φ : H →L[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ)) ∧
    (∃ f : ℝ → ℝ, MemLp f 2 volume ∧ ¬ MemLp f 4 volume) ∧
    (∃ f : ℝ → ℝ, MemLp f 4 volume ∧ ¬ MemLp f 2 volume) ∧
    (∃ f : ℝ → ℝ,
      MemLp f 2 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 4 (volume.restrict (Set.Icc 0 1))) ∧
    (¬ ∃ f : ℝ → ℝ,
      MemLp f 4 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 2 (volume.restrict (Set.Icc 0 1))) := by
  have hfiniteLp : ¬ ∃ f : ℝ → ℝ,
      MemLp f 4 (volume.restrict (Set.Icc 0 1)) ∧
      ¬ MemLp f 2 (volume.restrict (Set.Icc 0 1)) := by
    rintro ⟨f, hf4, hf2⟩
    exact hf2 (hf4.mono_exponent (by norm_num))
  /-
  Boundary: the remaining ten clauses require bundling concrete Banach
  spaces with separability/reflexivity proofs, including a nonseparable
  Hilbert space and the theorem that separability of `StrongDual ℝ X`
  forces separability of `X`. They also require a concrete bounded operator
  on the restricted-measure `Lp` space with dense proper range, plus three
  explicit power-singularity/tail functions with exact `MemLp` and
  non-`MemLp` calculations.

  I searched the `MemLp` comparison API and used
  `MemLp.mono_exponent` above to prove the finite-measure impossibility.
  I did not find compiled sibling constructions covering the bundled
  separability/reflexivity examples or the required `Lp` multiplication
  operator and power-integrability calculations within this pass.
  -/
  have hremaining :
      (∃ X : apm_m93j07_Banach, ¬ apm_m93j07_Separable X) ∧
      (∃ X : apm_m93j07_Banach,
        apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
      (∃ X : apm_m93j07_Banach,
        ¬ apm_m93j07_Separable X ∧ apm_m93j07_Reflexive X) ∧
      (∃ X : apm_m93j07_Banach,
        ¬ apm_m93j07_Separable X ∧ ¬ apm_m93j07_Reflexive X) ∧
      (∃ X : apm_m93j07_Banach,
        apm_m93j07_Separable X ∧ ¬ apm_m93j07_DualSeparable X) ∧
      (¬ ∃ X : apm_m93j07_Banach,
        ¬ apm_m93j07_Separable X ∧ apm_m93j07_DualSeparable X) ∧
      (let H := Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1));
        (∃ Φ : H →ₗ[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ) ∧
        (∃ Φ : H →L[ℝ] H, DenseRange Φ ∧ ¬ Function.Surjective Φ)) ∧
      (∃ f : ℝ → ℝ, MemLp f 2 volume ∧ ¬ MemLp f 4 volume) ∧
      (∃ f : ℝ → ℝ, MemLp f 4 volume ∧ ¬ MemLp f 2 volume) ∧
      (∃ f : ℝ → ℝ,
        MemLp f 2 (volume.restrict (Set.Icc 0 1)) ∧
        ¬ MemLp f 4 (volume.restrict (Set.Icc 0 1))) := by
    sorry
  exact ⟨hremaining.1, hremaining.2.1, hremaining.2.2.1,
    hremaining.2.2.2.1, hremaining.2.2.2.2.1,
    hremaining.2.2.2.2.2.1, hremaining.2.2.2.2.2.2.1,
    hremaining.2.2.2.2.2.2.2.1, hremaining.2.2.2.2.2.2.2.2.1,
    hremaining.2.2.2.2.2.2.2.2.2, hfiniteLp⟩
