import Mathlib

/-! # APM t93A04: a line with smooth inverse image

## Statement repairs

None.

## Encoding notes

The domain is a genuine finite-dimensional Mathlib smooth manifold. A smooth
inverse image is certified by transversality to an actual affine line: at each
point mapping to the line, the image of the manifold derivative together with
the line direction spans `ℝ³`. This is the concrete regular-preimage
criterion, with the subset pinned to the actual set-theoretic inverse image.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t93a04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t93a04_Model (n : ℕ) := 𝓘(ℝ, apm_t93a04_E n)
abbrev apm_t93a04_Point := EuclideanSpace ℝ (Fin 3)

def apm_t93a04_line (p v : apm_t93a04_Point) : Set apm_t93a04_Point :=
  {x | ∃ t : ℝ, x = p + t • v}

def apm_t93a04_IsSmoothLinePreimage
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (apm_t93a04_E n) M]
    (f : M → apm_t93a04_Point) (ℓ : Set apm_t93a04_Point) (S : Set M) : Prop :=
  S = f ⁻¹' ℓ ∧
    ∃ (p v : apm_t93a04_Point),
      v ≠ 0 ∧ ℓ = apm_t93a04_line p v ∧
      ∀ x : M, f x ∈ ℓ →
        LinearMap.range
            (mfderiv (apm_t93a04_Model n) (𝓘(ℝ, apm_t93a04_Point)) f x).toLinearMap ⊔
          Submodule.span ℝ ({v} : Set apm_t93a04_Point) = ⊤

theorem apm_t93a04 :
    ∀ (n : ℕ) (M : Type)
      [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (apm_t93a04_E n) M]
      [IsManifold (apm_t93a04_Model n) ∞ M]
      (f : M → apm_t93a04_Point),
      ContMDiff (apm_t93a04_Model n) (𝓘(ℝ, apm_t93a04_Point)) ∞ f →
      ∃ ℓ : Set apm_t93a04_Point,
        apm_t93a04_IsSmoothLinePreimage (n := n) f ℓ (f ⁻¹' ℓ) := by
  sorry
