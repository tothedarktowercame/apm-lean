import Mathlib

/-!
# APM m02J02

## Statement repairs

None.  "Basis" is made precise as a linearly independent family whose finite
linear span is dense in the `H¹` graph norm.  No orthogonality is asserted:
the Hermite functions are a natural complete family on the unbounded domains,
but are not orthogonal for the ordinary `H¹` inner product.

## Encoding notes

Because Mathlib has no packaged Sobolev-space type, `H¹₀(Ω)` is encoded
directly as value/weak-derivative pairs that are graph-norm limits of smooth
compactly supported functions.  Thus the central Sobolev object is retained,
including its distributional derivative and closure definition.
-/

open MeasureTheory Polynomial Set
open scoped BigOperators ContDiff ENNReal

def apm_m02j02_IsWeakDerivativeOn (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m02j02_InH10 (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  MemLp u 2 (volume.restrict s) ∧ MemLp du 2 (volume.restrict s) ∧
  apm_m02j02_IsWeakDerivativeOn s u du ∧
  ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ s ∧
    eLpNorm (u - φ) 2 (volume.restrict s) +
      eLpNorm (du - deriv φ) 2 (volume.restrict s) < ENNReal.ofReal ε

def apm_m02j02_IsH10Basis
    (s : Set ℝ) (e de : ℕ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, apm_m02j02_InH10 s (e n) (de n)) ∧
  LinearIndependent ℝ (fun n ↦ (e n, de n)) ∧
  ∀ u du : ℝ → ℝ, apm_m02j02_InH10 s u du →
    ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
      eLpNorm (u - c.sum fun n a ↦ a • e n) 2 (volume.restrict s) +
        eLpNorm (du - c.sum fun n a ↦ a • de n) 2 (volume.restrict s) <
          ENNReal.ofReal ε

noncomputable def apm_m02j02_sine (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_sineDeriv (n : ℕ) (x : ℝ) : ℝ :=
  (n + 1 : ℝ) * Real.pi * Real.cos ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.eval x ((Polynomial.hermite n).map (Int.castRingHom ℝ)) *
    Real.exp (-(x ^ 2) / 4)

noncomputable def apm_m02j02_hermiteFunctionDeriv (n : ℕ) (x : ℝ) : ℝ :=
  deriv (apm_m02j02_hermiteFunction n) x

theorem apm_m02j02 :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
        apm_m02j02_sine apm_m02j02_sineDeriv ∧
    apm_m02j02_IsH10Basis (Ioi (0 : ℝ))
        (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
        (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) ∧
    apm_m02j02_IsH10Basis (Set.univ : Set ℝ)
        apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv := by
  sorry
