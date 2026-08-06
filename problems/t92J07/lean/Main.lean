import Mathlib

/-!
# APM t92J07

## Statement repairs

The source has the evident typo `f_i : M_x → ℝ^m`; this is repaired to
`f_i : M_i → ℝ^m`. The usual Hausdorff and second-countable assumptions
implicit in "smooth manifold" are made explicit, since they are required by
Sard's theorem.

## Encoding questions

The domains are a genuinely countable family of finite-dimensional Mathlib
smooth manifolds, indexed by positive naturals, and regularity is expressed by
surjectivity of the actual manifold derivative. Mathlib has no general bundled
predicate for a subset being a smooth embedded submanifold, so only that final
predicate is isolated as a typed placeholder on the actual fiber subset.
-/

open Set
open scoped Manifold ContDiff

noncomputable section

abbrev apm_t92J07_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A regular value, expressed using surjectivity of the manifold derivative. -/
def apm_t92J07_IsRegularValue
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E m) (x : apm_t92J07_E m) : Prop :=
  ∀ p : M, f p = x →
    Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ (apm_t92J07_E n))
        (modelWithCornersSelf ℝ (apm_t92J07_E m)) f p)

/-- The assertion that a subset of a smooth manifold is a smooth embedded submanifold. -/
opaque apm_t92J07_IsSmoothSubmanifold
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M] (s : Set M) : Prop

theorem apm_t92j07
    (m : ℕ) (d : PNat → ℕ) (M : PNat → Type*)
    [∀ i, TopologicalSpace (M i)]
    [∀ i, T2Space (M i)]
    [∀ i, SecondCountableTopology (M i)]
    [∀ i, ChartedSpace (apm_t92J07_E (d i)) (M i)]
    [∀ i, IsManifold
      (modelWithCornersSelf ℝ (apm_t92J07_E (d i))) ∞ (M i)]
    (f : ∀ i, M i → apm_t92J07_E m)
    (hf : ∀ i, ContMDiff
      (modelWithCornersSelf ℝ (apm_t92J07_E (d i)))
      (modelWithCornersSelf ℝ (apm_t92J07_E m)) ∞ (f i)) :
    ∃ x : apm_t92J07_E m, ∀ i : PNat,
      apm_t92J07_IsRegularValue (n := d i) (m := m) (M := M i) (f i) x ∧
      apm_t92J07_IsSmoothSubmanifold (n := d i) (M := M i) ((f i) ⁻¹' {x}) := by
  sorry
