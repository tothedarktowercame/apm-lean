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
smooth manifolds, indexed by positive naturals. A fiber is certified as a
smooth submanifold by the concrete regular-value criterion: it is pinned to
the actual preimage and the actual manifold derivative is surjective at every
point of that fiber.
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

/-- A concrete regular-level-set certificate for a smooth fiber submanifold. -/
def apm_t92J07_IsSmoothRegularFiber
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E m) (x : apm_t92J07_E m) (s : Set M) : Prop :=
  s = f ⁻¹' {x} ∧
    apm_t92J07_IsRegularValue (n := n) (m := m) f x

@[simp] lemma apm_t92J07_isSmoothRegularFiber_preimage_iff
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E m) (x : apm_t92J07_E m) :
    apm_t92J07_IsSmoothRegularFiber (n := n) (m := m) f x (f ⁻¹' {x}) ↔
      apm_t92J07_IsRegularValue (n := n) (m := m) f x := by
  simp [apm_t92J07_IsSmoothRegularFiber]

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
      apm_t92J07_IsSmoothRegularFiber (n := d i) (m := m) (M := M i)
        (f i) x ((f i) ⁻¹' {x}) := by
  /-
  CLOSER HOP 1 boundary. The regular-fiber packaging is now eliminated by
  `apm_t92J07_isSmoothRegularFiber_preimage_iff`: for the actual preimage used
  in the frozen theorem, the conclusion is definitionally just common regular
  value regularity.

  The intended remaining proof assigns to each `i : PNat` the set of critical
  values of `f i`. Manifold Sard makes each such set Lebesgue-null; countable
  union nullity then shows their union cannot cover `ℝ^m` (for `m = 0`, the
  target is a singleton and every derivative to the zero-dimensional space is
  automatically surjective). Choosing a point outside the union supplies the
  common regular value, after which the lemma above closes every fiber.

  Mathlib's `MeasureTheory/Function/Jacobian.lean` and
  `Topology/MetricSpace/HausdorffDimension.lean` provide Sard-type statements
  for maps between finite-dimensional normed vector spaces. They do not apply
  to an arbitrary manifold domain `M i`, and searches found no chartwise
  manifold Sard theorem converting `ContMDiff` and second countability into
  nullity of the `mfderiv` critical-value set. Applying the vector-space result
  chart by chart would require a countable atlas, measurability of each chart's
  critical image, compatibility between `mfderiv` surjectivity and chart
  derivatives, and countable-null-union bookkeeping.

  Searches covered `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  Sard/regular-value siblings (`a94A05`, `t01A08`, `t01J04`, `t96J05`),
  Mathlib's Jacobian, Hausdorff-dimension, manifold derivative/chart,
  second-countability, null-union, and Euclidean measure APIs, plus git history.
  The fixed-dimensional Sard lemmas were found but discarded as direct
  dependencies because their domain is not a manifold. The chartwise extension
  remains the precise open bridge.
  -/
  sorry
