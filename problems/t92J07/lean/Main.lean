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
open MeasureTheory
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

/-- The critical values of one member of the family.  Keeping this as an
explicit set isolates the genuinely differential-topological input (Sard)
from the countable measure argument below. -/
def apm_t92J07_criticalValues
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E m) : Set (apm_t92J07_E m) :=
  {x | ¬ apm_t92J07_IsRegularValue (n := n) (m := m) f x}

/-- Every value of a map to the zero-dimensional Euclidean space is regular:
the codomain of every manifold derivative is a subsingleton. -/
lemma apm_t92J07_isRegularValue_fin_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E 0) (x : apm_t92J07_E 0) :
    apm_t92J07_IsRegularValue (n := n) (m := 0) f x := by
  intro p hp y
  refine ⟨0, ?_⟩
  apply (NormedSpace.fromTangentSpace (f p)).injective
  exact Subsingleton.elim _ _

@[simp] lemma apm_t92J07_criticalValues_fin_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (apm_t92J07_E n) M]
    (f : M → apm_t92J07_E 0) :
    apm_t92J07_criticalValues (n := n) (m := 0) f = ∅ := by
  ext x
  simp [apm_t92J07_criticalValues, apm_t92J07_isRegularValue_fin_zero]

/-- Countably many null critical-value sets have a common regular value.
This is the complete measure-theoretic assembly needed after manifold Sard. -/
lemma apm_t92J07_exists_common_regularValue_of_null
    (m : ℕ) (d : PNat → ℕ) (M : PNat → Type*)
    [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (apm_t92J07_E (d i)) (M i)]
    (f : ∀ i, M i → apm_t92J07_E m)
    (hnull : ∀ i, volume (apm_t92J07_criticalValues
      (n := d i) (m := m) (M := M i) (f i)) = 0) :
    ∃ x : apm_t92J07_E m, ∀ i, apm_t92J07_IsRegularValue
      (n := d i) (m := m) (M := M i) (f i) x := by
  let C : Set (apm_t92J07_E m) := ⋃ i, apm_t92J07_criticalValues
    (n := d i) (m := m) (M := M i) (f i)
  have hC : volume C = 0 := measure_iUnion_null hnull
  have hCne : C ≠ Set.univ := by
    intro hCu
    have huniv : volume (Set.univ : Set (apm_t92J07_E m)) = 0 := by simpa [hCu] using hC
    have hball : volume (Metric.ball (0 : apm_t92J07_E m) 1) ≠ 0 :=
      (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne'
    exact hball (measure_mono_null (Set.subset_univ _) huniv)
  have hex : ∃ x, x ∉ C := by
    by_contra h
    push_neg at h
    exact hCne (Set.eq_univ_of_forall h)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, fun i => ?_⟩
  have hxi : x ∉ apm_t92J07_criticalValues
      (n := d i) (m := m) (M := M i) (f i) := by
    intro hi
    exact hx (Set.mem_iUnion.2 ⟨i, hi⟩)
  simpa [apm_t92J07_criticalValues] using hxi

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

  CLOSER HOP 2: `apm_t92J07_criticalValues` and
  `apm_t92J07_exists_common_regularValue_of_null` now compile the entire
  countable-family avoidance argument.  In particular, the latter proves that
  nullity of each critical-value set produces one point regular for every
  `i : PNat`; its proof also handles the zero-dimensional target uniformly by
  using positivity of a Euclidean open ball rather than assuming positive
  dimension.  This leaves exactly one missing input: for a second-countable
  finite-dimensional manifold and a `ContMDiff ... ∞` map, prove
  `volume (apm_t92J07_criticalValues f) = 0`.

  Going beyond the previous source search, I checked whether the manifold
  derivative can be reduced globally using `writtenInExtChartAt` and the
  source-chart countability lemmas.  Mathlib supplies local identities between
  `mfderiv` and derivatives of chart representatives, but no countable family
  of source charts whose critical images can be fed directly to the
  vector-space Sard lemmas.  The available Sard statements also require maps
  on whole vector spaces (or fixed-dimensional same-space Jacobians), whereas
  a chart representative is defined only on a chart source.  Extending each
  representative while preserving the required differentiability and
  critical-image inclusion is therefore still a substantive theorem, not
  countable-union bookkeeping.  No statement defect or alternate route was
  found; the frozen statement is unchanged.

  CLOSER HOP 3 routes around manifold Sard for the complete
  zero-dimensional-target branch. `apm_t92J07_isRegularValue_fin_zero` proves
  directly that every derivative into `EuclideanSpace ℝ (Fin 0)` is
  surjective, and `apm_t92J07_criticalValues_fin_zero` identifies its critical
  values with the empty set. The `m = 0` branch of the frozen theorem is now
  closed below without Sard, measure theory, or chart extension.

  For `m = k + 1`, renewed inspection of the Hausdorff-dimension Sard theorem,
  Jacobian null-image results, `ContMDiff` chart representatives, smooth bump
  extension APIs, Lindelöf/countable-cover results, `LEMMA-INDEX.md`, every
  `ConstructionTargets/` module, related Sard artifacts, and git history found
  no within-set Sard theorem or smooth extension theorem with the required
  critical-image control. Thus only positive-dimensional manifold Sard
  remains open. The frozen statement is unchanged; no placeholder declaration
  was introduced.
  -/
  cases m with
  | zero =>
      refine ⟨0, fun i => ?_⟩
      exact (apm_t92J07_isSmoothRegularFiber_preimage_iff
        (f := f i) 0).2 (apm_t92J07_isRegularValue_fin_zero (f i) 0)
  | succ m =>
      sorry
