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

@[simp] lemma apm_t93a04_isSmoothLinePreimage_preimage_iff
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (apm_t93a04_E n) M]
    (f : M → apm_t93a04_Point) (ℓ : Set apm_t93a04_Point) :
    apm_t93a04_IsSmoothLinePreimage (n := n) f ℓ (f ⁻¹' ℓ) ↔
      ∃ (p v : apm_t93a04_Point),
        v ≠ 0 ∧ ℓ = apm_t93a04_line p v ∧
        ∀ x : M, f x ∈ ℓ →
          LinearMap.range
              (mfderiv (apm_t93a04_Model n)
                (modelWithCornersSelf ℝ apm_t93a04_Point) f x).toLinearMap ⊔
            Submodule.span ℝ ({v} : Set apm_t93a04_Point) = ⊤ := by
  simp [apm_t93a04_IsSmoothLinePreimage]

/-- The linear-algebra bridge in the projection proof: if projection along
`v` is surjective on the derivative range, that range together with `v`
spans the target. -/
lemma apm_t93a04_range_sup_span_eq_top_of_projection_surjective
    {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℝ E] [Module ℝ F] [Module ℝ G]
    (L : E →ₗ[ℝ] F) (q : F →ₗ[ℝ] G) (v : F)
    (hker : LinearMap.ker q = Submodule.span ℝ ({v} : Set F))
    (hsurj : Function.Surjective (q.comp L)) :
    LinearMap.range L ⊔ Submodule.span ℝ ({v} : Set F) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, hy⟩ := hsurj (q x)
  have hd : x - L y ∈ Submodule.span ℝ ({v} : Set F) := by
    rw [← hker, LinearMap.mem_ker]
    simpa [LinearMap.comp_apply] using congrArg (fun z => q x - z) hy
  rw [← add_sub_cancel (L y) x]
  exact Submodule.add_mem_sup ⟨y, rfl⟩ hd

def apm_t93a04_lineDirection : apm_t93a04_Point :=
  EuclideanSpace.single 0 1

lemma apm_t93a04_lineDirection_ne_zero : apm_t93a04_lineDirection ≠ 0 := by
  intro h
  have h0 := congrFun (congrArg WithLp.ofLp h) 0
  simpa [apm_t93a04_lineDirection] using h0

theorem apm_t93a04 :
    ∀ (n : ℕ) (M : Type)
      [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (apm_t93a04_E n) M]
      [IsManifold (apm_t93a04_Model n) ∞ M]
      (f : M → apm_t93a04_Point),
      ContMDiff (apm_t93a04_Model n) (𝓘(ℝ, apm_t93a04_Point)) ∞ f →
      ∃ ℓ : Set apm_t93a04_Point,
        apm_t93a04_IsSmoothLinePreimage (n := n) f ℓ (f ⁻¹' ℓ) := by
  /-
  Boundary (closer hop 1): the helper
  `apm_t93a04_isSmoothLinePreimage_preimage_iff` removes the redundant
  set-equality packaging, leaving exactly existence of an affine line
  transverse to `f`.  The intended proof fixes a nonzero direction, composes
  `f` with a linear projection onto `ℝ²`, applies manifold Sard to choose a
  regular value, and translates surjectivity of the projected derivative into
  the displayed range-plus-span equality.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/` modules, closed
  Sard/transversality siblings (especially `t92J07` and `t01A08`), git
  history, and Mathlib's Sard, Hausdorff-dimension, Jacobian, manifold-chart,
  `mfderiv`, and regular-value APIs found Sard theorems only for maps between
  finite-dimensional normed vector spaces.  No theorem covers an arbitrary
  second-countable manifold domain.  A local proof must pass to a countable
  chart cover, apply vector-space Sard chartwise, prove compatibility of
  criticality with chart derivatives, and combine the null critical-value
  sets.  That chartwise manifold-Sard bridge remains open.

  CLOSER HOP 2: the projection-to-transversality step is now compiled as
  `apm_t93a04_range_sup_span_eq_top_of_projection_surjective`.  It proves in
  full generality that when a linear projection has kernel `span {v}` and its
  composite with the derivative is surjective, the derivative range joined
  with `span {v}` is top. Thus no bespoke finite-dimensional coordinate
  calculation is needed after obtaining a regular value.

  The new `t92J07` closer artifact was also inspected. It now packages the
  countable avoidance of null critical-value sets, but deliberately assumes
  the same missing manifold-Sard nullity input and is local to that problem.
  Mathlib's `writtenInExtChartAt` lemmas relate `mfderiv` to a chart
  representative only locally/within the model range; the available Sard
  lemmas expect whole-space differentiability. Hence extending chart maps and
  proving the required critical-image inclusion remains the sole substantive
  bridge. The frozen statement is unchanged.

  CLOSER HOP 3 closes the previously hidden empty-domain branch. The concrete
  nonzero vector `apm_t93a04_lineDirection` supplies an affine line, and when
  `M` is empty the range-plus-span obligation is vacuous. Thus the main proof
  below dispatches every empty manifold without Sard and confines the
  remaining gap to nonempty domains.

  For nonempty `M`, renewed searches of the Hausdorff-dimension and Jacobian
  Sard lemmas, `writtenInExtChartAt`, smooth bump/partition-of-unity extension
  machinery, countable chart-cover APIs, the newly advanced `t92J07`,
  `LEMMA-INDEX.md`, every `ConstructionTargets/` module, related Sard
  artifacts, and git history still found no whole-space extension preserving
  critical-image inclusion and no manifold-domain Sard theorem. The frozen
  statement is unchanged; no placeholder declaration was introduced.
  -/
  intro n M _ _ _ _ _ f hf
  cases isEmpty_or_nonempty M with
  | inl hM =>
      letI : IsEmpty M := hM
      refine ⟨apm_t93a04_line 0 apm_t93a04_lineDirection, ?_⟩
      apply (apm_t93a04_isSmoothLinePreimage_preimage_iff f _).2
      refine ⟨0, apm_t93a04_lineDirection,
        apm_t93a04_lineDirection_ne_zero, rfl, ?_⟩
      intro x hx
      exact isEmptyElim x
  | inr hM =>
      sorry
