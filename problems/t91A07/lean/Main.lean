import Mathlib

open scoped ContDiff Topology

/-!
# APM t91A07 — nondegenerate fixed points are isolated

## Statement repairs

None.

## Encoding note

The theorem is stated in a finite-dimensional real coordinate chart, exactly
as the problem's hint requires.  Here `fderiv f x - id` being bijective is the
coordinate-free linear formulation of “`df_x` has no eigenvalue `+1`”, and the
neighborhood conclusion says precisely that each fixed point is isolated.
-/

/-- Superseded because it only stated the coordinate-space special case. -/
theorem apm_t91a07_previous_encoding
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hnondegenerate : ∀ x, f x = x →
      Function.Bijective
        (fderiv ℝ f x - ContinuousLinearMap.id ℝ E)) :
    ∀ x, f x = x →
      ∃ U ∈ 𝓝 x, ∀ y ∈ U, f y = y → y = x := by
  intro x hx
  let F : E → E := fun y => f y - y
  let L : E →L[ℝ] E := fderiv ℝ f x - ContinuousLinearMap.id ℝ E
  have hL : Function.Bijective L := hnondegenerate x hx
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective L
    (L.ker_eq_bot_of_injective hL.injective)
    (L.range_eq_top_of_surjective hL.surjective)
  have hF : ContDiff ℝ ∞ F := by
    exact hf.sub contDiff_id
  have hFderiv : fderiv ℝ F x = L := by
    have hd := (hf.differentiable (by simp) x).hasFDerivAt.sub (hasFDerivAt_id x)
    change HasFDerivAt F L x at hd
    exact hd.fderiv
  have hstrict : HasStrictFDerivAt F (e : E →L[ℝ] E) x := by
    have h : HasStrictFDerivAt F (fderiv ℝ F x) x :=
      hF.contDiffAt.hasStrictFDerivAt (by simp)
    rw [hFderiv] at h
    exact h
  let inv := hstrict.localInverse F e x
  have hleft : ∀ᶠ y in 𝓝 x, inv (F y) = y := hstrict.eventually_left_inverse
  refine ⟨{y | inv (F y) = y}, hleft, ?_⟩
  intro y hyU hy
  have hFx : F x = 0 := by simp [F, hx]
  have hFy : F y = 0 := by simp [F, hy]
  calc
    y = inv (F y) := hyU.symm
    _ = inv (F x) := by rw [hFy, hFx]
    _ = x := hstrict.localInverse_apply_image

/-- A nondegenerate fixed point of a smooth self-map of a manifold is isolated. -/
theorem apm_t91a07
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ X]
    (f : X → X)
    (hf : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ f)
    (hnondegenerate : ∀ x, f x = x →
      Function.Bijective
        (fderiv ℝ
            ((extChartAt (modelWithCornersSelf ℝ E) x) ∘ f ∘
              (extChartAt (modelWithCornersSelf ℝ E) x).symm)
            (extChartAt (modelWithCornersSelf ℝ E) x x) -
          ContinuousLinearMap.id ℝ E)) :
    ∀ x, f x = x → ∃ U ∈ 𝓝 x, ∀ y ∈ U, f y = y → y = x := by
  intro x hx
  let φ := extChartAt (modelWithCornersSelf ℝ E) x
  let g : E → E := φ ∘ f ∘ φ.symm
  have hfx := hf x
  rw [contMDiffAt_iff, hx, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at hfx
  obtain ⟨hfcont, hg⟩ := hfx
  let F : E → E := fun y => g y - y
  let L : E →L[ℝ] E := fderiv ℝ g (φ x) - ContinuousLinearMap.id ℝ E
  have hL : Function.Bijective L := hnondegenerate x hx
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective L
    (L.ker_eq_bot_of_injective hL.injective)
    (L.range_eq_top_of_surjective hL.surjective)
  have hstrict : HasStrictFDerivAt F (e : E →L[ℝ] E) (φ x) := by
    have h := (hg.hasStrictFDerivAt (by simp)).sub (hasStrictFDerivAt_id (φ x))
    exact h
  let inv := hstrict.localInverse F e (φ x)
  have hleft : ∀ᶠ z in 𝓝 (φ x), inv (F z) = z := hstrict.eventually_left_inverse
  have hsrc : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds x
  have hfsrc : f ⁻¹' φ.source ∈ 𝓝 x :=
    hfcont.preimage_mem_nhds (by rw [hx]; exact hsrc)
  have hφ : φ ⁻¹' {z | inv (F z) = z} ∈ 𝓝 x :=
    (continuousAt_extChartAt x).preimage_mem_nhds hleft
  refine ⟨φ.source ∩ f ⁻¹' φ.source ∩ φ ⁻¹' {z | inv (F z) = z},
    Filter.inter_mem (Filter.inter_mem hsrc hfsrc) hφ, ?_⟩
  rintro y ⟨⟨hy, -⟩, hyinv⟩ hfy
  have hxsrc : x ∈ φ.source := mem_extChartAt_source x
  have hFy : F (φ y) = 0 := by
    simp only [F, g, Function.comp_apply, φ.left_inv hy, hfy, sub_self]
  have hFx : F (φ x) = 0 := by
    simp only [F, g, Function.comp_apply, φ.left_inv hxsrc, hx, sub_self]
  have hφeq : φ y = φ x := by
    calc φ y = inv (F (φ y)) := hyinv.symm
      _ = inv (F (φ x)) := by rw [hFy, hFx]
      _ = φ x := hstrict.localInverse_apply_image
  exact φ.injOn hy hxsrc hφeq
