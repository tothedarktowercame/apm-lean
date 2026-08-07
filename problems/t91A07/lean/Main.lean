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

theorem apm_t91a07
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
