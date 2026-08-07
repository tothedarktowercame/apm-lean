import Mathlib
import ConstructionTargets.YoungConvolution
import ConstructionTargets.RadialMajorantAE
import YoungL2

open Filter MeasureTheory Set
open scoped NNReal

noncomputable section

/-!
# APM a98J03

## Statement repairs

The printed denominator `(x-t) + y^2` is repaired to `(x-t)^2 + y^2`.
Without the square this is not the Poisson kernel, has a real pole, and the three
requested conclusions are false.

## Encoding notes

The operators act on Mathlib's genuine quotient space `Lp ℝ 2 volume`. The
representative equation below binds each abstract bounded linear operator to the
displayed Poisson integral, rather than merely postulating an unrelated operator.
-/

noncomputable def apmPoissonKernel (y x : ℝ) : ℝ :=
  (y / Real.pi) / (x ^ 2 + y ^ 2)

noncomputable def apmPoissonIntegral (y : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, apmPoissonKernel y (x - t) * f t ∂volume

lemma apmPoissonKernel_eq_radial (y x : ℝ) :
    apmPoissonKernel y x =
      ConstructionTargets.RadialMajorantAE.poissonKernel y x := by
  rw [ConstructionTargets.RadialMajorantAE.poissonKernel_eq_formula]
  unfold apmPoissonKernel
  ring

lemma apmPoissonKernel_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (apmPoissonKernel y) volume := by
  refine (ConstructionTargets.RadialMajorantAE.poissonKernel_integrable hy).congr ?_
  filter_upwards with x
  exact (apmPoissonKernel_eq_radial y x).symm

lemma apmPoissonKernel_nonneg {y : ℝ} (hy : 0 < y) (x : ℝ) :
    0 ≤ apmPoissonKernel y x := by
  rw [apmPoissonKernel_eq_radial]
  exact ConstructionTargets.RadialMajorantAE.poissonKernel_nonneg hy x

lemma apmPoissonKernel_integral_one {y : ℝ} (hy : 0 < y) :
    ∫ x, apmPoissonKernel y x ∂volume = 1 := by
  rw [integral_congr_ae (Eventually.of_forall (apmPoissonKernel_eq_radial y))]
  exact ConstructionTargets.RadialMajorantAE.poissonKernel_integral hy

lemma apmPoissonIntegral_memLp
    {y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (apmPoissonIntegral y f) 2 volume := by
  simpa [apmPoissonIntegral, ConstructionTargets.YoungConvolution.convolution]
    using ConstructionTargets.YoungConvolution.convolution_memLp
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (apmPoissonKernel_integrable hy) hf

/-- The displayed raw Poisson convolution satisfies the sharp `L²`
contraction estimate. -/
lemma apmPoissonIntegral_L2_contraction
    {y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (apmPoissonIntegral y f) 2 volume ≤ eLpNorm f 2 volume := by
  simpa [apmPoissonIntegral, ConstructionTargets.YoungConvolution.convolution]
    using convolution_L2_contraction_of_probability_kernel
      (apmPoissonKernel_nonneg hy) (apmPoissonKernel_integral_one hy) hf

theorem apm_a98j03 :
    ∃ T : ℝ → (Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 volume),
      (∀ y : ℝ, 0 < y → ‖T y‖ ≤ 1) ∧
      (∀ (f : ℝ → ℝ) (hf : MemLp f 2 volume) (y : ℝ), 0 < y →
        ∃ hgy : MemLp (apmPoissonIntegral y f) 2 volume,
          T y (hf.toLp f) = hgy.toLp (apmPoissonIntegral y f)) ∧
      (∀ F : Lp ℝ 2 volume,
        Tendsto (fun y ↦ T y F) (nhdsWithin 0 (Ioi 0)) (nhds F)) := by
  /-
  PARTIAL boundary (closer hop 1).

  The original missing-dependency diagnosis is resolved. The frozen kernel is
  identified with `ConstructionTargets.RadialMajorantAE.poissonKernel` by
  `apmPoissonKernel_eq_radial`; its L¹ integrability is transported in
  `apmPoissonKernel_integrable`; and
  `apmPoissonIntegral_memLp` applies the sorry-free
  `ConstructionTargets.YoungConvolution.convolution_memLp` theorem. Thus the
  representative's membership in L² is now compiled for every `y > 0`.

  The remaining packaging is to descend convolution through the a.e. quotient
  as a linear map, use the sharp Young estimate plus kernel integral one to
  prove boundedness/norm at most one, bundle it as a continuous linear map,
  and connect the resulting quotient-valued operator to the frozen raw
  representative. Strong convergence can reuse the complete translated-Lp
  argument in closed sibling `a94J04` (`poissonConv_tendsto_L2`), whose kernel
  and convolution are algebraically the same, but that theorem is local to the
  sibling namespace/file rather than an importable construction module.

  Searches of `LEMMA-INDEX.md`, all closed artifacts, Mathlib's `Lp` quotient
  and convolution APIs, `ConstructionTargets/`, and git history found no
  already-bundled convolution continuous linear map. Hence the remaining
  bridge is quotient/operator construction and transport, not Young's
  inequality or approximate-identity analysis. No statement defect was found.

  CLOSER HOP 2: the repository-root module `YoungL2.lean` is importable and
  already contains the sharp theorem
  `convolution_L2_contraction_of_probability_kernel` used by `a94J04`.
  Transporting reusable-kernel nonnegativity and normalization gives compiled
  lemmas `apmPoissonKernel_nonneg`, `apmPoissonKernel_integral_one`, and
  `apmPoissonIntegral_L2_contraction`. Hence the norm-one analytic estimate is
  closed too. What remains is purely quotient descent/continuous-linear-map
  construction and transport of strong convergence.
  -/
  sorry
