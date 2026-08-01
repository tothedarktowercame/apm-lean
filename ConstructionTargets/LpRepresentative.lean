import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Representatives of Bochner integrals in `Lᵖ`

This file identifies a Bochner integral of `Lᵖ` classes with the pointwise
integral of an explicitly supplied jointly measurable lift.  The lift is
essential: evaluation at a point is not a continuous operation on `Lᵖ`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ConstructionTargets.LpRepresentative

/-- Integration over a finite-measure measurable set, as a continuous linear
functional on `Lᵖ`.  Continuity is supplied by Hölder pairing with the
indicator of the set. -/
noncomputable def setIntegralCLM
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal}
    [Fact (1 ≤ p)] (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Lp ℝ p μ →L[ℝ] ℝ := by
  letI : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p p.conjExponent).flip
    (indicatorConstLp p.conjExponent hs hμs 1)

@[simp]
lemma setIntegralCLM_apply
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal}
    [Fact (1 ≤ p)] (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : Lp ℝ p μ) :
    setIntegralCLM s hs hμs f = ∫ x in s, f x ∂μ := by
  letI : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  rw [setIntegralCLM, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  calc
    (∫ x, f x * (indicatorConstLp p.conjExponent hs hμs 1) x ∂μ) =
        ∫ x, s.indicator (fun x => f x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := p.conjExponent)
        (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = ∫ x in s, f x ∂μ := integral_indicator hs

/-- A jointly measurable lift commutes with Bochner integration into `Lᵖ`.

The local product-integrability hypothesis is deliberately stated after
restriction to finite-measure sets.  This is enough for the uniqueness
theorem for `Lᵖ` representatives and applies on infinite-measure spaces where
the lift need not be globally integrable on `Y × X`. -/
theorem toLp_integral_eq_integral
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    {ν : Measure Y} {μ : Measure X} [SFinite ν] [SFinite μ]
    {p : ENNReal} [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {φ : Y × X → ℝ} (hφ : AEStronglyMeasurable φ (ν.prod μ))
    {F : Y → Lp ℝ p μ} (hF : Integrable F ν)
    (hFφ : ∀ᵐ y ∂ν, (F y : X → ℝ) =ᵐ[μ] fun x => φ (y, x))
    (hφ_local : ∀ s : Set X, MeasurableSet s → μ s ≠ ∞ →
      HasFiniteIntegral (fun z : Y × X => s.indicator (fun x => φ (z.1, x)) z.2)
        (ν.prod μ))
    (hψ : MemLp (fun x => ∫ y, φ (y, x) ∂ν) p μ) :
    hψ.toLp (fun x => ∫ y, φ (y, x) ∂ν) = ∫ y, F y ∂ν := by
  apply Lp.ext
  apply (Lp.ae_eq_of_forall_setIntegral_eq
    (hψ.toLp (fun x => ∫ y, φ (y, x) ∂ν)) (∫ y, F y ∂ν)
    (zero_lt_one.trans_le Fact.out).ne' hp_top
    (fun s _ hμs => integrableOn_Lp_of_measure_ne_top _ Fact.out hμs.ne)
    (fun s _ hμs => integrableOn_Lp_of_measure_ne_top _ Fact.out hμs.ne) ?_)
  intro s hs hμs
  have hprod : Integrable
      (fun z : Y × X => s.indicator (fun x => φ (z.1, x)) z.2)
      (ν.prod μ) := by
    refine ⟨?_, hφ_local s hs hμs.ne⟩
    refine (hφ.indicator (MeasurableSet.univ.prod hs)).congr ?_
    filter_upwards with z
    by_cases hzs : z.2 ∈ s <;> simp [hzs]
  have hslice : ∀ᵐ y ∂ν,
      ∫ x in s, F y x ∂μ = ∫ x in s, φ (y, x) ∂μ := by
    filter_upwards [hFφ] with y hy
    exact integral_congr_ae (ae_restrict_of_ae hy)
  calc
    ∫ x in s, (hψ.toLp (fun x => ∫ y, φ (y, x) ∂ν)) x ∂μ =
        ∫ x in s, ∫ y, φ (y, x) ∂ν ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hψ.coeFn_toLp)
    _ = ∫ y, ∫ x in s, φ (y, x) ∂μ ∂ν := by
      have hprod' : Integrable
          (Function.uncurry (fun y x => s.indicator (fun x => φ (y, x)) x))
          (ν.prod μ) := by
        simpa [Function.uncurry] using hprod
      have hswap :
          (∫ y, ∫ x, s.indicator (fun x => φ (y, x)) x ∂μ ∂ν) =
            ∫ x, ∫ y, s.indicator (fun x => φ (y, x)) x ∂ν ∂μ :=
        integral_integral_swap hprod'
      calc
        (∫ x in s, ∫ y, φ (y, x) ∂ν ∂μ) =
            ∫ x, s.indicator (fun x => ∫ y, φ (y, x) ∂ν) x ∂μ :=
          (integral_indicator hs).symm
        _ = ∫ x, ∫ y, s.indicator (fun x => φ (y, x)) x ∂ν ∂μ := by
          congr 1
          funext x
          by_cases hxs : x ∈ s <;> simp [hxs]
        _ = ∫ y, ∫ x, s.indicator (fun x => φ (y, x)) x ∂μ ∂ν := hswap.symm
        _ = ∫ y, ∫ x in s, φ (y, x) ∂μ ∂ν := by
          congr 1
          funext y
          rw [integral_indicator hs]
    _ = ∫ y, ∫ x in s, F y x ∂μ ∂ν :=
      integral_congr_ae (Filter.EventuallyEq.symm hslice)
    _ = ∫ y, setIntegralCLM s hs hμs.ne (F y) ∂ν := by
      congr 1
      funext y
      rw [setIntegralCLM_apply]
    _ = setIntegralCLM s hs hμs.ne (∫ y, F y ∂ν) :=
      (setIntegralCLM s hs hμs.ne).integral_comp_comm hF
    _ = ∫ x in s, (∫ y, F y ∂ν) x ∂μ := setIntegralCLM_apply _ _ _ _

end ConstructionTargets.LpRepresentative
