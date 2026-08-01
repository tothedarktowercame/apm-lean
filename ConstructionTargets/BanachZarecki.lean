import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import ConstructionTargets.LusinN

/-!
# Banach--Zarecki infrastructure for monotone functions on `[0,1]`

This file starts the positive Lebesgue--Stieltjes route to Banach--Zarecki.
It packages the monotone continuous extension to the real line and proves the
interval formula for its Stieltjes measure.  The remaining construction target
is the Borel-image comparison needed to turn Lusin condition `(N)` into
absolute continuity of that measure with respect to Lebesgue measure.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace ConstructionTargets.BanachZarecki

/-- Retraction of the real line onto the unit interval. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clamp01_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x := by
  simp [clamp01, hx.1, hx.2]

lemma monotone_clamp01 : Monotone clamp01 := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

lemma continuous_clamp01 : Continuous clamp01 := by
  exact continuous_const.max (continuous_const.min continuous_id)

/-- Extend a function on `[0,1]` constantly past both endpoints. -/
def monotoneExtension (f : ℝ → ℝ) (x : ℝ) : ℝ := f (clamp01 x)

lemma monotoneExtension_eq_self (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    monotoneExtension f x = f x := by
  rw [monotoneExtension, clamp01_eq_self hx]

lemma monotone_monotoneExtension {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    Monotone (monotoneExtension f) := by
  intro x y hxy
  exact hf (clamp01_mem x) (clamp01_mem y) (monotone_clamp01 hxy)

lemma continuous_monotoneExtension {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Continuous (monotoneExtension f) := by
  rw [← continuousOn_univ]
  exact hf.comp continuous_clamp01.continuousOn (fun x _ => clamp01_mem x)

/-- The positive Stieltjes measure associated to the clamped monotone
extension of `f`. -/
noncomputable def stieltjesMeasure (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) : Measure ℝ :=
  (monotone_monotoneExtension hf).stieltjesFunction.measure

lemma stieltjesFunction_monotoneExtension_eq
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    (monotone_monotoneExtension hf_mono).stieltjesFunction x =
      monotoneExtension f x := by
  rw [Monotone.stieltjesFunction_eq]
  exact (continuous_monotoneExtension hf_cont).continuousAt.continuousWithinAt.rightLim_eq

/-- Workhorse interval formula: on `[0,1]`, the Stieltjes measure has exactly
the increment prescribed by `f`. -/
theorem stieltjesMeasure_Ioc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    stieltjesMeasure f hf_mono (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  rw [stieltjesMeasure, StieltjesFunction.measure_Ioc,
    stieltjesFunction_monotoneExtension_eq hf_cont hf_mono,
    stieltjesFunction_monotoneExtension_eq hf_cont hf_mono,
    monotoneExtension_eq_self f hb, monotoneExtension_eq_self f ha]

/-- A continuous monotone function maps a closed subinterval onto the closed
interval between its endpoint values.  This uses no form of Lusin `(N)`. -/
theorem image_Icc_eq_Icc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    f '' Icc a b = Icc (f a) (f b) := by
  have hab_sub : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hf_mono ha (hab_sub hx) hx.1, hf_mono (hab_sub hx) hb hx.2⟩
  · exact intermediate_value_Icc hab (hf_cont.mono hab_sub)

/-- On interval generators, the Stieltjes mass is exactly the Lebesgue
measure of the corresponding closed image interval.  This is the
continuity-and-monotonicity-only input to the remaining Carathéodory step. -/
theorem stieltjesMeasure_Ioc_eq_volume_image_Icc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    stieltjesMeasure f hf_mono (Ioc a b) = volume (f '' Icc a b) := by
  rw [stieltjesMeasure_Ioc hf_cont hf_mono ha hb,
    image_Icc_eq_Icc hf_cont hf_mono ha hb hab, Real.volume_Icc]

/-- Continuity removes all atoms from the associated Stieltjes measure.  This
is needed when image intervals overlap at endpoint or flat-fiber values. -/
theorem stieltjesMeasure_singleton
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    stieltjesMeasure f hf_mono {x} = 0 := by
  let S := (monotone_monotoneExtension hf_mono).stieltjesFunction
  have hS : (S : ℝ → ℝ) = monotoneExtension f := by
    funext y
    exact stieltjesFunction_monotoneExtension_eq hf_cont hf_mono y
  rw [stieltjesMeasure, StieltjesFunction.measure_singleton]
  change ENNReal.ofReal (S x - Function.leftLim S x) = 0
  rw [hS]
  rw [(continuous_monotoneExtension hf_cont).continuousAt.continuousWithinAt.leftLim_eq,
    sub_self, ENNReal.ofReal_zero]

/-- The clamped extension is bounded, hence its Stieltjes measure is finite.
This supplies the finiteness input for the eventual Radon--Nikodym step. -/
theorem stieltjesMeasure_isFinite
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    IsFiniteMeasure (stieltjesMeasure f hf_mono) := by
  let S := (monotone_monotoneExtension hf_mono).stieltjesFunction
  change IsFiniteMeasure S.measure
  apply S.isFiniteMeasure_of_forall_abs_le
  intro x
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hx := clamp01_mem x
  have hlo : f 0 ≤ monotoneExtension f x := by
    exact hf_mono h0 hx hx.1
  have hhi : monotoneExtension f x ≤ f 1 := by
    exact hf_mono hx h1 hx.2
  change |S x| ≤ max |f 0| |f 1|
  rw [stieltjesFunction_monotoneExtension_eq hf_cont hf_mono]
  exact abs_le_max_abs_abs hlo hhi

/-!
## Exact remaining frontier

The next reusable theorem is deliberately recorded without an axiom or a
relocated `sorry`:

```lean
theorem stieltjesMeasure_absolutelyContinuous_of_maps_null
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    (hf_N : ∀ E ⊆ Icc (0 : ℝ) 1, volume E = 0 → volume (f '' E) = 0) :
    stieltjesMeasure f hf_mono ≪ volume
```

The missing Carathéodory step is an inequality sufficient for that theorem:

```lean
∀ E, MeasurableSet E → E ⊆ Icc (0 : ℝ) 1 →
  stieltjesMeasure f hf_mono E ≤ volume (f '' E)
```

It must use only continuity and monotonicity; Lusin `(N)` is applied after
this comparison, not during its proof.  A bare interval outer-cover argument
does not suffice: it gives `volume (f '' E) ≤ ∑ volume (f '' I n)`, whereas
the desired estimate needs the reverse comparison with the Stieltjes mass.
The extension must additionally control overlaps of interval images.  For a
non-strict monotone map these overlaps are precisely flat-fiber values;
`stieltjesMeasure_singleton` proves that the source measure has no atoms, so
those fibers can be discarded once their countability/decomposition is
formalized.
-/

end ConstructionTargets.BanachZarecki
