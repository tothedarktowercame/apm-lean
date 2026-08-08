import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-!
# APM t91A08 — a two-form on the torus

The torus is the genuine quotient `(ℝ/ℤ)²`, equipped with its normalized Haar
measure.  Forms are continuous fields of alternating continuous multilinear
maps on the standard tangent model.  Descent is expressed along the quotient
map, pullback uses the actual derivative matrix, and integration is a Haar
integral over the torus.

## Statement repairs

None.

## Encoding questions

The tangent bundle of the quotient Lie group is represented in its canonical
translation trivialization by `ℝ²`; this is why every fiber below has the same
model vector space.

The alternating-form and Haar-integral encoding follows `t01J06`.
-/

open MeasureTheory
open scoped LinearAlgebra

noncomputable section

abbrev T91A08Torus := UnitAddCircle × UnitAddCircle
abbrev T91A08R2 := EuclideanSpace ℝ (Fin 2)
abbrev T91A08Alt2 := T91A08R2 [⋀^Fin 2]→L[ℝ] ℝ
abbrev T91A08Form2 := C(T91A08Torus, T91A08Alt2)

/-- The quotient covering `ℝ² → (ℝ/ℤ)²`. -/
def t91A08Cover (x : T91A08R2) : T91A08Torus :=
  (x 0, x 1)

/-- Pointwise descent of `3 dx ∧ dy` along the quotient covering. -/
def t91A08IsInduced (beta : T91A08Form2) : Prop :=
  ∀ (x : T91A08R2) (v : Fin 2 → T91A08R2),
    beta (t91A08Cover x) v =
      3 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def t91A08Linear (u : T91A08R2) : T91A08R2 :=
  WithLp.toLp 2 ![5 * u 0 + 2 * u 1, 4 * u 0 + 3 * u 1]

/-- The torus map induced by the integer matrix `[[5,2],[4,3]]`. -/
def t91A08g : C(T91A08Torus, T91A08Torus) :=
  ⟨fun p ↦ (5 • p.1 + 2 • p.2, 4 • p.1 + 3 • p.2), by fun_prop⟩

/-- `gamma` is the pullback of `beta` by `g`, in translation-trivialized
tangent coordinates. -/
def t91A08IsPullback (gamma beta : T91A08Form2) : Prop :=
  ∀ (p : T91A08Torus) (v : Fin 2 → T91A08R2),
    gamma p v = beta (t91A08g p) (fun i ↦ t91A08Linear (v i))

/-- Integral of a top-degree form against normalized Haar measure, using the
standard oriented translation-invariant frame. -/
def t91A08Integral (beta : T91A08Form2) : ℝ :=
  ∫ p : T91A08Torus,
    beta p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]

lemma t91A08Cover_surjective : Function.Surjective t91A08Cover := by
  rintro ⟨p, q⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) p
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) q
  refine ⟨WithLp.toLp 2 ![x, y], ?_⟩
  ext <;> simp [t91A08Cover]

lemma t91A08Integral_induced (beta : T91A08Form2)
    (hbeta : t91A08IsInduced beta) : t91A08Integral beta = 3 := by
  have hconst (p : T91A08Torus) :
      beta p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1] = 3 := by
    obtain ⟨x, rfl⟩ := t91A08Cover_surjective p
    simpa [EuclideanSpace.single_apply] using
      hbeta x ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]
  simp_rw [t91A08Integral, hconst]
  rw [integral_const]
  norm_num [Measure.real, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    AddCircle.measure_univ]

lemma t91A08Integral_pullback (beta gamma : T91A08Form2)
    (hbeta : t91A08IsInduced beta)
    (hgamma : t91A08IsPullback gamma beta) : t91A08Integral gamma = 21 := by
  have hconst (p : T91A08Torus) :
      gamma p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1] = 21 := by
    rw [hgamma p]
    obtain ⟨x, hx⟩ := t91A08Cover_surjective (t91A08g p)
    rw [← hx]
    rw [hbeta x]
    norm_num [t91A08Linear, EuclideanSpace.single_apply]
  simp_rw [t91A08Integral, hconst]
  rw [integral_const]
  norm_num [Measure.real, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    AddCircle.measure_univ]

def t91A08FirstCircle : C(UnitAddCircle, T91A08Torus) :=
  ⟨fun z ↦ (z, 0), by fun_prop⟩

def t91A08FirstProjection : C(T91A08Torus, UnitAddCircle) :=
  ⟨Prod.fst, continuous_fst⟩

def t91A08TimesFive : C(UnitAddCircle, UnitAddCircle) :=
  ⟨fun z ↦ 5 • z, by fun_prop⟩

lemma t91A08_timesFive_homotopic_of_g_homotopic
    (h : ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus)) :
    ContinuousMap.Homotopic t91A08TimesFive
      (ContinuousMap.id UnitAddCircle) := by
  have hpost := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl t91A08FirstProjection) h
  have hpre := ContinuousMap.Homotopic.comp hpost
    (ContinuousMap.Homotopic.refl t91A08FirstCircle)
  convert hpre using 1 <;>
    ext z <;>
    simp [t91A08FirstProjection, t91A08FirstCircle, t91A08TimesFive, t91A08g]

theorem apm_t91a08
    (beta gamma : T91A08Form2)
    (hbeta : t91A08IsInduced beta)
    (hgamma : t91A08IsPullback gamma beta) :
    t91A08Integral beta = 3 ∧
    t91A08Integral gamma = 21 ∧
    ¬ ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus) := by
  refine ⟨t91A08Integral_induced beta hbeta,
    t91A08Integral_pullback beta gamma hbeta hgamma, ?_⟩
  /-
  CLOSER HOP 2 BOUNDARY (statement unchanged).

  This hop reconstructs the two integral computations for the repaired genuine
  quotient/Haar formulation. `t91A08Cover_surjective` supplies representatives
  for every torus point; the induced equation makes the first integrand
  constantly `3`, while the pullback equation and the explicit matrix give
  the determinant factor `7`, hence the constant `21`. Both Haar integrals are
  then evaluated using `Measure.volume_eq_prod`, `Measure.prod_prod`, and
  `AddCircle.measure_univ`.

  It also reconstructs the homotopy reduction in the additive-circle encoding:
  `t91A08_timesFive_homotopic_of_g_homotopic` restricts a hypothetical torus
  homotopy to the first coordinate and projects back, producing a homotopy
  between `z ↦ 5 • z` and the identity on `UnitAddCircle`. The sole remaining
  bridge is proving those circle maps nonhomotopic. Renewed searches of
  `LEMMA-INDEX.md`, `ConstructionTargets`, solved circle/covering artifacts,
  Mathlib's `AddCircle`, homotopy, fundamental-group, and lifting sources, and
  git history found no compiled integer-degree classification or winding-number
  invariant for `UnitAddCircle` self-maps.
  -/
  sorry
