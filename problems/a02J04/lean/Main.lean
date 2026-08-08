import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# APM a02J04 — a projected planar measure and its Lebesgue decomposition

## Statement repairs

None.

## Encoding questions

None. The planar measure is defined by `Measure.withDensity`, the first-coordinate
pushforward by `Measure.map`, and the Radon–Nikodym derivative by
`Measure.rnDeriv`.
-/

open MeasureTheory Set ENNReal

noncomputable section

def apm_a02J04_g (p : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 then 2 else 0

def apm_a02J04_mu : Measure (ℝ × ℝ) :=
  volume.withDensity apm_a02J04_g

def apm_a02J04_P : ℝ × ℝ → ℝ := Prod.fst

def apm_a02J04_tau : Measure ℝ :=
  Measure.map apm_a02J04_P apm_a02J04_mu

def apm_a02J04_tauDensity (x : ℝ) : ℝ :=
  if x ∈ Icc 0 1 then 2 * x else 0

lemma apm_a02J04_measurable_g : Measurable apm_a02J04_g := by
  unfold apm_a02J04_g
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
  · exact measurable_const
  · exact measurable_const

lemma apm_a02J04_measurable_tauDensity :
  Measurable fun x : ℝ ↦ ENNReal.ofReal (apm_a02J04_tauDensity x) := by
  unfold apm_a02J04_tauDensity
  apply ENNReal.measurable_ofReal.comp
  exact (measurable_const.mul measurable_id).ite measurableSet_Icc measurable_const

@[simp] lemma apm_a02J04_tauDensity_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) = ENNReal.ofReal (2 * x) := by
  simp [apm_a02J04_tauDensity, hx]

@[simp] lemma apm_a02J04_tauDensity_of_not_mem {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) = 0 := by
  simp [apm_a02J04_tauDensity, hx]

lemma apm_a02J04_tauDensity_ne_zero {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hx0 : x ≠ 0) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) ≠ 0 := by
  rw [apm_a02J04_tauDensity_of_mem hx]
  exact (ENNReal.ofReal_pos.mpr
    (mul_pos (by norm_num) (lt_of_le_of_ne hx.1 (Ne.symm hx0)))).ne'

/-- The vertical section of the triangular support has exactly the expected
Lebesgue measure (and is automatically empty when `x < 0`). -/
lemma apm_a02J04_volume_verticalSection (x : ℝ) :
    volume {y : ℝ | 0 ≤ y ∧ y ≤ x} = ENNReal.ofReal x := by
  change volume (Icc (0 : ℝ) x) = ENNReal.ofReal x
  rw [Real.volume_Icc, sub_zero]

/-- The inner Tonelli integral of the planar density is the proposed marginal
density. This is the scalar heart of the pushforward calculation. -/
lemma apm_a02J04_lintegral_g_right (x : ℝ) :
    (∫⁻ y : ℝ, apm_a02J04_g (x, y) ∂volume) =
      ENNReal.ofReal (apm_a02J04_tauDensity x) := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hfun : (fun y : ℝ ↦ apm_a02J04_g (x, y)) =
        (Icc (0 : ℝ) x).indicator (fun _ ↦ (2 : ℝ≥0∞)) := by
      funext y
      by_cases hy : 0 ≤ y ∧ y ≤ x <;>
        simp [apm_a02J04_g, Set.indicator, hy, hx.2, mem_Icc]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    rw [apm_a02J04_tauDensity_of_mem hx]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · have hzero : ∀ y : ℝ, apm_a02J04_g (x, y) = 0 := by
      intro y
      simp only [apm_a02J04_g]
      split_ifs with h
      · exfalso
        exact hx ⟨le_trans h.1 h.2.1, h.2.2⟩
      · rfl
    simp [hzero, apm_a02J04_tauDensity_of_not_mem hx]

theorem apm_a02j04 :
    apm_a02J04_tau =
      volume.withDensity (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)) ∧
    (volume.restrict (Icc (0 : ℝ) 1)).AbsolutelyContinuous apm_a02J04_tau ∧
    Measure.MutuallySingular (volume.restrict ((Icc (0 : ℝ) 1)ᶜ)) apm_a02J04_tau ∧
    (volume.restrict (Icc (0 : ℝ) 1)).rnDeriv apm_a02J04_tau
      =ᵐ[apm_a02J04_tau]
        fun x ↦ ENNReal.ofReal (1 / (2 * x)) := by
  /-
  Closer hop 2 builds on the measurable-density prerequisites compiled by
  hop 1. In particular, the planar and proposed marginal densities are measurable,
  the latter vanishes off `[0,1]`, and it is nonzero on `[0,1] \ {0}`.  These
  are exactly the support and reciprocal-density facts needed by Mathlib's
  `rnDeriv_withDensity_right` API after the marginal identity is known.

  Going beyond that boundary, `apm_a02J04_volume_verticalSection` proves the
  exact interval measure `volume {y | 0 ≤ y ∧ y ≤ x} = ofReal x`, including
  negative `x`. `apm_a02J04_lintegral_g_right` then performs the complete
  inner Tonelli calculation and identifies it pointwise with the proposed
  marginal density, treating both `x ∈ [0,1]` and the zero-density complement.
  Thus the vertical-section calculation is no longer open.

  Renewed searches of `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  prior measure-decomposition artifacts (especially `a01J03`), Mathlib's marginal,
  product-measure, `withDensity`, and Radon--Nikodym sources, and git history
  found no packaged theorem computing the first-coordinate marginal of this
  triangular density. The remaining first bridge is measure-level Tonelli and
  map extensionality: for measurable `s`, rewrite the mapped measure as

    `∫⁻ x, 2 * volume ({y | 0 ≤ y ∧ y ≤ x}) * 1_s x ∂volume`,

  substitute the compiled inner integral, and identify the result with
  `volume.withDensity (ofReal (2*x))`. Once this equality is
  compiled, absolute continuity and singularity follow from the support and
  positivity lemmas above (the exceptional point `{0}` is volume-null), and
  `Measure.rnDeriv_withDensity_right` gives the displayed reciprocal density.
  -/
  sorry
