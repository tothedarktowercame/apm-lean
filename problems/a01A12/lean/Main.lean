import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# APM a01A12 — conformal maps onto a wedge with a slit

## Statement repairs

None. The previous artifact covered only containment of the image. This
statement restores the source's requirements that the displayed map be
one-to-one and onto, and that all such maps be described.

## Encoding questions

None. Conformality is represented by complex differentiability with nonzero
derivative on the domain, and automorphisms of the upper half-plane are
represented concretely by real Möbius transformations with positive
determinant.
-/

open Complex Set

noncomputable section

def apm_a01A12_H : Set ℂ := {z : ℂ | 0 < z.im}

def apm_a01A12_wedgeSlit : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ |z.arg| < Real.pi / 4} \
    {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0}

def apm_a01A12_conformalMap (z : ℂ) : ℂ :=
  (1 - z ^ 2) ^ (1 / 4 : ℂ)

def apm_a01A12_mobius (a b c d : ℝ) (z : ℂ) : ℂ :=
  ((a : ℂ) * z + b) / ((c : ℂ) * z + d)

def apm_a01A12_ConformalBijOn (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  Set.BijOn f U V ∧
    ∀ z ∈ U, DifferentiableAt ℂ f z ∧ fderiv ℂ f z ≠ 0

/-- The quadratic input to the fourth root has no zero in the upper
half-plane.  This is the first branch-domain obligation in the explicit
conformal-map proof. -/
lemma apm_a01A12_one_sub_sq_ne_zero {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    1 - z ^ 2 ≠ 0 := by
  intro hzero
  have hfac : (1 - z) * (1 + z) = 0 := by
    calc
      (1 - z) * (1 + z) = 1 - z ^ 2 := by ring
      _ = 0 := hzero
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · have hz1 : z = 1 := (sub_eq_zero.mp hminus).symm
    subst z
    simpa [apm_a01A12_H] using hz
  · have hzn1 : z = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hplus
    subst z
    simpa [apm_a01A12_H] using hz

/-- The positive-determinant Möbius family contains the identity map. -/
lemma apm_a01A12_mobius_one_zero_zero_one (z : ℂ) :
    apm_a01A12_mobius 1 0 0 1 z = z := by
  simp [apm_a01A12_mobius]

lemma apm_a01A12_identity_parameters_positive :
    (0 : ℝ) < 1 * 1 - 0 * 0 := by norm_num

/-- Squaring sends the right half-plane away from the nonpositive real axis.
This is adapted from the earlier, range-only a01A12 artifact at commit
`fddc86c`. -/
lemma apm_a01A12_sq_mem_slitPlane {w : ℂ} (hw : 0 < w.re) :
    0 < (w ^ 2).re ∨ (w ^ 2).im ≠ 0 := by
  by_cases him : (w ^ 2).im = 0
  · left
    have him' : w.re * w.im + w.im * w.re = 0 := by
      simpa [pow_two, Complex.mul_im] using him
    have hmul : w.re * w.im = 0 := by nlinarith
    have hwim : w.im = 0 := (mul_eq_zero.mp hmul).resolve_left hw.ne'
    simp [pow_two, Complex.mul_re, hwim]
    exact hw.ne'
  · exact Or.inr him

/-- The principal fourth root still satisfies the exact fourth-power identity;
this avoids all branch bookkeeping when proving injectivity. -/
lemma apm_a01A12_conformalMap_pow_four (z : ℂ) :
    apm_a01A12_conformalMap z ^ 4 = 1 - z ^ 2 := by
  unfold apm_a01A12_conformalMap
  simpa only [one_div] using
    (Complex.cpow_nat_inv_pow (1 - z ^ 2) (by norm_num : (4 : ℕ) ≠ 0))

lemma apm_a01A12_conformalMap_ne_zero {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    apm_a01A12_conformalMap z ≠ 0 := by
  rw [apm_a01A12_conformalMap, Complex.cpow_ne_zero_iff]
  exact Or.inl (apm_a01A12_one_sub_sq_ne_zero hz)

/-- Equality of the fourth roots forces equality of the quadratic inputs;
the alternative `z = -w` is impossible for two upper-half-plane points. -/
lemma apm_a01A12_conformalMap_injOn :
    Set.InjOn apm_a01A12_conformalMap apm_a01A12_H := by
  intro z hz w hw hzw
  have hpow := congrArg (fun u : ℂ ↦ u ^ 4) hzw
  dsimp only at hpow
  rw [apm_a01A12_conformalMap_pow_four,
    apm_a01A12_conformalMap_pow_four] at hpow
  have hsq : z ^ 2 = w ^ 2 := by
    exact sub_right_inj.mp hpow
  have hfac : (z - w) * (z + w) = 0 := by
    calc
      (z - w) * (z + w) = z ^ 2 - w ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · have hneg : z = -w := eq_neg_of_add_eq_zero_left h
    have hzpos : 0 < z.im := hz
    have hwpos : 0 < w.im := hw
    rw [hneg] at hzpos
    simp at hzpos
    linarith

theorem apm_a01a12 :
    apm_a01A12_ConformalBijOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit ∧
    ∀ g : ℂ → ℂ,
      apm_a01A12_ConformalBijOn g apm_a01A12_H apm_a01A12_wedgeSlit ↔
        ∃ a b c d : ℝ, 0 < a * d - b * c ∧
          Set.EqOn g
            (apm_a01A12_conformalMap ∘ apm_a01A12_mobius a b c d)
            apm_a01A12_H := by
  /-
  CLOSER HOP 2 boundary. Going beyond the recovered range-only development,
  this hop closes injectivity of the explicit fourth-root map on the upper
  half-plane. `apm_a01A12_conformalMap_pow_four` uses
  `Complex.cpow_nat_inv_pow` to prove the branch-independent identity
  `f(z)^4 = 1-z²`. Thus equal images imply `z²=w²`; factoring the difference
  leaves `z=w` or `z=-w`, and the latter contradicts positive imaginary parts.
  This is compiled as `apm_a01A12_conformalMap_injOn`.
  `apm_a01A12_conformalMap_ne_zero` also records nonvanishing of the map from
  the already-proved nonzero quadratic input.

  Renewed searches consulted `LEMMA-INDEX.md`, every `ConstructionTargets/`
  module, prior a01A12 commits, complex-analysis siblings, Mathlib's complex
  power and derivative sources, `UpperHalfPlane` Möbius-action sources, and
  git history. The complex-power identity was used above. No theorem was found
  that constructs the required inverse onto the exact wedge slit, packages the
  derivative of this `cpow` composite with its branch hypotheses, or classifies
  every conformal upper-half-plane automorphism as a positive-determinant real
  Möbius map.

  The explicit-map bridge is therefore narrowed to surjectivity and the
  conformal derivative; the independent automorphism-classification bridge
  remains open. The frozen statement is unchanged.
  -/
  sorry
