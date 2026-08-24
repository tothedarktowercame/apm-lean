import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.Schwarz

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
open scoped ComplexConjugate

noncomputable section

def apm_a01A12_H : Set ℂ := {z : ℂ | 0 < z.im}

lemma apm_a01A12_isOpen_H : IsOpen apm_a01A12_H := by
  exact isOpen_lt continuous_const Complex.continuous_im

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

lemma apm_a01A12_deriv_ne_zero_of_fderiv_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : fderiv ℂ f z ≠ 0) : deriv f z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_deriv_eq_norm_fderiv]
  exact norm_ne_zero_iff.mpr hf

lemma apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : deriv f z ≠ 0) : fderiv ℂ f z ≠ 0 := by
  rw [← norm_ne_zero_iff, ← norm_deriv_eq_norm_fderiv]
  exact norm_ne_zero_iff.mpr hf

lemma apm_a01A12_ConformalBijOn.comp {f g : ℂ → ℂ} {U V W : Set ℂ}
    (hf : apm_a01A12_ConformalBijOn f V W)
    (hg : apm_a01A12_ConformalBijOn g U V) :
    apm_a01A12_ConformalBijOn (f ∘ g) U W := by
  refine ⟨hf.1.comp hg.1, ?_⟩
  intro z hz
  have hgz : g z ∈ V := hg.1.1 hz
  rcases hf.2 (g z) hgz with ⟨hfdiff, hffder⟩
  rcases hg.2 z hz with ⟨hgdiff, hgfder⟩
  have hfder : deriv f (g z) ≠ 0 :=
    apm_a01A12_deriv_ne_zero_of_fderiv_ne_zero hffder
  have hgder : deriv g z ≠ 0 :=
    apm_a01A12_deriv_ne_zero_of_fderiv_ne_zero hgfder
  have hcomp : HasDerivAt (f ∘ g) (deriv f (g z) * deriv g z) z :=
    hfdiff.hasDerivAt.comp z hgdiff.hasDerivAt
  have hcompder : deriv (f ∘ g) z ≠ 0 := by
    rw [hcomp.deriv]
    exact mul_ne_zero hfder hgder
  exact ⟨hcomp.differentiableAt,
    apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero hcompder⟩

lemma apm_a01A12_ConformalBijOn.congr_H {f g : ℂ → ℂ} {V : Set ℂ}
    (hf : apm_a01A12_ConformalBijOn f apm_a01A12_H V)
    (hfg : Set.EqOn f g apm_a01A12_H) :
    apm_a01A12_ConformalBijOn g apm_a01A12_H V := by
  refine ⟨hf.1.congr hfg, ?_⟩
  intro z hz
  have heq : Filter.EventuallyEq (nhds z) f g :=
    hfg.eventuallyEq_of_mem (apm_a01A12_isOpen_H.mem_nhds hz)
  rcases hf.2 z hz with ⟨hfdiff, hffder⟩
  refine ⟨hfdiff.congr_of_eventuallyEq heq.symm, ?_⟩
  rw [← heq.fderiv_eq]
  exact hffder

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

lemma apm_a01A12_one_sub_sq_mem_slitPlane {z : ℂ}
    (hz : z ∈ apm_a01A12_H) : 1 - z ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 - z ^ 2).im = 0
  · left
    have hzIm : 0 < z.im := hz
    have hmul : z.re * z.im = 0 := by
      simp [pow_two, Complex.mul_im] at him
      linarith
    have hzRe : z.re = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hzIm.ne'
    simp [pow_two, Complex.mul_re, hzRe]
    positivity
  · exact Or.inr him

/-- The positive-determinant Möbius family contains the identity map. -/
lemma apm_a01A12_mobius_one_zero_zero_one (z : ℂ) :
    apm_a01A12_mobius 1 0 0 1 z = z := by
  simp [apm_a01A12_mobius]

lemma apm_a01A12_identity_parameters_positive :
    (0 : ℝ) < 1 * 1 - 0 * 0 := by norm_num

lemma apm_a01A12_mobius_denom_ne_zero {a b c d : ℝ} {z : ℂ}
    (hdet : 0 < a * d - b * c) (hz : z ∈ apm_a01A12_H) :
    (c : ℂ) * z + d ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  have hre := congrArg Complex.re hzero
  have hc : c = 0 := by
    simp [Complex.mul_im] at him
    exact him.resolve_right hz.ne'
  have hd : d = 0 := by
    simp [Complex.mul_re, hc] at hre
    exact hre
  rw [hc, hd] at hdet
  norm_num at hdet

/-- Imaginary-part formula for the concrete real Möbius family. -/
lemma apm_a01A12_mobius_im {a b c d : ℝ} {z : ℂ}
    (hdet : 0 < a * d - b * c) (hz : z ∈ apm_a01A12_H) :
    (apm_a01A12_mobius a b c d z).im =
      (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [apm_a01A12_mobius, Complex.div_im]
  field_simp [mt Complex.normSq_eq_zero.mp
    (apm_a01A12_mobius_denom_ne_zero hdet hz)]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma apm_a01A12_mobius_mapsTo {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) :
    Set.MapsTo (apm_a01A12_mobius a b c d)
      apm_a01A12_H apm_a01A12_H := by
  intro z hz
  change 0 < (apm_a01A12_mobius a b c d z).im
  rw [apm_a01A12_mobius_im hdet hz]
  exact div_pos (mul_pos hdet hz) (Complex.normSq_pos.mpr
    (apm_a01A12_mobius_denom_ne_zero hdet hz))

lemma apm_a01A12_mobius_inverse_apply {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    apm_a01A12_mobius d (-b) (-c) a
      (apm_a01A12_mobius a b c d z) = z := by
  let D : ℂ := (c : ℂ) * z + d
  let N : ℂ := (a : ℂ) * z + b
  have hD : D ≠ 0 := apm_a01A12_mobius_denom_ne_zero hdet hz
  have hδ : ((a * d - b * c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdet.ne'
  have hnum : (d : ℂ) * (N / D) + (-b : ℝ) =
      ((a * d - b * c : ℝ) : ℂ) * z / D := by
    field_simp [hD]
    dsimp [N, D]
    push_cast
    ring
  have hden : ((-c : ℝ) : ℂ) * (N / D) + a =
      ((a * d - b * c : ℝ) : ℂ) / D := by
    field_simp [hD]
    dsimp [N, D]
    push_cast
    ring
  change ((d : ℂ) * (N / D) + (-b : ℝ)) /
      (((-c : ℝ) : ℂ) * (N / D) + a) = z
  rw [hnum, hden]
  field_simp [hD, hδ]

lemma apm_a01A12_mobius_bijOn {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) :
    Set.BijOn (apm_a01A12_mobius a b c d)
      apm_a01A12_H apm_a01A12_H := by
  have hdet' : 0 < d * a - (-b) * (-c) := by nlinarith
  refine ⟨apm_a01A12_mobius_mapsTo hdet, ?_, ?_⟩
  · intro z hz w hw heq
    have heq' := congrArg (apm_a01A12_mobius d (-b) (-c) a) heq
    rw [apm_a01A12_mobius_inverse_apply hdet hz,
      apm_a01A12_mobius_inverse_apply hdet hw] at heq'
    exact heq'
  · intro w hw
    refine ⟨apm_a01A12_mobius d (-b) (-c) a w,
      apm_a01A12_mobius_mapsTo hdet' hw, ?_⟩
    simpa only [neg_neg] using apm_a01A12_mobius_inverse_apply hdet' hw

lemma apm_a01A12_mobius_hasDerivAt {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    HasDerivAt (apm_a01A12_mobius a b c d)
      (((a * d - b * c : ℝ) : ℂ) /
        (((c : ℂ) * z + d) ^ 2)) z := by
  have hnum : HasDerivAt (fun w : ℂ => (a : ℂ) * w + b) a z := by
    convert ((hasDerivAt_id z).const_mul (a : ℂ)).add
      (hasDerivAt_const z (b : ℂ)) using 1 <;> simp [id]
  have hden : HasDerivAt (fun w : ℂ => (c : ℂ) * w + d) c z := by
    convert ((hasDerivAt_id z).const_mul (c : ℂ)).add
      (hasDerivAt_const z (d : ℂ)) using 1 <;> simp [id]
  unfold apm_a01A12_mobius
  convert hnum.div hden (apm_a01A12_mobius_denom_ne_zero hdet hz) using 1
  push_cast
  field_simp
  ring

lemma apm_a01A12_mobius_fderiv_ne_zero {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    fderiv ℂ (apm_a01A12_mobius a b c d) z ≠ 0 := by
  have hscalar : ((a * d - b * c : ℝ) : ℂ) /
      (((c : ℂ) * z + d) ^ 2) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast hdet.ne')
      (pow_ne_zero _ (apm_a01A12_mobius_denom_ne_zero hdet hz))
  rw [(apm_a01A12_mobius_hasDerivAt hdet hz).hasFDerivAt.fderiv]
  intro hzero
  have happ := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hzero
  exact hscalar (by simpa using happ)

lemma apm_a01A12_mobius_conformalBijOn {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) :
    apm_a01A12_ConformalBijOn (apm_a01A12_mobius a b c d)
      apm_a01A12_H apm_a01A12_H := by
  refine ⟨apm_a01A12_mobius_bijOn hdet, ?_⟩
  intro z hz
  exact ⟨(apm_a01A12_mobius_hasDerivAt hdet hz).differentiableAt,
    apm_a01A12_mobius_fderiv_ne_zero hdet hz⟩

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

/-- The principal fourth root lies strictly in the right half-plane.  This is
the branch-selection fact needed by both the exact-range construction and its
inverse: it rules out the other three fourth roots without choosing an
explicit polar representative. -/
lemma apm_a01A12_conformalMap_re_pos {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    0 < (apm_a01A12_conformalMap z).re := by
  have hexp : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [apm_a01A12_conformalMap, hexp, Complex.cpow_ofReal_re]
  apply mul_pos
  · exact Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (apm_a01A12_one_sub_sq_ne_zero hz)) _
  · apply Real.cos_pos_of_mem_Ioo
    constructor
    · have harg := Complex.neg_pi_lt_arg (1 - z ^ 2)
      have hpi := Real.pi_pos
      norm_num at harg ⊢
      linarith
    · have harg := Complex.arg_le_pi (1 - z ^ 2)
      have hpi := Real.pi_pos
      norm_num at harg ⊢
      linarith

/-- On the slit plane, the principal fourth root divides the principal
argument by four. -/
lemma apm_a01A12_arg_cpow_quarter {x : ℂ} (hx : x ≠ 0) :
    (x ^ (1 / 4 : ℂ)).arg = x.arg / 4 := by
  have hexp : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hexp, Complex.cpow_ofReal]
  have hr : 0 < ‖x‖ ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _
  have hθ : x.arg / 4 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · have harg := Complex.neg_pi_lt_arg x
      have hpi := Real.pi_pos
      norm_num at harg ⊢
      linarith
    · have harg := Complex.arg_le_pi x
      have hpi := Real.pi_pos
      norm_num at harg ⊢
      linarith
  convert Complex.arg_mul_cos_add_sin_mul_I hr hθ using 1 <;> norm_num <;> ring

lemma apm_a01A12_conformalMap_arg_abs_lt {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    |(apm_a01A12_conformalMap z).arg| < Real.pi / 4 := by
  rw [apm_a01A12_conformalMap,
    apm_a01A12_arg_cpow_quarter (apm_a01A12_one_sub_sq_ne_zero hz)]
  rw [abs_lt]
  have hlo := Complex.neg_pi_lt_arg (1 - z ^ 2)
  have hslit := apm_a01A12_one_sub_sq_mem_slitPlane hz
  rw [Complex.mem_slitPlane_iff] at hslit
  have hhi : (1 - z ^ 2).arg < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    exact hslit.imp (fun h => h.le) id
  constructor <;> nlinarith [Real.pi_pos]

/-- The selected fourth root never lands on the deleted unit segment.  The
key point is that a real image would force the upper-half-plane input to be
purely imaginary, in which case its fourth power has real part strictly
larger than one. -/
lemma apm_a01A12_conformalMap_not_mem_unitSegment {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    ¬ (0 ≤ (apm_a01A12_conformalMap z).re ∧
      (apm_a01A12_conformalMap z).re ≤ 1 ∧
      (apm_a01A12_conformalMap z).im = 0) := by
  rintro ⟨hw0, hw1, hwim⟩
  let w := apm_a01A12_conformalMap z
  have hp := apm_a01A12_conformalMap_pow_four z
  have hpim := congrArg Complex.im hp
  have hpre := congrArg Complex.re hp
  have hzre : z.re = 0 := by
    have hprod : z.re * z.im = 0 := by
      dsimp [w] at hwim hpim
      simp [pow_succ, Complex.mul_im, hwim] at hpim
      nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right hz.ne'
  dsimp [w] at hw0 hw1 hwim hpre
  simp [pow_succ, Complex.mul_re, hwim, hzre] at hpre
  have hsquare :
      (apm_a01A12_conformalMap z).re ^ 2 ≤ 1 := by nlinarith
  have hfour :
      (apm_a01A12_conformalMap z).re ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg ((apm_a01A12_conformalMap z).re ^ 2 - 1)]
  have hzim : 0 < z.im := hz
  ring_nf at hpre hfour
  nlinarith [sq_pos_of_pos hzim]

lemma apm_a01A12_conformalMap_mapsTo :
    Set.MapsTo apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit := by
  intro z hz
  rw [apm_a01A12_wedgeSlit, Set.mem_diff]
  exact ⟨⟨apm_a01A12_conformalMap_ne_zero hz,
      apm_a01A12_conformalMap_arg_abs_lt hz⟩,
    apm_a01A12_conformalMap_not_mem_unitSegment hz⟩

/-- Consumer-facing inverse seam: once a square root of `1 - w⁴` has been
oriented into the upper half-plane, the principal fourth-root branch returns
the original wedge point. -/
lemma apm_a01A12_conformalMap_eq_of_sq_eq {w z : ℂ}
    (hwarg : |w.arg| < Real.pi / 4)
    (hzsq : z ^ 2 = 1 - w ^ 4) :
    apm_a01A12_conformalMap z = w := by
  have hlo : -(Real.pi / (4 : ℝ)) < w.arg := by
    exact (abs_lt.mp hwarg).1
  have hhi : w.arg ≤ Real.pi / (4 : ℝ) :=
    (abs_lt.mp hwarg).2.le
  unfold apm_a01A12_conformalMap
  rw [hzsq, sub_sub_cancel]
  simpa only [one_div] using
    (Complex.pow_cpow_nat_inv (x := w) (n := 4) (by norm_num) hlo hhi)

/-- Either sign of a nonreal square root can be selected so that it lies in
the upper half-plane. -/
lemma apm_a01A12_exists_upper_sq_of_exists_nonreal_sq {x : ℂ}
    (hroot : ∃ z : ℂ, z ^ 2 = x ∧ z.im ≠ 0) :
    ∃ z ∈ apm_a01A12_H, z ^ 2 = x := by
  rcases hroot with ⟨z, hzsq, hzim⟩
  rcases lt_or_gt_of_ne hzim with hneg | hpos
  · refine ⟨-z, ?_, ?_⟩
    · simpa [apm_a01A12_H] using neg_pos.mpr hneg
    · simpa using hzsq
  · exact ⟨z, hpos, hzsq⟩

/-- Exact producer seam left for surjectivity: every target point needs a
nonreal square root of `1-w⁴`.  All branch and sign bookkeeping downstream of
that fact is discharged here. -/
lemma apm_a01A12_conformalMap_surjOn_of_nonreal_roots
    (hroots : ∀ w ∈ apm_a01A12_wedgeSlit,
      ∃ z : ℂ, z ^ 2 = 1 - w ^ 4 ∧ z.im ≠ 0) :
    Set.SurjOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit := by
  intro w hw
  obtain ⟨z, hzH, hzsq⟩ :=
    apm_a01A12_exists_upper_sq_of_exists_nonreal_sq (hroots w hw)
  refine ⟨z, hzH, ?_⟩
  exact apm_a01A12_conformalMap_eq_of_sq_eq hw.1.2 hzsq

lemma apm_a01A12_wedgeSlit_has_nonreal_root (w : ℂ)
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    ∃ z : ℂ, z ^ 2 = 1 - w ^ 4 ∧ z.im ≠ 0 := by
  let z : ℂ := (1 - w ^ 4) ^ (2⁻¹ : ℂ)
  have hzsq : z ^ 2 = 1 - w ^ 4 := by
    dsimp [z]
    simpa [← sq] using Complex.cpow_nat_inv_pow (1 - w ^ 4)
      (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨z, hzsq, ?_⟩
  intro hzim
  have hzre0 : 0 ≤ z.re ^ 2 := sq_nonneg z.re
  have hpim : (w ^ 4).im = 0 := by
    have := congrArg Complex.im hzsq
    simp [pow_two, Complex.mul_im, hzim] at this
    linarith
  have hpre : (w ^ 4).re ≤ 1 := by
    have := congrArg Complex.re hzsq
    simp [pow_two, Complex.mul_re, hzim] at this
    nlinarith
  have hw4ne : w ^ 4 ≠ 0 := pow_ne_zero _ hw.1.1
  have hwrecover : (w ^ 4) ^ (1 / 4 : ℂ) = w := by
    have hlo : -(Real.pi / (4 : ℝ)) < w.arg := (abs_lt.mp hw.1.2).1
    have hhi : w.arg ≤ Real.pi / (4 : ℝ) := (abs_lt.mp hw.1.2).2.le
    simpa only [one_div] using
      (Complex.pow_cpow_nat_inv (x := w) (n := 4) (by norm_num) hlo hhi)
  have harg4 : (w ^ 4).arg < Real.pi := by
    have hargEq := apm_a01A12_arg_cpow_quarter hw4ne
    rw [hwrecover] at hargEq
    have := (abs_lt.mp hw.1.2).2
    nlinarith [Real.pi_pos]
  have hpnonneg : 0 ≤ (w ^ 4).re := by
    exact (Complex.arg_lt_pi_iff.mp harg4).resolve_right (fun h => h hpim)
  have hargpow : (w ^ 4).arg = 0 :=
    Complex.arg_eq_zero_iff.mpr ⟨hpnonneg, hpim⟩
  have hargw : w.arg = 0 := by
    have hargEq := apm_a01A12_arg_cpow_quarter hw4ne
    rw [hwrecover, hargpow] at hargEq
    simpa using hargEq
  have hwreal := Complex.arg_eq_zero_iff.mp hargw
  apply hw.2
  refine ⟨hwreal.1, ?_, hwreal.2⟩
  have hpcalc := congrArg Complex.re (show w ^ 4 = w ^ 4 from rfl)
  simp [pow_succ, Complex.mul_re, hwreal.2] at hpre
  nlinarith [sq_nonneg (w.re ^ 2 - 1)]

lemma apm_a01A12_wedgeSlit_fourth_sub_one_mem_slitPlane {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    w ^ 4 - 1 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (w ^ 4 - 1).im = 0
  · left
    rcases apm_a01A12_wedgeSlit_has_nonreal_root w hw with ⟨u, hu, huim⟩
    by_contra hre
    have hrele : (w ^ 4 - 1).re ≤ 0 := le_of_not_gt hre
    have hw4im : (w ^ 4).im = 0 := by simpa using him
    have hure : u.re = 0 := by
      have huimEq := congrArg Complex.im hu
      simp [pow_two, Complex.mul_im, hw4im] at huimEq
      have hprod : u.re * u.im = 0 := by nlinarith
      exact (mul_eq_zero.mp hprod).resolve_right huim
    have hureEq := congrArg Complex.re hu
    simp [pow_two, Complex.mul_re, hure] at hureEq
    have huimsq : 0 < u.im ^ 2 := sq_pos_of_ne_zero huim
    simp at hrele
    ring_nf at hureEq huimsq
    nlinarith
  · exact Or.inr him

def apm_a01A12_analyticInverse (w : ℂ) : ℂ :=
  Complex.I * (w ^ 4 - 1) ^ (1 / 2 : ℂ)

lemma apm_a01A12_fourth_sub_one_ne_zero {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) : w ^ 4 - 1 ≠ 0 := by
  have hslit := apm_a01A12_wedgeSlit_fourth_sub_one_mem_slitPlane hw
  rw [Complex.mem_slitPlane_iff] at hslit
  intro hzero
  rw [hzero] at hslit
  simp at hslit

lemma apm_a01A12_sqrt_fourth_sub_one_re_pos {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    0 < ((w ^ 4 - 1) ^ (1 / 2 : ℂ)).re := by
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp, Complex.cpow_ofReal_re]
  apply mul_pos
  · exact Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (apm_a01A12_fourth_sub_one_ne_zero hw)) _
  · apply Real.cos_pos_of_mem_Ioo
    have hlo := Complex.neg_pi_lt_arg (w ^ 4 - 1)
    have hslit := apm_a01A12_wedgeSlit_fourth_sub_one_mem_slitPlane hw
    rw [Complex.mem_slitPlane_iff] at hslit
    have hhi : (w ^ 4 - 1).arg < Real.pi := by
      apply Complex.arg_lt_pi_iff.mpr
      exact hslit.imp (fun h => h.le) id
    constructor <;> norm_num at hlo hhi ⊢ <;> nlinarith [Real.pi_pos]

lemma apm_a01A12_analyticInverse_mem_H {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    apm_a01A12_analyticInverse w ∈ apm_a01A12_H := by
  change 0 < (Complex.I * (w ^ 4 - 1) ^ (1 / 2 : ℂ)).im
  simpa [Complex.mul_im] using apm_a01A12_sqrt_fourth_sub_one_re_pos hw

lemma apm_a01A12_analyticInverse_sq (w : ℂ) :
    apm_a01A12_analyticInverse w ^ 2 = 1 - w ^ 4 := by
  rw [apm_a01A12_analyticInverse, mul_pow]
  rw [show Complex.I ^ 2 = -1 by norm_num]
  have hsqrt := Complex.cpow_nat_inv_pow (w ^ 4 - 1)
    (by norm_num : (2 : ℕ) ≠ 0)
  rw [show ((1 / 2 : ℂ)) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  rw [hsqrt]
  ring

lemma apm_a01A12_analyticInverse_hasDerivAt {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    HasDerivAt apm_a01A12_analyticInverse
      (Complex.I * ((1 / 2 : ℂ) * (w ^ 4 - 1) ^ ((1 / 2 : ℂ) - 1) *
        (4 * w ^ 3))) w := by
  have hinner : HasDerivAt (fun u : ℂ => u ^ 4 - 1) (4 * w ^ 3) w := by
    convert ((hasDerivAt_id w).pow 4).sub_const 1 using 1 <;> norm_num
  change HasDerivAt
    (fun u : ℂ => Complex.I * (u ^ 4 - 1) ^ (1 / 2 : ℂ)) _ w
  convert (hasDerivAt_const w Complex.I).mul
      (hinner.cpow_const (c := (1 / 2 : ℂ))
        (apm_a01A12_wedgeSlit_fourth_sub_one_mem_slitPlane hw)) using 1 <;>
    simp [Pi.mul_apply]

lemma apm_a01A12_analyticInverse_deriv_ne_zero {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    deriv apm_a01A12_analyticInverse w ≠ 0 := by
  rw [(apm_a01A12_analyticInverse_hasDerivAt hw).deriv]
  apply mul_ne_zero
  · exact Complex.I_ne_zero
  apply mul_ne_zero
  · apply mul_ne_zero
    · norm_num
    · rw [Complex.cpow_ne_zero_iff]
      left
      exact apm_a01A12_fourth_sub_one_ne_zero hw
  · apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero _ hw.1.1

def apm_a01A12_inverseMap (w : ℂ) : ℂ :=
  apm_a01A12_analyticInverse w

lemma apm_a01A12_inverseMap_mem_H {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    apm_a01A12_inverseMap w ∈ apm_a01A12_H := by
  exact apm_a01A12_analyticInverse_mem_H hw

lemma apm_a01A12_inverseMap_sq {w : ℂ} :
    apm_a01A12_inverseMap w ^ 2 = 1 - w ^ 4 := by
  exact apm_a01A12_analyticInverse_sq w

lemma apm_a01A12_conformalMap_inverseMap {w : ℂ}
    (hw : w ∈ apm_a01A12_wedgeSlit) :
    apm_a01A12_conformalMap (apm_a01A12_inverseMap w) = w :=
  apm_a01A12_conformalMap_eq_of_sq_eq hw.1.2 apm_a01A12_inverseMap_sq


lemma apm_a01A12_conformalMap_hasDerivAt {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    HasDerivAt apm_a01A12_conformalMap
      ((1 / 4 : ℂ) * (1 - z ^ 2) ^ ((1 / 4 : ℂ) - 1) * (-2 * z)) z := by
  have hinner : HasDerivAt (fun w : ℂ ↦ 1 - w ^ 2) (-2 * z) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).pow 2) using 1 <;> simp [id] <;> ring
  change HasDerivAt (fun w : ℂ ↦ (1 - w ^ 2) ^ (1 / 4 : ℂ)) _ z
  exact hinner.cpow_const (c := (1 / 4 : ℂ))
    (apm_a01A12_one_sub_sq_mem_slitPlane hz)

lemma apm_a01A12_conformalMap_fderiv_ne_zero {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    fderiv ℂ apm_a01A12_conformalMap z ≠ 0 := by
  let c : ℂ :=
    (1 / 4 : ℂ) * (1 - z ^ 2) ^ ((1 / 4 : ℂ) - 1) * (-2 * z)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
    · rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (apm_a01A12_one_sub_sq_ne_zero hz)
    · apply mul_ne_zero
      · norm_num
      · intro hz0
        subst z
        simpa [apm_a01A12_H] using hz
  have hderiv :=
    (apm_a01A12_conformalMap_hasDerivAt hz).hasFDerivAt.fderiv
  rw [hderiv]
  intro hzero
  have happ := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) hzero
  exact hc (by simpa [c] using happ)

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

lemma apm_a01A12_inverseMap_conformalMap {z : ℂ}
    (hz : z ∈ apm_a01A12_H) :
    apm_a01A12_inverseMap (apm_a01A12_conformalMap z) = z := by
  apply apm_a01A12_conformalMap_injOn
    (apm_a01A12_inverseMap_mem_H (apm_a01A12_conformalMap_mapsTo hz)) hz
  exact apm_a01A12_conformalMap_inverseMap
    (apm_a01A12_conformalMap_mapsTo hz)

lemma apm_a01A12_inverseMap_bijOn :
    Set.BijOn apm_a01A12_inverseMap
      apm_a01A12_wedgeSlit apm_a01A12_H := by
  refine ⟨fun _ hw => apm_a01A12_inverseMap_mem_H hw, ?_, ?_⟩
  · intro w hw v hv heq
    have heq' := congrArg apm_a01A12_conformalMap heq
    rw [apm_a01A12_conformalMap_inverseMap hw,
      apm_a01A12_conformalMap_inverseMap hv] at heq'
    exact heq'
  · intro z hz
    exact ⟨apm_a01A12_conformalMap z,
      apm_a01A12_conformalMap_mapsTo hz,
      apm_a01A12_inverseMap_conformalMap hz⟩

theorem apm_a01A12_inverseMap_conformalBijOn :
    apm_a01A12_ConformalBijOn apm_a01A12_inverseMap
      apm_a01A12_wedgeSlit apm_a01A12_H := by
  refine ⟨apm_a01A12_inverseMap_bijOn, ?_⟩
  intro w hw
  constructor
  · simpa [apm_a01A12_inverseMap] using
      (apm_a01A12_analyticInverse_hasDerivAt hw).differentiableAt
  · apply apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero
    simpa [apm_a01A12_inverseMap] using
      apm_a01A12_analyticInverse_deriv_ne_zero hw

/-- Once the exact range is known, the previously compiled injectivity and
derivative calculations assemble the displayed map into a conformal
bijection. -/
theorem apm_a01A12_conformalMap_conformalBijOn
    (hmap : Set.MapsTo apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit)
    (hsurj : Set.SurjOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    apm_a01A12_ConformalBijOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit := by
  constructor
  · exact ⟨hmap, apm_a01A12_conformalMap_injOn, hsurj⟩
  · intro z hz
    exact ⟨(apm_a01A12_conformalMap_hasDerivAt hz).differentiableAt,
      apm_a01A12_conformalMap_fderiv_ne_zero hz⟩

def apm_a01A12_inducedAutomorphism (g : ℂ → ℂ) : ℂ → ℂ :=
  apm_a01A12_inverseMap ∘ g

lemma apm_a01A12_inducedAutomorphism_conformalBijOn {g : ℂ → ℂ}
    (hg : apm_a01A12_ConformalBijOn g
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    apm_a01A12_ConformalBijOn (apm_a01A12_inducedAutomorphism g)
      apm_a01A12_H apm_a01A12_H := by
  exact apm_a01A12_inverseMap_conformalBijOn.comp hg

lemma apm_a01A12_conformalMap_inducedAutomorphism {g : ℂ → ℂ}
    (hg : apm_a01A12_ConformalBijOn g
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    Set.EqOn (apm_a01A12_conformalMap ∘
      apm_a01A12_inducedAutomorphism g) g apm_a01A12_H := by
  intro z hz
  exact apm_a01A12_conformalMap_inverseMap (hg.1.1 hz)

def apm_a01A12_disk : Set ℂ := {w : ℂ | ‖w‖ < 1}

def apm_a01A12_cayley (z : ℂ) : ℂ :=
  (z - Complex.I) / (z + Complex.I)

def apm_a01A12_cayleyInv (w : ℂ) : ℂ :=
  Complex.I * (1 + w) / (1 - w)

lemma apm_a01A12_add_I_ne_zero {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    z + Complex.I ≠ 0 := by
  change 0 < z.im at hz
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

lemma apm_a01A12_one_sub_ne_zero {w : ℂ} (hw : w ∈ apm_a01A12_disk) :
    1 - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := (sub_eq_zero.mp h).symm
  rw [hw1] at hw
  simpa [apm_a01A12_disk] using hw

lemma apm_a01A12_cayley_mapsTo :
    Set.MapsTo apm_a01A12_cayley apm_a01A12_H apm_a01A12_disk := by
  intro z hz
  change 0 < z.im at hz
  change ‖(z - Complex.I) / (z + Complex.I)‖ < 1
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (apm_a01A12_add_I_ne_zero hz))]
  have hsq : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]

lemma apm_a01A12_cayleyInv_mapsTo :
    Set.MapsTo apm_a01A12_cayleyInv apm_a01A12_disk apm_a01A12_H := by
  intro w hw
  change ‖w‖ < 1 at hw
  change 0 < (Complex.I * (1 + w) / (1 - w)).im
  have him : (Complex.I * (1 + w) / (1 - w)).im =
      (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [him]
  apply div_pos
  · have hn : ‖w‖ ^ 2 < 1 := by nlinarith [hw, norm_nonneg w]
    simpa [Complex.normSq_eq_norm_sq] using hn
  · exact Complex.normSq_pos.mpr (apm_a01A12_one_sub_ne_zero hw)

lemma apm_a01A12_cayleyInv_cayley {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    apm_a01A12_cayleyInv (apm_a01A12_cayley z) = z := by
  rw [apm_a01A12_cayleyInv, apm_a01A12_cayley]
  field_simp [apm_a01A12_add_I_ne_zero hz]
  ring

lemma apm_a01A12_cayley_cayleyInv {w : ℂ} (hw : w ∈ apm_a01A12_disk) :
    apm_a01A12_cayley (apm_a01A12_cayleyInv w) = w := by
  rw [apm_a01A12_cayley, apm_a01A12_cayleyInv]
  field_simp [apm_a01A12_one_sub_ne_zero hw]
  ring

lemma apm_a01A12_cayley_bijOn :
    Set.BijOn apm_a01A12_cayley apm_a01A12_H apm_a01A12_disk := by
  refine ⟨apm_a01A12_cayley_mapsTo, ?_, ?_⟩
  · intro z hz u hu heq
    have := congrArg apm_a01A12_cayleyInv heq
    simpa [apm_a01A12_cayleyInv_cayley hz,
      apm_a01A12_cayleyInv_cayley hu] using this
  · intro w hw
    exact ⟨apm_a01A12_cayleyInv w, apm_a01A12_cayleyInv_mapsTo hw,
      apm_a01A12_cayley_cayleyInv hw⟩

lemma apm_a01A12_cayleyInv_bijOn :
    Set.BijOn apm_a01A12_cayleyInv apm_a01A12_disk apm_a01A12_H := by
  refine ⟨apm_a01A12_cayleyInv_mapsTo, ?_, ?_⟩
  · intro w hw v hv heq
    have := congrArg apm_a01A12_cayley heq
    simpa [apm_a01A12_cayley_cayleyInv hw,
      apm_a01A12_cayley_cayleyInv hv] using this
  · intro z hz
    exact ⟨apm_a01A12_cayley z, apm_a01A12_cayley_mapsTo hz,
      apm_a01A12_cayleyInv_cayley hz⟩

lemma apm_a01A12_cayley_hasDerivAt {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    HasDerivAt apm_a01A12_cayley
      (2 * Complex.I / (z + Complex.I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const Complex.I).div
    ((hasDerivAt_id z).add_const Complex.I) (apm_a01A12_add_I_ne_zero hz)
  convert h using 1 <;> simp [apm_a01A12_cayley] <;> ring

lemma apm_a01A12_cayleyInv_hasDerivAt {w : ℂ}
    (hw : w ∈ apm_a01A12_disk) :
    HasDerivAt apm_a01A12_cayleyInv
      (2 * Complex.I / (1 - w) ^ 2) w := by
  have hnum := (hasDerivAt_const w Complex.I).mul
    ((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w))
  have hden := (hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)
  have h := hnum.div hden (apm_a01A12_one_sub_ne_zero hw)
  convert h using 1 <;> simp [apm_a01A12_cayleyInv] <;> ring

theorem apm_a01A12_cayley_conformalBijOn :
    apm_a01A12_ConformalBijOn apm_a01A12_cayley
      apm_a01A12_H apm_a01A12_disk := by
  refine ⟨apm_a01A12_cayley_bijOn, ?_⟩
  intro z hz
  refine ⟨(apm_a01A12_cayley_hasDerivAt hz).differentiableAt, ?_⟩
  apply apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero
  rw [(apm_a01A12_cayley_hasDerivAt hz).deriv]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (pow_ne_zero _ (apm_a01A12_add_I_ne_zero hz))

theorem apm_a01A12_cayleyInv_conformalBijOn :
    apm_a01A12_ConformalBijOn apm_a01A12_cayleyInv
      apm_a01A12_disk apm_a01A12_H := by
  refine ⟨apm_a01A12_cayleyInv_bijOn, ?_⟩
  intro w hw
  refine ⟨(apm_a01A12_cayleyInv_hasDerivAt hw).differentiableAt, ?_⟩
  apply apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero
  rw [(apm_a01A12_cayleyInv_hasDerivAt hw).deriv]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (pow_ne_zero _ (apm_a01A12_one_sub_ne_zero hw))

def apm_a01A12_diskConjugate (h : ℂ → ℂ) : ℂ → ℂ :=
  apm_a01A12_cayley ∘ h ∘ apm_a01A12_cayleyInv

lemma apm_a01A12_diskConjugate_conformalBijOn {h : ℂ → ℂ}
    (hh : apm_a01A12_ConformalBijOn h apm_a01A12_H apm_a01A12_H) :
    apm_a01A12_ConformalBijOn (apm_a01A12_diskConjugate h)
      apm_a01A12_disk apm_a01A12_disk := by
  exact apm_a01A12_cayley_conformalBijOn.comp
    (hh.comp apm_a01A12_cayleyInv_conformalBijOn)

lemma apm_a01A12_induced_diskAutomorphism {g : ℂ → ℂ}
    (hg : apm_a01A12_ConformalBijOn g
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    apm_a01A12_ConformalBijOn
      (apm_a01A12_diskConjugate (apm_a01A12_inducedAutomorphism g))
      apm_a01A12_disk apm_a01A12_disk := by
  exact apm_a01A12_diskConjugate_conformalBijOn
    (apm_a01A12_inducedAutomorphism_conformalBijOn hg)

def apm_a01A12_diskShift (a z : ℂ) : ℂ :=
  (z - a) / (1 - conj a * z)

lemma apm_a01A12_diskShift_denom_ne_zero {a z : ℂ}
    (ha : a ∈ apm_a01A12_disk) (hz : z ∈ apm_a01A12_disk) :
    1 - conj a * z ≠ 0 := by
  change ‖a‖ < 1 at ha
  change ‖z‖ < 1 at hz
  intro h
  have heq : conj a * z = 1 := (sub_eq_zero.mp h).symm
  have hn := congrArg norm heq
  simp [norm_mul] at hn
  nlinarith [norm_nonneg a, norm_nonneg z]

lemma apm_a01A12_diskShift_normSq (a z : ℂ)
    (hden : 1 - conj a * z ≠ 0) :
    1 - Complex.normSq (apm_a01A12_diskShift a z) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) /
        Complex.normSq (1 - conj a * z) := by
  rw [apm_a01A12_diskShift, Complex.normSq_div]
  have hdnsq : Complex.normSq (1 - conj a * z) ≠ 0 :=
    (Complex.normSq_pos.mpr hden).ne'
  apply (eq_div_iff hdnsq).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hdnsq]
  simp [Complex.normSq_sub, Complex.normSq_mul, mul_comm]
  ring

lemma apm_a01A12_diskShift_mapsTo (a : ℂ) (ha : a ∈ apm_a01A12_disk) :
    Set.MapsTo (apm_a01A12_diskShift a)
      apm_a01A12_disk apm_a01A12_disk := by
  intro z hz
  have hden := apm_a01A12_diskShift_denom_ne_zero ha hz
  have hid := apm_a01A12_diskShift_normSq a z hden
  change ‖apm_a01A12_diskShift a z‖ < 1
  rw [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
  have ha' : 0 < 1 - Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]
    change ‖a‖ < 1 at ha
    nlinarith [norm_nonneg a]
  have hz' : 0 < 1 - Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    change ‖z‖ < 1 at hz
    nlinarith [norm_nonneg z]
  have hd' : 0 < Complex.normSq (1 - conj a * z) :=
    Complex.normSq_pos.mpr hden
  rw [← sub_pos] at ⊢
  rw [hid]
  positivity

lemma apm_a01A12_neg_mem_disk {a : ℂ} (ha : a ∈ apm_a01A12_disk) :
    -a ∈ apm_a01A12_disk := by
  simpa [apm_a01A12_disk] using ha

lemma apm_a01A12_diskShift_neg_left {a z : ℂ}
    (ha : a ∈ apm_a01A12_disk) (hz : z ∈ apm_a01A12_disk) :
    apm_a01A12_diskShift (-a) (apm_a01A12_diskShift a z) = z := by
  have hden := apm_a01A12_diskShift_denom_ne_zero ha hz
  have himage := apm_a01A12_diskShift_mapsTo a ha hz
  have hden' := apm_a01A12_diskShift_denom_ne_zero
    (apm_a01A12_neg_mem_disk ha) himage
  simp only [apm_a01A12_diskShift] at hden' ⊢
  apply (div_eq_iff hden').2
  have hdencomm : 1 - z * conj a ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hden, hdencomm]
  simp
  ring

lemma apm_a01A12_diskShift_bijOn (a : ℂ) (ha : a ∈ apm_a01A12_disk) :
    Set.BijOn (apm_a01A12_diskShift a)
      apm_a01A12_disk apm_a01A12_disk := by
  refine ⟨apm_a01A12_diskShift_mapsTo a ha, ?_, ?_⟩
  · intro z hz w hw heq
    have heq' := congrArg (apm_a01A12_diskShift (-a)) heq
    rw [apm_a01A12_diskShift_neg_left ha hz,
      apm_a01A12_diskShift_neg_left ha hw] at heq'
    exact heq'
  · intro w hw
    refine ⟨apm_a01A12_diskShift (-a) w,
      apm_a01A12_diskShift_mapsTo (-a) (apm_a01A12_neg_mem_disk ha) hw, ?_⟩
    simpa using apm_a01A12_diskShift_neg_left
      (apm_a01A12_neg_mem_disk ha) hw

lemma apm_a01A12_diskShift_hasDerivAt {a z : ℂ}
    (ha : a ∈ apm_a01A12_disk) (hz : z ∈ apm_a01A12_disk) :
    HasDerivAt (apm_a01A12_diskShift a)
      ((1 - (Complex.normSq a : ℂ)) / (1 - conj a * z) ^ 2) z := by
  have hnum := (hasDerivAt_id z).sub_const a
  have hden := (hasDerivAt_const z (1 : ℂ)).sub
    ((hasDerivAt_const z (conj a)).mul (hasDerivAt_id z))
  have h := hnum.div hden (apm_a01A12_diskShift_denom_ne_zero ha hz)
  convert h using 1 <;> simp [apm_a01A12_diskShift, Complex.normSq_eq_conj_mul_self] <;> ring

theorem apm_a01A12_diskShift_conformalBijOn (a : ℂ)
    (ha : a ∈ apm_a01A12_disk) :
    apm_a01A12_ConformalBijOn (apm_a01A12_diskShift a)
      apm_a01A12_disk apm_a01A12_disk := by
  refine ⟨apm_a01A12_diskShift_bijOn a ha, ?_⟩
  intro z hz
  refine ⟨(apm_a01A12_diskShift_hasDerivAt ha hz).differentiableAt, ?_⟩
  apply apm_a01A12_fderiv_ne_zero_of_deriv_ne_zero
  rw [(apm_a01A12_diskShift_hasDerivAt ha hz).deriv]
  apply div_ne_zero
  · norm_cast
    rw [Complex.normSq_eq_norm_sq]
    change ‖a‖ < 1 at ha
    nlinarith [norm_nonneg a]
  · exact pow_ne_zero _ (apm_a01A12_diskShift_denom_ne_zero ha hz)

lemma apm_a01A12_zero_mem_disk : (0 : ℂ) ∈ apm_a01A12_disk := by
  simp [apm_a01A12_disk]

lemma apm_a01A12_isOpen_disk : IsOpen apm_a01A12_disk := by
  exact isOpen_lt continuous_norm continuous_const

def apm_a01A12_normalizeDiskMap (f : ℂ → ℂ) : ℂ → ℂ :=
  apm_a01A12_diskShift (f 0) ∘ f

lemma apm_a01A12_normalizeDiskMap_conformalBijOn {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    apm_a01A12_ConformalBijOn (apm_a01A12_normalizeDiskMap f)
      apm_a01A12_disk apm_a01A12_disk := by
  exact (apm_a01A12_diskShift_conformalBijOn (f 0)
    (hf.1.1 apm_a01A12_zero_mem_disk)).comp hf

lemma apm_a01A12_normalizeDiskMap_zero {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    apm_a01A12_normalizeDiskMap f 0 = 0 := by
  simp [apm_a01A12_normalizeDiskMap, apm_a01A12_diskShift]

lemma apm_a01A12_normalized_induced_diskAutomorphism {g : ℂ → ℂ}
    (hg : apm_a01A12_ConformalBijOn g
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    let k := apm_a01A12_normalizeDiskMap
      (apm_a01A12_diskConjugate (apm_a01A12_inducedAutomorphism g))
    apm_a01A12_ConformalBijOn k apm_a01A12_disk apm_a01A12_disk ∧
      k 0 = 0 := by
  intro k
  have hf := apm_a01A12_induced_diskAutomorphism hg
  exact ⟨apm_a01A12_normalizeDiskMap_conformalBijOn hf,
    apm_a01A12_normalizeDiskMap_zero hf⟩

def apm_a01A12_diskInverse (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn f apm_a01A12_disk

lemma apm_a01A12_diskInverse_invOn {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    Set.InvOn (apm_a01A12_diskInverse f) f
      apm_a01A12_disk apm_a01A12_disk := by
  exact hf.1.invOn_invFunOn

lemma apm_a01A12_diskInverse_mapsTo {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    Set.MapsTo (apm_a01A12_diskInverse f)
      apm_a01A12_disk apm_a01A12_disk := by
  exact hf.1.2.2.mapsTo_invFunOn

lemma apm_a01A12_diskInverse_differentiableOn {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    DifferentiableOn ℂ (apm_a01A12_diskInverse f) apm_a01A12_disk := by
  intro w hw
  let z := apm_a01A12_diskInverse f w
  have hz : z ∈ apm_a01A12_disk := apm_a01A12_diskInverse_mapsTo hf hw
  have hfw : f z = w := apm_a01A12_diskInverse_invOn hf |>.2 hw
  have hfOn : DifferentiableOn ℂ f apm_a01A12_disk :=
    fun u hu => (hf.2 u hu).1.differentiableWithinAt
  have hf_at : AnalyticAt ℂ f z :=
    hfOn.analyticAt (apm_a01A12_isOpen_disk.mem_nhds hz)
  have hf_deriv : deriv f z ≠ 0 :=
    apm_a01A12_deriv_ne_zero_of_fderiv_ne_zero (hf.2 z hz).2
  have hcomp : AnalyticAt ℂ (apm_a01A12_diskInverse f ∘ f) z := by
    apply analyticAt_id.congr
    filter_upwards [apm_a01A12_isOpen_disk.eventually_mem hz] with u hu
    exact (apm_a01A12_diskInverse_invOn hf |>.1 hu).symm
  rw [← hfw]
  exact ((analyticAt_comp_iff_of_deriv_ne_zero hf_at hf_deriv).mp hcomp).differentiableAt
    |>.differentiableWithinAt

lemma apm_a01A12_norm_deriv_eq_one_of_diskAutomorphism_zero {k : ℂ → ℂ}
    (hk : apm_a01A12_ConformalBijOn k
      apm_a01A12_disk apm_a01A12_disk)
    (hk0 : k 0 = 0) : ‖deriv k 0‖ = 1 := by
  let j := apm_a01A12_diskInverse k
  have hkdiff : DifferentiableOn ℂ k (Metric.ball 0 1) := by
    intro z hz
    exact (hk.2 z (by simpa [apm_a01A12_disk, Metric.mem_ball,
      dist_zero_right] using hz)).1.differentiableWithinAt
  have hjdiff : DifferentiableOn ℂ j (Metric.ball 0 1) := by
    intro z hz
    have hz' : z ∈ apm_a01A12_disk := by
      simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using hz
    have hj := apm_a01A12_diskInverse_differentiableOn hk z hz'
    exact (hj.differentiableAt (apm_a01A12_isOpen_disk.mem_nhds hz')).differentiableWithinAt
  have hkmaps : Set.MapsTo k (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    apply Metric.ball_subset_closedBall
    simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using
      hk.1.1 (by simpa [apm_a01A12_disk, Metric.mem_ball,
        dist_zero_right] using hz)
  have hjmaps : Set.MapsTo j (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    apply Metric.ball_subset_closedBall
    simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right, j] using
      apm_a01A12_diskInverse_mapsTo hk (by
        simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using hz)
  have hj0 : j 0 = 0 := by
    have hleft := apm_a01A12_diskInverse_invOn hk |>.1 apm_a01A12_zero_mem_disk
    simpa [j, hk0] using hleft
  have hk_le : ‖deriv k 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hkdiff (by simpa [hk0] using hkmaps) (by norm_num)
  have hj_le : ‖deriv j 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hjdiff (by simpa [hj0] using hjmaps) (by norm_num)
  have hk_at : DifferentiableAt ℂ k 0 :=
    hkdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hj_at : DifferentiableAt ℂ j 0 :=
    hjdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hk_at_j : DifferentiableAt ℂ k (j 0) := by simpa [hj0] using hk_at
  have hcomp : deriv (k ∘ j) 0 = deriv k (j 0) * deriv j 0 :=
    deriv_comp 0 hk_at_j hj_at
  have hcomp_id : deriv (k ∘ j) 0 = 1 := by
    have heq : (k ∘ j) =ᶠ[nhds 0] id := by
      filter_upwards [Metric.isOpen_ball.eventually_mem (by simp : (0 : ℂ) ∈ Metric.ball 0 1)]
        with z hz
      exact apm_a01A12_diskInverse_invOn hk |>.2
        (by simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using hz)
    simpa using heq.deriv_eq
  rw [hj0] at hcomp
  have hprod : ‖deriv k 0‖ * ‖deriv j 0‖ = 1 := by
    rw [← norm_mul, ← hcomp, hcomp_id, norm_one]
  nlinarith [norm_nonneg (deriv k 0), norm_nonneg (deriv j 0)]

lemma apm_a01A12_schwarz_rotation {k : ℂ → ℂ}
    (hk : apm_a01A12_ConformalBijOn k
      apm_a01A12_disk apm_a01A12_disk)
    (hk0 : k 0 = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ Set.EqOn k (fun z => c * z) apm_a01A12_disk := by
  have hkdiff : DifferentiableOn ℂ k (Metric.ball 0 1) := by
    intro z hz
    exact (hk.2 z (by simpa [apm_a01A12_disk, Metric.mem_ball,
      dist_zero_right] using hz)).1.differentiableWithinAt
  have hmaps : Set.MapsTo k (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro z hz
    simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using
      hk.1.1 (by simpa [apm_a01A12_disk, Metric.mem_ball,
        dist_zero_right] using hz)
  have hnorm := apm_a01A12_norm_deriv_eq_one_of_diskAutomorphism_zero hk hk0
  refine ⟨deriv k 0, hnorm, ?_⟩
  intro z hz
  have hzero : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
  have hslope : ‖dslope k 0 0‖ = (1 : ℝ) / 1 := by simpa using hnorm
  have hmapsClosed : Set.MapsTo k (Metric.ball 0 1)
      (Metric.closedBall (k 0) 1) := by
    rw [hk0]
    exact fun u hu => Metric.ball_subset_closedBall (hmaps hu)
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hkdiff hmapsClosed hzero hslope
  simpa [hk0, mul_comm] using haffine
    (by simpa [apm_a01A12_disk, Metric.mem_ball, dist_zero_right] using hz)

lemma apm_a01A12_diskAutomorphism_formula {f : ℂ → ℂ}
    (hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk) :
    ∃ a c : ℂ, a ∈ apm_a01A12_disk ∧ ‖c‖ = 1 ∧
      Set.EqOn f (fun z => apm_a01A12_diskShift (-a) (c * z))
        apm_a01A12_disk := by
  let a := f 0
  let k := apm_a01A12_normalizeDiskMap f
  have ha : a ∈ apm_a01A12_disk := hf.1.1 apm_a01A12_zero_mem_disk
  have hk : apm_a01A12_ConformalBijOn k
      apm_a01A12_disk apm_a01A12_disk :=
    apm_a01A12_normalizeDiskMap_conformalBijOn hf
  have hk0 : k 0 = 0 := apm_a01A12_normalizeDiskMap_zero hf
  obtain ⟨c, hc, hkc⟩ := apm_a01A12_schwarz_rotation hk hk0
  refine ⟨a, c, ha, hc, ?_⟩
  intro z hz
  have hfz : f z ∈ apm_a01A12_disk := hf.1.1 hz
  have hcz : c * z ∈ apm_a01A12_disk := by
    change ‖c * z‖ < 1
    rw [norm_mul, hc, one_mul]
    exact hz
  calc
    f z = apm_a01A12_diskShift (-a) (apm_a01A12_diskShift a (f z)) :=
      (apm_a01A12_diskShift_neg_left ha hfz).symm
    _ = apm_a01A12_diskShift (-a) (c * z) := by
      congr 1
      exact hkc hz

def apm_a01A12_diskBeta (a s : ℂ) : ℂ := a * conj s

def apm_a01A12_realA (a s : ℂ) : ℝ := s.re + (apm_a01A12_diskBeta a s).re
def apm_a01A12_realB (a s : ℂ) : ℝ := s.im - (apm_a01A12_diskBeta a s).im
def apm_a01A12_realC (a s : ℂ) : ℝ := -s.im - (apm_a01A12_diskBeta a s).im
def apm_a01A12_realD (a s : ℂ) : ℝ := s.re - (apm_a01A12_diskBeta a s).re

lemma apm_a01A12_unit_sqrt {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ s : ℂ, s ^ 2 = c ∧ ‖s‖ = 1 := by
  let s : ℂ := c ^ ((2 : ℕ)⁻¹ : ℂ)
  have hs : s ^ 2 = c := by
    exact Complex.cpow_nat_inv_pow c (by norm_num)
  refine ⟨s, hs, ?_⟩
  have hn := congrArg norm hs
  rw [norm_pow, hc] at hn
  nlinarith [norm_nonneg s]

lemma apm_a01A12_real_coeff_det {a s : ℂ}
    (ha : a ∈ apm_a01A12_disk) (hs : ‖s‖ = 1) :
    0 < apm_a01A12_realA a s * apm_a01A12_realD a s -
      apm_a01A12_realB a s * apm_a01A12_realC a s := by
  have hdet : apm_a01A12_realA a s * apm_a01A12_realD a s -
      apm_a01A12_realB a s * apm_a01A12_realC a s =
      Complex.normSq s - Complex.normSq (apm_a01A12_diskBeta a s) := by
    simp [apm_a01A12_realA, apm_a01A12_realB, apm_a01A12_realC,
      apm_a01A12_realD, Complex.normSq_apply]
    ring
  rw [hdet, apm_a01A12_diskBeta, Complex.normSq_mul, Complex.normSq_conj]
  simp only [Complex.normSq_eq_norm_sq, hs, one_pow, mul_one]
  change ‖a‖ < 1 at ha
  nlinarith [norm_nonneg a]

lemma apm_a01A12_conj_mul_self_eq_one {s : ℂ} (hs : ‖s‖ = 1) :
    conj s * s = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hs]
  norm_num

lemma apm_a01A12_diskShift_su_formula (a s w : ℂ) (hs : ‖s‖ = 1) :
    apm_a01A12_diskShift (-a) (s ^ 2 * w) =
      (s * w + apm_a01A12_diskBeta a s) /
        (conj (apm_a01A12_diskBeta a s) * w + conj s) := by
  have hs0 : conj s ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp [hs] at hn
  have hunit := apm_a01A12_conj_mul_self_eq_one hs
  have hqsq : conj s * s ^ 2 = s := by
    rw [pow_two, ← mul_assoc, hunit, one_mul]
  rw [apm_a01A12_diskShift]
  simp [apm_a01A12_diskBeta]
  symm
  calc
    (s * w + a * conj s) / (conj a * s * w + conj s) =
        conj s * (s ^ 2 * w + a) /
          (conj s * (1 + conj a * (s ^ 2 * w))) := by
      congr 1
      · rw [mul_add]
        symm
        calc
          conj s * (s ^ 2 * w) + conj s * a =
              (conj s * s ^ 2) * w + a * conj s := by ring
          _ = s * w + a * conj s := by rw [hqsq]
      · rw [mul_add, mul_one]
        symm
        calc
          conj s + conj s * (conj a * (s ^ 2 * w)) =
              conj s + conj a * (conj s * s ^ 2) * w := by ring
          _ = conj a * s * w + conj s := by rw [hqsq]; ring
    _ = (s ^ 2 * w + a) / (1 + conj a * (s ^ 2 * w)) :=
      mul_div_mul_left _ _ hs0

def apm_a01A12_suNum (a s z : ℂ) : ℂ :=
  (s + apm_a01A12_diskBeta a s) * z +
    Complex.I * (apm_a01A12_diskBeta a s - s)

def apm_a01A12_suDen (a s z : ℂ) : ℂ :=
  (conj (apm_a01A12_diskBeta a s) + conj s) * z +
    Complex.I * (conj s - conj (apm_a01A12_diskBeta a s))

lemma apm_a01A12_su_at_cayley (a s z : ℂ)
    (hzi : z + Complex.I ≠ 0) :
    (s * apm_a01A12_cayley z + apm_a01A12_diskBeta a s) /
        (conj (apm_a01A12_diskBeta a s) * apm_a01A12_cayley z + conj s) =
      apm_a01A12_suNum a s z / apm_a01A12_suDen a s z := by
  have hNrel :
      (s * apm_a01A12_cayley z + apm_a01A12_diskBeta a s) *
          (z + Complex.I) = apm_a01A12_suNum a s z := by
    rw [apm_a01A12_cayley]
    field_simp [hzi]
    simp [apm_a01A12_suNum]
    ring
  have hDrel :
      (conj (apm_a01A12_diskBeta a s) * apm_a01A12_cayley z + conj s) *
          (z + Complex.I) = apm_a01A12_suDen a s z := by
    rw [apm_a01A12_cayley]
    field_simp [hzi]
    simp [apm_a01A12_suDen]
    ring
  rw [← hNrel, ← hDrel]
  exact (mul_div_mul_right _ _ hzi).symm

lemma apm_a01A12_cayleyInv_div (N D : ℂ) (hD : D ≠ 0)
    (hone : 1 - N / D ≠ 0) :
    apm_a01A12_cayleyInv (N / D) =
      Complex.I * (D + N) / (D - N) := by
  rw [apm_a01A12_cayleyInv, one_add_div hD, one_sub_div hD]
  field_simp [hD, hone]

lemma apm_a01A12_suDen_add_suNum (a s z : ℂ) :
    apm_a01A12_suDen a s z + apm_a01A12_suNum a s z =
      2 * ((apm_a01A12_realA a s : ℂ) * z + apm_a01A12_realB a s) := by
  apply Complex.ext <;>
    simp [apm_a01A12_suDen, apm_a01A12_suNum, apm_a01A12_realA,
      apm_a01A12_realB, apm_a01A12_diskBeta, Complex.mul_re, Complex.mul_im] <;>
    ring

lemma apm_a01A12_suDen_sub_suNum (a s z : ℂ) :
    apm_a01A12_suDen a s z - apm_a01A12_suNum a s z =
      2 * Complex.I * ((apm_a01A12_realC a s : ℂ) * z +
        apm_a01A12_realD a s) := by
  apply Complex.ext <;>
    simp [apm_a01A12_suDen, apm_a01A12_suNum, apm_a01A12_realC,
      apm_a01A12_realD, apm_a01A12_diskBeta, Complex.mul_re, Complex.mul_im] <;>
    ring

lemma apm_a01A12_su_real_mobius (a s z : ℂ)
    (hdet : 0 < apm_a01A12_realA a s * apm_a01A12_realD a s -
      apm_a01A12_realB a s * apm_a01A12_realC a s)
    (hz : z ∈ apm_a01A12_H) :
    Complex.I * (apm_a01A12_suDen a s z + apm_a01A12_suNum a s z) /
        (apm_a01A12_suDen a s z - apm_a01A12_suNum a s z) =
      apm_a01A12_mobius (apm_a01A12_realA a s)
        (apm_a01A12_realB a s) (apm_a01A12_realC a s)
        (apm_a01A12_realD a s) z := by
  rw [apm_a01A12_suDen_add_suNum, apm_a01A12_suDen_sub_suNum,
    apm_a01A12_mobius]
  have hden := apm_a01A12_mobius_denom_ne_zero hdet hz
  field_simp [hden]

lemma apm_a01A12_cayley_su_formula_real_mobius {a s z : ℂ}
    (ha : a ∈ apm_a01A12_disk) (hs : ‖s‖ = 1)
    (hz : z ∈ apm_a01A12_H) :
    apm_a01A12_cayleyInv
        (apm_a01A12_diskShift (-a) (s ^ 2 * apm_a01A12_cayley z)) =
      apm_a01A12_mobius (apm_a01A12_realA a s)
        (apm_a01A12_realB a s) (apm_a01A12_realC a s)
        (apm_a01A12_realD a s) z := by
  let w := apm_a01A12_cayley z
  have hsnorm : ‖s ^ 2‖ = 1 := by rw [norm_pow, hs]; norm_num
  have hw : s ^ 2 * w ∈ apm_a01A12_disk := by
    change ‖s ^ 2 * w‖ < 1
    rw [norm_mul, hsnorm, one_mul]
    exact apm_a01A12_cayley_mapsTo hz
  have hu := apm_a01A12_diskShift_mapsTo (-a)
    (apm_a01A12_neg_mem_disk ha) hw
  have hzi := apm_a01A12_add_I_ne_zero hz
  have heq := apm_a01A12_su_at_cayley a s z hzi
  have hDrel :
      (conj (apm_a01A12_diskBeta a s) * w + conj s) *
          (z + Complex.I) = apm_a01A12_suDen a s z := by
    dsimp [w]
    rw [apm_a01A12_cayley]
    field_simp [hzi]
    simp [apm_a01A12_suDen]
    ring
  have hshift := apm_a01A12_diskShift_denom_ne_zero
    (apm_a01A12_neg_mem_disk ha) hw
  have hs0 : conj s ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp [hs] at hn
  have hunit := apm_a01A12_conj_mul_self_eq_one hs
  have hqsq : conj s * s ^ 2 = s := by
    rw [pow_two, ← mul_assoc, hunit, one_mul]
  have hsu : conj (apm_a01A12_diskBeta a s) * w + conj s ≠ 0 := by
    have hrel : conj (apm_a01A12_diskBeta a s) * w + conj s =
        conj s * (1 - conj (-a) * (s ^ 2 * w)) := by
      simp [apm_a01A12_diskBeta]
      calc
        conj a * s * w + conj s = conj s + conj a * s * w := by ring
        _ = conj s + conj a * (conj s * s ^ 2) * w := by rw [hqsq]
        _ = conj s * (1 + conj a * (s ^ 2 * w)) := by ring
    rw [hrel]
    exact mul_ne_zero hs0 hshift
  have hD : apm_a01A12_suDen a s z ≠ 0 := by
    rw [← hDrel]
    exact mul_ne_zero hsu hzi
  have hone : 1 - apm_a01A12_suNum a s z / apm_a01A12_suDen a s z ≠ 0 := by
    rw [← heq, ← apm_a01A12_diskShift_su_formula a s w hs]
    exact apm_a01A12_one_sub_ne_zero hu
  calc
    apm_a01A12_cayleyInv (apm_a01A12_diskShift (-a) (s ^ 2 * w)) =
        apm_a01A12_cayleyInv
          ((s * w + apm_a01A12_diskBeta a s) /
            (conj (apm_a01A12_diskBeta a s) * w + conj s)) := by
      rw [apm_a01A12_diskShift_su_formula a s w hs]
    _ = apm_a01A12_cayleyInv
        (apm_a01A12_suNum a s z / apm_a01A12_suDen a s z) := congrArg _ heq
    _ = Complex.I * (apm_a01A12_suDen a s z + apm_a01A12_suNum a s z) /
        (apm_a01A12_suDen a s z - apm_a01A12_suNum a s z) :=
      apm_a01A12_cayleyInv_div _ _ hD hone
    _ = _ := apm_a01A12_su_real_mobius a s z
      (apm_a01A12_real_coeff_det ha hs) hz

lemma apm_a01A12_H_automorphism_real_mobius {h : ℂ → ℂ}
    (hh : apm_a01A12_ConformalBijOn h apm_a01A12_H apm_a01A12_H) :
    ∃ A B C D : ℝ, 0 < A * D - B * C ∧
      Set.EqOn h (apm_a01A12_mobius A B C D) apm_a01A12_H := by
  let f := apm_a01A12_diskConjugate h
  have hf : apm_a01A12_ConformalBijOn f
      apm_a01A12_disk apm_a01A12_disk :=
    apm_a01A12_diskConjugate_conformalBijOn hh
  obtain ⟨a, c, ha, hc, hformula⟩ := apm_a01A12_diskAutomorphism_formula hf
  obtain ⟨s, hs2, hs⟩ := apm_a01A12_unit_sqrt hc
  refine ⟨apm_a01A12_realA a s, apm_a01A12_realB a s,
    apm_a01A12_realC a s, apm_a01A12_realD a s,
    apm_a01A12_real_coeff_det ha hs, ?_⟩
  intro z hz
  have hw := apm_a01A12_cayley_mapsTo hz
  have heq := hformula hw
  have heq' := congrArg apm_a01A12_cayleyInv heq
  have hhz := hh.1.1 hz
  dsimp [f, apm_a01A12_diskConjugate] at heq'
  rw [apm_a01A12_cayleyInv_cayley hz,
    apm_a01A12_cayleyInv_cayley hhz] at heq'
  rw [← hs2] at heq'
  exact heq'.trans (apm_a01A12_cayley_su_formula_real_mobius ha hs hz)

/-- Why this unblocks `apm_a01a12`: once the displayed fourth-root map is
known to be a conformal bijection, this is the missing automorphism
classification.  It states that all conformal bijections with the same source
and target form exactly the right torsor under positive-determinant real
Möbius automorphisms of the upper half-plane. -/
theorem apm_a01A12_bridge_automorphism_classification
    (hF : apm_a01A12_ConformalBijOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit) :
    ∀ g : ℂ → ℂ,
      apm_a01A12_ConformalBijOn g apm_a01A12_H apm_a01A12_wedgeSlit ↔
        ∃ a b c d : ℝ, 0 < a * d - b * c ∧
          Set.EqOn g
            (apm_a01A12_conformalMap ∘
              apm_a01A12_mobius a b c d)
            apm_a01A12_H := by
  intro g
  constructor
  · intro hg
    obtain ⟨a, b, c, d, hdet, heq⟩ :=
      apm_a01A12_H_automorphism_real_mobius
        (apm_a01A12_inducedAutomorphism_conformalBijOn hg)
    refine ⟨a, b, c, d, hdet, ?_⟩
    intro z hz
    calc
      g z = apm_a01A12_conformalMap
          (apm_a01A12_inducedAutomorphism g z) :=
        (apm_a01A12_conformalMap_inducedAutomorphism hg hz).symm
      _ = apm_a01A12_conformalMap (apm_a01A12_mobius a b c d z) :=
        congrArg apm_a01A12_conformalMap (heq hz)
  · rintro ⟨a, b, c, d, hdet, heq⟩
    exact (hF.comp (apm_a01A12_mobius_conformalBijOn hdet)).congr_H heq.symm

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
  CLOSER HOP 3 boundary. This hop goes beyond injectivity and closes the
  differential part of the explicit biholomorphism. The new slit-plane lemma
  proves that `1-z²` lies in the domain of the principal logarithm for every
  upper-half-plane `z`. Mathlib's `HasDerivAt.cpow_const` then gives the exact
  derivative of `(1-z²)^(1/4)`, and
  `apm_a01A12_conformalMap_fderiv_ne_zero` proves the resulting continuous
  linear map is nonzero.

  Consultations covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, prior
  a01A12 commits, complex-analysis siblings, Mathlib's complex-power
  derivative and slit-plane sources, the `UpperHalfPlane` Möbius-action
  sources, and git history. The `cpow` derivative API was found and used. No
  theorem constructs an inverse onto this exact wedge slit or classifies every
  conformal upper-half-plane automorphism as a positive-determinant real
  Möbius map.

  Thus the explicit-map bridge is narrowed to surjectivity onto the frozen
  wedge slit. The independent automorphism-classification bridge remains
  open. The frozen statement is unchanged.

  CLOSER HOP 4: current Mathlib and Loogle/LeanSearch searches still expose
  the `SL(2,ℝ)` action on `UpperHalfPlane` but no converse classification of
  every conformal automorphism.  The explicit-map side is now packaged by
  `apm_a01A12_conformalMap_conformalBijOn`: only the exact range statement
  (`MapsTo` plus `SurjOn`) remains, with no injectivity or differential
  bookkeeping hidden in that gap.  Once that range pair is proved, the main
  theorem routes directly through the independent classification bridge.
  -/
  have hrange :
      Set.MapsTo apm_a01A12_conformalMap
          apm_a01A12_H apm_a01A12_wedgeSlit ∧
        Set.SurjOn apm_a01A12_conformalMap
          apm_a01A12_H apm_a01A12_wedgeSlit := by
    refine ⟨apm_a01A12_conformalMap_mapsTo, ?_⟩
    apply apm_a01A12_conformalMap_surjOn_of_nonreal_roots
    intro w hw
    exact apm_a01A12_wedgeSlit_has_nonreal_root w hw
  have hF := apm_a01A12_conformalMap_conformalBijOn hrange.1 hrange.2
  exact ⟨hF, apm_a01A12_bridge_automorphism_classification hF⟩

#print axioms apm_a01a12
