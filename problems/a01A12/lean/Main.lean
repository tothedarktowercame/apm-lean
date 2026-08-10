import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
  sorry

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
    sorry
  have hF := apm_a01A12_conformalMap_conformalBijOn hrange.1 hrange.2
  exact ⟨hF, apm_a01A12_bridge_automorphism_classification hF⟩
