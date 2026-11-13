import Mathlib
import ConstructionTargets.CotangentLocal
import ConstructionTargets.AnalyticDivision
import ConstructionTargets.FinitePolePatch
import ConstructionTargets.FiniteResidueRectangle

/-!
# APM a95A07

The prescribed exponential integrand is reduced algebraically to the
logarithmic derivative `π cot (πz) / z²`.  A finite rectangle residue
calculation (the argument principle for the simple zeros of `sin (πz)`),
followed by an ML estimate on half-integer squares, determines the sum.
-/

open Complex Real Set Function Filter Topology
open ConstructionTargets.CotangentLocal
open ConstructionTargets.AnalyticDivision
open ConstructionTargets.FinitePolePatch
open ConstructionTargets.FiniteResidueRectangle

noncomputable section

/-- The integrand specified in the problem. -/
def baselIntegrand (z : ℂ) : ℂ :=
  (1 / z ^ 2) * Complex.exp (2 * (Real.pi : ℂ) * I * z) /
    (Complex.exp (2 * (Real.pi : ℂ) * I * z) - 1)

/-- The equivalent cotangent logarithmic-derivative kernel. -/
def baselCotKernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) / z ^ 2

/-- Remove the cubic principal part at zero.  Its square integral is zero. -/
def baselModifiedKernel (z : ℂ) : ℂ :=
  baselCotKernel z - z ^ (-3 : ℤ)

/-- The analytic remainder at a nonzero integer pole. -/
def baselNonzeroPoleRemainder (k : ℤ) (z : ℂ) : ℂ :=
  regularCot (z - (k : ℂ)) / z ^ 2 +
    dslope (fun w : ℂ => 1 / w ^ 2) (k : ℂ) z - z ^ (-3 : ℤ)

lemma baselNonzeroPoleRemainder_analyticAt (k : ℤ) (hk : k ≠ 0) :
    AnalyticAt ℂ (baselNonzeroPoleRemainder k) (k : ℂ) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hreg : AnalyticAt ℂ
      (fun z : ℂ => regularCot (z - (k : ℂ))) (k : ℂ) := by
    simpa [Function.comp_def] using analyticAt_regularCot_zero.comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => z - (k : ℂ)) (k : ℂ) by fun_prop) (by simp)
  have hinv : AnalyticAt ℂ (fun z : ℂ => 1 / z ^ 2) (k : ℂ) :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hkC)
  have hds := analyticAt_dslope (k : ℂ) (fun z : ℂ => 1 / z ^ 2) hinv
  have hz3 : AnalyticAt ℂ (fun z : ℂ => z ^ (-3 : ℤ)) (k : ℂ) :=
    analyticAt_id.zpow hkC
  unfold baselNonzeroPoleRemainder
  exact ((hreg.div (analyticAt_id.pow 2) (pow_ne_zero 2 hkC)).add hds).sub hz3

/-- At a nonzero integer, the residue is `1/k²`. -/
lemma baselModifiedKernel_sub_nonzero_residue
    (k : ℤ) (hk : k ≠ 0) (z : ℂ) (hz : z ≠ (k : ℂ))
    (hw : z - (k : ℂ) ∈ Complex.integerComplement) :
    baselModifiedKernel z - (1 / (k : ℂ) ^ 2) * (z - (k : ℂ))⁻¹ =
      baselNonzeroPoleRemainder k z := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcot : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      1 / (z - (k : ℂ)) + regularCot (z - (k : ℂ)) := by
    have hp := regularCot_eq_cot_sub_inv hw
    have hper := cot_pi_add_int (z - (k : ℂ)) k
    rw [show z - (k : ℂ) + (k : ℂ) = z by ring] at hper
    rw [← hper] at hp
    rw [hp]
    ring
  have hds : dslope (fun w : ℂ => 1 / w ^ 2) (k : ℂ) z =
      ((1 / z ^ 2) - (1 / (k : ℂ) ^ 2)) / (z - (k : ℂ)) := by
    rw [dslope_of_ne _ hz, slope]
    simp [smul_eq_mul, vsub_eq_sub, div_eq_mul_inv, mul_comm]
  unfold baselModifiedKernel baselNonzeroPoleRemainder baselCotKernel
  rw [hds, hcot]
  have hzmem : z ∈ Complex.integerComplement := by
    rw [← show z - (k : ℂ) + (k : ℂ) = z by ring,
      Complex.add_intCast_mem_integerComplement]
    exact hw
  have hz0 := Complex.integerComplement.ne_zero hzmem
  simp only [zpow_neg]
  field_simp [hkC, hz0, Complex.integerComplement.ne_zero hw]
  ring

/-- At zero, the logarithmic-derivative calculation gives residue `-π²/3`. -/
lemma baselModifiedKernel_sub_zero_residue
    (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    baselModifiedKernel z - (-(Real.pi : ℂ) ^ 2 / 3) * z⁻¹ =
      cotSecondRemainder z := by
  have hz0 := Complex.integerComplement.ne_zero hz
  have hcot := regularCot_eq_cot_sub_inv hz
  have hpi : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      regularCot z + 1 / z := by rw [hcot]; ring
  rw [cotSecondRemainder_eq_div hz0]
  unfold baselModifiedKernel baselCotKernel cotSecondNumerator
  rw [hpi]
  simp only [zpow_neg]
  field_simp [hz0]
  ring

/-- Integer poles enclosed by the half-integer square. -/
def baselIntegerPoles (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- Residues of the modified cotangent kernel. -/
def baselResidue (k : ℤ) : ℂ :=
  if k = 0 then -(Real.pi : ℂ) ^ 2 / 3 else 1 / (k : ℂ) ^ 2

/-- A uniform local formula for the analytic remainder at a nonzero pole. -/
def baselGenericPoleRemainder (a z : ℂ) : ℂ :=
  regularCot (z - a) / z ^ 2 +
    dslope (fun w : ℂ => 1 / w ^ 2) a z - z ^ (-3 : ℤ)

lemma baselGenericPoleRemainder_analyticAt (a : ℂ) (ha : a ≠ 0) :
    AnalyticAt ℂ (baselGenericPoleRemainder a) a := by
  have hreg : AnalyticAt ℂ (fun z : ℂ => regularCot (z - a)) a := by
    simpa [Function.comp_def] using analyticAt_regularCot_zero.comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => z - a) a by fun_prop) (by simp)
  have hinv : AnalyticAt ℂ (fun z : ℂ => 1 / z ^ 2) a :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 ha)
  have hds := analyticAt_dslope a (fun z : ℂ => 1 / z ^ 2) hinv
  have hz3 : AnalyticAt ℂ (fun z : ℂ => z ^ (-3 : ℤ)) a := analyticAt_id.zpow ha
  unfold baselGenericPoleRemainder
  exact ((hreg.div (analyticAt_id.pow 2) (pow_ne_zero 2 ha)).add hds).sub hz3

/-- The modified kernel after subtracting all listed simple principal parts. -/
def baselRawRemainder (n : ℕ) (z : ℂ) : ℂ :=
  baselModifiedKernel z - ∑ k ∈ baselIntegerPoles n,
    baselResidue k * (z - (k : ℂ))⁻¹

/-- A local analytic extension of the raw remainder at a listed pole. -/
def baselLocalExtension (n : ℕ) (a z : ℂ) : ℂ :=
  (if a = 0 then cotSecondRemainder z else baselGenericPoleRemainder a z) -
    ∑ k ∈ (baselIntegerPoles n).filter (fun k : ℤ => (k : ℂ) ≠ a),
      baselResidue k * (z - (k : ℂ))⁻¹

lemma baselLocalExtension_analyticAt (n : ℕ) (a : ℂ)
    (ha : a ∈ (baselIntegerPoles n).image fun k : ℤ => (k : ℂ)) :
    AnalyticAt ℂ (baselLocalExtension n a) a := by
  have hbase : AnalyticAt ℂ
      (fun z => if a = 0 then cotSecondRemainder z
        else baselGenericPoleRemainder a z) a := by
    by_cases ha0 : a = 0
    · subst a
      simpa using analyticAt_cotSecondRemainder_zero
    · simpa [ha0] using baselGenericPoleRemainder_analyticAt a ha0
  have hsum : AnalyticAt ℂ
      (fun z => ∑ k ∈ (baselIntegerPoles n).filter
          (fun k : ℤ => (k : ℂ) ≠ a),
        baselResidue k * (z - (k : ℂ))⁻¹) a := by
    let s := (baselIntegerPoles n).filter (fun k : ℤ => (k : ℂ) ≠ a)
    have hs : AnalyticAt ℂ
        (∑ k ∈ s, fun z : ℂ => baselResidue k * (z - (k : ℂ))⁻¹) a :=
      Finset.analyticAt_sum s (fun k hk => by
        simp only [s, Finset.mem_filter] at hk
        have hden : AnalyticAt ℂ (fun z : ℂ => (z - (k : ℂ))⁻¹) a :=
          (analyticAt_id.sub analyticAt_const).fun_inv (by
            simpa [sub_ne_zero] using hk.2.symm)
        simpa only [Pi.mul_apply] using
          (analyticAt_const.mul hden : AnalyticAt ℂ
            ((fun _ : ℂ => baselResidue k) *
              fun z : ℂ => (z - (k : ℂ))⁻¹) a))
    have heq : (fun z => ∑ k ∈ s, baselResidue k * (z - (k : ℂ))⁻¹) =
        ∑ k ∈ s, (fun z : ℂ => baselResidue k * (z - (k : ℂ))⁻¹) := by
      funext z
      simp
    simpa [s, heq] using hs
  unfold baselLocalExtension
  exact hbase.sub hsum

lemma baselRawRemainder_eventually_localExtension
    (n : ℕ) (a : ℂ)
    (ha : a ∈ (baselIntegerPoles n).image fun k : ℤ => (k : ℂ)) :
    baselRawRemainder n =ᶠ[nhdsWithin a {a}ᶜ] baselLocalExtension n a := by
  rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
  apply eventually_nhdsWithin_iff.mpr
  have hball : ∀ᶠ z : ℂ in nhds (k : ℂ), z ∈ Metric.ball (k : ℂ) 1 :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hball] with z hdist hz
  have hnorm : ‖z - (k : ℂ)‖ < 1 := by
    simpa only [Metric.mem_ball, Complex.dist_eq] using hdist
  have hw : z - (k : ℂ) ∈ Complex.integerComplement :=
    mem_integerComplement_of_norm_lt_one (sub_ne_zero.mpr hz) hnorm
  have hfilter : (baselIntegerPoles n).filter (fun j : ℤ => (j : ℂ) ≠ (k : ℂ)) =
      (baselIntegerPoles n).erase k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hjs, hjk⟩
      exact ⟨by exact_mod_cast hjk, hjs⟩
    · rintro ⟨hjk, hjs⟩
      exact ⟨hjs, by exact_mod_cast hjk⟩
  have hsum := Finset.sum_erase_add
    (s := baselIntegerPoles n)
    (f := fun j : ℤ => baselResidue j * (z - (j : ℂ))⁻¹) hk
  by_cases hk0 : k = 0
  · subst k
    have hprincipal := baselModifiedKernel_sub_zero_residue z (by simpa using hw)
    unfold baselRawRemainder baselLocalExtension
    rw [hfilter]
    simp only [Int.cast_zero, if_pos rfl]
    rw [← hsum]
    simp [baselResidue] at hsum ⊢
    linear_combination hprincipal
  · have hprincipal := baselModifiedKernel_sub_nonzero_residue k hk0 z hz hw
    have hgeneric : baselNonzeroPoleRemainder k z =
        baselGenericPoleRemainder (k : ℂ) z := by rfl
    rw [hgeneric] at hprincipal
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    unfold baselRawRemainder baselLocalExtension
    rw [hfilter, if_neg hkC]
    rw [← hsum]
    simp [baselResidue, hk0] at hsum ⊢
    linear_combination hprincipal

/-- Every integer in the closed half-integer square is listed. -/
lemma basel_integerComplement_of_mem_square
    (n : ℕ) (z : ℂ)
    (hz : z ∈ (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
      Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))))
    (hnot : z ∉ (baselIntegerPoles n).image fun k : ℤ => (k : ℂ)) :
    z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨k, hkz⟩
  have hR : 0 ≤ n + (1 / 2 : ℝ) := by positivity
  have hre := hz.1
  rw [uIcc_of_le (neg_le_self hR)] at hre
  have hkreal : (k : ℝ) = z.re := by rw [← hkz]; simp
  have hklt : (k : ℝ) < (n : ℝ) + 1 := by
    rw [hkreal]
    calc
      z.re ≤ n + (1 / 2 : ℝ) := hre.2
      _ < (n : ℝ) + 1 := by norm_num
  have hnlt : (-(n : ℤ) - 1 : ℤ) < k := by
    have hreal : (-(n : ℤ) - 1 : ℤ) < (k : ℝ) := by
      rw [hkreal]
      calc
        ((-(n : ℤ) - 1 : ℤ) : ℝ) < -(n + (1 / 2 : ℝ)) := by
          push_cast
          linarith
        _ ≤ z.re := hre.1
    exact_mod_cast hreal
  have hkle : k ≤ (n : ℤ) := by
    have : k < (n : ℤ) + 1 := by exact_mod_cast hklt
    omega
  have hnle : -(n : ℤ) ≤ k := by omega
  apply hnot
  exact Finset.mem_image.mpr ⟨k, by simp [baselIntegerPoles, hnle, hkle], hkz⟩

lemma baselModifiedKernel_differentiableAt
    (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ baselModifiedKernel z := by
  have hz0 := Complex.integerComplement.ne_zero hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := sin_pi_mul_ne_zero hz
  have hcosD : DifferentiableAt ℂ
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w)) z := by fun_prop
  have hsinD : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by fun_prop
  have hcot : DifferentiableAt ℂ
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) /
        Complex.sin ((Real.pi : ℂ) * w)) z := hcosD.div hsinD hsin
  have hmain : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * w) /
          Complex.sin ((Real.pi : ℂ) * w)) / w ^ 2) z :=
    (analyticAt_const.differentiableAt.mul hcot).div (by fun_prop)
      (pow_ne_zero 2 hz0)
  have hz3 : DifferentiableAt ℂ (fun w : ℂ => w ^ (-3 : ℤ)) z :=
    (analyticAt_id.zpow hz0).differentiableAt
  unfold baselModifiedKernel baselCotKernel Complex.cot
  exact hmain.sub hz3

lemma baselRawRemainder_differentiableAt
    (n : ℕ) (z : ℂ)
    (hz : z ∈ (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
      Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))))
    (hnot : z ∉ (baselIntegerPoles n).image fun k : ℤ => (k : ℂ)) :
    DifferentiableAt ℂ (baselRawRemainder n) z := by
  have hzint := basel_integerComplement_of_mem_square n z hz hnot
  have hmod := baselModifiedKernel_differentiableAt z hzint
  have hsum : DifferentiableAt ℂ
      (fun w => ∑ k ∈ baselIntegerPoles n,
        baselResidue k * (w - (k : ℂ))⁻¹) z := by
    apply DifferentiableAt.fun_sum
    intro k hk
    have hzk : z ≠ (k : ℂ) := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨k, hk, h.symm⟩
    exact (differentiableAt_const (baselResidue k)).mul
      ((differentiableAt_id.sub (differentiableAt_const (k : ℂ))).inv
        (sub_ne_zero.mpr hzk))
  change DifferentiableAt ℂ (fun w => baselModifiedKernel w -
    ∑ k ∈ baselIntegerPoles n, baselResidue k * (w - (k : ℂ))⁻¹) z
  exact hmod.sub hsum

/-- Fill the finitely many removable singularities of the subtracted kernel. -/
def baselPatchedRemainder (n : ℕ) : ℂ → ℂ :=
  patchFinite ((baselIntegerPoles n).image fun k : ℤ => (k : ℂ))
    (baselRawRemainder n) (baselLocalExtension n)

lemma baselPatchedRemainder_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (baselPatchedRemainder n)
      (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
        Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))) := by
  unfold baselPatchedRemainder
  apply differentiableOn_patchFinite
  · exact fun z hz hnot => baselRawRemainder_differentiableAt n z hz hnot
  · exact fun a ha => baselLocalExtension_analyticAt n a ha
  · exact fun a ha => baselRawRemainder_eventually_localExtension n a ha

lemma baselIntegerPole_abs_lt (n : ℕ) (k : ℤ) (hk : k ∈ baselIntegerPoles n) :
    |(k : ℝ)| < n + (1 / 2 : ℝ) := by
  simp only [baselIntegerPoles, Finset.mem_Icc] at hk
  have habs : |(k : ℝ)| ≤ n := by
    rw [abs_le]
    exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
  linarith

lemma baselBoundary_not_mem_poles (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    z ∉ (baselIntegerPoles n).image fun k : ℤ => (k : ℂ) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
  have hkabs := baselIntegerPole_abs_lt n k hk
  rcases hz with hz | hz
  · have hre : ((k : ℂ)).re = (k : ℝ) := by simp
    rw [hre] at hz
    linarith
  · have hR : 0 < n + (1 / 2 : ℝ) := by positivity
    have him : ((k : ℂ)).im = 0 := by simp
    rw [him, abs_zero] at hz
    linarith

lemma baselPatchedRemainder_eq_on_boundary (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    baselPatchedRemainder n z = baselRawRemainder n z := by
  unfold baselPatchedRemainder
  exact patchFinite_eq (baselBoundary_not_mem_poles n z hz)

def baselRealPoles (n : ℕ) : Finset ℝ :=
  (baselIntegerPoles n).image fun k : ℤ => (k : ℝ)

def baselRealResidue (a : ℝ) : ℂ :=
  if a = 0 then -(Real.pi : ℂ) ^ 2 / 3 else 1 / (a : ℂ) ^ 2

lemma baselRealResidue_intCast (k : ℤ) :
    baselRealResidue (k : ℝ) = baselResidue k := by
  by_cases hk : k = 0
  · subst k
    simp [baselRealResidue, baselResidue]
  · have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp [baselRealResidue, baselResidue, hk, hkr]

lemma baselRealPole_sum_eq (n : ℕ) (z : ℂ) :
    (∑ a ∈ baselRealPoles n, baselRealResidue a * (z - (a : ℂ))⁻¹) =
      ∑ k ∈ baselIntegerPoles n, baselResidue k * (z - (k : ℂ))⁻¹ := by
  unfold baselRealPoles
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [baselRealResidue_intCast]
    norm_cast
  · intro k hk j hj hcast
    change (k : ℝ) = (j : ℝ) at hcast
    exact_mod_cast hcast

/-- The argument-principle residue sum is the zero residue plus twice the
positive partial Basel sum. -/
lemma basel_residue_sum_eq (n : ℕ) :
    (∑ a ∈ baselRealPoles n, baselRealResidue a) =
      -(Real.pi : ℂ) ^ 2 / 3 +
        2 * ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℂ) ^ 2 := by
  have himage : (∑ a ∈ baselRealPoles n, baselRealResidue a) =
      ∑ k ∈ baselIntegerPoles n, baselResidue k := by
    unfold baselRealPoles
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      exact baselRealResidue_intCast k
    · intro k hk j hj hcast
      change (k : ℝ) = (j : ℝ) at hcast
      exact_mod_cast hcast
  have hint : ∀ m : ℕ,
      (∑ k ∈ baselIntegerPoles m, baselResidue k) =
        -(Real.pi : ℂ) ^ 2 / 3 +
          2 * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℂ) ^ 2 := by
    intro m
    induction m with
    | zero => simp [baselIntegerPoles, baselResidue]
    | succ n ih =>
      have hfin : baselIntegerPoles (n + 1) =
          insert (-((n + 1 : ℕ) : ℤ))
            (insert ((n + 1 : ℕ) : ℤ) (baselIntegerPoles n)) := by
        ext k
        simp only [baselIntegerPoles, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hpos : ((n + 1 : ℕ) : ℤ) ∉ baselIntegerPoles n := by
        simp [baselIntegerPoles]
      have hneg : (-((n + 1 : ℕ) : ℤ)) ∉
          insert ((n + 1 : ℕ) : ℤ) (baselIntegerPoles n) := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨by omega, by simp [baselIntegerPoles]⟩
      rw [hfin, Finset.sum_insert hneg, Finset.sum_insert hpos, ih,
        Finset.sum_range_succ]
      have hn0 : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
      have hnn0 : (-((n + 1 : ℕ) : ℤ)) ≠ 0 := neg_ne_zero.mpr hn0
      simp only [baselResidue, if_neg hn0, if_neg hnn0]
      push_cast
      ring
  exact himage.trans (hint n)

/-- Finite residue identity for the modified cotangent kernel. -/
lemma baselModifiedKernel_residue_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselModifiedKernel (n + (1 / 2 : ℝ)) =
      2 * Real.pi * I * ∑ a ∈ baselRealPoles n, baselRealResidue a := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hdiff : DifferentiableOn ℂ (baselPatchedRemainder n)
      (Set.uIcc (-R) R ×ℂ Set.uIcc (-R) R) := by
    simpa [R] using baselPatchedRemainder_differentiableOn n
  have hint : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (baselPatchedRemainder n) (-R - R * I) (R + R * I) := by
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegrable_of_differentiableOn
    simpa using hdiff
  apply centeredSquareBoundaryIntegral_eq_finset_residues_of_differentiableOn
    baselModifiedKernel (baselPatchedRemainder n)
      (baselRealPoles n) baselRealResidue R hR
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact baselIntegerPole_abs_lt n k hk
  · exact hdiff
  · exact hint
  · intro z hz
    rw [baselPatchedRemainder_eq_on_boundary n z (by simpa [R] using hz)]
    unfold baselRawRemainder
    rw [baselRealPole_sum_eq]
    ring

lemma baselModifiedKernel_boundaryIntegrable (n : ℕ) :
    ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      baselModifiedKernel
      (-(n + (1 / 2 : ℝ)) - (n + (1 / 2 : ℝ)) * I)
      ((n + (1 / 2 : ℝ)) + (n + (1 / 2 : ℝ)) * I) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hdiff : DifferentiableOn ℂ (baselPatchedRemainder n)
      (Set.uIcc (-R) R ×ℂ Set.uIcc (-R) R) := by
    simpa [R] using baselPatchedRemainder_differentiableOn n
  have hpatch : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (baselPatchedRemainder n) (-R - R * I) (R + R * I) := by
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegrable_of_differentiableOn
    simpa using hdiff
  let p : ℝ → ℂ → ℂ := fun a z => baselRealResidue a * (z - (a : ℂ))⁻¹
  have hp : ∀ a ∈ baselRealPoles n,
      ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
        (p a) (-R - R * I) (R + R * I) := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact (ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_sub_inv
      (k : ℝ) R (by simpa [R] using baselIntegerPole_abs_lt n k hk)).const_mul
        (baselRealResidue (k : ℝ))
  have htotal : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z => baselPatchedRemainder n z + ∑ a ∈ baselRealPoles n, p a z)
      (-R - R * I) (R + R * I) :=
    hpatch.add (ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable.finset_sum hp)
  have hdecomp (z : ℂ) (hz : OnCenteredSquareBoundary R z) :
      baselPatchedRemainder n z + ∑ a ∈ baselRealPoles n, p a z =
        baselModifiedKernel z := by
    rw [baselPatchedRemainder_eq_on_boundary n z (by simpa [R] using hz)]
    unfold baselRawRemainder p
    rw [baselRealPole_sum_eq]
    ring
  have hout := htotal.congr
    (fun x hx => hdecomp (x + (-R - R * I).im * I) (by
      convert onBoundary_horizontal R x (-R) hR.le (by simp [abs_of_pos hR])
        (by simpa using hx) using 1 <;> simp))
    (fun x hx => hdecomp (x + (R + R * I).im * I) (by
      convert onBoundary_horizontal R x R hR.le (by simp [abs_of_pos hR])
        (by simpa using hx) using 1 <;> simp))
    (fun y hy => hdecomp ((R + R * I).re + y * I) (by
      convert onBoundary_vertical R R y hR.le (by simp [abs_of_pos hR])
        (by simpa using hy) using 1 <;> simp))
    (fun y hy => hdecomp ((-R - R * I).re + y * I) (by
      convert onBoundary_vertical R (-R) y hR.le (by simp [abs_of_pos hR])
        (by simpa using hy) using 1 <;> simp))
  simpa [R] using hout

lemma baselCotKernel_boundaryIntegrable (n : ℕ) :
    ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      baselCotKernel
      (-(n + (1 / 2 : ℝ)) - (n + (1 / 2 : ℝ)) * I)
      ((n + (1 / 2 : ℝ)) + (n + (1 / 2 : ℝ)) * I) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hmod : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      baselModifiedKernel (-R - R * I) (R + R * I) := by
    simpa [R] using baselModifiedKernel_boundaryIntegrable n
  have h3 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-3 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-3)
  have hsum := hmod.add h3
  have heq (z : ℂ) : baselModifiedKernel z + z ^ (-3 : ℤ) = baselCotKernel z := by
    unfold baselModifiedKernel
    ring
  have hout := hsum.congr
    (fun x hx => heq (x + (-R - R * I).im * I))
    (fun x hx => heq (x + (R + R * I).im * I))
    (fun y hy => heq ((R + R * I).re + y * I))
    (fun y hy => heq ((-R - R * I).re + y * I))
  simpa [R] using hout

/-- Removing the cubic principal part does not alter the contour integral. -/
lemma baselCotKernel_integral_eq_modified (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselCotKernel (n + (1 / 2 : ℝ)) =
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselModifiedKernel (n + (1 / 2 : ℝ)) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hm : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      baselModifiedKernel (-R - R * I) (R + R * I) := by
    simpa [R] using baselModifiedKernel_boundaryIntegrable n
  have h3 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-3 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-3)
  have hadd := ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_add hm h3
  have hzero : ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z : ℂ => z ^ (-3 : ℤ)) (-R - R * I) (R + R * I) = 0 := by
    simpa [ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral] using
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral_zpow_eq_zero
        0 R (by simpa using hR) (-3) (by norm_num)
  rw [hzero, add_zero] at hadd
  have heq (z : ℂ) : baselModifiedKernel z + z ^ (-3 : ℤ) = baselCotKernel z := by
    unfold baselModifiedKernel
    ring
  have hrect : ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      baselCotKernel (-R - R * I) (R + R * I) =
      ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
        baselModifiedKernel (-R - R * I) (R + R * I) := by
    rw [← hadd]
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_congr
    all_goals intro t ht; exact (heq _).symm
  simpa [R, ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral] using hrect

lemma baselCotKernel_residue_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselCotKernel (n + (1 / 2 : ℝ)) =
      2 * Real.pi * I * ∑ a ∈ baselRealPoles n, baselRealResidue a := by
  rw [baselCotKernel_integral_eq_modified]
  exact baselModifiedKernel_residue_identity n

lemma norm_cot_pi_le_of_im_ge_half (z : ℂ) (hz : (1 / 2 : ℝ) ≤ z.im) :
    ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤
      (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi)) := by
  let q : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * z)
  let r : ℝ := Real.exp (-Real.pi)
  have hr1 : r < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos Real.pi_pos
  have hqnorm : ‖q‖ ≤ r := by
    rw [show ‖q‖ = Real.exp (-2 * Real.pi * z.im) by
      simp [q, Complex.norm_exp, mul_re]]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hden : 1 - r ≤ ‖1 - q‖ := by
    calc
      1 - r ≤ 1 - ‖q‖ := by linarith
      _ ≤ ‖1 - q‖ := by simpa using (norm_sub_norm_le (1 : ℂ) q)
  have hden0 : 0 < ‖1 - q‖ := lt_of_lt_of_le (sub_pos.mpr hr1) hden
  rw [Complex.cot_pi_eq_exp_ratio]
  change ‖(q + 1) / (I * (1 - q))‖ ≤ _
  rw [norm_div, norm_mul, norm_I, one_mul]
  have hnum : ‖q + 1‖ ≤ r + 1 :=
    (norm_add_le q 1).trans (by simpa using add_le_add_right hqnorm 1)
  calc
    ‖q + 1‖ / ‖1 - q‖ ≤ (r + 1) / ‖1 - q‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (r + 1) / (1 - r) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hr1) hden
    _ = (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi)) := by
      simp only [r]
      congr 1 <;> ring

lemma norm_cot_pi_half_add_mul_I_le (y : ℝ) :
    ‖Complex.cot ((Real.pi : ℂ) * ((1 / 2 : ℝ) + y * I))‖ ≤ 1 := by
  have harg : (Real.pi : ℂ) * ((1 / 2 : ℝ) + y * I) =
      (Real.pi / 2 : ℝ) + (Real.pi * y : ℝ) * I := by
    push_cast
    ring
  rw [harg, Complex.cot_eq_cos_div_sin, Complex.sin_add_mul_I,
    Complex.cos_add_mul_I]
  simp only [ofReal_div, ofReal_one, ofReal_ofNat, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two, one_mul, zero_mul, zero_add, zero_sub]
  rw [norm_div, norm_neg, norm_mul, norm_I, mul_one]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  simp only [add_zero, Complex.norm_real]
  simpa [Real.norm_eq_abs, Real.tanh_eq_sinh_div_cosh, ← abs_div] using
    (Real.abs_tanh_lt_one (Real.pi * y)).le

lemma norm_cot_pi_le_on_square (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤
      (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi)) := by
  let C := (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))
  have hr : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos Real.pi_pos
  have hC : 1 ≤ C := by
    dsimp [C]
    apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    nlinarith [Real.exp_pos (-Real.pi)]
  rcases hz with ⟨hre, him⟩ | ⟨him, hre⟩
  · rcases abs_eq (show (0 : ℝ) ≤ n + (1 / 2 : ℝ) by positivity) |>.mp hre with
      hre | hre
    · have hzform : z = ((1 / 2 : ℝ) + z.im * I) + (n : ℤ) := by
        apply Complex.ext
        · rw [hre]
          simp
          ring
        · simp
      rw [hzform, cot_pi_add_int]
      exact (norm_cot_pi_half_add_mul_I_le z.im).trans hC
    · have hzform : z = ((1 / 2 : ℝ) + z.im * I) + (-(n : ℤ) - 1 : ℤ) := by
        apply Complex.ext
        · rw [hre]
          push_cast
          simp
          ring
        · simp
      rw [hzform, cot_pi_add_int]
      exact (norm_cot_pi_half_add_mul_I_le z.im).trans hC
  · have hhalf : (1 / 2 : ℝ) ≤ |z.im| := by simpa [him]
    rcases abs_cases z.im with him0 | him0
    · apply norm_cot_pi_le_of_im_ge_half
      simpa [him0] using hhalf
    · have hc := norm_cot_pi_le_of_im_ge_half ((starRingEnd ℂ) z) (by
          simp only [conj_im]
          simpa [him0] using hhalf)
      have heq : Complex.cot ((Real.pi : ℂ) * (starRingEnd ℂ) z) =
          (starRingEnd ℂ) (Complex.cot ((Real.pi : ℂ) * z)) := by
        rw [← Complex.cot_conj]
        congr 2
        simp
      rw [heq, Complex.norm_conj] at hc
      exact hc

lemma norm_baselCotKernel_le_on_square (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    ‖baselCotKernel z‖ ≤
      Real.pi * ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) /
        (n + (1 / 2 : ℝ)) ^ 2 := by
  let R : ℝ := n + (1 / 2 : ℝ)
  let C : ℝ := (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))
  have hR : 0 ≤ R := by positivity
  have hznorm : R ≤ ‖z‖ := by
    rcases hz with ⟨hre, him⟩ | ⟨him, hre⟩
    · change n + (1 / 2 : ℝ) ≤ ‖z‖
      rw [← hre]
      exact abs_re_le_norm z
    · change n + (1 / 2 : ℝ) ≤ ‖z‖
      rw [← him]
      exact abs_im_le_norm z
  have hcot : ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤ C := by
    simpa [R, C] using norm_cot_pi_le_on_square n z hz
  have hnum : ‖(Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)‖ ≤
      Real.pi * C := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hcot Real.pi_pos.le
  unfold baselCotKernel
  rw [norm_div, norm_pow]
  change _ ≤ Real.pi * C / R ^ 2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hcot
  calc
    _ ≤ (Real.pi * C) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (Real.pi * C) / R ^ 2 := by
      apply div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le hC0) (by positivity)
      exact pow_le_pow_left₀ hR hznorm 2

/-- The ML inequality gives inverse-linear decay of the cotangent-kernel
integral on the half-integer squares. -/
theorem norm_baselCotContour_le (n : ℕ) :
    ‖ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselCotKernel (n + (1 / 2 : ℝ))‖ ≤
      8 * Real.pi * ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) /
        (n + (1 / 2 : ℝ)) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  let M : ℝ := Real.pi *
    ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) / R ^ 2
  have hR : 0 ≤ R := by positivity
  have hs (z : ℂ) (hz : OnCenteredSquareBoundary R z) :
      ‖baselCotKernel z‖ ≤ M := by
    simpa [R, M] using norm_baselCotKernel_le_on_square n z (by simpa [R] using hz)
  have hml := ConstructionTargets.RectangleCauchy.norm_centeredSquareBoundaryIntegral_le
    baselCotKernel R M hR
    (fun x hx => hs _ (by simpa using (onBoundary_horizontal R x (-R) hR
      (by simp [abs_of_nonneg hR]) hx)))
    (fun x hx => hs _ (onBoundary_horizontal R x R hR
      (by simp [abs_of_nonneg hR]) hx))
    (fun y hy => hs _ (onBoundary_vertical R R y hR
      (by simp [abs_of_nonneg hR]) hy))
    (fun y hy => hs _ (by simpa using (onBoundary_vertical R (-R) y hR
      (by simp [abs_of_nonneg hR]) hy)))
  change ‖ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
    baselCotKernel R‖ ≤ 8 * Real.pi *
      ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) / R
  calc
    _ ≤ M * (8 * R) := hml
    _ = _ := by dsimp [M]; field_simp

theorem baselCotContour_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselCotKernel (n + (1 / 2 : ℝ))) atTop (nhds 0) := by
  apply squeeze_zero_norm norm_baselCotContour_le
  apply tendsto_const_nhds.div_atTop
  exact Filter.tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
    tendsto_natCast_atTop_atTop

/-- Away from the integer poles, the integrand prescribed in the question is
the cotangent kernel divided by `2πi`, plus a second-order principal part. -/
lemma baselIntegrand_eq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    baselIntegrand z = (2 * (Real.pi : ℂ) * I)⁻¹ * baselCotKernel z +
      (1 / 2 : ℂ) * z ^ (-2 : ℤ) := by
  have hz0 := Complex.integerComplement.ne_zero hz
  have hq : Complex.exp (2 * (Real.pi : ℂ) * I * z) ≠ 1 := by
    intro h
    rcases Complex.exp_eq_one_iff.mp h with ⟨k, hk⟩
    rw [Complex.mem_integerComplement_iff] at hz
    apply hz
    refine ⟨k, ?_⟩
    apply (mul_right_cancel₀ Complex.two_pi_I_ne_zero)
    calc
      (k : ℂ) * (2 * (Real.pi : ℂ) * I) =
          2 * (Real.pi : ℂ) * I * z := hk.symm
      _ = z * (2 * (Real.pi : ℂ) * I) := by ring
  have hq0 : Complex.exp (2 * (Real.pi : ℂ) * I * z) - 1 ≠ 0 :=
    sub_ne_zero.mpr hq
  unfold baselIntegrand baselCotKernel
  rw [Complex.cot_pi_eq_exp_ratio]
  simp only [zpow_neg, Nat.cast_ofNat]
  let q := Complex.exp (2 * (Real.pi : ℂ) * I * z)
  change 1 / z ^ 2 * q / (q - 1) =
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      ((Real.pi : ℂ) * ((q + 1) / (I * (1 - q))) / z ^ 2) +
        (1 / 2 : ℂ) * (z ^ 2)⁻¹
  have hq0' : q - 1 ≠ 0 := by simpa [q] using hq0
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (by simpa [q] using hq))
  field_simp [hz0, hq0', h1q, Real.pi_ne_zero, I_ne_zero, I_mul_I]
  simp only [pow_two, I_mul_I]
  ring

lemma baselBoundary_integerComplement (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    z ∈ Complex.integerComplement := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 ≤ R := by positivity
  have hmem : z ∈ Set.uIcc (-R) R ×ℂ Set.uIcc (-R) R := by
    rw [mem_reProdIm]
    rw [uIcc_of_le (neg_le_self hR)]
    rcases hz with ⟨hre, him⟩ | ⟨him, hre⟩
    · exact ⟨(abs_le.mp hre.le), (abs_le.mp him)⟩
    · exact ⟨(abs_le.mp hre), (abs_le.mp him.le)⟩
  exact basel_integerComplement_of_mem_square n z (by simpa [R] using hmem)
    (baselBoundary_not_mem_poles n z hz)

set_option maxHeartbeats 600000 in
/-- The prescribed exponential contour integral is exactly `1/(2πi)` times
the cotangent-kernel integral; the remaining `z⁻²` term has a primitive. -/
theorem baselIntegrand_contour_eq_cot (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselIntegrand (n + (1 / 2 : ℝ)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
          baselCotKernel (n + (1 / 2 : ℝ)) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let d : ℂ := 1 / 2
  have hcot : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      baselCotKernel (-R - R * I) (R + R * I) := by
    simpa [R] using baselCotKernel_boundaryIntegrable n
  have hz2 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-2 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-2)
  have hadd := ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_add
    (hcot.const_mul c) (hz2.const_mul d)
  rw [ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_const_mul,
    ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_const_mul] at hadd
  have hz2zero : ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
      (fun z : ℂ => z ^ (-2 : ℤ)) R = 0 := by
    simpa using
      (ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral_zpow_eq_zero
        0 R (by simpa using hR) (-2) (by norm_num))
  have hcongr : ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
      baselIntegrand R =
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        (fun z => c * baselCotKernel z + d * z ^ (-2 : ℤ)) R := by
    unfold ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_congr
    all_goals
      intro t ht
      apply baselIntegrand_eq
      apply baselBoundary_integerComplement n
    · simpa [R] using (onBoundary_horizontal R t (-R) hR.le
        (by simp [abs_of_pos hR]) (by simpa using ht))
    · simpa [R] using (onBoundary_horizontal R t R hR.le
        (by simp [abs_of_pos hR]) (by simpa using ht))
    · simpa [R] using (onBoundary_vertical R R t hR.le
        (by simp [abs_of_pos hR]) (by simpa using ht))
    · simpa [R] using (onBoundary_vertical R (-R) t hR.le
        (by simp [abs_of_pos hR]) (by simpa using ht))
  rw [hcongr]
  change ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z => c * baselCotKernel z + d * z ^ (-2 : ℤ)) (-R - R * I) (R + R * I) = _
  rw [hadd, show ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z : ℂ => z ^ (-2 : ℤ)) (-R - R * I) (R + R * I) = 0 by
        simpa [ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral] using hz2zero,
    mul_zero, add_zero]
  rfl

theorem baselIntegrand_contour_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselIntegrand (n + (1 / 2 : ℝ))) atTop (nhds 0) := by
  have h := baselCotContour_tendsto_zero.const_mul
    ((2 * (Real.pi : ℂ) * I)⁻¹)
  have h' : Tendsto (fun n : ℕ => (2 * (Real.pi : ℂ) * I)⁻¹ *
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselCotKernel (n + (1 / 2 : ℝ))) atTop (nhds 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [] with n
  exact (baselIntegrand_contour_eq_cot n).symm

/-- The argument-principle computation on the `n`th prescribed square. -/
theorem baselIntegrand_contour_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        baselIntegrand (n + (1 / 2 : ℝ)) =
      -(Real.pi : ℂ) ^ 2 / 3 +
        2 * ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℂ) ^ 2 := by
  rw [baselIntegrand_contour_eq_cot, baselCotKernel_residue_identity,
    basel_residue_sum_eq]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp, I_ne_zero]

/-- Main theorem: Σ_{n=1}^∞ 1/n² = π²/6, obtained by passing to the
limit in the prescribed argument-principle contour identity. -/
theorem sum_inv_sq_eq_pi_sq_div_six :
    HasSum (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) (π ^ 2 / 6) := by
  let uR : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  let uC : ℕ → ℂ := fun k => 1 / ((k + 1 : ℕ) : ℂ) ^ 2
  have hsumR : Summable uR := by
    rw [show uR = fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ by
      funext n; simp [uR, one_div]]
    exact (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num))
  have hsumC : Summable uC := by
    apply Summable.of_norm
    convert hsumR using 1
    funext k
    simp [uC, uR, norm_inv, norm_pow]
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by norm_cast,
      Complex.norm_natCast]
    norm_cast
  have hpartial : Tendsto (fun n => ∑ k ∈ Finset.range n, uC k) atTop
      (nhds (∑' k, uC k)) :=
    hsumC.hasSum_iff_tendsto_nat.mp hsumC.hasSum
  have hrhs : Tendsto (fun n : ℕ => -(Real.pi : ℂ) ^ 2 / 3 +
      2 * ∑ k ∈ Finset.range n, uC k) atTop (nhds 0) := by
    apply baselIntegrand_contour_tendsto_zero.congr'
    filter_upwards [] with n
    simpa [uC] using baselIntegrand_contour_identity n
  have hcomputed : Tendsto (fun n : ℕ => -(Real.pi : ℂ) ^ 2 / 3 +
      2 * ∑ k ∈ Finset.range n, uC k) atTop
      (nhds (-(Real.pi : ℂ) ^ 2 / 3 + 2 * ∑' k, uC k)) := by
    simpa using tendsto_const_nhds.add (hpartial.const_mul 2)
  have hzero : -(Real.pi : ℂ) ^ 2 / 3 + 2 * ∑' k, uC k = 0 :=
    tendsto_nhds_unique hcomputed hrhs
  have htsumC : (∑' k, uC k) = (Real.pi : ℂ) ^ 2 / 6 := by
    linear_combination hzero / 2
  have hcast : ((∑' k, uR k) : ℂ) = (∑' k, uC k) := by
    apply tsum_congr
    intro k
    simp [uR, uC]
  change HasSum uR (Real.pi ^ 2 / 6)
  have htsumR : (∑' k, uR k) = Real.pi ^ 2 / 6 := by
    exact_mod_cast hcast.trans htsumC
  simpa [htsumR] using hsumR.hasSum

/-- The tsum version: ∑' n, 1/(n+1)² = π²/6. -/
theorem tsum_inv_sq :
    ∑' n : ℕ, 1 / (↑(n + 1) : ℝ) ^ 2 = π ^ 2 / 6 :=
  sum_inv_sq_eq_pi_sq_div_six.tsum_eq

/-- The series Σ 1/n² converges (p-series with p = 2 > 1).

Directly from the HasSum result. -/
theorem summable_inv_sq :
    Summable (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) :=
  sum_inv_sq_eq_pi_sq_div_six.summable

#print axioms sum_inv_sq_eq_pi_sq_div_six

end
