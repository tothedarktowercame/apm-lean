import Mathlib
import ConstructionTargets.CotangentLocal
import ConstructionTargets.AnalyticDivision
import ConstructionTargets.FinitePolePatch
import ConstructionTargets.FiniteResidueRectangle

/-!
# APM aunk03
-/

open Complex Real Set Function Filter Topology
open ConstructionTargets.CotangentLocal
open ConstructionTargets.AnalyticDivision
open ConstructionTargets.FinitePolePatch
open ConstructionTargets.FiniteResidueRectangle

noncomputable def apm_aunk03_kernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) / z ^ 4

def apm_aunk03_squareContour (n : ℕ) : Set ℂ :=
  let r : ℝ := n + (1 / 2 : ℝ)
  {z | (|z.re| = r ∧ |z.im| ≤ r) ∨ (|z.im| = r ∧ |z.re| ≤ r)}

/-- Subtract the two higher principal parts at zero.  They have zero square
integral, leaving a function with only simple poles. -/
noncomputable def apm_aunk03_modifiedKernel (z : ℂ) : ℂ :=
  apm_aunk03_kernel z - z ^ (-5 : ℤ) +
    (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ)

/-- The analytic remainder after subtracting the simple pole at a nonzero
integer `k`. -/
noncomputable def apm_aunk03_nonzeroPoleRemainder (k : ℤ) (z : ℂ) : ℂ :=
  regularCot (z - (k : ℂ)) / z ^ 4 +
    dslope (fun w : ℂ => 1 / w ^ 4) (k : ℂ) z -
    z ^ (-5 : ℤ) + (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ)

/-- The translated nonzero-pole remainder is analytic at its integer pole. -/
theorem apm_aunk03_nonzeroPoleRemainder_analyticAt
    (k : ℤ) (hk : k ≠ 0) :
    AnalyticAt ℂ (apm_aunk03_nonzeroPoleRemainder k) (k : ℂ) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hreg : AnalyticAt ℂ
      (fun z : ℂ => regularCot (z - (k : ℂ))) (k : ℂ) := by
    simpa [Function.comp_def] using analyticAt_regularCot_zero.comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => z - (k : ℂ)) (k : ℂ) by fun_prop) (by simp)
  have hinv4 : AnalyticAt ℂ (fun z : ℂ => 1 / z ^ 4) (k : ℂ) :=
    analyticAt_const.div (analyticAt_id.pow 4) (pow_ne_zero 4 hkC)
  have hds := analyticAt_dslope (k : ℂ) (fun z : ℂ => 1 / z ^ 4) hinv4
  have hz5 : AnalyticAt ℂ (fun z : ℂ => z ^ (-5 : ℤ)) (k : ℂ) :=
    analyticAt_id.zpow hkC
  have hz3 : AnalyticAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ)) (k : ℂ) :=
    analyticAt_const.mul (analyticAt_id.zpow hkC)
  unfold apm_aunk03_nonzeroPoleRemainder
  exact (((hreg.div (analyticAt_id.pow 4) (pow_ne_zero 4 hkC)).add hds).sub
    hz5).add hz3

/-- At a nonzero integer, the residue of the modified kernel is `1/k⁴`. -/
theorem apm_aunk03_modifiedKernel_sub_nonzero_residue
    (k : ℤ) (hk : k ≠ 0) (z : ℂ) (hz : z ≠ (k : ℂ))
    (hw : z - (k : ℂ) ∈ Complex.integerComplement) :
    apm_aunk03_modifiedKernel z -
        (1 / (k : ℂ) ^ 4) * (z - (k : ℂ))⁻¹ =
      apm_aunk03_nonzeroPoleRemainder k z := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcot : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      1 / (z - (k : ℂ)) + regularCot (z - (k : ℂ)) := by
    have hp := regularCot_eq_cot_sub_inv hw
    have hper := cot_pi_add_int (z - (k : ℂ)) k
    rw [show z - (k : ℂ) + (k : ℂ) = z by ring] at hper
    rw [← hper] at hp
    rw [hp]
    ring
  have hds : dslope (fun w : ℂ => 1 / w ^ 4) (k : ℂ) z =
      ((1 / z ^ 4) - (1 / (k : ℂ) ^ 4)) / (z - (k : ℂ)) := by
    rw [dslope_of_ne _ hz, slope]
    simp [smul_eq_mul, vsub_eq_sub, div_eq_mul_inv, mul_comm]
  unfold apm_aunk03_modifiedKernel apm_aunk03_nonzeroPoleRemainder
    apm_aunk03_kernel
  rw [hds, hcot]
  have hzmem : z ∈ Complex.integerComplement := by
    rw [← show z - (k : ℂ) + (k : ℂ) = z by ring,
      Complex.add_intCast_mem_integerComplement]
    exact hw
  have hz0 := Complex.integerComplement.ne_zero hzmem
  simp only [zpow_neg]
  field_simp [hkC, hz0, Complex.integerComplement.ne_zero hw]
  ring

/-- At zero, the analytic cotangent calculation gives residue `-π⁴/45`. -/
theorem apm_aunk03_modifiedKernel_sub_zero_residue
    (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    apm_aunk03_modifiedKernel z -
        (-(Real.pi : ℂ) ^ 4 / 45) * z⁻¹ = cotFourthRemainder z := by
  have hz0 := Complex.integerComplement.ne_zero hz
  have hcot := regularCot_eq_cot_sub_inv hz
  have hpi : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      regularCot z + 1 / z := by
    rw [hcot]
    ring
  rw [cotFourthRemainder_eq_div hz0]
  unfold apm_aunk03_modifiedKernel apm_aunk03_kernel cotFourthNumerator
  rw [hpi]
  simp only [zpow_neg]
  field_simp [hz0]
  ring

/-- Integer poles enclosed by the square of half-side `n+1/2`. -/
noncomputable def apm_aunk03_integerPoles (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- The residue coefficient at an integer pole. -/
noncomputable def apm_aunk03_residue (k : ℤ) : ℂ :=
  if k = 0 then -(Real.pi : ℂ) ^ 4 / 45 else 1 / (k : ℂ) ^ 4

/-- The remainder formula at an arbitrary nonzero candidate pole.  Membership
in the integer pole set is only needed when it is compared with cotangent. -/
noncomputable def apm_aunk03_genericPoleRemainder (a z : ℂ) : ℂ :=
  regularCot (z - a) / z ^ 4 +
    dslope (fun w : ℂ => 1 / w ^ 4) a z -
    z ^ (-5 : ℤ) + (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ)

/-- The generic nonzero-pole remainder is analytic at its candidate pole. -/
theorem apm_aunk03_genericPoleRemainder_analyticAt
    (a : ℂ) (ha : a ≠ 0) :
    AnalyticAt ℂ (apm_aunk03_genericPoleRemainder a) a := by
  have hreg : AnalyticAt ℂ (fun z : ℂ => regularCot (z - a)) a := by
    simpa [Function.comp_def] using analyticAt_regularCot_zero.comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => z - a) a by fun_prop) (by simp)
  have hinv4 : AnalyticAt ℂ (fun z : ℂ => 1 / z ^ 4) a :=
    analyticAt_const.div (analyticAt_id.pow 4) (pow_ne_zero 4 ha)
  have hds := analyticAt_dslope a (fun z : ℂ => 1 / z ^ 4) hinv4
  have hz5 : AnalyticAt ℂ (fun z : ℂ => z ^ (-5 : ℤ)) a :=
    analyticAt_id.zpow ha
  have hz3 : AnalyticAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ)) a :=
    analyticAt_const.mul (analyticAt_id.zpow ha)
  unfold apm_aunk03_genericPoleRemainder
  exact (((hreg.div (analyticAt_id.pow 4) (pow_ne_zero 4 ha)).add hds).sub
    hz5).add hz3

/-- The modified kernel after all of its listed simple principal parts have
been subtracted. -/
noncomputable def apm_aunk03_rawRemainder (n : ℕ) (z : ℂ) : ℂ :=
  apm_aunk03_modifiedKernel z -
    ∑ k ∈ apm_aunk03_integerPoles n,
      apm_aunk03_residue k * (z - (k : ℂ))⁻¹

/-- A local analytic extension of the raw remainder at a listed pole `a`:
use the local cotangent extension there and retain all other principal parts. -/
noncomputable def apm_aunk03_localExtension (n : ℕ) (a z : ℂ) : ℂ :=
  (if a = 0 then cotFourthRemainder z
    else apm_aunk03_genericPoleRemainder a z) -
  ∑ k ∈ (apm_aunk03_integerPoles n).filter (fun k : ℤ => (k : ℂ) ≠ a),
    apm_aunk03_residue k * (z - (k : ℂ))⁻¹

/-- The proposed local extension is analytic at every listed complex pole. -/
theorem apm_aunk03_localExtension_analyticAt
    (n : ℕ) (a : ℂ)
    (ha : a ∈ (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ)) :
    AnalyticAt ℂ (apm_aunk03_localExtension n a) a := by
  have hbase : AnalyticAt ℂ
      (fun z => if a = 0 then cotFourthRemainder z
        else apm_aunk03_genericPoleRemainder a z) a := by
    by_cases ha0 : a = 0
    · subst a
      simpa using analyticAt_cotFourthRemainder_zero
    · simpa [ha0] using apm_aunk03_genericPoleRemainder_analyticAt a ha0
  have hsum : AnalyticAt ℂ
      (fun z => ∑ k ∈ (apm_aunk03_integerPoles n).filter
          (fun k : ℤ => (k : ℂ) ≠ a),
        apm_aunk03_residue k * (z - (k : ℂ))⁻¹) a := by
    let s := (apm_aunk03_integerPoles n).filter
      (fun k : ℤ => (k : ℂ) ≠ a)
    have hs : AnalyticAt ℂ
        (∑ k ∈ s, (fun z : ℂ => apm_aunk03_residue k *
          (z - (k : ℂ))⁻¹)) a :=
      Finset.analyticAt_sum s (fun k hk => by
        simp only [s, Finset.mem_filter] at hk
        have hden : AnalyticAt ℂ (fun z : ℂ => (z - (k : ℂ))⁻¹) a :=
          (analyticAt_id.sub analyticAt_const).fun_inv (by
            simpa [sub_ne_zero] using hk.2.symm)
        simpa only [Pi.mul_apply] using
          (analyticAt_const.mul hden : AnalyticAt ℂ
            ((fun _ : ℂ => apm_aunk03_residue k) *
              fun z : ℂ => (z - (k : ℂ))⁻¹) a))
    have heq : (fun z => ∑ k ∈ s, apm_aunk03_residue k *
        (z - (k : ℂ))⁻¹) =
        ∑ k ∈ s, (fun z : ℂ => apm_aunk03_residue k *
          (z - (k : ℂ))⁻¹) := by
      funext z
      simp
    simpa [s, heq] using hs
  unfold apm_aunk03_localExtension
  exact hbase.sub hsum

/-- On a punctured neighborhood of each listed pole, the raw remainder agrees
with its analytic local extension. -/
theorem apm_aunk03_rawRemainder_eventually_localExtension
    (n : ℕ) (a : ℂ)
    (ha : a ∈ (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ)) :
    apm_aunk03_rawRemainder n =ᶠ[𝓝[≠] a]
      apm_aunk03_localExtension n a := by
  rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
  apply eventually_nhdsWithin_iff.mpr
  have hball : ∀ᶠ z : ℂ in 𝓝 (k : ℂ), z ∈ Metric.ball (k : ℂ) 1 :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hball] with z hdist hz
  have hnorm : ‖z - (k : ℂ)‖ < 1 := by
    simpa only [Metric.mem_ball, Complex.dist_eq] using hdist
  have hw : z - (k : ℂ) ∈ Complex.integerComplement :=
    mem_integerComplement_of_norm_lt_one (sub_ne_zero.mpr hz) hnorm
  have hfilter : (apm_aunk03_integerPoles n).filter
      (fun j : ℤ => (j : ℂ) ≠ (k : ℂ)) =
      (apm_aunk03_integerPoles n).erase k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hjs, hjk⟩
      exact ⟨by exact_mod_cast hjk, hjs⟩
    · rintro ⟨hjk, hjs⟩
      exact ⟨hjs, by exact_mod_cast hjk⟩
  have hsum := Finset.sum_erase_add
    (s := apm_aunk03_integerPoles n)
    (f := fun j : ℤ => apm_aunk03_residue j * (z - (j : ℂ))⁻¹) hk
  by_cases hk0 : k = 0
  · subst k
    have hprincipal := apm_aunk03_modifiedKernel_sub_zero_residue z (by simpa using hw)
    unfold apm_aunk03_rawRemainder apm_aunk03_localExtension
    rw [hfilter]
    simp only [Int.cast_zero, if_pos rfl]
    rw [← hsum]
    simp [apm_aunk03_residue] at hsum ⊢
    linear_combination hprincipal
  · have hprincipal :=
      apm_aunk03_modifiedKernel_sub_nonzero_residue k hk0 z hz hw
    have hgeneric : apm_aunk03_nonzeroPoleRemainder k z =
        apm_aunk03_genericPoleRemainder (k : ℂ) z := by rfl
    rw [hgeneric] at hprincipal
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    unfold apm_aunk03_rawRemainder apm_aunk03_localExtension
    rw [hfilter, if_neg hkC]
    rw [← hsum]
    simp [apm_aunk03_residue, hk0] at hsum ⊢
    linear_combination hprincipal

/-- Every integer in the closed square of half-side `n+1/2` is one of the
listed poles `-n,…,n`. -/
theorem apm_aunk03_integerComplement_of_mem_square
    (n : ℕ) (z : ℂ)
    (hz : z ∈ (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
      Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))))
    (hnot : z ∉ (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ)) :
    z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨k, hkz⟩
  have hR : 0 ≤ n + (1 / 2 : ℝ) := by positivity
  have hre := hz.1
  rw [uIcc_of_le (neg_le_self hR)] at hre
  have hkreal : (k : ℝ) = z.re := by
    rw [← hkz]
    simp
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
  apply Finset.mem_image.mpr
  exact ⟨k, by simp [apm_aunk03_integerPoles, hnle, hkle], hkz⟩

/-- Away from the integer lattice, the modified cotangent kernel is
holomorphic. -/
theorem apm_aunk03_modifiedKernel_differentiableAt
    (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ apm_aunk03_modifiedKernel z := by
  have hz0 := Complex.integerComplement.ne_zero hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    sin_pi_mul_ne_zero hz
  have hcosD : DifferentiableAt ℂ
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w)) z := by fun_prop
  have hsinD : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by fun_prop
  have hcot : DifferentiableAt ℂ
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) /
        Complex.sin ((Real.pi : ℂ) * w)) z :=
    hcosD.div hsinD hsin
  have hmain : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) *
        (Complex.cos ((Real.pi : ℂ) * w) /
          Complex.sin ((Real.pi : ℂ) * w)) / w ^ 4) z :=
    (analyticAt_const.differentiableAt.mul hcot).div (by fun_prop)
      (pow_ne_zero 4 hz0)
  have hz5 : DifferentiableAt ℂ (fun w : ℂ => w ^ (-5 : ℤ)) z :=
    (analyticAt_id.zpow hz0).differentiableAt
  have hz3 : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ 2 / 3 * w ^ (-3 : ℤ)) z :=
    (analyticAt_const.mul (analyticAt_id.zpow hz0)).differentiableAt
  unfold apm_aunk03_modifiedKernel apm_aunk03_kernel Complex.cot
  exact (hmain.sub hz5).add hz3

/-- Inside the square, away from the listed poles, the raw remainder is
holomorphic. -/
theorem apm_aunk03_rawRemainder_differentiableAt
    (n : ℕ) (z : ℂ)
    (hz : z ∈ (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
      Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))))
    (hnot : z ∉ (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ)) :
    DifferentiableAt ℂ (apm_aunk03_rawRemainder n) z := by
  have hzint := apm_aunk03_integerComplement_of_mem_square n z hz hnot
  have hmod := apm_aunk03_modifiedKernel_differentiableAt z hzint
  have hsum : DifferentiableAt ℂ
      (fun w => ∑ k ∈ apm_aunk03_integerPoles n,
        apm_aunk03_residue k * (w - (k : ℂ))⁻¹) z := by
    apply DifferentiableAt.fun_sum
    intro k hk
    have hzk : z ≠ (k : ℂ) := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨k, hk, h.symm⟩
    have hden : DifferentiableAt ℂ (fun w : ℂ => (w - (k : ℂ))⁻¹) z :=
      (differentiableAt_id.sub (differentiableAt_const (k : ℂ))).inv
        (sub_ne_zero.mpr hzk)
    exact (differentiableAt_const (apm_aunk03_residue k)).mul hden
  change DifferentiableAt ℂ (fun w => apm_aunk03_modifiedKernel w -
    ∑ k ∈ apm_aunk03_integerPoles n,
      apm_aunk03_residue k * (w - (k : ℂ))⁻¹) z
  exact hmod.sub hsum

/-- The raw remainder with all enclosed removable singularities filled. -/
noncomputable def apm_aunk03_patchedRemainder (n : ℕ) : ℂ → ℂ :=
  patchFinite ((apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ))
    (apm_aunk03_rawRemainder n) (apm_aunk03_localExtension n)

/-- The patched remainder is holomorphic throughout the closed square. -/
theorem apm_aunk03_patchedRemainder_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (apm_aunk03_patchedRemainder n)
      (Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ)) ×ℂ
        Set.uIcc (-(n + (1 / 2 : ℝ))) (n + (1 / 2 : ℝ))) := by
  unfold apm_aunk03_patchedRemainder
  apply differentiableOn_patchFinite
  · exact fun z hz hnot => apm_aunk03_rawRemainder_differentiableAt n z hz hnot
  · exact fun a ha => apm_aunk03_localExtension_analyticAt n a ha
  · exact fun a ha => apm_aunk03_rawRemainder_eventually_localExtension n a ha

/-- Each listed real pole lies strictly inside the half-integer square. -/
theorem apm_aunk03_integerPole_abs_lt (n : ℕ) (k : ℤ)
    (hk : k ∈ apm_aunk03_integerPoles n) :
    |(k : ℝ)| < n + (1 / 2 : ℝ) := by
  simp only [apm_aunk03_integerPoles, Finset.mem_Icc] at hk
  have habs : |(k : ℝ)| ≤ n := by
    rw [abs_le]
    constructor
    · exact_mod_cast hk.1
    · exact_mod_cast hk.2
  linarith

/-- No listed integer pole lies on the half-integer square boundary. -/
theorem apm_aunk03_boundary_not_mem_poles (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    z ∉ (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℂ) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
  have hkabs := apm_aunk03_integerPole_abs_lt n k hk
  rcases hz with hz | hz
  · have hre : ((k : ℂ)).re = (k : ℝ) := by simp
    rw [hre] at hz
    linarith
  · have hR : 0 < n + (1 / 2 : ℝ) := by positivity
    have him : ((k : ℂ)).im = 0 := by simp
    rw [him, abs_zero] at hz
    linarith

/-- On the contour, finite patching leaves the raw remainder unchanged. -/
theorem apm_aunk03_patchedRemainder_eq_on_boundary
    (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    apm_aunk03_patchedRemainder n z = apm_aunk03_rawRemainder n z := by
  unfold apm_aunk03_patchedRemainder
  exact patchFinite_eq (apm_aunk03_boundary_not_mem_poles n z hz)

/-- The same finite pole set, represented as real locations for the rectangle
residue theorem. -/
noncomputable def apm_aunk03_realPoles (n : ℕ) : Finset ℝ :=
  (apm_aunk03_integerPoles n).image fun k : ℤ => (k : ℝ)

/-- Residue coefficient as a function of a real pole location. -/
noncomputable def apm_aunk03_realResidue (a : ℝ) : ℂ :=
  if a = 0 then -(Real.pi : ℂ) ^ 4 / 45 else 1 / (a : ℂ) ^ 4

theorem apm_aunk03_realResidue_intCast (k : ℤ) :
    apm_aunk03_realResidue (k : ℝ) = apm_aunk03_residue k := by
  by_cases hk : k = 0
  · subst k
    simp [apm_aunk03_realResidue, apm_aunk03_residue]
  · have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp [apm_aunk03_realResidue, apm_aunk03_residue, hk, hkr]

/-- The real-pole sum is the integer-indexed principal-part sum. -/
theorem apm_aunk03_realPole_sum_eq (n : ℕ) (z : ℂ) :
    (∑ a ∈ apm_aunk03_realPoles n,
      apm_aunk03_realResidue a * (z - (a : ℂ))⁻¹) =
    ∑ k ∈ apm_aunk03_integerPoles n,
      apm_aunk03_residue k * (z - (k : ℂ))⁻¹ := by
  unfold apm_aunk03_realPoles
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [apm_aunk03_realResidue_intCast]
    norm_cast
  · intro k hk j hj hcast
    change (k : ℝ) = (j : ℝ) at hcast
    exact_mod_cast hcast

/-- The symmetric residue sum is the zero residue plus twice the positive
partial Basel sum. -/
theorem apm_aunk03_residue_sum_eq (n : ℕ) :
    (∑ a ∈ apm_aunk03_realPoles n, apm_aunk03_realResidue a) =
      -(Real.pi : ℂ) ^ 4 / 45 +
        2 * ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℂ) ^ 4 := by
  have himage : (∑ a ∈ apm_aunk03_realPoles n, apm_aunk03_realResidue a) =
      ∑ k ∈ apm_aunk03_integerPoles n, apm_aunk03_residue k := by
    unfold apm_aunk03_realPoles
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      exact apm_aunk03_realResidue_intCast k
    · intro k hk j hj hcast
      change (k : ℝ) = (j : ℝ) at hcast
      exact_mod_cast hcast
  have hint : ∀ m : ℕ,
      (∑ k ∈ apm_aunk03_integerPoles m, apm_aunk03_residue k) =
        -(Real.pi : ℂ) ^ 4 / 45 +
          2 * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℂ) ^ 4 := by
    intro m
    induction m with
    | zero =>
        simp [apm_aunk03_integerPoles, apm_aunk03_residue]
    | succ n ih =>
      have hfin : apm_aunk03_integerPoles (n + 1) =
          insert (-((n + 1 : ℕ) : ℤ))
            (insert ((n + 1 : ℕ) : ℤ) (apm_aunk03_integerPoles n)) := by
        ext k
        simp only [apm_aunk03_integerPoles, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hpos : ((n + 1 : ℕ) : ℤ) ∉ apm_aunk03_integerPoles n := by
        simp [apm_aunk03_integerPoles]
      have hneg : (-((n + 1 : ℕ) : ℤ)) ∉
          insert ((n + 1 : ℕ) : ℤ) (apm_aunk03_integerPoles n) := by
        simp only [Finset.mem_insert, not_or]
        constructor
        · omega
        · simp [apm_aunk03_integerPoles]
      rw [hfin, Finset.sum_insert hneg, Finset.sum_insert hpos, ih,
        Finset.sum_range_succ]
      have hn0 : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
      have hnn0 : (-((n + 1 : ℕ) : ℤ)) ≠ 0 := neg_ne_zero.mpr hn0
      simp only [apm_aunk03_residue, if_neg hn0, if_neg hnn0]
      push_cast
      ring
  exact himage.trans (hint n)

/-- Finite residue identity on the prescribed half-integer square, after the
higher zero principal parts have been removed. -/
theorem apm_aunk03_modifiedKernel_residue_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_modifiedKernel (n + (1 / 2 : ℝ)) =
      2 * Real.pi * I * ∑ a ∈ apm_aunk03_realPoles n,
        apm_aunk03_realResidue a := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hdiff := apm_aunk03_patchedRemainder_differentiableOn n
  have hdiff' : DifferentiableOn ℂ (apm_aunk03_patchedRemainder n)
      (Set.uIcc (-R) R ×ℂ Set.uIcc (-R) R) := by
    simpa [R] using hdiff
  have hint : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (apm_aunk03_patchedRemainder n) (-R - R * I) (R + R * I) := by
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegrable_of_differentiableOn
    simpa using hdiff'
  apply centeredSquareBoundaryIntegral_eq_finset_residues_of_differentiableOn
    apm_aunk03_modifiedKernel (apm_aunk03_patchedRemainder n)
      (apm_aunk03_realPoles n) apm_aunk03_realResidue R hR
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact apm_aunk03_integerPole_abs_lt n k hk
  · exact hdiff'
  · exact hint
  · intro z hz
    rw [apm_aunk03_patchedRemainder_eq_on_boundary n z (by simpa [R] using hz)]
    unfold apm_aunk03_rawRemainder
    rw [apm_aunk03_realPole_sum_eq]
    ring

/-- The modified kernel is integrable on the prescribed square boundary. -/
theorem apm_aunk03_modifiedKernel_boundaryIntegrable (n : ℕ) :
    ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      apm_aunk03_modifiedKernel
      (-(n + (1 / 2 : ℝ)) - (n + (1 / 2 : ℝ)) * I)
      ((n + (1 / 2 : ℝ)) + (n + (1 / 2 : ℝ)) * I) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hdiff : DifferentiableOn ℂ (apm_aunk03_patchedRemainder n)
      (Set.uIcc (-R) R ×ℂ Set.uIcc (-R) R) := by
    simpa [R] using apm_aunk03_patchedRemainder_differentiableOn n
  have hpatch : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (apm_aunk03_patchedRemainder n) (-R - R * I) (R + R * I) := by
    apply ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegrable_of_differentiableOn
    simpa using hdiff
  let p : ℝ → ℂ → ℂ := fun a z =>
    apm_aunk03_realResidue a * (z - (a : ℂ))⁻¹
  have hp : ∀ a ∈ apm_aunk03_realPoles n,
      ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
        (p a) (-R - R * I) (R + R * I) := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact (ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_sub_inv
      (k : ℝ) R (by simpa [R] using apm_aunk03_integerPole_abs_lt n k hk)).const_mul
        (apm_aunk03_realResidue (k : ℝ))
  have htotal : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z => apm_aunk03_patchedRemainder n z +
        ∑ a ∈ apm_aunk03_realPoles n, p a z)
      (-R - R * I) (R + R * I) :=
    hpatch.add (ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable.finset_sum hp)
  have hdecomp (z : ℂ) (hz : OnCenteredSquareBoundary R z) :
      apm_aunk03_patchedRemainder n z +
          ∑ a ∈ apm_aunk03_realPoles n, p a z =
        apm_aunk03_modifiedKernel z := by
    rw [apm_aunk03_patchedRemainder_eq_on_boundary n z (by simpa [R] using hz)]
    unfold apm_aunk03_rawRemainder p
    rw [apm_aunk03_realPole_sum_eq]
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

/-- The prescribed kernel itself is integrable on every half-integer square. -/
theorem apm_aunk03_kernel_boundaryIntegrable (n : ℕ) :
    ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      apm_aunk03_kernel
      (-(n + (1 / 2 : ℝ)) - (n + (1 / 2 : ℝ)) * I)
      ((n + (1 / 2 : ℝ)) + (n + (1 / 2 : ℝ)) * I) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hmod : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      apm_aunk03_modifiedKernel (-R - R * I) (R + R * I) := by
    simpa [R] using apm_aunk03_modifiedKernel_boundaryIntegrable n
  have h5 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-5 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-5)
  have h3 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ))
      (-R - R * I) (R + R * I) := by
    simpa using (ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-3)).const_mul ((Real.pi : ℂ) ^ 2 / 3)
  have htemp := hmod.add h5 |>.sub h3
  have heq (z : ℂ) :
      (apm_aunk03_modifiedKernel z + z ^ (-5 : ℤ)) -
          (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ) =
        apm_aunk03_kernel z := by
    unfold apm_aunk03_modifiedKernel
    ring
  have hout := htemp.congr
    (fun x hx => heq (x + (-R - R * I).im * I))
    (fun x hx => heq (x + (R + R * I).im * I))
    (fun y hy => heq ((R + R * I).re + y * I))
    (fun y hy => heq ((-R - R * I).re + y * I))
  simpa [R] using hout

/-- Subtracting the fifth- and third-order principal parts does not change
the square integral, since both have explicit single-valued primitives. -/
theorem apm_aunk03_kernel_integral_eq_modified (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_kernel (n + (1 / 2 : ℝ)) =
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_modifiedKernel (n + (1 / 2 : ℝ)) := by
  let R : ℝ := n + (1 / 2 : ℝ)
  have hR : 0 < R := by positivity
  have hk : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      apm_aunk03_kernel (-R - R * I) (R + R * I) := by
    simpa [R] using apm_aunk03_kernel_boundaryIntegrable n
  have h5 : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-5 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-5)
  have h3base : ConstructionTargets.RectangleCauchy.RectangleBoundaryIntegrable
      (fun z : ℂ => z ^ (-3 : ℤ)) (-R - R * I) (R + R * I) := by
    simpa using ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegrable_zpow
      0 R (by simpa using hR) (-3)
  have h3 := h3base.const_mul ((Real.pi : ℂ) ^ 2 / 3)
  have hsub := ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_sub hk h5
  have hadd := ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_add
    (hk.sub h5) h3
  have hzero5 : ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z : ℂ => z ^ (-5 : ℤ)) (-R - R * I) (R + R * I) = 0 := by
    simpa [ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral] using
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral_zpow_eq_zero
        0 R (by simpa using hR) (-5) (by norm_num)
  have hzero3 : ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z : ℂ => z ^ (-3 : ℤ)) (-R - R * I) (R + R * I) = 0 := by
    simpa [ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral] using
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral_zpow_eq_zero
        0 R (by simpa using hR) (-3) (by norm_num)
  have hconst3 := ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_const_mul
    ((Real.pi : ℂ) ^ 2 / 3) (fun z : ℂ => z ^ (-3 : ℤ))
      (-R - R * I) (R + R * I)
  rw [hsub, hzero5, sub_zero] at hadd
  rw [hconst3, hzero3, mul_zero, add_zero] at hadd
  have hrect : ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral apm_aunk03_kernel
      (-R - R * I) (R + R * I) =
    ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
      (fun z => (apm_aunk03_kernel z - z ^ (-5 : ℤ)) +
        (Real.pi : ℂ) ^ 2 / 3 * z ^ (-3 : ℤ))
      (-R - R * I) (R + R * I) := by
    rw [hadd]
  simpa [R, ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral,
    apm_aunk03_modifiedKernel] using hrect

/-- The prescribed kernel therefore satisfies the finite residue identity
on every square `Cₙ`. -/
theorem apm_aunk03_residue_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_kernel (n + (1 / 2 : ℝ)) =
      2 * Real.pi * I * ∑ a ∈ apm_aunk03_realPoles n,
        apm_aunk03_realResidue a := by
  rw [apm_aunk03_kernel_integral_eq_modified]
  exact apm_aunk03_modifiedKernel_residue_identity n

/-- In the upper half-plane, the exponential formula bounds cotangent away
from the real axis.  The deliberately non-sharp constant is uniform in the
real part, which is what the horizontal sides of the squares require. -/
theorem apm_aunk03_norm_cot_pi_le_of_im_ge_half (z : ℂ)
    (hz : (1 / 2 : ℝ) ≤ z.im) :
    ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤
      (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi)) := by
  let q : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * z)
  let r : ℝ := Real.exp (-Real.pi)
  have hr0 : 0 ≤ r := Real.exp_pos _ |>.le
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
      _ ≤ ‖1 - q‖ := by
        simpa using (norm_sub_norm_le (1 : ℂ) q)
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

/-- On a vertical half-integer line, cotangent is a hyperbolic tangent and
has norm at most one. -/
theorem apm_aunk03_norm_cot_pi_half_add_mul_I_le (y : ℝ) :
    ‖Complex.cot ((Real.pi : ℂ) * ((1 / 2 : ℝ) + y * I))‖ ≤ 1 := by
  have harg : (Real.pi : ℂ) * ((1 / 2 : ℝ) + y * I) =
      (Real.pi / 2 : ℝ) + (Real.pi * y : ℝ) * I := by
    push_cast
    ring
  rw [harg]
  rw [Complex.cot_eq_cos_div_sin, Complex.sin_add_mul_I,
    Complex.cos_add_mul_I]
  simp only [ofReal_div, ofReal_one, ofReal_ofNat, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two, one_mul, zero_mul, zero_add, zero_sub]
  rw [norm_div, norm_neg, norm_mul, norm_I, mul_one]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  simp only [add_zero, Complex.norm_real]
  simpa [Real.norm_eq_abs, Real.tanh_eq_sinh_div_cosh, ← abs_div] using
    (Real.abs_tanh_lt_one (Real.pi * y)).le

/-- Cotangent is uniformly bounded on all four sides of the prescribed
half-integer square. -/
theorem apm_aunk03_norm_cot_pi_le_on_square (n : ℕ) (z : ℂ)
    (hz : z ∈ apm_aunk03_squareContour n) :
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
  change OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z at hz
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
      exact (apm_aunk03_norm_cot_pi_half_add_mul_I_le z.im).trans hC
    · have hzform : z = ((1 / 2 : ℝ) + z.im * I) + (-(n : ℤ) - 1 : ℤ) := by
        apply Complex.ext
        · rw [hre]
          push_cast
          simp
          ring
        · simp
      rw [hzform, cot_pi_add_int]
      exact (apm_aunk03_norm_cot_pi_half_add_mul_I_le z.im).trans hC
  · have hhalf : (1 / 2 : ℝ) ≤ |z.im| := by simpa [him]
    rcases abs_cases z.im with him0 | him0
    · apply apm_aunk03_norm_cot_pi_le_of_im_ge_half
      simpa [him0] using hhalf
    · have hc := apm_aunk03_norm_cot_pi_le_of_im_ge_half ((starRingEnd ℂ) z) (by
          simp only [conj_im]
          simpa [him0] using hhalf)
      have heq : Complex.cot ((Real.pi : ℂ) * (starRingEnd ℂ) z) =
          (starRingEnd ℂ) (Complex.cot ((Real.pi : ℂ) * z)) := by
        rw [← Complex.cot_conj]
        congr 2
        simp
      rw [heq, Complex.norm_conj] at hc
      exact hc

/-- The prescribed kernel is `O(R⁻⁴)` pointwise on the square of
half-side `R = n + 1/2`. -/
theorem apm_aunk03_norm_kernel_le_on_square (n : ℕ) (z : ℂ)
    (hz : OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z) :
    ‖apm_aunk03_kernel z‖ ≤
      Real.pi * ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) /
        (n + (1 / 2 : ℝ)) ^ 4 := by
  let R : ℝ := n + (1 / 2 : ℝ)
  let C : ℝ := (1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))
  have hR : 0 ≤ R := by positivity
  have hzset : z ∈ apm_aunk03_squareContour n := by
    change OnCenteredSquareBoundary (n + (1 / 2 : ℝ)) z
    exact hz
  have hznorm : R ≤ ‖z‖ := by
    rcases hz with ⟨hre, him⟩ | ⟨him, hre⟩
    · change n + (1 / 2 : ℝ) ≤ ‖z‖
      rw [← hre]
      exact abs_re_le_norm z
    · change n + (1 / 2 : ℝ) ≤ ‖z‖
      rw [← him]
      exact abs_im_le_norm z
  have hcot : ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤ C := by
    simpa [R, C] using apm_aunk03_norm_cot_pi_le_on_square n z hzset
  have hnum : ‖(Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)‖ ≤
      Real.pi * C := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hcot Real.pi_pos.le
  unfold apm_aunk03_kernel
  rw [norm_div, norm_pow]
  change _ ≤ Real.pi * C / R ^ 4
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hcot
  calc
    _ ≤ (Real.pi * C) / ‖z‖ ^ 4 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (Real.pi * C) / R ^ 4 := by
      apply div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le hC0) (by positivity)
      exact pow_le_pow_left₀ hR hznorm 4

/-- The ML inequality on the four explicit interval integrals gives a cubic
decay bound for the prescribed contour integral. -/
theorem apm_aunk03_norm_contourIntegral_le (n : ℕ) :
    ‖ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_kernel (n + (1 / 2 : ℝ))‖ ≤
      8 * Real.pi * ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) /
        (n + (1 / 2 : ℝ)) ^ 3 := by
  let R : ℝ := n + (1 / 2 : ℝ)
  let M : ℝ := Real.pi *
    ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) / R ^ 4
  have hR : 0 < R := by positivity
  change ‖ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
      apm_aunk03_kernel R‖ ≤
    8 * Real.pi * ((1 + Real.exp (-Real.pi)) / (1 - Real.exp (-Real.pi))) /
      R ^ 3
  have hside (x y : ℝ) (hxy : OnCenteredSquareBoundary R (x + y * I)) :
      ‖apm_aunk03_kernel (x + y * I)‖ ≤ M := by
    simpa [R, M] using apm_aunk03_norm_kernel_le_on_square n (x + y * I)
      (by simpa [R] using hxy)
  have hinterval (g : ℝ → ℂ) (hg : ∀ t ∈ Set.uIcc (-R) R, ‖g t‖ ≤ M) :
      ‖∫ t : ℝ in -R..R, g t‖ ≤ M * (2 * R) := by
    calc
      _ ≤ M * |R - -R| := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t ht => hg t (uIoc_subset_uIcc ht))
      _ = M * (2 * R) := by rw [abs_of_nonneg (by linarith)]; ring
  have hb := hinterval (fun x : ℝ => apm_aunk03_kernel (x + (-R) * I))
    (fun x hx => by simpa using (hside x (-R)
      (onBoundary_horizontal R x (-R) hR.le (by simp [abs_of_pos hR]) hx)))
  have ht := hinterval (fun x : ℝ => apm_aunk03_kernel (x + R * I))
    (fun x hx => hside x R
      (onBoundary_horizontal R x R hR.le (by simp [abs_of_pos hR]) hx))
  have hr := hinterval (fun y : ℝ => apm_aunk03_kernel (R + y * I))
    (fun y hy => hside R y
      (onBoundary_vertical R R y hR.le (by simp [abs_of_pos hR]) hy))
  have hl := hinterval (fun y : ℝ => apm_aunk03_kernel (-R + y * I))
    (fun y hy => by simpa using (hside (-R) y
      (onBoundary_vertical R (-R) y hR.le (by simp [abs_of_pos hR]) hy)))
  unfold ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
    ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral
  simp only [neg_re, ofReal_re, mul_re, mul_im, I_re, ofReal_im, I_im, mul_zero,
    mul_one, sub_re, sub_im, neg_im, add_re, add_im, zero_mul, add_zero,
    zero_add, sub_zero, neg_zero, zero_sub, ofReal_neg]
  calc
    _ ≤ (‖∫ x : ℝ in -R..R, apm_aunk03_kernel (x + -R * I)‖ +
          ‖∫ x : ℝ in -R..R, apm_aunk03_kernel (x + R * I)‖) +
        ‖I * ∫ y : ℝ in -R..R, apm_aunk03_kernel (R + y * I)‖ +
        ‖I * ∫ y : ℝ in -R..R, apm_aunk03_kernel (-R + y * I)‖ := by
      calc
        _ ≤ ‖(∫ x : ℝ in -R..R, apm_aunk03_kernel (x + -R * I)) -
              (∫ x : ℝ in -R..R, apm_aunk03_kernel (x + R * I))‖ +
            ‖I * ∫ y : ℝ in -R..R, apm_aunk03_kernel (R + y * I)‖ +
            ‖I * ∫ y : ℝ in -R..R, apm_aunk03_kernel (-R + y * I)‖ := by
              calc
                _ ≤ ‖(∫ x : ℝ in -R..R, apm_aunk03_kernel (x + -R * I)) -
                      (∫ x : ℝ in -R..R, apm_aunk03_kernel (x + R * I)) +
                      I * (∫ y : ℝ in -R..R, apm_aunk03_kernel (R + y * I))‖ +
                      ‖I * ∫ y : ℝ in -R..R, apm_aunk03_kernel (-R + y * I)‖ :=
                    norm_sub_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ (M * (2 * R) + M * (2 * R)) + M * (2 * R) + M * (2 * R) := by
      simpa using add_le_add (add_le_add (add_le_add hb ht)
        (by simpa using hr)) (by simpa using hl)
    _ = 8 * Real.pi * ((1 + Real.exp (-Real.pi)) /
          (1 - Real.exp (-Real.pi))) / R ^ 3 := by
      dsimp [M]
      field_simp
      ring
    _ = _ := by rfl

/-- The boundary integral on the prescribed squares tends to zero. -/
theorem apm_aunk03_contourIntegral_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_kernel (n + (1 / 2 : ℝ))) atTop (nhds 0) := by
  apply squeeze_zero_norm apm_aunk03_norm_contourIntegral_le
  apply tendsto_const_nhds.div_atTop
  apply Filter.tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) |>.comp
  exact Filter.tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
    tendsto_natCast_atTop_atTop

/-- The finite contour computation in the form used to pass to the limit. -/
theorem apm_aunk03_contour_identity (n : ℕ) :
    ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral
        apm_aunk03_kernel (n + (1 / 2 : ℝ)) =
      2 * Real.pi * I * (-(Real.pi : ℂ) ^ 4 / 45 +
        2 * ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℂ) ^ 4) := by
  rw [apm_aunk03_residue_identity, apm_aunk03_residue_sum_eq]

theorem apm_aunk03 :
    (∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 4) = Real.pi ^ 4 / 90 := by
  let uR : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ) ^ 4
  let uC : ℕ → ℂ := fun k => 1 / ((k + 1 : ℕ) : ℂ) ^ 4
  have hsumR : Summable uR := by
    rw [show uR = fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹ by
      funext n; simp [uR, one_div]]
    exact (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ 4)⁻¹)) 1).mpr
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
    (hsumC.hasSum_iff_tendsto_nat.mp hsumC.hasSum)
  have hrhs : Tendsto (fun n : ℕ =>
      2 * Real.pi * I * (-(Real.pi : ℂ) ^ 4 / 45 +
        2 * ∑ k ∈ Finset.range n, uC k)) atTop (nhds 0) := by
    apply apm_aunk03_contourIntegral_tendsto_zero.congr'
    filter_upwards [] with n
    simpa [uC] using apm_aunk03_contour_identity n
  have hcomputed : Tendsto (fun n : ℕ =>
      2 * Real.pi * I * (-(Real.pi : ℂ) ^ 4 / 45 +
        2 * ∑ k ∈ Finset.range n, uC k)) atTop
      (nhds (2 * Real.pi * I * (-(Real.pi : ℂ) ^ 4 / 45 +
        2 * ∑' k, uC k))) := by
    simpa using ((tendsto_const_nhds.add (hpartial.const_mul 2)).const_mul
      (2 * (Real.pi : ℂ) * I))
  have hzero : 2 * Real.pi * I * (-(Real.pi : ℂ) ^ 4 / 45 +
      2 * ∑' k, uC k) = 0 := tendsto_nhds_unique hcomputed hrhs
  have hpref : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hinner : -(Real.pi : ℂ) ^ 4 / 45 + 2 * ∑' k, uC k = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left hpref
  have htsumC : (∑' k, uC k) = (Real.pi : ℂ) ^ 4 / 90 := by
    linear_combination hinner / 2
  have hcast : ((∑' k, uR k) : ℂ) = (∑' k, uC k) := by
    apply tsum_congr
    intro k
    simp [uR, uC]
  change (∑' k, uR k) = Real.pi ^ 4 / 90
  exact_mod_cast hcast.trans htsumC

#print axioms apm_aunk03
