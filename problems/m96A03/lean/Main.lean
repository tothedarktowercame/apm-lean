import Mathlib

/-!
# APM m96A03

## Statement repairs

None.

## Encoding notes

The first part uses Mathlib's `OrthonormalBasis` on the genuine complex
`L²` space over the restricted Lebesgue measure.  The second part is stated
on an arbitrary complex Hilbert space.
-/

open scoped BigOperators ENNReal Interval
open MeasureTheory Set

theorem apm_m96a03
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :
    (∀ (a b : ℝ) (hab : a ≤ b)
      (u : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Icc a b))))
      (t : ℝ), t ∈ Icc a b →
        ∑' n : ℕ, ‖∫ s in a..t, u n s‖ ^ 2 = t - a) ∧
    (∀ (A : X →L[ℂ] X) (b : X), IsClosed (Set.range A) →
      ((∃ x : X, A x = b) ↔ ∀ y : X, A.adjoint y = 0 → inner ℂ b y = 0)) := by
  constructor
  · intro a b hab u t ht
    let μ := volume.restrict (Icc a b)
    let v : Lp ℂ 2 μ :=
      indicatorConstLp 2 (s := Icc a t) measurableSet_Icc (by finiteness) 1
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hcoeff (n : ℕ) : (∫ s in a..t, u n s) = inner ℂ v (u n) := by
      rw [L2.inner_indicatorConstLp_one]
      change (∫ s in a..t, u n s ∂volume) =
        ∫ s in Icc a t, u n s ∂(volume.restrict (Icc a b))
      rw [Measure.restrict_restrict_of_subset hsub]
      rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    have hsum := u.summable_inner_mul_inner v v
    calc
      ∑' n : ℕ, ‖∫ s in a..t, u n s‖ ^ 2 =
          ∑' n : ℕ, ((inner ℂ v (u n) * inner ℂ (u n) v).re) := by
            apply tsum_congr
            intro n
            rw [hcoeff]
            have hsymm : inner ℂ (u n) v = star (inner ℂ v (u n)) :=
              (inner_conj_symm (u n) v).symm
            rw [hsymm]
            exact_mod_cast
              (congrArg Complex.re (RCLike.mul_conj (inner ℂ v (u n)))).symm
      _ = (∑' n : ℕ, inner ℂ v (u n) * inner ℂ (u n) v).re :=
        (Complex.re_tsum hsum).symm
      _ = (inner ℂ v v).re := by rw [u.tsum_inner_mul_inner]
      _ = ‖v‖ ^ 2 := @inner_self_eq_norm_sq ℂ _ _ _ _ v
      _ = t - a := by
        rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
        simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
        rw [Measure.real, Measure.restrict_apply measurableSet_Icc,
          inter_eq_left.mpr hsub, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr ht.1)]
        norm_num
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (sub_nonneg.mpr ht.1)]
  · intro A b hclosed
    constructor
    · rintro ⟨x, rfl⟩ y hy
      rw [← A.adjoint_inner_right]
      simp [hy]
    · intro hb
      have hbker : b ∈ A.adjoint.kerᗮ := by
        rw [Submodule.mem_orthogonal']
        intro y hy
        exact hb y (by simpa [LinearMap.mem_ker] using hy)
      have hbrangeoo : b ∈ A.rangeᗮᗮ := by
        rwa [A.orthogonal_range]
      have hclosure : A.range.topologicalClosure = A.range := by
        change IsClosed (A.range : Set X) at hclosed
        apply SetLike.coe_injective
        simpa only [Submodule.topologicalClosure_coe] using
          (closure_eq_iff_isClosed.mpr hclosed)
      have hbmem : b ∈ A.range := by
        rw [Submodule.orthogonal_orthogonal_eq_closure, hclosure] at hbrangeoo
        exact hbrangeoo
      exact hbmem
