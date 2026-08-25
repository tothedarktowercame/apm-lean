import Mathlib
import ConstructionTargets.Rouche

/-!
# APM a95J03 — winding number of a trigonometric polynomial

## Statement repairs

None.

## Encoding questions

Mathlib has no directly usable integer-valued winding-number definition for a
parametrized path of this form. The index is therefore encoded by its genuine
normalized contour integral. The theorem asserts that this complex integral
is an integer and that the integer lies between `-N` and `N`.
-/

open Complex Polynomial
open scoped Interval Real BigOperators

noncomputable section

set_option maxHeartbeats 2000000


def apm_a95J03_trigPoly (a : ℤ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (Finset.Icc (-(N : ℤ)) N).sum
    (fun n ↦ a n * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))

def apm_a95J03_algPoly (a : ℤ → ℂ) (N : ℕ) : Polynomial ℂ :=
  (Finset.range (2 * N + 1)).sum
    (fun k ↦ Polynomial.C (a ((k : ℤ) - N)) * Polynomial.X ^ k)

/-- The algebraic polynomial obtained after clearing the `N` negative powers
has degree at most `2N`. Reused from the sound algebraic layer at commit
`1bf56f4`; unlike that commit's opaque winding-number placeholder, this lemma
applies unchanged to the repaired encoding. -/
lemma apm_a95J03_algPoly_degree_le (a : ℤ → ℂ) (N : ℕ) :
    (apm_a95J03_algPoly a N).natDegree ≤ 2 * N := by
  unfold apm_a95J03_algPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ k).trans (by
    simp only [Finset.mem_range] at hk
    omega)

/-- Subtracting `z Xⁿ` preserves the `2N` degree bound. -/
lemma apm_a95J03_algPoly_sub_degree_le
    (a : ℤ → ℂ) (N : ℕ) (z : ℂ) :
    (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).natDegree ≤
      2 * N := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · exact apm_a95J03_algPoly_degree_le a N
  · by_cases hz : z = 0
    · simp [hz, Polynomial.natDegree_zero]
    · rw [Polynomial.natDegree_C_mul_X_pow N z hz]
      omega

lemma apm_a95J03_trigPoly_hasDerivAt (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (apm_a95J03_trigPoly a N)
      ((Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) t := by
  unfold apm_a95J03_trigPoly
  apply HasDerivAt.fun_sum
  intro n _
  convert (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (n : ℂ))).comp_ofReal.cexp
    |>.const_mul (a n)) using 1 <;> simp [id] <;> ring

lemma apm_a95J03_fderiv_apply_one (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 =
      (Finset.Icc (-(N : ℤ)) N).sum (fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) := by
  have h := apm_a95J03_trigPoly_hasDerivAt a N t
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    congrArg (fun L : ℝ →L[ℝ] ℂ ↦ L 1) h.hasFDerivAt.fderiv

lemma apm_a95J03_trigPoly_eq_laurent (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    apm_a95J03_trigPoly a N t =
      (Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * Complex.exp (Complex.I * (t : ℂ)) ^ n := by
  unfold apm_a95J03_trigPoly
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- Clearing the negative powers in the Laurent sum gives exactly the
algebraic polynomial. -/
lemma apm_a95J03_algPoly_eval_eq_mul_laurent
    (a : ℤ → ℂ) (N : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (apm_a95J03_algPoly a N).eval w =
      w ^ N * ((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n) := by
  rw [apm_a95J03_algPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => (k : ℤ) - N) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro k₁ hk₁ k₂ hk₂ heq
    have hi : (k₁ : ℤ) = k₂ := sub_left_inj.mp heq
    exact Int.ofNat_inj.mp hi
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n + N).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have hnonneg : 0 ≤ n + (N : ℤ) := by omega
      change (((n + (N : ℤ)).toNat : ℕ) : ℤ) - N = n
      rw [Int.toNat_of_nonneg hnonneg]
      ring
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    have hpow : w ^ k = w ^ N * w ^ ((k : ℤ) - N) := by
      calc
        w ^ k = w ^ (k : ℤ) := by rw [zpow_natCast]
        _ = w ^ ((N : ℤ) + ((k : ℤ) - N)) := by congr 1 <;> omega
        _ = w ^ (N : ℤ) * w ^ ((k : ℤ) - N) := zpow_add₀ hw _ _
        _ = w ^ N * w ^ ((k : ℤ) - N) := by rw [zpow_natCast]
    rw [hpow]
    ring

lemma apm_a95J03_clearedPoly_eval_eq
    (a : ℤ → ℂ) (N : ℕ) (z w : ℂ) (hw : w ≠ 0) :
    (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval w =
      w ^ N *
        (((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n) - z) := by
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X,
    apm_a95J03_algPoly_eval_eq_mul_laurent a N w hw]
  ring

def apm_a95J03_windingIntegral (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * Complex.I)⁻¹) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (fderiv ℝ γ t) 1 / (γ t - z)

/-- The cleared polynomial has no zero on the unit circle whenever the
trigonometric curve avoids the target value on one full period. -/
lemma apm_a95J03_clearedPoly_ne_on_unitCircle
    {a : ℤ → ℂ} {N : ℕ} {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    ∀ w ∈ Metric.sphere (0 : ℂ) 1,
      (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval w ≠ 0 := by
  intro w hw
  have hw' : w ∈ circleMap (0 : ℂ) 1 '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc]
    simpa using hw
  obtain ⟨t, ht, rfl⟩ := hw'
  have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨ht.1.le, ht.2⟩
  have heq : circleMap 0 1 t = Complex.exp (Complex.I * (t : ℂ)) := by
    simp only [circleMap, ofReal_one, one_mul, zero_add]
    congr 1
    ring
  have hw0 : circleMap 0 1 t ≠ 0 := by
    rw [heq]
    exact Complex.exp_ne_zero _
  rw [apm_a95J03_clearedPoly_eval_eq a N z _ hw0]
  apply mul_ne_zero (pow_ne_zero _ hw0)
  rw [heq, ← apm_a95J03_trigPoly_eq_laurent]
  exact sub_ne_zero.mpr (hz t ht')

/-- Argument principle for the cleared polynomial, now with its boundary
nonvanishing obligation discharged directly from the problem hypothesis. -/
lemma apm_a95J03_clearedPoly_circleIntegral
    {a : ℤ → ℂ} {N : ℕ} {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    (∮ w in C(0, 1), logDeriv (fun u : ℂ ↦
        (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u) w) =
      (∑ᶠ w, (MeromorphicOn.divisor (fun u : ℂ ↦
        (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
        (Metric.closedBall 0 1) w : ℂ)) * (2 * Real.pi * Complex.I) := by
  apply ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum
  · norm_num
  · exact (analyticOnNhd_id.aeval_polynomial _).mono (Set.subset_univ _)
  · exact apm_a95J03_clearedPoly_ne_on_unitCircle hz

/-- The analytic divisor of a nonzero polynomial evaluation records its usual
algebraic root multiplicity. -/
lemma apm_a95J03_divisor_polynomial_eval_apply
    (p : Polynomial ℂ) (hp : p ≠ 0) (U : Set ℂ) {w : ℂ} (hw : w ∈ U) :
    MeromorphicOn.divisor (fun u : ℂ ↦ p.eval u) U w = p.rootMultiplicity w := by
  let m := p.rootMultiplicity w
  obtain ⟨q, hpq, hq⟩ : ∃ q : Polynomial ℂ,
      p = (Polynomial.X - Polynomial.C w) ^ m * q ∧
        ¬(Polynomial.X - Polynomial.C w) ∣ q := by
    simpa [m] using p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp w
  have hqeval : q.eval w ≠ 0 := by
    exact fun heval ↦ hq (Polynomial.dvd_iff_isRoot.mpr heval)
  have hqanalytic : AnalyticAt ℂ (fun u : ℂ ↦ q.eval u) w :=
    AnalyticOnNhd.eval_polynomial q w (Set.mem_univ w)
  have hpmer : MeromorphicOn (fun u : ℂ ↦ p.eval u) U := by
    exact ((AnalyticOnNhd.eval_polynomial p).mono
      (Set.subset_univ U)).meromorphicOn
  rw [MeromorphicOn.divisor_apply hpmer hw]
  have hord : meromorphicOrderAt (fun u : ℂ ↦ p.eval u) w =
      (m : ℤ) := by
    apply (meromorphicOrderAt_eq_int_iff
      (AnalyticOnNhd.eval_polynomial p w (Set.mem_univ w)).meromorphicAt).mpr
    refine ⟨fun u : ℂ ↦ q.eval u, hqanalytic, hqeval, ?_⟩
    filter_upwards with u
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    simp only [smul_eq_mul, zpow_natCast]
  rw [hord]
  simp [m]

/-- On a disk whose boundary contains no root, the polynomial divisor sum is
exactly the multiplicity-counted cardinality of the roots in the open disk. -/
lemma apm_a95J03_divisor_finsum_eq_filter_roots_card
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hne : ∀ w ∈ Metric.sphere (0 : ℂ) 1, p.eval w ≠ 0) :
    (∑ᶠ w, MeromorphicOn.divisor (fun u : ℂ ↦ p.eval u)
      (Metric.closedBall 0 1) w) =
      (((p.roots.filter fun w : ℂ ↦ ‖w‖ < 1).card : ℕ) : ℤ) := by
  classical
  let s : Finset ℂ := (p.roots.filter fun w : ℂ ↦ ‖w‖ < 1).toFinset
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · calc
      (∑ w ∈ s, MeromorphicOn.divisor (fun u : ℂ ↦ p.eval u)
          (Metric.closedBall 0 1) w) =
          ∑ w ∈ s, ((p.roots.filter fun u : ℂ ↦ ‖u‖ < 1).count w : ℤ) := by
            apply Finset.sum_congr rfl
            intro w hw
            have hwfilter : w ∈ p.roots.filter (fun u : ℂ ↦ ‖u‖ < 1) := by
              simpa [s] using hw
            have hwnorm : ‖w‖ < 1 := (Multiset.mem_filter.mp hwfilter).2
            have hwclosed : w ∈ Metric.closedBall (0 : ℂ) 1 := by
              simpa [Metric.mem_closedBall, dist_zero_right] using hwnorm.le
            rw [apm_a95J03_divisor_polynomial_eval_apply p hp _ hwclosed]
            rw [← Polynomial.count_roots p,
              Multiset.count_filter_of_pos (p := fun u : ℂ ↦ ‖u‖ < 1)
                (a := w) (s := p.roots) hwnorm]
      _ = ((p.roots.filter fun w : ℂ ↦ ‖w‖ < 1).card : ℤ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast (Multiset.toFinset_sum_count_eq
          (p.roots.filter fun w : ℂ ↦ ‖w‖ < 1))
  · intro w hw
    have hwdiv : MeromorphicOn.divisor (fun u : ℂ ↦ p.eval u)
        (Metric.closedBall 0 1) w ≠ 0 := Function.mem_support.mp hw
    have hwclosed : w ∈ Metric.closedBall (0 : ℂ) 1 := by
      by_contra hn
      exact hwdiv (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hrootmul : p.rootMultiplicity w ≠ 0 := by
      simpa [apm_a95J03_divisor_polynomial_eval_apply p hp _ hwclosed] using hwdiv
    have hwroot : w ∈ p.roots := by
      rw [Polynomial.mem_roots hp, Polynomial.IsRoot]
      exact (Polynomial.rootMultiplicity_pos hp).mp (Nat.pos_of_ne_zero hrootmul)
    have hwnormle : ‖w‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hwclosed
    have hwnorm : ‖w‖ < 1 := lt_of_le_of_ne hwnormle fun heq ↦ by
      have hwsphere : w ∈ Metric.sphere (0 : ℂ) 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using heq
      exact (hne w hwsphere) ((Polynomial.mem_roots hp).mp hwroot)
    simpa [s, Multiset.mem_filter, hwnorm] using hwroot

/-- The argument-principle circle integral for the cleared polynomial, stated
directly using the multiplicity-counted roots in the open unit disk. -/
lemma apm_a95J03_clearedPoly_circleIntegral_eq_roots
    {a : ℤ → ℂ} {N : ℕ} {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    (∮ w in C(0, 1), logDeriv (fun u : ℂ ↦
        (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u) w) =
      (((apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).roots.filter
        fun w : ℂ ↦ ‖w‖ < 1).card : ℂ) * (2 * Real.pi * Complex.I) := by
  let p := apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N
  have hne := apm_a95J03_clearedPoly_ne_on_unitCircle hz
  have hp : p ≠ 0 := by
    intro hp0
    have hone : (1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by simp
    exact hne 1 hone (by simp [p, hp0])
  rw [apm_a95J03_clearedPoly_circleIntegral hz]
  have hsum := apm_a95J03_divisor_finsum_eq_filter_roots_card p hp hne
  dsimp [p] at hsum
  have hpmer : MeromorphicOn (fun u : ℂ ↦
      (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
      (Metric.closedBall 0 1) := by
    exact ((AnalyticOnNhd.eval_polynomial _).mono
      (Set.subset_univ _)).meromorphicOn
  have hsumc : (∑ᶠ w, (MeromorphicOn.divisor (fun u : ℂ ↦
      (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
      (Metric.closedBall 0 1) w : ℂ)) =
      (((apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).roots.filter
        fun w : ℂ ↦ ‖w‖ < 1).card : ℂ) := by
    calc
      (∑ᶠ w, (MeromorphicOn.divisor (fun u : ℂ ↦
          (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
          (Metric.closedBall 0 1) w : ℂ)) =
          (Int.castAddHom ℂ) (∑ᶠ w, MeromorphicOn.divisor (fun u : ℂ ↦
            (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
            (Metric.closedBall 0 1) w) := by
              exact ((Int.castAddHom ℂ).map_finsum
                ((MeromorphicOn.divisor (fun u : ℂ ↦
                  (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
                  (Metric.closedBall 0 1)).finiteSupport
                    (isCompact_closedBall 0 1))).symm
      _ = _ := by rw [hsum]; norm_cast
  rw [hsumc]

/-- Pointwise logarithmic-derivative identity along the unit circle.  Clearing
the `N` negative powers contributes the constant term `N * I`. -/
lemma apm_a95J03_logDeriv_circleMap_eq
    (a : ℤ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ)
    (hz : apm_a95J03_trigPoly a N t ≠ z) :
    deriv (circleMap (0 : ℂ) 1) t *
        logDeriv (fun u : ℂ ↦
          (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
          (circleMap 0 1 t) =
      (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 /
          (apm_a95J03_trigPoly a N t - z) + (N : ℂ) * Complex.I := by
  let w : ℂ := circleMap 0 1 t
  let p := apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N
  have hwexp : w = Complex.exp (Complex.I * (t : ℂ)) := by
    simp only [w, circleMap, ofReal_one, one_mul, zero_add]
    congr 1
    ring
  have hw0 : w ≠ 0 := hwexp.symm ▸ Complex.exp_ne_zero _
  have hpval : p.eval w = w ^ N * (apm_a95J03_trigPoly a N t - z) := by
    dsimp [p]
    rw [apm_a95J03_clearedPoly_eval_eq a N z w hw0]
    congr 2
    rw [hwexp, ← apm_a95J03_trigPoly_eq_laurent]
  have hp0 : p.eval w ≠ 0 := hpval.symm ▸ mul_ne_zero (pow_ne_zero _ hw0) (sub_ne_zero.mpr hz)
  have hcircle := hasDerivAt_circleMap (0 : ℂ) 1 t
  have hpoly := (Polynomial.hasDerivAt p w).comp t hcircle
  have htrig := apm_a95J03_trigPoly_hasDerivAt a N t
  have hprod := (hcircle.pow N).mul (htrig.sub_const z)
  have hfun : (fun u : ℝ ↦ p.eval (circleMap 0 1 u)) =
      fun u : ℝ ↦ (circleMap 0 1 u) ^ N * (apm_a95J03_trigPoly a N u - z) := by
    funext u
    have hu0 : circleMap (0 : ℂ) 1 u ≠ 0 := by
      simp [circleMap]
    dsimp [p]
    rw [apm_a95J03_clearedPoly_eval_eq a N z _ hu0]
    congr 2
    have huexp : circleMap (0 : ℂ) 1 u = Complex.exp (Complex.I * (u : ℂ)) := by
      simp only [circleMap, ofReal_one, one_mul, zero_add]
      congr 1
      ring
    rw [huexp, ← apm_a95J03_trigPoly_eq_laurent]
  have hder :
      p.derivative.eval w * (circleMap 0 1 t * Complex.I) =
        (N : ℂ) * circleMap 0 1 t ^ (N - 1) * (circleMap 0 1 t * Complex.I) *
            (apm_a95J03_trigPoly a N t - z) +
          circleMap 0 1 t ^ N *
            ((Finset.Icc (-(N : ℤ)) N).sum fun n ↦
              a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
                (Complex.I * (n : ℂ)))) := by
    calc
      _ = deriv ((fun x ↦ p.eval x) ∘ circleMap 0 1) t := hpoly.deriv.symm
      _ = deriv (fun u ↦ circleMap 0 1 u ^ N *
          (apm_a95J03_trigPoly a N u - z)) t :=
        congrArg (fun f : ℝ → ℂ ↦ deriv f t) hfun
      _ = _ := by simpa only [Pi.pow_apply] using hprod.deriv
  rw [logDeriv_apply, hcircle.deriv]
  dsimp [p, w] at hpval hp0 hder ⊢
  rw [(Polynomial.hasDerivAt _ _).deriv,
    apm_a95J03_fderiv_apply_one]
  rw [hpval]
  cases N with
  | zero =>
      simp at hder ⊢
      exact Or.inl hder
  | succ N =>
      simp only [Nat.cast_succ, Nat.succ_sub_one, pow_succ] at hder ⊢
      have hd0 : apm_a95J03_trigPoly a (N + 1) t - z ≠ 0 := sub_ne_zero.mpr hz
      have hder' := congrArg (fun x : ℂ ↦ x / circleMap 0 1 t) hder
      field_simp [hw0] at hder'
      field_simp [hd0]
      ring_nf at hder' ⊢
      rw [hder']
      ring_nf

/-- Why this unblocks `apm_a95j03`: this is the exact argument-principle
conversion for the cleared Laurent polynomial.  It includes the contribution
`-N` from the cleared monomial factor and expresses the remaining divisor mass
as the number of polynomial roots in the open unit disk. -/
theorem apm_a95J03_bridge_1
    {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    apm_a95J03_windingIntegral (apm_a95J03_trigPoly a N) z =
      (((((apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).roots
        ).filter (fun w : ℂ ↦ ‖w‖ < 1)).card : ℤ) - (N : ℤ) : ℂ) := by
  let q : ℝ → ℂ := fun t ↦
    (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 /
      (apm_a95J03_trigPoly a N t - z)
  have hqcont : ContinuousOn q (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    have hnum : Continuous (fun t : ℝ ↦
        (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1) := by
      rw [show (fun t : ℝ ↦ (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1) =
          fun t : ℝ ↦ (Finset.Icc (-(N : ℤ)) N).sum (fun n ↦
            a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
              (Complex.I * (n : ℂ)))) by
        funext t
        exact apm_a95J03_fderiv_apply_one a N t]
      fun_prop
    have htrig : Continuous (apm_a95J03_trigPoly a N) := by
      unfold apm_a95J03_trigPoly
      fun_prop
    exact hnum.continuousOn.div (htrig.sub continuous_const).continuousOn
      (fun t ht ↦ sub_ne_zero.mpr (hz t ht))
  have hqint : IntervalIntegrable q MeasureTheory.volume 0 (2 * Real.pi) :=
    (show ContinuousOn q (Set.uIcc (0 : ℝ) (2 * Real.pi)) by
      simpa [Set.uIcc_of_le Real.two_pi_pos.le] using hqcont).intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (N : ℂ) * Complex.I)
      MeasureTheory.volume 0 (2 * Real.pi) := intervalIntegrable_const
  have hinter :
      (∮ w in C(0, 1), logDeriv (fun u : ℂ ↦
        (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u) w) =
        (∫ t in (0 : ℝ)..2 * Real.pi, q t) +
          (2 * Real.pi : ℝ) • ((N : ℂ) * Complex.I) := by
    rw [circleIntegral]
    calc
      (∫ θ : ℝ in 0..2 * Real.pi,
          deriv (circleMap 0 1) θ • logDeriv (fun u : ℂ ↦
            (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval u)
            (circleMap 0 1 θ)) =
          ∫ t : ℝ in 0..2 * Real.pi, q t + (N : ℂ) * Complex.I := by
            apply intervalIntegral.integral_congr
            intro t ht
            simpa [q, smul_eq_mul] using
              apm_a95J03_logDeriv_circleMap_eq a N z t
                (hz t (by simpa [Set.uIcc_of_le Real.two_pi_pos.le] using ht))
      _ = (∫ t in (0 : ℝ)..2 * Real.pi, q t) +
          ∫ _t in (0 : ℝ)..2 * Real.pi, (N : ℂ) * Complex.I :=
        intervalIntegral.integral_add hqint hconst
      _ = _ := by rw [intervalIntegral.integral_const, sub_zero]; rfl
  have hroot := apm_a95J03_clearedPoly_circleIntegral_eq_roots hz
  rw [hinter] at hroot
  unfold apm_a95J03_windingIntegral
  dsimp [q] at hroot ⊢
  have hpi : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast mul_ne_zero (by norm_num) Real.pi_ne_zero
    · exact Complex.I_ne_zero
  field_simp
  push_cast at hroot ⊢
  linear_combination hroot

/-- Why this unblocks `apm_a95j03`: the root multiplicity inside the disk is
bounded by the total root multiplicity, hence by the already compiled
`natDegree ≤ 2N` estimate for the cleared polynomial. -/
theorem apm_a95J03_bridge_2
    (a : ℤ → ℂ) (N : ℕ) (z : ℂ) :
    (((apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).roots
      ).filter (fun w : ℂ ↦ ‖w‖ < 1)).card ≤ 2 * N := by
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans
    ((Polynomial.card_roots' _).trans (apm_a95J03_algPoly_sub_degree_le a N z))

theorem apm_a95j03 {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    ∃ k : ℤ,
      apm_a95J03_windingIntegral (apm_a95J03_trigPoly a N) z = (k : ℂ) ∧
      -(N : ℤ) ≤ k ∧ k ≤ N := by
  /-
  CLOSER HOP 3 boundary. The finite-sum reindexing left by hop 2 is now
  compiled. `apm_a95J03_algPoly_eval_eq_mul_laurent` gives the exact identity
  obtained by multiplying the Laurent sum by `w^N`; its proof constructs the
  bijection `k ↦ k-N` between `range (2N+1)` and `Icc (-N) N` and handles
  integer powers at nonzero `w`. `apm_a95J03_clearedPoly_eval_eq` incorporates
  the target value `z`, so zeros of the cleared polynomial on the unit circle
  now correspond directly to forbidden curve hits.

  Further consultation of `LEMMA-INDEX.md`, `ConstructionTargets.CircleParam`,
  `ConstructionTargets.Rouche`, Mathlib's `circleIntegral`, polynomial root
  multiplicity/divisor APIs, sibling artifacts, and git history found no
  compiled logarithmic-derivative rule converting the frozen real interval
  integral of the Laurent curve into the cleared polynomial's contour
  integral. The remaining bridge is that analytic conversion and the ensuing
  divisor-mass bound by `natDegree ≤ 2N`. The frozen statement is unchanged.
  -/
  let k : ℤ :=
    (((apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).roots
      ).filter (fun w : ℂ ↦ ‖w‖ < 1)).card - (N : ℤ)
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa [k, Int.cast_sub] using apm_a95J03_bridge_1 hN hz
  · dsimp [k]
    omega
  · dsimp [k]
    have hcard := apm_a95J03_bridge_2 a N z
    omega
