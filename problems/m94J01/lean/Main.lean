import Mathlib

/-!
# APM m94J01

## Statement repairs

None.

## Encoding questions

Convergence in `𝓓′` and `𝓢′` is encoded in its defining weak form: convergence
after evaluation on every compactly supported smooth test function or Schwartz
function, respectively. The moving delta derivative is evaluated by the
problem's formula `(-1)^n f⁽ⁿ⁾(n)`.
-/

open Filter Set
open scoped Distributions SchwartzMap ContDiff

private noncomputable def apm_m94J01_plateauBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def apm_m94J01_localSummand (n : ℕ) (x : ℝ) : ℝ :=
  ((x - n) ^ n / n.factorial) * apm_m94J01_plateauBump (x - n)

/-- Each translated summand vanishes outside the radius-`1/2` neighborhood
of its integer center. -/
private lemma apm_m94J01_localSummand_eq_zero_of_half_le
    (n : ℕ) (x : ℝ) (hx : (1 / 2 : ℝ) ≤ |x - n|) :
    apm_m94J01_localSummand n x = 0 := by
  rw [apm_m94J01_localSummand,
    apm_m94J01_plateauBump.zero_of_le_dist]
  · simp
  · simpa [apm_m94J01_plateauBump, Real.dist_eq] using hx

/-- Zeroth-order quantitative decay of the translated summands. -/
private lemma apm_m94J01_localSummand_abs_le (n : ℕ) (x : ℝ) :
    |apm_m94J01_localSummand n x| ≤
      (1 / 2 : ℝ) ^ n / n.factorial := by
  by_cases hx : (1 / 2 : ℝ) ≤ |x - n|
  · rw [apm_m94J01_localSummand_eq_zero_of_half_le n x hx, abs_zero]
    positivity
  · have hpow : |x - n| ^ n ≤ (1 / 2 : ℝ) ^ n := by
      exact pow_le_pow_left₀ (abs_nonneg _) (le_of_not_ge hx) n
    have hb0 : 0 ≤ apm_m94J01_plateauBump (x - n) :=
      apm_m94J01_plateauBump.nonneg
    have hb1 : apm_m94J01_plateauBump (x - n) ≤ 1 :=
      apm_m94J01_plateauBump.le_one
    have hfac : (0 : ℝ) < n.factorial := by positivity
    rw [apm_m94J01_localSummand, abs_mul, abs_div, abs_pow,
      abs_of_nonneg hb0]
    rw [abs_of_nonneg hfac.le]
    calc
      |x - ↑n| ^ n / ↑n.factorial * apm_m94J01_plateauBump (x - ↑n) ≤
          ((1 / 2 : ℝ) ^ n / ↑n.factorial) * 1 := by
            gcongr
      _ = (1 / 2 : ℝ) ^ n / n.factorial := by ring

/-- The local summands are absolutely summable at every point. -/
private lemma apm_m94J01_localSummand_summable (x : ℝ) :
    Summable (fun n : ℕ ↦ (apm_m94J01_localSummand n x : ℂ)) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (1 / 2))
  intro n
  simpa using apm_m94J01_localSummand_abs_le n x

private noncomputable def apm_m94J01_globalFunction (x : ℝ) : ℂ :=
  ∑ᶠ n : ℕ, (apm_m94J01_localSummand n x : ℂ)

/-- The summed function is nontrivial; this also verifies the summation at a
concrete point. -/
private lemma apm_m94J01_globalFunction_zero :
    apm_m94J01_globalFunction 0 = 1 := by
  rw [apm_m94J01_globalFunction, finsum_eq_single _ 0]
  · simp only [apm_m94J01_localSummand, Nat.cast_zero, sub_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, one_mul, Complex.ofReal_eq_one]
    exact_mod_cast apm_m94J01_plateauBump.one_of_mem_closedBall (by
      dsimp [apm_m94J01_plateauBump]
      norm_num)
  · intro n hn
    norm_cast
    apply apm_m94J01_localSummand_eq_zero_of_half_le
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [zero_sub, abs_neg, abs_of_nonneg hnnonneg]
    linarith

private lemma apm_m94J01_natCenter_separated {m n : ℕ} (h : m ≠ n) :
    (1 : ℝ) ≤ |(n : ℝ) - m| := by
  rcases lt_or_gt_of_ne h with hmn | hnm
  · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    rw [abs_of_nonneg]
    · linarith
    · linarith
  · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
    rw [abs_of_nonpos]
    · linarith
    · linarith

/-- At every natural center the global sum has exactly its matching summand. -/
private lemma apm_m94J01_globalFunction_nat (n : ℕ) :
    apm_m94J01_globalFunction n = apm_m94J01_localSummand n n := by
  rw [apm_m94J01_globalFunction, finsum_eq_single _ n]
  intro m hmn
  norm_cast
  apply apm_m94J01_localSummand_eq_zero_of_half_le
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
    (apm_m94J01_natCenter_separated hmn)

/-- Near a natural center, every other translated bump vanishes. -/
private lemma apm_m94J01_globalFunction_eventuallyEq (n : ℕ) :
    apm_m94J01_globalFunction =ᶠ[nhds (n : ℝ)]
      (fun x ↦ (apm_m94J01_localSummand n x : ℂ)) := by
  have hnhds : Ioo ((n : ℝ) - 1 / 4) ((n : ℝ) + 1 / 4) ∈ nhds (n : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hnhds] with x hx
  rw [apm_m94J01_globalFunction, finsum_eq_single _ n]
  intro m hmn
  norm_cast
  apply apm_m94J01_localSummand_eq_zero_of_half_le
  have hnear : |x - (n : ℝ)| < 1 / 4 := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hsep := apm_m94J01_natCenter_separated hmn
  have htri : |(n : ℝ) - m| ≤ |(n : ℝ) - x| + |x - m| := by
    calc
      |(n : ℝ) - m| = |((n : ℝ) - x) + (x - m)| := by congr 1 <;> ring
      _ ≤ |(n : ℝ) - x| + |x - m| := abs_add_le _ _
  rw [abs_sub_comm (n : ℝ) x] at htri
  linarith

private lemma apm_m94J01_normalizedMonomial_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ (x - n) ^ n / n.factorial) (n : ℝ) = 1 := by
  rw [iteratedDeriv_div_const]
  change iteratedDeriv n (fun x : ℝ ↦ (fun z : ℝ ↦ z ^ n) (x - n)) (n : ℝ) /
      n.factorial = 1
  rw [congrFun (iteratedDeriv_comp_sub_const n (fun z : ℝ ↦ z ^ n) n) n]
  rw [iteratedDeriv_pow]
  simp [Nat.descFactorial_self, Nat.factorial_ne_zero]

private lemma apm_m94J01_localSummand_eventuallyEq (n : ℕ) :
    apm_m94J01_localSummand n =ᶠ[nhds (n : ℝ)]
      (fun x : ℝ ↦ (x - n) ^ n / n.factorial) := by
  have hshift : Tendsto (fun x : ℝ ↦ x - n) (nhds (n : ℝ)) (nhds 0) := by
    simpa using (continuousAt_id.sub
      (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (n : ℝ)) (n : ℝ))).tendsto
  have hb := apm_m94J01_plateauBump.eventuallyEq_one.comp_tendsto hshift
  filter_upwards [hb] with x hx
  change apm_m94J01_plateauBump (x - n) = 1 at hx
  rw [apm_m94J01_localSummand, hx, mul_one]

/-- Real-to-complex inclusion commutes with every scalar iterated derivative. -/
private lemma apm_m94J01_iteratedDeriv_ofReal
    (f : ℝ → ℝ) (n : ℕ) (hf : ContDiff ℝ n f) :
    iteratedDeriv n (fun x : ℝ ↦ (f x : ℂ)) =
      fun x : ℝ ↦ ((iteratedDeriv (F := ℝ) n f x : ℝ) : ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih f hfn]
      funext x
      exact ((hf.differentiable_iteratedDeriv n (by
        exact WithTop.coe_lt_coe.mpr
          (ENat.coe_lt_coe.mpr n.lt_succ_self))).differentiableAt.hasDerivAt
        |>.ofReal_comp).deriv

private lemma apm_m94J01_localSummand_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (apm_m94J01_localSummand n) (n : ℝ) = 1 := by
  rw [(apm_m94J01_localSummand_eventuallyEq n).iteratedDeriv_eq n]
  exact apm_m94J01_normalizedMonomial_iteratedDeriv n

/-- The global complex-valued sum has the prescribed diagonal jet at every
natural center. -/
private lemma apm_m94J01_globalFunction_iteratedDeriv (n : ℕ) :
    iteratedDeriv n apm_m94J01_globalFunction (n : ℝ) = 1 := by
  rw [(apm_m94J01_globalFunction_eventuallyEq n).iteratedDeriv_eq n]
  have hs : ContDiff ℝ n (apm_m94J01_localSummand n) := by
    unfold apm_m94J01_localSummand
    apply ContDiff.mul
    · fun_prop
    · exact (apm_m94J01_plateauBump.contDiff (n := n)).comp
        ((contDiff_id : ContDiff ℝ n (fun x : ℝ ↦ x)).sub
          (contDiff_const : ContDiff ℝ n (fun _ : ℝ ↦ (n : ℝ))))
  rw [congrFun (apm_m94J01_iteratedDeriv_ofReal
    (apm_m94J01_localSummand n) n hs) n]
  norm_cast
  exact apm_m94J01_localSummand_iteratedDeriv n

/-- Every individual complexified summand has compact support. -/
private lemma apm_m94J01_localSummand_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fun x : ℝ ↦ (apm_m94J01_localSummand n x : ℂ)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (n : ℝ) (1 / 2))
  intro x hx
  norm_cast
  apply apm_m94J01_localSummand_eq_zero_of_half_le
  have : (1 / 2 : ℝ) < dist x (n : ℝ) := by
    simpa [Metric.mem_closedBall] using hx
  simpa [Real.dist_eq] using this.le

/-- Each local jet carrier is a Schwartz function before the carriers are
summed. -/
private lemma apm_m94J01_exists_localSchwartz (n : ℕ) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ x : ℝ,
      f x = (apm_m94J01_localSummand n x : ℂ) := by
  have hsmooth : ContDiff ℝ ∞
      (fun x : ℝ ↦ (apm_m94J01_localSummand n x : ℂ)) := by
    have hr : ContDiff ℝ ∞ (apm_m94J01_localSummand n) := by
      unfold apm_m94J01_localSummand
      apply ContDiff.mul
      · fun_prop
      · exact (apm_m94J01_plateauBump.contDiff (n := (⊤ : ℕ∞))).comp
          ((contDiff_id : ContDiff ℝ ∞ (fun x : ℝ ↦ x)).sub
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (n : ℝ))))
    exact Complex.ofRealCLM.contDiff.comp hr
  let f : 𝓢(ℝ, ℂ) :=
    (apm_m94J01_localSummand_hasCompactSupport n).toSchwartzMap hsmooth
  exact ⟨f, fun x => rfl⟩

/-- Every derivative order of the fixed plateau bump has a global bound;
the bound is independent of all later translations. -/
private lemma apm_m94J01_exists_bump_deriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ j apm_m94J01_plateauBump x‖ ≤ C := by
  let g : ℝ → ℝ := fun x =>
    ‖iteratedFDeriv ℝ j apm_m94J01_plateauBump x‖
  have hgcont : Continuous g := by
    dsimp [g]
    exact ((apm_m94J01_plateauBump.contDiff (n := (⊤ : ℕ∞))).of_le
      (mod_cast le_top)).continuous_iteratedFDeriv'.norm
  have hgcomp : HasCompactSupport g :=
    (apm_m94J01_plateauBump.hasCompactSupport.iteratedFDeriv j).norm
  obtain ⟨x₀, hx₀⟩ := hgcont.exists_forall_ge_of_hasCompactSupport hgcomp
  exact ⟨max (g x₀) 0, le_max_right _ _, fun x =>
    (hx₀ x).trans (le_max_left _ _)⟩

/-- The same derivative bound applies uniformly to every translated bump. -/
private lemma apm_m94J01_exists_translated_bump_deriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ),
      ‖iteratedFDeriv ℝ j
        (fun z : ℝ => apm_m94J01_plateauBump (z - n)) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := apm_m94J01_exists_bump_deriv_bound j
  refine ⟨C, hC0, fun n x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    congrFun (iteratedDeriv_comp_sub_const j apm_m94J01_plateauBump n) x,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hC (x - n)

/-- Exact derivative formula for the factorially normalized translated
monomial occurring in every local carrier. -/
private lemma apm_m94J01_normalizedMonomial_iteratedDeriv_formula
    (n i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun z : ℝ ↦ (z - n) ^ n / n.factorial) x =
      (n.descFactorial i : ℝ) * (x - n) ^ (n - i) / n.factorial := by
  rw [iteratedDeriv_div_const]
  change iteratedDeriv i (fun z : ℝ ↦ (fun w : ℝ ↦ w ^ n) (z - n)) x /
      n.factorial = _
  rw [congrFun (iteratedDeriv_comp_sub_const i (fun w : ℝ ↦ w ^ n) n) x,
    iteratedDeriv_pow]

/-- On the bump support, each normalized monomial derivative retains
factorial decay. -/
private lemma apm_m94J01_normalizedMonomial_iteratedDeriv_abs_le
    {n i : ℕ} (hi : i ≤ n) {x : ℝ} (hx : |x - n| ≤ (1 / 2 : ℝ)) :
    |iteratedDeriv i (fun z : ℝ ↦ (z - n) ^ n / n.factorial) x| ≤
      (1 / 2 : ℝ) ^ (n - i) / (n - i).factorial := by
  rw [apm_m94J01_normalizedMonomial_iteratedDeriv_formula,
    abs_div, abs_mul, abs_pow]
  have hdesc : 0 ≤ (n.descFactorial i : ℝ) := by positivity
  have hnfac : 0 < (n.factorial : ℝ) := by positivity
  have hmfac : 0 < ((n - i).factorial : ℝ) := by positivity
  rw [abs_of_nonneg hdesc, abs_of_pos hnfac]
  have hp := pow_le_pow_left₀ (abs_nonneg (x - n)) hx (n - i)
  have hfac : ((n - i).factorial : ℝ) * n.descFactorial i = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hi
  calc
    (n.descFactorial i : ℝ) * |x - ↑n| ^ (n - i) / ↑n.factorial ≤
        (n.descFactorial i : ℝ) * (1 / 2 : ℝ) ^ (n - i) / ↑n.factorial := by
          gcongr
    _ = (1 / 2 : ℝ) ^ (n - i) / ↑(n - i).factorial := by
      field_simp
      nlinarith

private lemma apm_m94J01_normalizedMonomial_iteratedDeriv_abs_le_all
    (n i : ℕ) {x : ℝ} (hx : |x - n| ≤ (1 / 2 : ℝ)) :
    |iteratedDeriv i (fun z : ℝ ↦ (z - n) ^ n / n.factorial) x| ≤
      (1 / 2 : ℝ) ^ (n - i) / (n - i).factorial := by
  by_cases hi : i ≤ n
  · exact apm_m94J01_normalizedMonomial_iteratedDeriv_abs_le hi hx
  · rw [apm_m94J01_normalizedMonomial_iteratedDeriv_formula,
      Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hi)]
    simp only [Nat.cast_zero, zero_mul, zero_div, abs_zero]
    positivity

/-- Strictly outside its support, every scalar derivative of a local summand
vanishes. -/
private lemma apm_m94J01_localSummand_iteratedDeriv_eq_zero_of_half_lt
    (n j : ℕ) {x : ℝ} (hx : (1 / 2 : ℝ) < |x - n|) :
    iteratedDeriv j (apm_m94J01_localSummand n) x = 0 := by
  have hopen : {z : ℝ | (1 / 2 : ℝ) < |z - n|} ∈ nhds x := by
    apply IsOpen.mem_nhds
    · exact isOpen_Ioi.preimage
        (continuous_abs.comp (continuous_id.sub continuous_const))
    · exact hx
  have heq : apm_m94J01_localSummand n =ᶠ[nhds x] (fun _ => 0) := by
    filter_upwards [hopen] with z hz
    exact apm_m94J01_localSummand_eq_zero_of_half_le n z hz.le
  rw [heq.iteratedDeriv_eq j]
  simp

/-- A finite Leibniz majorant for every derivative of every local carrier. -/
private lemma apm_m94J01_exists_localSummand_deriv_majorant (j : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (n : ℕ) (x : ℝ),
        |iteratedDeriv j (apm_m94J01_localSummand n) x| ≤
          ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) *
              ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i) := by
  choose C hC0 hC using fun q => apm_m94J01_exists_translated_bump_deriv_bound q
  refine ⟨C, hC0, fun n x => ?_⟩
  by_cases hx : |x - n| ≤ (1 / 2 : ℝ)
  · let p : ℝ → ℝ := fun z => (z - n) ^ n / n.factorial
    let b : ℝ → ℝ := fun z => apm_m94J01_plateauBump (z - n)
    have hp : ContDiffAt ℝ j p x := by
      dsimp [p]
      fun_prop
    have hb : ContDiffAt ℝ j b x := by
      dsimp [b]
      exact ((apm_m94J01_plateauBump.contDiff (n := j)).comp
        ((contDiff_id : ContDiff ℝ j (fun z : ℝ => z)).sub
          (contDiff_const : ContDiff ℝ j (fun _ : ℝ => (n : ℝ))))).contDiffAt
    change |iteratedDeriv j (p * b) x| ≤ _
    rw [iteratedDeriv_mul hp hb]
    calc
      |∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * iteratedDeriv i p x * iteratedDeriv (j - i) b x| ≤
          ∑ i ∈ Finset.range (j + 1),
            |(j.choose i : ℝ) * iteratedDeriv i p x *
              iteratedDeriv (j - i) b x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) *
              ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.choose i)]
          have hpbound := apm_m94J01_normalizedMonomial_iteratedDeriv_abs_le_all
            n i hx
          have hbbound : |iteratedDeriv (j - i) b x| ≤ C (j - i) := by
            rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
            exact hC (j - i) n x
          gcongr
  · have hz := apm_m94J01_localSummand_iteratedDeriv_eq_zero_of_half_lt
      n j (lt_of_not_ge hx)
    rw [hz, abs_zero]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by positivity) (by positivity)))
      (hC0 (j - i))

/-- On the support of the carrier centered at `n`, the polynomial weight is
controlled solely in terms of `n`. -/
private lemma apm_m94J01_abs_le_center_succ
    (n : ℕ) {x : ℝ} (hx : |x - n| ≤ (1 / 2 : ℝ)) :
    |x| ≤ (n + 1 : ℕ) := by
  have htri : |x| ≤ |x - n| + |(n : ℝ)| := by
    have := abs_add_le (x - n) (n : ℝ)
    simpa using this
  calc
    |x| ≤ |x - n| + |(n : ℝ)| := htri
    _ ≤ (1 / 2 : ℝ) + n := by
      have hnabs : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
      rw [hnabs]
      gcongr
    _ ≤ (n + 1 : ℕ) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith

/-- The finite Leibniz majorant remains valid after inserting any fixed
polynomial weight. -/
private lemma apm_m94J01_exists_localSummand_weighted_deriv_majorant
    (k j : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (n : ℕ) (x : ℝ),
        |x| ^ k * |iteratedDeriv j (apm_m94J01_localSummand n) x| ≤
          (n + 1 : ℝ) ^ k *
            (∑ i ∈ Finset.range (j + 1),
              (j.choose i : ℝ) *
                ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i)) := by
  obtain ⟨C, hC0, hC⟩ := apm_m94J01_exists_localSummand_deriv_majorant j
  refine ⟨C, hC0, fun n x => ?_⟩
  by_cases hx : |x - n| ≤ (1 / 2 : ℝ)
  · have hx' : |x| ^ k ≤ (n + 1 : ℝ) ^ k := by
      exact pow_le_pow_left₀ (abs_nonneg x)
        (by exact_mod_cast apm_m94J01_abs_le_center_succ n hx) k
    have hsum : 0 ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) *
          ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by positivity) (by positivity)))
        (hC0 (j - i))
    exact mul_le_mul hx' (hC n x) (abs_nonneg _) (by positivity)
  · rw [apm_m94J01_localSummand_iteratedDeriv_eq_zero_of_half_lt
      n j (lt_of_not_ge hx), abs_zero, mul_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi =>
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by positivity) (by positivity)))
        (hC0 (j - i)))

/-- Shifting the factorial index only changes finitely many initial terms, so
the scalar sequence occurring in every Leibniz summand is summable. -/
private lemma apm_m94J01_summable_shifted_factorial (i : ℕ) :
    Summable (fun n : ℕ ↦
      (1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) := by
  apply (summable_nat_add_iff i).mp
  simpa [Nat.add_sub_cancel_left] using
    (Real.summable_pow_div_factorial (1 / 2))

private lemma apm_m94J01_summable_pow_shifted_factorial (c : ℝ) (i : ℕ) :
    Summable (fun n : ℕ ↦ c ^ n / (n - i).factorial) := by
  apply (summable_nat_add_iff i).mp
  simpa [pow_add, Nat.add_sub_cancel_left, mul_div_assoc, mul_comm] using
    (Real.summable_pow_div_factorial c).mul_left (c ^ i)

/-- For every derivative order, the global derivative series has a summable
uniform scalar majorant. -/
private lemma apm_m94J01_exists_summable_localSummand_deriv_majorant (j : ℕ) :
    ∃ v : ℕ → ℝ, Summable v ∧ ∀ n x,
      |iteratedDeriv j (apm_m94J01_localSummand n) x| ≤ v n := by
  obtain ⟨C, hC0, hC⟩ := apm_m94J01_exists_localSummand_deriv_majorant j
  let v : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) *
      ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i)
  refine ⟨v, ?_, hC⟩
  dsimp [v]
  exact summable_sum (fun i hi =>
    ((apm_m94J01_summable_shifted_factorial i).mul_left
      (j.choose i : ℝ)).mul_right (C (j - i)))

/-- The pointwise `tsum` of the complexified carriers is smooth. -/
private lemma apm_m94J01_contDiff_tsum_localSummand :
    ContDiff ℝ ∞ (fun x : ℝ =>
      ∑' n : ℕ, (apm_m94J01_localSummand n x : ℂ)) := by
  choose v hv hbound using fun j =>
    apm_m94J01_exists_summable_localSummand_deriv_majorant j
  apply contDiff_tsum
  · intro n
    have hr : ContDiff ℝ ∞ (apm_m94J01_localSummand n) := by
      unfold apm_m94J01_localSummand
      apply ContDiff.mul
      · fun_prop
      · exact (apm_m94J01_plateauBump.contDiff (n := (⊤ : ℕ∞))).comp
          ((contDiff_id : ContDiff ℝ ∞ (fun x : ℝ ↦ x)).sub
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (n : ℝ))))
    exact Complex.ofRealCLM.contDiff.comp hr
  · intro j hj
    exact hv j
  · intro j n x hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hs : ContDiff ℝ j (apm_m94J01_localSummand n) := by
      unfold apm_m94J01_localSummand
      apply ContDiff.mul
      · fun_prop
      · exact (apm_m94J01_plateauBump.contDiff (n := j)).comp
          ((contDiff_id : ContDiff ℝ j (fun x : ℝ ↦ x)).sub
            (contDiff_const : ContDiff ℝ j (fun _ : ℝ ↦ (n : ℝ))))
    rw [congrFun (apm_m94J01_iteratedDeriv_ofReal
      (apm_m94J01_localSummand n) j hs) x, Complex.norm_real]
    exact hbound j n x

private lemma apm_m94J01_nat_succ_le_two_pow (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Polynomially weighted shifted factorial decay is uniformly bounded. -/
private lemma apm_m94J01_exists_bound_weighted_shifted_factorial
    (k i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      (n + 1 : ℝ) ^ k *
          ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) ≤ B := by
  let f : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ k *
    ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial)
  let g : ℕ → ℝ := fun n => ((2 : ℝ) ^ k) ^ n / (n - i).factorial
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    have hn : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast apm_m94J01_nat_succ_le_two_pow n
    have hpow : (n + 1 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ n := by
      calc
        (n + 1 : ℝ) ^ k ≤ ((2 : ℝ) ^ n) ^ k :=
          pow_le_pow_left₀ (by positivity) hn k
        _ = ((2 : ℝ) ^ k) ^ n := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
    dsimp [f, g]
    have hhalf : (1 / 2 : ℝ) ^ (n - i) ≤ 1 := by
      exact pow_le_one₀ (by positivity) (by norm_num)
    have hfac : (0 : ℝ) < (n - i).factorial := by positivity
    calc
      (n + 1 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial)
          ≤ ((2 : ℝ) ^ k) ^ n * (1 / (n - i).factorial) := by
            gcongr
      _ = ((2 : ℝ) ^ k) ^ n / (n - i).factorial := by ring
  have hg : Tendsto g atTop (nhds 0) := by
    simpa [g] using
      (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop
        (1 : ℝ) ((2 : ℝ) ^ k) i)
  have hf : Tendsto f atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      dsimp [f]
      positivity
    · exact Filter.Eventually.of_forall hfg
    · exact hg
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto f hf).exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun n => ?_⟩
  have := hB (f n) ⟨n, rfl⟩
  exact le_trans (le_abs_self (f n)) (le_trans (by simpa [Real.norm_eq_abs] using this)
    (le_max_left _ _))

private lemma apm_m94J01_summable_weighted_shifted_factorial (k i : ℕ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ k *
      ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hn : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast apm_m94J01_nat_succ_le_two_pow n
    have hpow : (n + 1 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ n := by
      calc
        (n + 1 : ℝ) ^ k ≤ ((2 : ℝ) ^ n) ^ k :=
          pow_le_pow_left₀ (by positivity) hn k
        _ = ((2 : ℝ) ^ k) ^ n := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
    have hhalf : (1 / 2 : ℝ) ^ (n - i) ≤ 1 :=
      pow_le_one₀ (by positivity) (by norm_num)
    calc
      (n + 1 : ℝ) ^ k *
          ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial)
          ≤ ((2 : ℝ) ^ k) ^ n * (1 / (n - i).factorial) := by
            gcongr
      _ = ((2 : ℝ) ^ k) ^ n / (n - i).factorial := by ring
  · exact apm_m94J01_summable_pow_shifted_factorial ((2 : ℝ) ^ k) i

/-- Every weighted scalar derivative of every carrier has one bound which
is independent of the center and the evaluation point. -/
private lemma apm_m94J01_exists_uniform_weighted_localSummand_bound
    (k j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x,
      |x| ^ k * |iteratedDeriv j (apm_m94J01_localSummand n) x| ≤ B := by
  obtain ⟨C, hC0, hmajor⟩ :=
    apm_m94J01_exists_localSummand_weighted_deriv_majorant k j
  choose B hB0 hB using fun i =>
    apm_m94J01_exists_bound_weighted_shifted_factorial k i
  let M : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * C (j - i) * B i
  refine ⟨M, ?_, fun n x => ?_⟩
  · dsimp [M]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 (j - i))) (hB0 i)
  · refine (hmajor n x).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := hB i n
    have hc : 0 ≤ (j.choose i : ℝ) * C (j - i) :=
      mul_nonneg (Nat.cast_nonneg _) (hC0 (j - i))
    calc
      (n + 1 : ℝ) ^ k *
          ((j.choose i : ℝ) *
            ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i))
          = ((j.choose i : ℝ) * C (j - i)) *
            ((n + 1 : ℝ) ^ k *
              ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial)) := by ring
      _ ≤ ((j.choose i : ℝ) * C (j - i)) * B i :=
        mul_le_mul_of_nonneg_left hb hc
      _ = (j.choose i : ℝ) * C (j - i) * B i := by ring

private lemma apm_m94J01_exists_summable_weighted_deriv_majorant (k j : ℕ) :
    ∃ v : ℕ → ℝ, Summable v ∧ ∀ n x,
      |x| ^ k * |iteratedDeriv j (apm_m94J01_localSummand n) x| ≤ v n := by
  obtain ⟨C, hC0, hmajor⟩ :=
    apm_m94J01_exists_localSummand_weighted_deriv_majorant k j
  let v : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ k *
    (∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
        ((1 / 2 : ℝ) ^ (n - i) / (n - i).factorial) * C (j - i))
  refine ⟨v, ?_, hmajor⟩
  dsimp [v]
  simp_rw [Finset.mul_sum]
  exact summable_sum (fun i hi => by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((apm_m94J01_summable_weighted_shifted_factorial k i).mul_left
        (j.choose i : ℝ)).mul_right (C (j - i)))

private lemma apm_m94J01_tsum_decay (k j : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ j
        (fun y : ℝ => ∑' n : ℕ, (apm_m94J01_localSummand n y : ℂ)) x‖ ≤ B := by
  let f : ℕ → ℝ → ℂ := fun n x => (apm_m94J01_localSummand n x : ℂ)
  have hf : ∀ n, ContDiff ℝ ∞ (f n) := by
    intro n
    have hr : ContDiff ℝ ∞ (apm_m94J01_localSummand n) := by
      unfold apm_m94J01_localSummand
      apply ContDiff.mul
      · fun_prop
      · exact (apm_m94J01_plateauBump.contDiff (n := (⊤ : ℕ∞))).comp
          ((contDiff_id : ContDiff ℝ ∞ (fun x : ℝ ↦ x)).sub
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (n : ℝ))))
    exact Complex.ofRealCLM.contDiff.comp hr
  choose v hv hbound using fun q =>
    apm_m94J01_exists_summable_localSummand_deriv_majorant q
  obtain ⟨w, hw, hwbound⟩ :=
    apm_m94J01_exists_summable_weighted_deriv_majorant k j
  refine ⟨∑' n, w n, fun x => ?_⟩
  have hlocal : ∀ q n x, ‖iteratedFDeriv ℝ q (f n) x‖ ≤ v q n := by
    intro q n y
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hs : ContDiff ℝ q (apm_m94J01_localSummand n) := by
      unfold apm_m94J01_localSummand
      apply ContDiff.mul
      · fun_prop
      · exact (apm_m94J01_plateauBump.contDiff (n := q)).comp
          ((contDiff_id : ContDiff ℝ q (fun x : ℝ ↦ x)).sub
            (contDiff_const : ContDiff ℝ q (fun _ : ℝ ↦ (n : ℝ))))
    rw [congrFun (apm_m94J01_iteratedDeriv_ofReal
      (apm_m94J01_localSummand n) q hs) y, Complex.norm_real]
    exact hbound q n y
  have hderiv := iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) hf
    (fun q hq => hv q) (fun q n y hq => hlocal q n y)
    (show (j : ℕ∞) ≤ (⊤ : ℕ∞) from le_top) x
  rw [hderiv]
  have hnormSummable : Summable (fun n => ‖iteratedFDeriv ℝ j (f n) x‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hlocal j n x) (hv j)
  calc
    ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ j (f n) x‖
        ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ j (f n) x‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnormSummable) (by positivity)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (f n) x‖ := by
          rw [tsum_mul_left]
    _ ≤ ∑' n, w n := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        have hs : ContDiff ℝ j (apm_m94J01_localSummand n) := by
          unfold apm_m94J01_localSummand
          apply ContDiff.mul
          · fun_prop
          · exact (apm_m94J01_plateauBump.contDiff (n := j)).comp
              ((contDiff_id : ContDiff ℝ j (fun x : ℝ ↦ x)).sub
                (contDiff_const : ContDiff ℝ j (fun _ : ℝ ↦ (n : ℝ))))
        rw [congrFun (apm_m94J01_iteratedDeriv_ofReal
          (apm_m94J01_localSummand n) j hs) x, Complex.norm_real]
        simpa [f, Real.norm_eq_abs] using hwbound n x
      · exact hnormSummable.mul_left (‖x‖ ^ k)
      · exact hw

private lemma apm_m94J01_pointwise_hasFiniteSupport (x : ℝ) :
    Function.HasFiniteSupport
      (fun n : ℕ => (apm_m94J01_localSummand n x : ℂ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| + 1)
  apply (Set.finite_Iio N).subset
  intro n hn
  have hnz : apm_m94J01_localSummand n x ≠ 0 := by
    simpa [Function.mem_support] using hn
  have hd : |x - n| < (1 / 2 : ℝ) := by
    exact lt_of_not_ge (fun h => hnz
      (apm_m94J01_localSummand_eq_zero_of_half_le n x h))
  have hnle : (n : ℝ) ≤ |x| + |x - n| := by
    have ht := abs_add_le x (-(x - n))
    rw [show x + -(x - n) = (n : ℝ) by ring] at ht
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [hnabs, abs_neg] at ht
    exact ht
  have hnlt : (n : ℝ) < |x| + 1 := by linarith
  exact_mod_cast hnlt.trans hN

private lemma apm_m94J01_negOnePow_not_tendsto (a : ℂ) :
    ¬ Tendsto (fun n : ℕ ↦ (-1 : ℂ) ^ n) atTop (nhds a) := by
  intro h
  have hd : Tendsto
      (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n)
      atTop (nhds 0) := by
    simpa using (h.comp (tendsto_add_atTop_nat 1)).sub h
  have hnorm := hd.norm
  have hconst : (fun n : ℕ ↦
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖) = fun _ ↦ (2 : ℝ) := by
    funext n
    calc
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖ =
          ‖-((2 : ℂ) * (-1 : ℂ) ^ n)‖ := by
            congr 1
            rw [pow_succ]
            ring
      _ = ‖(2 : ℂ) * (-1 : ℂ) ^ n‖ := norm_neg _
      _ = 2 := by rw [norm_mul, norm_pow]; norm_num
  rw [hconst] at hnorm
  have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 0) := by
    simpa using hnorm
  have : (2 : ℝ) = 0 := tendsto_nhds_unique htwo hzero
  norm_num at this

/-- Why this unblocks `apm_m94j01`: the factorially normalized, pairwise
disjoint translated bumps have uniformly bounded weighted derivatives of every
order, so their pointwise `finsum` is a Schwartz function.  Its prescribed
diagonal jets turn evaluation of the moving delta derivatives into the
nonconvergent sequence `(-1)^n`. -/
theorem apm_m94J01_bridge_1 :
    ∃ φ : 𝓢(ℝ, ℂ),
      (∀ x : ℝ,
        φ x = ∑ᶠ n : ℕ, (apm_m94J01_localSummand n x : ℂ)) ∧
      ∀ n : ℕ, iteratedDeriv n (φ : ℝ → ℂ) (n : ℝ) = 1 := by
  let φ : 𝓢(ℝ, ℂ) :=
    { toFun := fun x : ℝ =>
        ∑' n : ℕ, (apm_m94J01_localSummand n x : ℂ)
      smooth' := apm_m94J01_contDiff_tsum_localSummand
      decay' := fun k j => apm_m94J01_tsum_decay k j }
  have hspec : ∀ x : ℝ,
      φ x = ∑ᶠ n : ℕ, (apm_m94J01_localSummand n x : ℂ) := by
    intro x
    change (∑' n : ℕ, (apm_m94J01_localSummand n x : ℂ)) = _
    exact tsum_eq_finsum (apm_m94J01_pointwise_hasFiniteSupport x)
  refine ⟨φ, hspec, fun n => ?_⟩
  have hfun : (φ : ℝ → ℂ) = apm_m94J01_globalFunction := by
    funext x
    exact hspec x
  rw [hfun]
  exact apm_m94J01_globalFunction_iteratedDeriv n

theorem apm_m94j01 :
    (∀ φ : TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ ⊤,
      Tendsto
        (fun n : ℕ ↦ (-1 : ℝ) ^ n * iteratedDeriv n φ (n : ℝ))
        atTop (nhds 0)) ∧
    ¬∃ T : TemperedDistribution ℝ ℂ,
      ∀ φ : 𝓢(ℝ, ℂ),
        Tendsto
          (fun n : ℕ ↦ (-1 : ℂ) ^ n * iteratedDeriv n φ (n : ℝ))
          atTop (nhds (T φ)) := by
  constructor
  · intro φ
    obtain ⟨b, hb⟩ := bddAbove_def.mp φ.hasCompactSupport.bddAbove
    have hev : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    have hn_support : (n : ℝ) ∉ tsupport φ := by
      intro hmem
      exact (not_le_of_gt hn) (hb _ hmem)
    have heq : (φ : ℝ → ℝ) =ᶠ[nhds (n : ℝ)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hn_support
    rw [heq.iteratedDeriv_eq n, iteratedDeriv_const_zero, mul_zero]
  · obtain ⟨φ, _, hjet⟩ := apm_m94J01_bridge_1
    rintro ⟨T, hT⟩
    have hconv := hT φ
    simp_rw [hjet, mul_one] at hconv
    exact apm_m94J01_negOnePow_not_tendsto (T φ) hconv
