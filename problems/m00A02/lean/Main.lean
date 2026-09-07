import Mathlib

/-!
# APM m00A02: Poincaré asymptotic expansions

## Statement repairs

Part (c) prints the formal derivative as `∑ n aₙ / xⁿ`. The derivative of
`aₙ / xⁿ` is instead `-n aₙ / xⁿ⁺¹`. We use this corrected sign and
index shift in the formal derivative coefficients.

## Encoding questions

None. An asymptotic expansion is encoded by the remainder limit for every
finite partial sum; no convergence of the infinite formal series is assumed.
-/

open Filter Finset
open scoped Topology ContDiff

noncomputable section

/-- Poincaré asymptotic expansion in descending integral powers at `+∞`. -/
def apm_m00A02_hasExpansion (f : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ N : ℕ,
    Tendsto
      (fun x : ℝ ↦
        x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n))
      atTop (nhds 0)

/-- Coefficients of the termwise derivative of `∑ aₙ x⁻ⁿ`. -/
def apm_m00A02_derivativeCoefficients (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => -(n : ℝ) * a n

private lemma apm_m00A02_hasDerivAt_div_pow
    (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => a / y ^ n)
      ((0 * x ^ n - a * ((n : ℝ) * x ^ (n - 1))) / (x ^ n) ^ 2) x := by
  exact (hasDerivAt_const x a).div
    (hasDerivAt_pow n x) (pow_ne_zero n hx)

private lemma apm_m00A02_hasDerivAt_partialSum
    (a : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => ∑ n ∈ range (N + 1), a n / y ^ n)
      (∑ n ∈ range (N + 1),
        (0 * x ^ n - a n * ((n : ℝ) * x ^ (n - 1))) / (x ^ n) ^ 2) x := by
  convert HasDerivAt.sum (u := range (N + 1))
    (fun n _ => apm_m00A02_hasDerivAt_div_pow (a n) n hx) using 1
  funext y
  simp

private lemma apm_m00A02_hasDerivAt_remainder
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℕ → ℝ) (N : ℕ)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ => f y - ∑ n ∈ range (N + 1), a n / y ^ n)
      (deriv f x - ∑ n ∈ range (N + 1),
        (0 * x ^ n - a n * ((n : ℝ) * x ^ (n - 1))) / (x ^ n) ^ 2) x := by
  exact (hf x).hasDerivAt.sub (apm_m00A02_hasDerivAt_partialSum a N hx)

private lemma apm_m00A02_scaled_remainder_eventuallyEq
    (f : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) :
    (fun x : ℝ => x ^ (N + 1) *
      (f x - ∑ n ∈ range (N + 1), a n / x ^ n)) =ᶠ[atTop]
    (fun x : ℝ => x ^ (N + 1) * f x -
      ∑ n ∈ range (N + 1), a n * x ^ (N + 1 - n)) := by
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hnle : n ≤ N + 1 := (mem_range.mp hn).le
  field_simp
  calc
    x ^ (N + 1) * a n = a n * x ^ (N + 1) := by ring
    _ = a n * (x ^ n * x ^ (N + 1 - n)) := by rw [pow_mul_pow_sub x hnle]
    _ = a n * x ^ n * x ^ (N + 1 - n) := by ring

private lemma apm_m00A02_scaled_remainder_differentiable
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℕ → ℝ) (N : ℕ) :
    Differentiable ℝ (fun x : ℝ => x ^ (N + 1) * f x -
      ∑ n ∈ range (N + 1), a n * x ^ (N + 1 - n)) := by
  fun_prop

private lemma apm_m00A02_hasDerivAt_scaled_remainder
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (N + 1) * f y -
      ∑ n ∈ range (N + 1), a n * y ^ (N + 1 - n))
      (((N + 1 : ℕ) : ℝ) * x ^ N * f x + x ^ (N + 1) * deriv f x -
        ∑ n ∈ range (N + 1),
          a n * (((N + 1 - n : ℕ) : ℝ) * x ^ (N + 1 - n - 1))) x := by
  have hleft := (hasDerivAt_pow (N + 1) x).mul (hf x).hasDerivAt
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ n ∈ range (N + 1), a n * y ^ (N + 1 - n))
      (∑ n ∈ range (N + 1),
        a n * (((N + 1 - n : ℕ) : ℝ) * x ^ (N + 1 - n - 1))) x := by
    convert HasDerivAt.sum (u := range (N + 1)) (fun n _ =>
      (hasDerivAt_const x (a n)).mul (hasDerivAt_pow (N + 1 - n) x)) using 1
    · funext y
      simp
    · apply sum_congr rfl
      intro n hn
      ring
  simpa using hleft.sub hsum

private lemma apm_m00A02_scaled_remainder_limit
    {f : ℝ → ℝ} {a : ℕ → ℝ} (ha : apm_m00A02_hasExpansion f a) (N : ℕ) :
    Tendsto (fun x : ℝ => x ^ (N + 1) * f x -
      ∑ n ∈ range (N + 1), a n * x ^ (N + 1 - n))
      atTop (nhds (a (N + 1))) := by
  have h := (ha (N + 1)).const_add (a (N + 1))
  have h' : Tendsto (fun x : ℝ => a (N + 1) + x ^ (N + 1) *
      (f x - ∑ n ∈ range (N + 1 + 1), a n / x ^ n))
      atTop (nhds (a (N + 1))) := by simpa using h
  have hrem : Tendsto (fun x : ℝ => x ^ (N + 1) *
      (f x - ∑ n ∈ range (N + 1), a n / x ^ n))
      atTop (nhds (a (N + 1))) := by
    apply h'.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    rw [sum_range_succ]
    field_simp
    ring
  exact hrem.congr' (apm_m00A02_scaled_remainder_eventuallyEq f a N)

/-- A convergent differentiable function cannot have its derivative converge
to a nonzero finite limit.  The unit-interval mean value theorem avoids any
integrability hypothesis on the derivative. -/
private lemma apm_m00A02_deriv_limit_eq_zero
    {f : ℝ → ℝ} {L d : ℝ} (hf : Differentiable ℝ f)
    (hflim : Tendsto f atTop (nhds L))
    (hdlim : Tendsto (deriv f) atTop (nhds d)) : d = 0 := by
  have hex (x : ℝ) : ∃ c ∈ Set.Ioo x (x + 1),
      deriv f c = (f (x + 1) - f x) / ((x + 1) - x) := by
    apply exists_deriv_eq_slope
    · linarith
    · exact hf.continuous.continuousOn
    · exact hf.differentiableOn
  let c : ℝ → ℝ := fun x => Classical.choose (hex x)
  have hc_mem (x : ℝ) : c x ∈ Set.Ioo x (x + 1) :=
    (Classical.choose_spec (hex x)).1
  have hc_deriv (x : ℝ) : deriv f (c x) = f (x + 1) - f x := by
    change deriv f (Classical.choose (hex x)) = _
    simpa using (Classical.choose_spec (hex x)).2
  have hc_top : Tendsto c atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Eventually.of_forall fun x => (hc_mem x).1.le)
    exact tendsto_id
  have hd : Tendsto (fun x => deriv f (c x)) atTop (nhds d) :=
    hdlim.comp hc_top
  have hshift : Tendsto (fun x : ℝ => f (x + 1)) atTop (nhds L) := by
    apply hflim.comp
    exact tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hz : Tendsto (fun x : ℝ => f (x + 1) - f x) atTop (nhds 0) := by
    simpa using hshift.sub hflim
  have hd0 : Tendsto (fun x => deriv f (c x)) atTop (nhds 0) := by
    simpa only [hc_deriv] using hz
  exact tendsto_nhds_unique hd hd0

/-- The coefficients in the frozen integral-power Poincaré encoding are
uniquely determined by the function. -/
lemma apm_m00A02_expansion_coefficients_unique
    {f : ℝ → ℝ} {a c : ℕ → ℝ}
    (ha : apm_m00A02_hasExpansion f a)
    (hc : apm_m00A02_hasExpansion f c) : a = c := by
  funext N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have ht := (ha N).sub (hc N)
    have heq : (fun x : ℝ =>
        x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n) -
        x ^ N * (f x - ∑ n ∈ range (N + 1), c n / x ^ n)) =ᶠ[atTop]
        fun _ => c N - a N := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      have hs : ∑ n ∈ range N, a n / x ^ n =
          ∑ n ∈ range N, c n / x ^ n := by
        apply sum_congr rfl
        intro n hn
        rw [ih n (mem_range.mp hn)]
      rw [sum_range_succ, sum_range_succ, hs]
      field_simp
      ring
    have ht0 : Tendsto (fun x : ℝ =>
        x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n) -
        x ^ N * (f x - ∑ n ∈ range (N + 1), c n / x ^ n))
        atTop (nhds 0) := by
      simpa using ht
    have ht' : Tendsto (fun _ : ℝ => c N - a N) atTop (nhds 0) :=
      ht0.congr' heq
    have hcst : Tendsto (fun _ : ℝ => c N - a N) atTop
        (nhds (c N - a N)) := tendsto_const_nhds
    have hz : (0 : ℝ) = c N - a N := tendsto_nhds_unique ht' hcst
    linarith

/-- A smooth, asymptotically null function whose derivative is not null. -/
def apm_m00A02_counterexample (x : ℝ) : ℝ :=
  Real.exp (-x) * Real.sin (Real.exp x)

private lemma apm_m00A02_counterexample_hasDerivAt (x : ℝ) :
    HasDerivAt apm_m00A02_counterexample
      (Real.cos (Real.exp x) - Real.exp (-x) * Real.sin (Real.exp x)) x := by
  unfold apm_m00A02_counterexample
  convert
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul
      ((Real.hasDerivAt_sin (Real.exp x)).comp x (Real.hasDerivAt_exp x)) using 1 <;>
    simp only [Function.comp_apply]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero x]
  <;> ring

/-- Why this unblocks `apm_m00a02`: this isolates the missing improper-FTC
argument. Integrating the order-by-order expansion of `deriv f` from a large
point to infinity forces its coefficients to be the termwise derivatives of
the coefficients of `f`; coefficient uniqueness then yields the expansion
required by the main theorem. -/
theorem apm_m00A02_derivative_expansion_coefficients
    {f : ℝ → ℝ} {a b : ℕ → ℝ}
    (hf : Differentiable ℝ f)
    (ha : apm_m00A02_hasExpansion f a)
    (hb : apm_m00A02_hasExpansion (deriv f) b) :
    b = apm_m00A02_derivativeCoefficients a := by
  have hflim : Tendsto f atTop (nhds (a 0)) := by
    have h := ha 0
    simpa [apm_m00A02_hasExpansion] using h.const_add (a 0)
  have hdlim : Tendsto (deriv f) atTop (nhds (b 0)) := by
    have h := hb 0
    simpa [apm_m00A02_hasExpansion] using h.const_add (b 0)
  have hb0 : b 0 = 0 :=
    apm_m00A02_deriv_limit_eq_zero hf hflim hdlim
  let g : ℝ → ℝ := fun x => x * (f x - a 0)
  have hglim : Tendsto g atTop (nhds (a 1)) := by
    have h := (ha 1).const_add (a 1)
    have h' : Tendsto (fun x => a 1 + x ^ 1 *
        (f x - ∑ n ∈ range (1 + 1), a n / x ^ n)) atTop (nhds (a 1)) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    simp only [g, sum_range_succ, sum_range_zero, zero_add,
      pow_zero, div_one, pow_one]
    field_simp
    ring
  have hgdiff : Differentiable ℝ g := by
    dsimp only [g]
    fun_prop
  have hxderiv : Tendsto (fun x : ℝ => x * deriv f x) atTop (nhds (b 1)) := by
    have h := (hb 1).const_add (b 1)
    have h' : Tendsto (fun x => b 1 + x ^ 1 *
        (deriv f x - ∑ n ∈ range (1 + 1), b n / x ^ n)) atTop (nhds (b 1)) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    simp only [hb0, sum_range_succ, sum_range_zero, zero_add,
      pow_zero, div_one, pow_one]
    field_simp
    ring
  have hderivg : Tendsto (deriv g) atTop (nhds (b 1)) := by
    have hzero : Tendsto (fun x : ℝ => f x - a 0) atTop (nhds 0) := by
      simpa using hflim.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => a 0) atTop (nhds (a 0)))
    have hsum := hzero.add hxderiv
    have hsum' : Tendsto (fun x : ℝ => f x - a 0 + x * deriv f x)
        atTop (nhds (b 1)) := by simpa using hsum
    apply hsum'.congr'
    filter_upwards [] with x
    have hh : HasDerivAt g (f x - a 0 + x * deriv f x) x := by
      dsimp only [g]
      convert (hasDerivAt_id x).mul ((hf x).hasDerivAt.sub_const (a 0)) using 1 <;>
        simp
    exact hh.deriv.symm
  have hb1 : b 1 = 0 :=
    apm_m00A02_deriv_limit_eq_zero hgdiff hglim hderivg
  have hrec : ∀ N : ℕ, b (N + 1) = -(N : ℝ) * a N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      let G : ℝ → ℝ := fun x => x ^ (N + 1) * f x -
        ∑ n ∈ range (N + 1), a n * x ^ (N + 1 - n)
      have hGdiff : Differentiable ℝ G :=
        apm_m00A02_scaled_remainder_differentiable hf a N
      have hGlim : Tendsto G atTop (nhds (a (N + 1))) :=
        apm_m00A02_scaled_remainder_limit ha N
      have haN0 : Tendsto (fun x : ℝ => ((N + 1 : ℕ) : ℝ) *
          (x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n)))
          atTop (nhds 0) := by
        simpa using (ha N).const_mul (((N + 1 : ℕ) : ℝ))
      have hbN0 := hb (N + 1)
      have hparts : Tendsto (fun x : ℝ =>
          ((N + 1 : ℕ) : ℝ) *
            (x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n)) +
          x ^ (N + 1) * (deriv f x -
            ∑ n ∈ range (N + 1 + 1), b n / x ^ n) +
          (b (N + 1) + (N : ℝ) * a N)) atTop
          (nhds (b (N + 1) + (N : ℝ) * a N)) := by
        have hz := haN0.add hbN0
        simpa using hz.add_const (b (N + 1) + (N : ℝ) * a N)
      have hDG : Tendsto (deriv G) atTop
          (nhds (b (N + 1) + (N : ℝ) * a N)) := by
        apply hparts.congr'
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
        have hshift : ∑ n ∈ range N, b (n + 1) / x ^ (n + 1) =
            ∑ n ∈ range N, (-(n : ℝ) * a n) / x ^ (n + 1) := by
          apply sum_congr rfl
          intro n hn
          rw [ih n (mem_range.mp hn)]
        have hbsum : ∑ n ∈ range (N + 1 + 1), b n / x ^ n =
            (∑ n ∈ range N, (-(n : ℝ) * a n) / x ^ (n + 1)) +
              b (N + 1) / x ^ (N + 1) := by
          rw [sum_range_succ, sum_range_succ', hshift, hb0]
          simp
        have hascale : x ^ N * (∑ n ∈ range (N + 1), a n / x ^ n) =
            ∑ n ∈ range (N + 1), a n * x ^ (N - n) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro n hn
          have hnle : n ≤ N := Nat.le_of_lt_succ (mem_range.mp hn)
          field_simp
          rw [show x ^ N = x ^ n * x ^ (N - n) from (pow_mul_pow_sub x hnle).symm]
          ring
        have hbscale : x ^ (N + 1) *
            (∑ n ∈ range N, (-(n : ℝ) * a n) / x ^ (n + 1)) =
            ∑ n ∈ range N, (-(n : ℝ) * a n) * x ^ (N - n) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro n hn
          have hnlt : n < N := mem_range.mp hn
          have hnle : n + 1 ≤ N + 1 := by omega
          have he : N + 1 - (n + 1) = N - n := by omega
          field_simp
          rw [show x ^ (N + 1) = x ^ (n + 1) * x ^ (N + 1 - (n + 1)) from
            (pow_mul_pow_sub x hnle).symm, he]
          ring
        have hcoef :
            ((N + 1 : ℕ) : ℝ) *
                (∑ n ∈ range (N + 1), a n * x ^ (N - n)) +
              (∑ n ∈ range N, (-(n : ℝ) * a n) * x ^ (N - n)) -
              (N : ℝ) * a N =
            ∑ n ∈ range (N + 1),
              a n * (((N + 1 - n : ℕ) : ℝ) * x ^ (N + 1 - n - 1)) := by
          have hi : ∑ n ∈ range N,
                a n * (((N + 1 - n : ℕ) : ℝ) * x ^ (N + 1 - n - 1)) =
              ((N + 1 : ℕ) : ℝ) * (∑ n ∈ range N, a n * x ^ (N - n)) +
                ∑ n ∈ range N, (-(n : ℝ) * a n) * x ^ (N - n) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply sum_congr rfl
            intro n hn
            have hnlt : n < N := mem_range.mp hn
            rw [Nat.cast_sub (by omega : n ≤ N + 1)]
            have he : N + 1 - n - 1 = N - n := by omega
            rw [he]
            push_cast
            ring
          rw [sum_range_succ, sum_range_succ]
          simp only [Nat.sub_self, pow_zero, mul_one, Nat.add_sub_cancel_left,
            Nat.cast_one]
          rw [hi, mul_add]
          push_cast
          ring
        rw [(apm_m00A02_hasDerivAt_scaled_remainder hf a N x).deriv]
        rw [hbsum]
        rw [mul_sub, hascale]
        let T : ℝ := ∑ n ∈ range N, (-(n : ℝ) * a n) / x ^ (n + 1)
        let S : ℝ := ∑ n ∈ range N, (-(n : ℝ) * a n) * x ^ (N - n)
        have hTS : x ^ (N + 1) * T = S := by
          exact hbscale
        have hsecond : x ^ (N + 1) *
              (deriv f x - (T + b (N + 1) / x ^ (N + 1))) =
            x ^ (N + 1) * deriv f x -
              S -
              b (N + 1) := by
          rw [mul_sub, mul_add, hTS]
          field_simp
          ring
        rw [hsecond]
        dsimp only [T, S]
        linear_combination -hcoef
      have hz := apm_m00A02_deriv_limit_eq_zero hGdiff hGlim hDG
      linarith
  funext k
  cases k with
  | zero => simpa [apm_m00A02_derivativeCoefficients] using hb0
  | succ N => simpa [apm_m00A02_derivativeCoefficients] using hrec N

theorem apm_m00a02 :
    apm_m00A02_hasExpansion (fun x : ℝ ↦ Real.exp (-x)) 0 ∧
    ContDiff ℝ ∞ apm_m00A02_counterexample ∧
    apm_m00A02_hasExpansion apm_m00A02_counterexample 0 ∧
    ¬apm_m00A02_hasExpansion (deriv apm_m00A02_counterexample) 0 ∧
    ∀ (f : ℝ → ℝ) (a b : ℕ → ℝ),
      Differentiable ℝ f →
      apm_m00A02_hasExpansion f a →
      apm_m00A02_hasExpansion (deriv f) b →
      apm_m00A02_hasExpansion (deriv f)
        (apm_m00A02_derivativeCoefficients a) := by
  have hexp : apm_m00A02_hasExpansion (fun x : ℝ ↦ Real.exp (-x)) 0 := by
    intro N
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hsmooth : ContDiff ℝ ∞ apm_m00A02_counterexample := by
    unfold apm_m00A02_counterexample
    fun_prop
  have hcounter : apm_m00A02_hasExpansion apm_m00A02_counterexample 0 := by
    intro N
    simp only [Pi.zero_apply, zero_div, sum_const_zero, sub_zero]
    apply squeeze_zero_norm
    · intro x
      unfold apm_m00A02_counterexample
      simp only [Real.norm_eq_abs, abs_mul]
      calc
        |x ^ N| * (|Real.exp (-x)| * |Real.sin (Real.exp x)|) ≤
            |x ^ N| * (|Real.exp (-x)| * 1) := by
              gcongr
              exact Real.abs_sin_le_one _
        _ = |x ^ N * Real.exp (-x)| := by rw [abs_mul, mul_one]
    · simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).abs
  refine ⟨hexp, hsmooth, hcounter, ?_, ?_⟩
  · intro hderiv
    have hzero : Tendsto (deriv apm_m00A02_counterexample) atTop (nhds 0) := by
      simpa [apm_m00A02_hasExpansion] using hderiv 0
    let u : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) * (2 * Real.pi)
    have hu : Tendsto u atTop atTop := by
      apply Tendsto.atTop_mul_const (mul_pos zero_lt_two Real.pi_pos)
      have hcast :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      convert hcast using 1
    have hlog : Tendsto (fun k => Real.log (u k)) atTop atTop :=
      Real.tendsto_log_atTop.comp hu
    have hone : Tendsto
        (fun k => deriv apm_m00A02_counterexample (Real.log (u k)))
        atTop (nhds 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [] with k
      rw [(apm_m00A02_counterexample_hasDerivAt _).deriv]
      have huk : 0 < u k := mul_pos (by positivity) (mul_pos zero_lt_two Real.pi_pos)
      rw [Real.exp_log huk]
      have hcos : Real.cos (u k) = 1 := by
        simpa [u] using Real.cos_nat_mul_two_pi (k + 1)
      have hsin : Real.sin (u k) = 0 := by
        convert Real.sin_nat_mul_pi (2 * (k + 1)) using 1 <;> push_cast <;> simp [u] <;> ring
      rw [hcos, hsin]
      ring
    have hzero' := hzero.comp hlog
    have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero' hone
    norm_num at this

  · /-
    Boundary for coefficient rigidity: the final implication requires a formal
    theorem that two integral-power Poincaré expansions have identical
    coefficients, plus integration of a derivative expansion from infinity.
    Searches of Mathlib and solved siblings found no reusable API for asymptotic
    expansion uniqueness or termwise integration in this custom encoding. A
    direct proof must first derive `b 0 = b 1 = 0` from convergence of `f`, then
    formalize improper FTC estimates order by order and compare coefficients.
    Closer hop 2 completed the independent counterexample-negation conjunct via
    the logarithmic sequence above. Further searches in the asymptotics and
    improper-integral APIs still found no theorem connecting this custom
    all-orders remainder predicate to the required integrated expansion.
    Closer hop 3 proves `apm_m00A02_expansion_coefficients_unique`, so the
    coefficient-rigidity half is no longer open. The remaining task is exactly
    the integration bridge: derive `b 0 = b 1 = 0` from convergence of `f`,
    integrate the order-by-order remainder estimate for `deriv f` on
    `[x, +∞)`, and use the improper FTC to produce the formal derivative
    expansion. Searches found `intervalIntegral.integral_deriv_eq_sub` and
    `integral_Ioi_rpow_of_lt`, but assembling their eventual hypotheses from
    the raw `Tendsto` remainder and merely `Differentiable ℝ f` remains open.
    -/
    intro f a b hf ha hb
    have hcoeff : b = apm_m00A02_derivativeCoefficients a :=
      apm_m00A02_derivative_expansion_coefficients hf ha hb
    simpa [← hcoeff] using hb
