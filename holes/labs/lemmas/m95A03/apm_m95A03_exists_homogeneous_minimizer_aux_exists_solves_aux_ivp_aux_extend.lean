import Mathlib

/-!
# APM m95A03: the Dirichlet principle for a Sturm--Liouville problem

## Statement repairs

The problem asks for appropriate hypotheses; we take `a < b`, `p ∈ C¹`
uniformly positive, and continuous `q ≥ 0` and `f`.

Uniqueness in part (c) is up to equality on `[a, b]`. The functions are
`ℝ → ℝ` and the energy only sees `[a, b]`, so a minimizer changed outside
`[a, b]` is another minimizer; `∃!` over all of `ℝ → ℝ` is false (compiled
counterexample: holes/labs/solve-loop/refutations/m95A03/Refute.lean).
Part (c) also records admissibility explicitly: Mathlib's `IsMinOn` compares a
point with members of a set but does not assert that the point itself belongs
to that set.  Uniqueness ranges over all admissible `C¹` minimizers, as in the
source, rather than only globally `C²` competitors.

## Encoding questions

Mathlib has no bundled Sobolev space. The problem's differential equation,
boundary constraints, energy, affine homogenization, minimization claim, and
existence/uniqueness conclusion are therefore encoded directly on `C¹`/`C²`
functions, without replacing any of those objects by a scalar surrogate.
-/

noncomputable section

open Set

/-- The energy from the printed variational problem. -/
def apm_m95A03_energy (a b : ℝ) (p q f u : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, p t * (deriv u t) ^ 2 + q t * (u t) ^ 2 + 2 * u t * f t

/-- The admissible `C¹` functions with the prescribed endpoint data. -/
def apm_m95A03_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {u | ContDiff ℝ 1 u ∧ u a = α ∧ u b = β}

/-- Classical solutions of `(p u')' - q u = f` with Dirichlet data. -/
def apm_m95A03_solves
    (a b α β : ℝ) (p q f u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 u ∧ u a = α ∧ u b = β ∧
    ∀ t ∈ Set.Icc a b,
      deriv (fun x => p x * deriv u x) t - q t * u t = f t

/-- Linear interpolant used to homogenize the boundary conditions. -/
def apm_m95A03_boundaryLift (a b α β t : ℝ) : ℝ :=
  α + (β - α) * ((t - a) / (b - a))

/-- Right-hand side after writing `u = v + w`. -/
def apm_m95A03_modifiedRHS
    (p q f w : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - (deriv (fun x => p x * deriv w x) t - q t * w t)

/-! ## Remaining bridges -/

theorem apm_m95A03_isMinOn_of_solves
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hu : apm_m95A03_solves a b α β p q f u) :
    IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b α β) u := by
  intro v hv
  rcases hu with ⟨hu2, hua, hub, huODE⟩
  rcases hv with ⟨hv1, hva, hvb⟩
  let h : ℝ → ℝ := fun x ↦ v x - u x
  have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
  have hh : ContDiff ℝ 1 h := hv1.sub hu1
  have ha0 : h a = 0 := by simp [h, hva, hua]
  have hb0 : h b = 0 := by simp [h, hvb, hub]
  let g : ℝ → ℝ := fun x ↦ p x * deriv u x
  have hdu : ContDiff ℝ 1 (deriv u) := hu2.deriv'
  have hg : ContDiff ℝ 1 g := hp.mul hdu
  have hgderiv : ∀ x ∈ Set.Icc a b,
      deriv g x = q x * u x + f x := by
    intro x hx
    dsimp [g]
    linarith [huODE x hx]
  have hHasG : ∀ x ∈ Set.uIcc a b, HasDerivAt g (deriv g x) x := by
    intro x hx
    exact (hg.differentiable (by norm_num) x).hasDerivAt
  have hHasH : ∀ x ∈ Set.uIcc a b, HasDerivAt h (deriv h x) x := by
    intro x hx
    exact (hh.differentiable (by norm_num) x).hasDerivAt
  have hgd : ContDiff ℝ 0 (deriv g) := hg.deriv'
  have hg'int : IntervalIntegrable (deriv g) MeasureTheory.volume a b :=
    hgd.continuous.intervalIntegrable _ _
  have hhd : ContDiff ℝ 0 (deriv h) := hh.deriv'
  have hh'int : IntervalIntegrable (deriv h) MeasureTheory.volume a b :=
    hhd.continuous.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hHasG hHasH hg'int hh'int
  rw [ha0, hb0] at hibp
  have hcross_cont : Continuous (fun x ↦
      g x * deriv h x + q x * u x * h x + f x * h x) := by
    have hgc : Continuous g := hg.continuous
    have hdhc : Continuous (deriv h) := hhd.continuous
    exact (hgc.mul hdhc).add
      ((hq.mul hu1.continuous).mul hh.continuous) |>.add (hf.mul hh.continuous)
  have hcross : (∫ x in a..b,
      g x * deriv h x + q x * u x * h x + f x * h x) = 0 := by
    have heq : (∫ x in a..b,
        g x * deriv h x + q x * u x * h x + f x * h x) =
        ∫ x in a..b, g x * deriv h x + deriv g x * h x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change g x * deriv h x + q x * u x * h x + f x * h x =
        g x * deriv h x + deriv g x * h x
      rw [hgderiv x (Set.uIcc_of_le hab.le ▸ hx)]
      ring
    rw [heq, intervalIntegral.integral_add]
    · rw [hibp]
      ring
    · exact (hg.continuous.mul hhd.continuous).intervalIntegrable _ _
    · exact (hgd.continuous.mul hh.continuous).intervalIntegrable _ _
  have hderiv (x : ℝ) : deriv v x = deriv u x + deriv h x := by
    have hdv := hv1.differentiable (by norm_num) x
    have hdu' := hu1.differentiable (by norm_num) x
    have hs := deriv_sub hdv hdu'
    change deriv h x = deriv v x - deriv u x at hs
    linarith
  let R : ℝ → ℝ := fun x ↦ p x * (deriv h x) ^ 2 + q x * (h x) ^ 2
  have hRcont : Continuous R := by
    dsimp [R]
    fun_prop
  have hRnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ R x := by
    intro x hx
    dsimp [R]
    have hpnonneg : 0 ≤ p x := le_trans hp₀.le (hp_lower x hx)
    exact add_nonneg (mul_nonneg hpnonneg (sq_nonneg _))
      (mul_nonneg (hq_nonneg x hx) (sq_nonneg _))
  have hRint : 0 ≤ ∫ x in a..b, R x :=
    intervalIntegral.integral_nonneg hab.le hRnonneg
  have hUcont : Continuous (fun x ↦
      p x * deriv u x ^ 2 + q x * u x ^ 2 + 2 * u x * f x) := by
    have hduc : Continuous (deriv u) := hdu.continuous
    fun_prop
  have hTwocross : Continuous (fun x ↦
      2 * (g x * deriv h x + q x * u x * h x + f x * h x)) :=
    hcross_cont.const_mul 2
  have hexpand : apm_m95A03_energy a b p q f v =
      apm_m95A03_energy a b p q f u +
        2 * (∫ x in a..b,
          g x * deriv h x + q x * u x * h x + f x * h x) +
        ∫ x in a..b, R x := by
    unfold apm_m95A03_energy
    calc
      (∫ t in a..b, p t * deriv v t ^ 2 + q t * v t ^ 2 + 2 * v t * f t) =
          ∫ t in a..b,
            (p t * deriv u t ^ 2 + q t * u t ^ 2 + 2 * u t * f t) +
            2 * (g t * deriv h t + q t * u t * h t + f t * h t) + R t := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [g, R, h]
        rw [hderiv x]
        ring
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        rw [← intervalIntegral.integral_add
          (hUcont.intervalIntegrable _ _) (hTwocross.intervalIntegrable _ _)]
        simpa only [Pi.add_apply] using (intervalIntegral.integral_add
          (μ := MeasureTheory.volume) (a := a) (b := b)
          ((hUcont.add hTwocross).intervalIntegrable _ _)
          (hRcont.intervalIntegrable _ _))
  change apm_m95A03_energy a b p q f u ≤ apm_m95A03_energy a b p q f v
  rw [hexpand, hcross, mul_zero, add_zero]
  exact le_add_of_nonneg_right hRint

lemma apm_m95A03_solves_of_isMinOn_aux_residual_continuous
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f) (hu2 : ContDiff ℝ 2 u) :
    Continuous (fun t =>
      deriv (fun x => p x * deriv u x) t - q t * u t - f t) := by
  have hdu : ContDiff ℝ 1 (deriv u) := hu2.deriv'
  have hg : ContDiff ℝ 1 (fun x => p x * deriv u x) := hp.mul hdu
  have hgd : ContDiff ℝ 0 (deriv (fun x => p x * deriv u x)) := hg.deriv'
  exact (hgd.continuous.sub (hq.mul hu2.continuous)).sub hf

lemma apm_m95A03_solves_of_isMinOn_aux_perturb_admissible
    (a b α β s : ℝ) (u η : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hua : u a = α) (hub : u b = β)
    (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (fun x => u x + s * η x) ∈ apm_m95A03_admissible a b α β := by
  refine ⟨hu.add (contDiff_const.mul hη), ?_, ?_⟩
  · simp [hua, hηa]
  · simp [hub, hηb]

/-- First variation: minimality against `u + s η` for both signs of `s` kills the
linear term of the quadratic `s ↦ energy (u + s η)`. -/
lemma apm_m95A03_solves_of_isMinOn_aux_first_variation
    (a b α β : ℝ) (hab : a < b)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hu2 : ContDiff ℝ 2 u) (hua : u a = α) (hub : u b = β)
    (hmin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b α β) u)
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (∫ t in a..b, p t * deriv u t * deriv η t + q t * u t * η t + f t * η t) = 0 := by
  let L := ∫ t in a..b,
    p t * deriv u t * deriv η t + q t * u t * η t + f t * η t
  let Q := ∫ t in a..b, p t * (deriv η t) ^ 2 + q t * (η t) ^ 2
  have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
  have hdu1 : ContDiff ℝ 1 (deriv u) := hu2.deriv'
  have hdη0 : ContDiff ℝ 0 (deriv η) := hη.deriv'
  have hdu : Continuous (deriv u) := hdu1.continuous
  have hdη : Continuous (deriv η) := hdη0.continuous
  have hU : Continuous (fun t =>
      p t * deriv u t ^ 2 + q t * u t ^ 2 + 2 * u t * f t) := by
    fun_prop
  have hLin : Continuous (fun t =>
      p t * deriv u t * deriv η t + q t * u t * η t + f t * η t) := by
    fun_prop
  have hQuad : Continuous (fun t =>
      p t * deriv η t ^ 2 + q t * η t ^ 2) := by
    fun_prop
  have hderiv (s x : ℝ) :
      deriv (fun y => u y + s * η y) x = deriv u x + s * deriv η x := by
    exact ((hu1.differentiable (by norm_num) x).hasDerivAt.add
      ((hη.differentiable (by norm_num) x).hasDerivAt.const_mul s)).deriv
  have hexpand (s : ℝ) :
      apm_m95A03_energy a b p q f (fun x => u x + s * η x) =
        apm_m95A03_energy a b p q f u + 2 * s * L + s ^ 2 * Q := by
    unfold apm_m95A03_energy
    rw [show (∫ t in a..b,
        p t * deriv (fun x => u x + s * η x) t ^ 2 +
          q t * (u t + s * η t) ^ 2 + 2 * (u t + s * η t) * f t) =
        ∫ t in a..b,
          (p t * deriv u t ^ 2 + q t * u t ^ 2 + 2 * u t * f t) +
          (2 * s) * (p t * deriv u t * deriv η t +
            q t * u t * η t + f t * η t) +
          s ^ 2 * (p t * deriv η t ^ 2 + q t * η t ^ 2) by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [hderiv s x]
      ring]
    simp only [L, Q]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hU.intervalIntegrable _ _)
        ((hLin.const_mul (2 * s)).intervalIntegrable _ _)]
    convert intervalIntegral.integral_add (μ := MeasureTheory.volume)
      ((hU.add (hLin.const_mul (2 * s))).intervalIntegrable _ _)
      ((hQuad.const_mul (s ^ 2)).intervalIntegrable _ _) using 1 <;> rfl
  have hineq (s : ℝ) : 0 ≤ 2 * s * L + s ^ 2 * Q := by
    have hv := apm_m95A03_solves_of_isMinOn_aux_perturb_admissible
      a b α β s u η hu1 hua hub hη hηa hηb
    have hm := hmin hv
    change apm_m95A03_energy a b p q f u ≤
      apm_m95A03_energy a b p q f (fun x => u x + s * η x) at hm
    rw [hexpand s] at hm
    linarith
  by_contra hL
  let D := |Q| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hi := hineq (-L / D)
  have hLsq : 0 < L ^ 2 := sq_pos_of_ne_zero hL
  have hQ : Q ≤ |Q| := le_abs_self Q
  dsimp [D] at hi hD
  field_simp at hi
  nlinarith

/-- Integration by parts of the weak form against a variation vanishing at both ends. -/
lemma apm_m95A03_solves_of_isMinOn_aux_ibp
    (a b : ℝ) (hab : a < b)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f) (hu2 : ContDiff ℝ 2 u)
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (∫ t in a..b, p t * deriv u t * deriv η t + q t * u t * η t + f t * η t) =
      -∫ t in a..b, (deriv (fun x => p x * deriv u x) t - q t * u t - f t) * η t := by
  have hu' : ContDiff ℝ 1 (deriv u) := by
    simpa using hu2.deriv'
  have hg : ContDiff ℝ 1 (fun x => p x * deriv u x) := hp.mul hu'
  have hdg : Continuous (fun x => deriv (fun y => p y * deriv u y) x) :=
    hg.continuous_deriv_one
  have hdη : Continuous (deriv η) := hη.continuous_deriv_one
  have hdg_int : IntervalIntegrable (deriv (fun x => p x * deriv u x))
      MeasureTheory.volume a b := by
    simpa only using hdg.intervalIntegrable (a := a) (b := b)
  have hdη_int : IntervalIntegrable (deriv η) MeasureTheory.volume a b :=
    hdη.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := fun x => p x * deriv u x) (v := η)
    (u' := deriv (fun x => p x * deriv u x)) (v' := deriv η)
    (fun x _ => (hg.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hη.differentiable (by simp) x).hasDerivAt)
    hdg_int hdη_int
  have hibp' :
      (∫ t in a..b, p t * deriv u t * deriv η t) =
        -∫ t in a..b, deriv (fun x => p x * deriv u x) t * η t := by
    simpa [hηa, hηb] using hibp
  have hqu : Continuous (fun t => q t * u t * η t) :=
    (hq.mul hu2.continuous).mul hη.continuous
  have hfη : Continuous (fun t => f t * η t) := hf.mul hη.continuous
  have hgdη : Continuous (fun t => deriv (fun x => p x * deriv u x) t * η t) :=
    hdg.mul hη.continuous
  have hA : IntervalIntegrable (fun t => p t * deriv u t * deriv η t)
      MeasureTheory.volume a b := by
    simpa only [Pi.mul_apply] using
      (hg.continuous.mul hdη).intervalIntegrable (a := a) (b := b)
  have hB : IntervalIntegrable (fun t => q t * u t * η t)
      MeasureTheory.volume a b := hqu.intervalIntegrable
        (μ := MeasureTheory.volume) (a := a) (b := b)
  have hC : IntervalIntegrable (fun t => f t * η t)
      MeasureTheory.volume a b := hfη.intervalIntegrable
        (μ := MeasureTheory.volume) (a := a) (b := b)
  have hD : IntervalIntegrable
      (fun t => deriv (fun x => p x * deriv u x) t * η t)
      MeasureTheory.volume a b := hgdη.intervalIntegrable
        (μ := MeasureTheory.volume) (a := a) (b := b)
  have hr : (∫ t in a..b,
      (deriv (fun x => p x * deriv u x) t - q t * u t - f t) * η t) =
      (∫ t in a..b, deriv (fun x => p x * deriv u x) t * η t) -
        (∫ t in a..b, q t * u t * η t) - (∫ t in a..b, f t * η t) := by
    rw [← intervalIntegral.integral_sub hD hB,
      ← intervalIntegral.integral_sub (hD.sub hB) hC]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB, hibp', hr]
  ring

/-- Fundamental lemma of the calculus of variations on `[a, b]`, for a continuous
function tested against `C¹` variations vanishing at both ends. -/
lemma apm_m95A03_solves_of_isMinOn_aux_fundamental
    (a b : ℝ) (hab : a < b) (R : ℝ → ℝ) (hR : Continuous R)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      (∫ t in a..b, R t * η t) = 0) :
    ∀ t ∈ Set.Icc a b, R t = 0 := by
  have hloc : MeasureTheory.LocallyIntegrableOn R (Set.Ioo a b) :=
    (hR.locallyIntegrable (μ := MeasureTheory.MeasureSpace.volume)).locallyIntegrableOn _
  have hae : ∀ᵐ t ∂MeasureTheory.MeasureSpace.volume,
      t ∈ Set.Ioo a b → R t = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
      intro g hg hgc hgs
      have hga : g a = 0 := by
        by_contra hga
        have ha_supp : a ∈ Function.support g := by simpa [Function.mem_support]
        have haU := hgs (subset_closure ha_supp)
        exact (not_lt_of_ge le_rfl) haU.1
      have hgb : g b = 0 := by
        by_contra hgb
        have hb_supp : b ∈ Function.support g := by simpa [Function.mem_support]
        have hbU := hgs (subset_closure hb_supp)
        exact (not_lt_of_ge le_rfl) hbU.2
      have hsupp : Function.support (fun t => R t * g t) ⊆ Set.Ioc a b := by
        intro t ht
        have htg : t ∈ Function.support g :=
          (Function.support_mul R g ▸ ht).2
        have htU := hgs (subset_closure htg)
        exact ⟨htU.1, htU.2.le⟩
      have hz := h g (hg.of_le (by norm_num)) hga hgb
      rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp] at hz
      simpa [smul_eq_mul, mul_comm] using hz)
  have hae' : R =ᵐ[(MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioo a b)] (0 : ℝ → ℝ) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
    simpa only [Pi.zero_apply] using hae
  have hinterior : Set.EqOn R 0 (Set.Ioo a b) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hR.continuousOn
      continuous_zero.continuousOn
  have hclosed : Set.EqOn R 0 (Set.Icc a b) := hinterior.of_subset_closure
    hR.continuousOn continuous_zero.continuousOn Set.Ioo_subset_Icc_self (by
      rw [closure_Ioo hab.ne])
  exact hclosed

theorem apm_m95A03_solves_of_isMinOn
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hu2 : ContDiff ℝ 2 u) (hua : u a = α) (hub : u b = β)
    (hmin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b α β) u) :
    apm_m95A03_solves a b α β p q f u := by
  refine ⟨hu2, hua, hub, fun t ht => ?_⟩
  have hR := apm_m95A03_solves_of_isMinOn_aux_residual_continuous p q f u hp hq hf hu2
  have hzero := apm_m95A03_solves_of_isMinOn_aux_fundamental a b hab _ hR (fun η hη hηa hηb => by
    have h1 := apm_m95A03_solves_of_isMinOn_aux_first_variation a b α β hab p q f u hp hq hf hu2 hua hub hmin
      η hη hηa hηb
    rw [apm_m95A03_solves_of_isMinOn_aux_ibp a b hab p q f u hp hq hf hu2 η hη hηa hηb, neg_eq_zero] at h1
    exact h1) t ht
  linarith

theorem apm_m95A03_homogenization
    (a b α β : ℝ) (hab : a < b) (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    let w := apm_m95A03_boundaryLift a b α β
    apm_m95A03_solves a b α β p q f u ↔
      apm_m95A03_solves a b 0 0 p q
        (apm_m95A03_modifiedRHS p q f w) (u - w) := by
  dsimp only
  let w := apm_m95A03_boundaryLift a b α β
  have hab0 : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hw : ContDiff ℝ ⊤ w := by
    change ContDiff ℝ ⊤ (fun t : ℝ => α + (β - α) * ((t - a) / (b - a)))
    fun_prop
  have hwa : w a = α := by
    simp [w, apm_m95A03_boundaryLift, hab0]
  have hwb : w b = β := by
    simp [w, apm_m95A03_boundaryLift, hab0]
  have hw_succ : ContDiff ℝ (1 + 1) w := hw.of_le le_top
  have hdw : ContDiff ℝ 1 (deriv w) := hw_succ.deriv'
  constructor
  · rintro ⟨hu, hua, hub, heq⟩
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    have hv : ContDiff ℝ 2 (u - w) := hu.sub (hw.of_le le_top)
    refine ⟨hv, ?_, ?_, ?_⟩
    · change u a - w a = 0
      rw [hua, hwa]
      ring
    · change u b - w b = 0
      rw [hub, hwb]
      ring
    · intro t ht
      have hdu (x : ℝ) : deriv (u - w) x = deriv u x - deriv w x := by
        exact deriv_sub (hu1.differentiable (by norm_num) x) (hw.differentiable (by simp) x)
      have hflux : (fun x => p x * deriv (u - w) x) =
          (fun x => p x * deriv u x) - (fun x => p x * deriv w x) := by
        funext x
        simp [hdu x, mul_sub]
      have hpu : Differentiable ℝ (fun x => p x * deriv u x) :=
        (hp.mul hu.deriv').differentiable (by norm_num)
      have hpw : Differentiable ℝ (fun x => p x * deriv w x) :=
        (hp.mul hdw).differentiable (by norm_num)
      rw [hflux, deriv_sub (hpu t) (hpw t)]
      simp only [Pi.sub_apply, apm_m95A03_modifiedRHS]
      linarith [heq t ht]
  · rintro ⟨hv, hva, hvb, heq⟩
    have hw2 : ContDiff ℝ 2 w := hw.of_le le_top
    have hu : ContDiff ℝ 2 u := by
      have huv : u = (u - w) + w := by ext x; simp
      rw [huv]
      exact hv.add hw2
    refine ⟨hu, ?_, ?_, ?_⟩
    · change u a - w a = 0 at hva
      linarith
    · change u b - w b = 0 at hvb
      linarith
    · intro t ht
      have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
      have hdu (x : ℝ) : deriv (u - w) x = deriv u x - deriv w x := by
        exact deriv_sub (hu1.differentiable (by norm_num) x) (hw.differentiable (by simp) x)
      have hflux : (fun x => p x * deriv (u - w) x) =
          (fun x => p x * deriv u x) - (fun x => p x * deriv w x) := by
        funext x
        simp [hdu x, mul_sub]
      have hpu : Differentiable ℝ (fun x => p x * deriv u x) :=
        (hp.mul hu.deriv').differentiable (by norm_num)
      have hpw : Differentiable ℝ (fun x => p x * deriv w x) :=
        (hp.mul hdw).differentiable (by norm_num)
      have h := heq t ht
      rw [hflux, deriv_sub (hpu t) (hpw t)] at h
      simp only [Pi.sub_apply, apm_m95A03_modifiedRHS] at h
      linarith

/-- Initial value problem for the linear equation `(p y')' - q y = g` on `[a, b]`, with a
global `C²` solution (solve on `[a, b]`, extend past the endpoints by second-order Taylor
polynomials). -/
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_p_pos
    (a b p₀ : ℝ) (hp₀ : 0 < p₀) (p : ℝ → ℝ)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t) :
    ∀ t ∈ Set.Icc a b, 0 < p t := by
  intro t ht
  exact lt_of_lt_of_le hp₀ (hp_lower t ht)

lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_p_ne
    (a b p₀ : ℝ) (hp₀ : 0 < p₀) (p : ℝ → ℝ)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t) :
    ∀ t ∈ Set.Icc a b, p t ≠ 0 := by
  intro t ht
  exact (apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_p_pos
    a b p₀ hp₀ p hp_lower t ht).ne'

lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_inv_continuousOn
    (a b p₀ : ℝ) (hp₀ : 0 < p₀) (p : ℝ → ℝ) (hp : Continuous p)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t) :
    ContinuousOn (fun t => (p t)⁻¹) (Set.Icc a b) := by
  exact hp.continuousOn.inv₀
    (apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_p_ne
      a b p₀ hp₀ p hp_lower)

/-- The first-order system `y' = z / p, z' = q y + g` has a solution on `[a, b]` with any
initial data (linear system with continuous coefficients: Picard iteration / Grönwall). -/
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_system
    (a b : ℝ) (hab : a < b) (p q g : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hg : Continuous g) (hpos : ∀ t ∈ Set.Icc a b, 0 < p t)
    (c₀ d₀ : ℝ) :
    ∃ y z : ℝ → ℝ, y a = c₀ ∧ z a = d₀ ∧ ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt y (z t / p t) (Set.Icc a b) t ∧
      HasDerivWithinAt z (q t * y t + g t) (Set.Icc a b) t := by
  sorry

/-- A solution of the system on `[a, b]` is the restriction of a global `C²` function `Y`
with `p Y' = z` there (`y` is `C²` on `[a, b]`; extend past the endpoints by second-order
Taylor polynomials). -/
-- BEGIN SEAT AREA
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_extend
    (a b : ℝ) (hab : a < b) (p q g : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hg : Continuous g) (hpos : ∀ t ∈ Set.Icc a b, 0 < p t)
    (y z : ℝ → ℝ) (hsys : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt y (z t / p t) (Set.Icc a b) t ∧
      HasDerivWithinAt z (q t * y t + g t) (Set.Icc a b) t) :
    ∃ Y : ℝ → ℝ, ContDiff ℝ 2 Y ∧ ∀ t ∈ Set.Icc a b, Y t = y t ∧ p t * deriv Y t = z t := by
  sorry
-- END SEAT AREA

/-- The equation on `[a, b]` for a global `C²` function whose flux `p Y'` agrees there with a
solution `z` of `z' = q Y + g`. -/
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_equation
    (a b : ℝ) (hab : a < b) (p q g : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (Y z : ℝ → ℝ) (hY : ContDiff ℝ 2 Y)
    (hYz : ∀ t ∈ Set.Icc a b, p t * deriv Y t = z t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivWithinAt z (q t * Y t + g t) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, deriv (fun x => p x * deriv Y x) t - q t * Y t = g t := by
  sorry

lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (hq : Continuous q)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (g : ℝ → ℝ) (hg : Continuous g) (c₀ c₁ : ℝ) :
    ∃ y : ℝ → ℝ, ContDiff ℝ 2 y ∧ y a = c₀ ∧ deriv y a = c₁ ∧
      ∀ t ∈ Set.Icc a b, deriv (fun x => p x * deriv y x) t - q t * y t = g t := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < p t := fun t ht => lt_of_lt_of_le hp₀ (hp_lower t ht)
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨y, z, hya, hza, hsys⟩ :=
    apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_system a b hab p q g hp hq hg hpos c₀ (p a * c₁)
  obtain ⟨Y, hY, hYy⟩ := apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_extend a b hab p q g hp hq hg hpos y z hsys
  refine ⟨Y, hY, by rw [(hYy a ha).1, hya], ?_, ?_⟩
  · have h1 := (hYy a ha).2
    rw [hza] at h1
    exact mul_left_cancel₀ (hpos a ha).ne' h1
  · refine apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp_aux_equation a b hab p q g hp Y z hY (fun t ht => (hYy t ht).2)
      (fun t ht => ?_)
    rw [(hYy t ht).1]
    exact (hsys t ht).2

/-- The homogeneous Dirichlet problem has only the zero solution (energy identity). -/
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_homogeneous_unique
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (hq : Continuous q)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y) (hya : y a = 0) (hyb : y b = 0)
    (heq : ∀ t ∈ Set.Icc a b, deriv (fun x => p x * deriv y x) t - q t * y t = 0) :
    ∀ t ∈ Set.Icc a b, y t = 0 := by
  let g : ℝ → ℝ := fun x ↦ p x * deriv y x
  have hy' : ContDiff ℝ 1 (deriv y) := hy.deriv'
  have hg : ContDiff ℝ 1 g := hp.mul hy'
  have hdg : Continuous (deriv g) := hg.continuous_deriv_one
  have hdy : Continuous (deriv y) := hy'.continuous
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := g) (v := y) (u' := deriv g) (v' := deriv y)
    (fun x _ ↦ (hg.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ ↦ (hy.differentiable (by norm_num) x).hasDerivAt)
    (hdg.intervalIntegrable _ _) (hdy.intervalIntegrable _ _)
  have henergy : (∫ x in a..b,
      p x * (deriv y x) ^ 2 + q x * (y x) ^ 2) = 0 := by
    have hibp' : (∫ x in a..b, g x * deriv y x) =
        -(∫ x in a..b, deriv g x * y x) := by
      simpa [hya, hyb] using hibp
    have hcont1 : Continuous (fun x ↦ g x * deriv y x) := hg.continuous.mul hdy
    have hcont2 : Continuous (fun x ↦ deriv g x * y x) := hdg.mul hy.continuous
    have hz : (∫ x in a..b, g x * deriv y x + deriv g x * y x) = 0 := by
      rw [intervalIntegral.integral_add (hcont1.intervalIntegrable a b)
        (hcont2.intervalIntegrable a b)]
      linarith
    rw [← hz]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc a b := Set.uIcc_of_le hab.le ▸ hx
    have he := heq x hx'
    dsimp [g]
    rw [show deriv (fun z => p z * deriv y z) x = q x * y x by linarith]
    ring
  let E : ℝ → ℝ := fun x ↦ p x * (deriv y x) ^ 2 + q x * (y x) ^ 2
  have hEc : Continuous E := by
    dsimp [E]
    fun_prop
  have hEnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ E x := by
    intro x hx
    dsimp [E]
    have hp_pos : 0 ≤ p x := le_trans hp₀.le (hp_lower x hx)
    exact add_nonneg (mul_nonneg hp_pos (sq_nonneg _))
      (mul_nonneg (hq_nonneg x hx) (sq_nonneg _))
  have hEae : E =ᵐ[MeasureTheory.volume.restrict (Set.Ioc a b)] 0 := by
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a b)] E := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact hEnonneg x ⟨hx.1.le, hx.2⟩
    exact (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le hnn
      (hEc.intervalIntegrable a b)).mp henergy
  have hEae' : E =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] 0 := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    exact hEae
  have hEpoint : Set.EqOn E 0 (Set.Icc a b) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq MeasureTheory.volume hab.ne hEae'
      hEc.continuousOn continuous_zero.continuousOn
  have hdyzero : ∀ x ∈ Set.Icc a b, deriv y x = 0 := by
    intro x hx
    have hz := hEpoint hx
    have hp_pos : 0 < p x := lt_of_lt_of_le hp₀ (hp_lower x hx)
    have hq0 := hq_nonneg x hx
    dsimp [E] at hz
    have hfirst : 0 ≤ p x * deriv y x ^ 2 :=
      mul_nonneg hp_pos.le (sq_nonneg _)
    have hsecond : 0 ≤ q x * y x ^ 2 := mul_nonneg hq0 (sq_nonneg _)
    have hzero : p x * deriv y x ^ 2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hp_pos))
  have hconst : ∀ x ∈ Set.Icc a b, y x = y a := by
    apply constant_of_has_deriv_right_zero hy.continuous.continuousOn
    intro x hx
    have hxa : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    simpa [hdyzero x hxa] using
      (hy.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt
  intro x hx
  rw [hconst x hx, hya]

/-- Shooting: a particular solution with `y₀ a = 0` minus a multiple of the homogeneous
solution with `y₁ a = 0, y₁' a = 1` (which has `y₁ b ≠ 0`). -/
lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_shooting
    (a b : ℝ) (hab : a < b) (p q f : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (y₀ y₁ : ℝ → ℝ) (h₀ : ContDiff ℝ 2 y₀) (h₁ : ContDiff ℝ 2 y₁)
    (h₀a : y₀ a = 0) (h₁a : y₁ a = 0) (h₁b : y₁ b ≠ 0)
    (e₀ : ∀ t ∈ Set.Icc a b, deriv (fun x => p x * deriv y₀ x) t - q t * y₀ t = f t)
    (e₁ : ∀ t ∈ Set.Icc a b, deriv (fun x => p x * deriv y₁ x) t - q t * y₁ t = 0) :
    ∃ u : ℝ → ℝ, apm_m95A03_solves a b 0 0 p q f u := by
  let c : ℝ := y₀ b / y₁ b
  let u : ℝ → ℝ := fun x => y₀ x - c * y₁ x
  have hu : ContDiff ℝ 2 u := by
    simpa [u, smul_eq_mul] using h₀.sub (h₁.const_smul c)
  have hua : u a = 0 := by simp [u, c, h₀a, h₁a]
  have hub : u b = 0 := by
    simp [u, c]
    field_simp
    ring
  refine ⟨u, hu, hua, hub, ?_⟩
  intro t ht
  have hdy (x : ℝ) : deriv u x = deriv y₀ x - c * deriv y₁ x := by
    have hd := (h₀.differentiable (by norm_num) x).hasDerivAt.sub
      (HasDerivAt.const_mul c (h₁.differentiable (by norm_num) x).hasDerivAt)
    simpa [u, Pi.sub_apply] using hd.deriv
  have hflux : (fun x => p x * deriv u x) =
      (fun x => p x * deriv y₀ x - c * (p x * deriv y₁ x)) := by
    funext x
    simp [hdy, mul_sub]
    ring
  have hd₀ : DifferentiableAt ℝ (fun x => p x * deriv y₀ x) t :=
    (hp.mul h₀.deriv').differentiable (by norm_num) t
  have hd₁ : DifferentiableAt ℝ (fun x => p x * deriv y₁ x) t :=
    (hp.mul h₁.deriv').differentiable (by norm_num) t
  have hdflux : deriv (fun x => p x * deriv y₀ x - c * (p x * deriv y₁ x)) t =
      deriv (fun x => p x * deriv y₀ x) t -
        c * deriv (fun x => p x * deriv y₁ x) t := by
    have hd := hd₀.hasDerivAt.sub (HasDerivAt.const_mul c hd₁.hasDerivAt)
    simpa [Pi.sub_apply] using hd.deriv
  rw [hflux, hdflux]
  dsimp [u]
  have he₀ := e₀ t ht
  have he₁ := e₁ t ht
  linear_combination he₀ - c * he₁

lemma apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t) :
    ∃ u : ℝ → ℝ, apm_m95A03_solves a b 0 0 p q f u := by
  obtain ⟨y₀, h₀, h₀a, -, e₀⟩ :=
    apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp a b p₀ hab hp₀ p q hp hq hp_lower f hf 0 0
  obtain ⟨y₁, h₁, h₁a, h₁a', e₁⟩ :=
    apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_ivp a b p₀ hab hp₀ p q hp hq hp_lower 0 continuous_const 0 1
  refine apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_shooting a b hab p q f hp y₀ y₁ h₀ h₁ h₀a h₁a ?_ e₀ e₁
  intro h₁b
  have hz := apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves_aux_homogeneous_unique a b p₀ hab hp₀ p q hp hq hp_lower hq_nonneg
    y₁ h₁ h₁a h₁b e₁
  -- y₁ vanishes on [a, b], so its right derivative at a is 0, contradicting y₁' a = 1.
  have hd : HasDerivWithinAt y₁ 0 (Set.Icc a b) a := by
    have : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Icc a b) a := hasDerivWithinAt_const _ _ _
    exact this.congr (fun t ht => hz t ht) (hz a ⟨le_rfl, hab.le⟩)
  have hd' : HasDerivWithinAt y₁ 1 (Set.Icc a b) a := by
    rw [← h₁a']
    exact (h₁.differentiable (by norm_num) a).hasDerivAt.hasDerivWithinAt
  have := ((uniqueDiffOn_Icc hab) a ⟨le_rfl, hab.le⟩).eq_deriv _ hd hd'
  norm_num at this

theorem apm_m95A03_exists_homogeneous_minimizer
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧
      u ∈ apm_m95A03_admissible a b 0 0 ∧
      IsMinOn (apm_m95A03_energy a b p q f)
        (apm_m95A03_admissible a b 0 0) u := by
  obtain ⟨u, hu⟩ :=
    apm_m95A03_exists_homogeneous_minimizer_aux_exists_solves
      a b p₀ hab hp₀ p q f hp hq hf hp_lower hq_nonneg
  refine ⟨u, hu.1, ⟨hu.1.of_le (by norm_num), hu.2.1, hu.2.2.1⟩, ?_⟩
  exact apm_m95A03_isMinOn_of_solves a b 0 0 p₀ hab hp₀ p q f u
    hp hq hf hp_lower hq_nonneg hu

theorem apm_m95A03_minimizers_eqOn
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u v : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (huadm : u ∈ apm_m95A03_admissible a b 0 0)
    (humin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b 0 0) u)
    (hvadm : v ∈ apm_m95A03_admissible a b 0 0)
    (hvmin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b 0 0) v) :
    Set.EqOn v u (Set.Icc a b) := by
  sorry

theorem apm_m95a03
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f : ℝ → ℝ)
    (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t) :
    (∀ u : ℝ → ℝ,
      ContDiff ℝ 2 u → u a = α → u b = β →
      (apm_m95A03_solves a b α β p q f u ↔
        IsMinOn (apm_m95A03_energy a b p q f)
          (apm_m95A03_admissible a b α β) u)) ∧
    (∀ u : ℝ → ℝ,
      let w := apm_m95A03_boundaryLift a b α β
      apm_m95A03_solves a b α β p q f u ↔
        apm_m95A03_solves a b 0 0 p q
          (apm_m95A03_modifiedRHS p q f w) (u - w)) ∧
    ∃ u : ℝ → ℝ,
      ContDiff ℝ 2 u ∧
      u ∈ apm_m95A03_admissible a b 0 0 ∧
      IsMinOn (apm_m95A03_energy a b p q f)
        (apm_m95A03_admissible a b 0 0) u ∧
      ∀ v : ℝ → ℝ,
        v ∈ apm_m95A03_admissible a b 0 0 →
        IsMinOn (apm_m95A03_energy a b p q f)
          (apm_m95A03_admissible a b 0 0) v →
        Set.EqOn v u (Set.Icc a b) := by
  constructor
  · intro u hu2 hua hub
    constructor
    · exact apm_m95A03_isMinOn_of_solves a b α β p₀ hab hp₀ p q f u
        hp hq hf hp_lower hq_nonneg
    · exact apm_m95A03_solves_of_isMinOn a b α β p₀ hab hp₀ p q f u
        hp hq hf hp_lower hq_nonneg hu2 hua hub
  constructor
  · exact fun u => apm_m95A03_homogenization a b α β hab p q f u hp
  · obtain ⟨u, hu2, huadm, humin⟩ :=
      apm_m95A03_exists_homogeneous_minimizer a b p₀ hab hp₀ p q f
        hp hq hf hp_lower hq_nonneg
    refine ⟨u, hu2, huadm, humin, ?_⟩
    intro v hvadm hvmin
    exact apm_m95A03_minimizers_eqOn a b p₀ hab hp₀ p q f u v hp hq hf
      hp_lower hq_nonneg huadm humin hvadm hvmin

#print axioms apm_m95a03
