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
  sorry

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
  sorry

theorem apm_m95A03_minimizers_eqOn
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u v : ℝ → ℝ)
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
    exact apm_m95A03_minimizers_eqOn a b p₀ hab hp₀ p q f u v
      hp_lower hq_nonneg huadm humin hvadm hvmin

#print axioms apm_m95a03
