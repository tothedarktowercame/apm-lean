import Mathlib

/-!
# APM m98J04

## Statement repairs

The source does not state regularity assumptions. The Euler--Lagrange part is
minimally stated for a `C²` Lagrangian and a `C²` stationary curve, while the
arc-length minimization ranges over `C¹` graph curves. The two endpoints are
assumed to have distinct horizontal coordinates, ordered as `a < b`, as is
required by the graph parametrization used in the question.

## Encoding questions

Stationarity means vanishing first variation against every `C¹` variation
which fixes both endpoints. Partial derivatives of the Lagrangian are encoded
as ordinary derivatives with the other two arguments held fixed.
-/

open Set intervalIntegral

/-- The variational functional associated to a first-order Lagrangian. -/
noncomputable def apm_m98J04_functional
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, F x (y x) (deriv y x)

/-- Vanishing first variation under endpoint-fixing variations. -/
def apm_m98J04_stationary
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
    HasDerivAt
      (fun t ↦ apm_m98J04_functional F a b (fun x ↦ y x + t * η x)) 0 0

/-- The pointwise Euler--Lagrange equation along a curve. -/
def apm_m98J04_eulerLagrange
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioo a b,
    HasDerivAt
      (fun t ↦ deriv (fun p ↦ F t (y t) p) (deriv y t))
      (deriv (fun q ↦ F x q (deriv y x)) (y x)) x

/-- Length of a plane curve presented as a graph. -/
noncomputable def apm_m98J04_arcLength (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, Real.sqrt (1 + (deriv y x) ^ 2)

/-- The line graph joining `(a, α)` and `(b, β)`. -/
noncomputable def apm_m98J04_line (a b α β : ℝ) (x : ℝ) : ℝ :=
  α + ((β - α) / (b - a)) * (x - a)

/-- `C¹` graph curves with the prescribed endpoints. -/
def apm_m98J04_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y a = α ∧ y b = β}

lemma apm_m98J04_hasDerivAt_deriv_of_contDiff
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt

lemma apm_m98J04_contDiff_partial_position
    {L : ℝ → ℝ → ℝ} (p : ℝ)
    (hL : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ L z.1 z.2)) :
    ContDiff ℝ 2 (fun q : ℝ ↦ L q p) := by
  exact hL.comp (contDiff_id.prodMk contDiff_const)

/-- Fixing the position coordinate preserves the regularity of a Lagrangian. -/
lemma apm_m98J04_contDiff_partial_velocity
    {L : ℝ → ℝ → ℝ} (q : ℝ)
    (hL : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ L z.1 z.2)) :
    ContDiff ℝ 2 (fun p : ℝ ↦ L q p) := by
  exact hL.comp (contDiff_const.prodMk contDiff_id)

/-- Both ordinary partial derivatives occurring in the frozen statement are
genuine derivatives under its `C²` hypothesis. -/
lemma apm_m98J04_hasDerivAt_partials
    {L : ℝ → ℝ → ℝ} (q p : ℝ)
    (hL : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ L z.1 z.2)) :
    HasDerivAt (fun r : ℝ ↦ L r p) (deriv (fun r : ℝ ↦ L r p) q) q ∧
      HasDerivAt (fun r : ℝ ↦ L q r) (deriv (fun r : ℝ ↦ L q r) p) p := by
  constructor
  · exact ((apm_m98J04_contDiff_partial_position p hL).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  · exact ((apm_m98J04_contDiff_partial_velocity q hL).differentiable
      (by norm_num)).differentiableAt.hasDerivAt

/-- Two-variable chain rule expressed using ordinary partial `deriv`s. -/
lemma apm_m98J04_hasDerivAt_comp₂
    {g : ℝ × ℝ → ℝ} {u v : ℝ → ℝ} {x u' v' : ℝ}
    (hg : DifferentiableAt ℝ g (u x, v x))
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun t ↦ g (u t, v t))
      (deriv (fun q ↦ g (q, v x)) (u x) * u' +
        deriv (fun p ↦ g (u x, p)) (v x) * v') x := by
  let G := fderiv ℝ g (u x, v x)
  have hG : HasFDerivAt g G (u x, v x) := hg.hasFDerivAt
  have hcomp : HasDerivAt (fun t ↦ g (u t, v t)) (G (u', v')) x :=
    by
      simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        (hG.comp x (hu.prodMk hv).hasFDerivAt).hasDerivAt
  have hq : deriv (fun q ↦ g (q, v x)) (u x) = G (1, 0) :=
    by
      simpa only [Function.comp_apply, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        (hG.comp (u x) (((hasDerivAt_id (u x)).prodMk
          (hasDerivAt_const (x := u x) (v x))).hasFDerivAt)).hasDerivAt.deriv
  have hp : deriv (fun p ↦ g (u x, p)) (v x) = G (0, 1) :=
    by
      simpa only [Function.comp_apply, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        (hG.comp (v x) (((hasDerivAt_const (x := v x) (u x)).prodMk
          (hasDerivAt_id (v x))).hasFDerivAt)).hasDerivAt.deriv
  convert hcomp using 1
  rw [hq, hp]
  have huv : (u', v') = u' • (1, 0) + v' • (0, 1) := by
    ext <;> simp
  rw [huv, map_add, map_smul, map_smul]
  simp [smul_eq_mul]
  ring

/-- The velocity partial is the Fréchet derivative in the second basis
direction. This bridge lets `ContDiff` machinery reason about the ordinary
`deriv` presentation used by the problem statement. -/
lemma apm_m98J04_partial_velocity_eq_fderiv
    {L : ℝ → ℝ → ℝ} (z : ℝ × ℝ)
    (hL : ContDiff ℝ 2 (fun w : ℝ × ℝ ↦ L w.1 w.2)) :
    deriv (fun p : ℝ ↦ L z.1 p) z.2 =
      fderiv ℝ (fun w : ℝ × ℝ ↦ L w.1 w.2) z (0, 1) := by
  let g : ℝ × ℝ → ℝ := fun w ↦ L w.1 w.2
  let G := fderiv ℝ g z
  have hG : HasFDerivAt g G z :=
    (hL.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  simpa only [g, G, Function.comp_apply, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    (hG.comp z.2 (((hasDerivAt_const (x := z.2) z.1).prodMk
      (hasDerivAt_id z.2)).hasFDerivAt)).hasDerivAt.deriv

/-- Under a `C²` hypothesis the velocity partial is jointly `C¹`. -/
lemma apm_m98J04_contDiff_velocity_partial
    {L : ℝ → ℝ → ℝ}
    (hL : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ L z.1 z.2)) :
    ContDiff ℝ 1
      (fun z : ℝ × ℝ ↦ deriv (fun p : ℝ ↦ L z.1 p) z.2) := by
  have hf : ContDiff ℝ 1
      (fun z : ℝ × ℝ ↦
        fderiv ℝ (fun w : ℝ × ℝ ↦ L w.1 w.2) z (0, 1)) :=
    (hL.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  convert hf using 1
  funext z
  exact apm_m98J04_partial_velocity_eq_fderiv z hL

/-- Beltrami's identity for a smooth autonomous Lagrangian. -/
lemma apm_m98J04_beltrami
    (L : ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ L z.1 z.2))
    (hy : ContDiff ℝ 2 y)
    (hEL : apm_m98J04_eulerLagrange (fun _ ↦ L) a b y) :
    ∀ x ∈ Ioo a b,
      HasDerivAt
        (fun t ↦ L (y t) (deriv y t) -
          deriv y t * deriv (fun p ↦ L (y t) p) (deriv y t)) 0 x := by
  intro x hx
  have hy1 : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hdy : HasDerivAt y (deriv y x) x :=
    apm_m98J04_hasDerivAt_deriv_of_contDiff hy1 x
  have hddy : HasDerivAt (deriv y) (deriv (deriv y) x) x :=
    (hy.differentiable_deriv_two x).hasDerivAt
  have hA : HasDerivAt (fun t ↦ L (y t) (deriv y t))
      (deriv (fun q ↦ L q (deriv y x)) (y x) * deriv y x +
        deriv (fun p ↦ L (y x) p) (deriv y x) * deriv (deriv y) x) x :=
    apm_m98J04_hasDerivAt_comp₂
      ((hL.differentiable (by norm_num)).differentiableAt) hdy hddy
  have hP : HasDerivAt
      (fun t ↦ deriv (fun p ↦ L (y t) p) (deriv y t))
      (deriv (fun q ↦ L q (deriv y x)) (y x)) x := by
    simpa [apm_m98J04_eulerLagrange] using hEL x hx
  convert hA.sub (hddy.mul hP) using 1
  ring

/-- Spatial differentiation commutes with the affine variations used in the
stationarity predicate. -/
lemma apm_m98J04_deriv_affine_variation
    {y η : ℝ → ℝ} (hy : Differentiable ℝ y) (hη : Differentiable ℝ η)
    (t x : ℝ) :
    deriv (fun z ↦ y z + t * η z) x = deriv y x + t * deriv η x := by
  simpa only [Pi.add_apply, Pi.mul_apply, zero_mul, zero_add] using
    ((hy x).hasDerivAt.add
      ((hasDerivAt_const (x := x) t).mul (hη x).hasDerivAt)).deriv

/-- A fixed-`x` slice of a smooth three-variable Lagrangian is smooth in its
position and velocity coordinates. -/
lemma apm_m98J04_contDiff_lagrangian_slice
    {F : ℝ → ℝ → ℝ → ℝ} (x : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2)) :
    ContDiff ℝ 2 (fun z : ℝ × ℝ ↦ F x z.1 z.2) := by
  exact hF.comp (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))

/-- Pointwise derivative of the Lagrangian along an affine variation. -/
lemma apm_m98J04_hasDerivAt_lagrangian_variation
    {F : ℝ → ℝ → ℝ → ℝ} {x y p η η' : ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2)) :
    HasDerivAt (fun t ↦ F x (y + t * η) (p + t * η'))
      (deriv (fun q ↦ F x q p) y * η +
        deriv (fun r ↦ F x y r) p * η') 0 := by
  let g : ℝ × ℝ → ℝ := fun z ↦ F x z.1 z.2
  have hg : DifferentiableAt ℝ g (y, p) :=
    ((apm_m98J04_contDiff_lagrangian_slice x hF).differentiable
      (by norm_num)).differentiableAt
  have hy : HasDerivAt (fun t : ℝ ↦ y + t * η) η 0 := by
    convert (hasDerivAt_const (x := 0) y).add
      ((hasDerivAt_id 0).mul_const η) using 1
    ring
  have hp : HasDerivAt (fun t : ℝ ↦ p + t * η') η' 0 := by
    convert (hasDerivAt_const (x := 0) p).add
      ((hasDerivAt_id 0).mul_const η') using 1
    ring
  have hg' : DifferentiableAt ℝ g (y + 0 * η, p + 0 * η') := by
    simpa using hg
  simpa [g] using apm_m98J04_hasDerivAt_comp₂ hg' hy hp

/-- Pointwise first-variation formula, including transport through the spatial
`deriv` in the functional's actual integrand. -/
lemma apm_m98J04_hasDerivAt_variation_integrand
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (x : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    HasDerivAt
      (fun t ↦ F x (y x + t * η x)
        (deriv (fun z ↦ y z + t * η z) x))
      (deriv (fun q ↦ F x q (deriv y x)) (y x) * η x +
        deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x) 0 := by
  have hy' : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hη' : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hpoint := apm_m98J04_hasDerivAt_lagrangian_variation
    (x := x) (y := y x) (p := deriv y x) (η := η x) (η' := deriv η x) hF
  convert hpoint using 1
  funext t
  rw [apm_m98J04_deriv_affine_variation hy' hη' t x]

/-- The two partial derivatives of a `C²` three-variable Lagrangian, viewed
jointly as functions of all three coordinates, are `C¹`. -/
lemma apm_m98J04_contDiff_lagrangian_partials
    {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2)) :
    ContDiff ℝ 1
        (fun z : ℝ × ℝ × ℝ ↦ deriv (fun q ↦ F z.1 q z.2.2) z.2.1) ∧
      ContDiff ℝ 1
        (fun z : ℝ × ℝ × ℝ ↦ deriv (fun p ↦ F z.1 z.2.1 p) z.2.2) := by
  let g : ℝ × ℝ × ℝ → ℝ := fun z ↦ F z.1 z.2.1 z.2.2
  have hD : ContDiff ℝ 1 (fderiv ℝ g) := hF.fderiv_right (m := 1) (by norm_num)
  have hqF : ContDiff ℝ 1 (fun z ↦ fderiv ℝ g z (0, (1, 0))) :=
    hD.clm_apply contDiff_const
  have hpF : ContDiff ℝ 1 (fun z ↦ fderiv ℝ g z (0, (0, 1))) :=
    hD.clm_apply contDiff_const
  have hq (z : ℝ × ℝ × ℝ) :
      deriv (fun q ↦ F z.1 q z.2.2) z.2.1 = fderiv ℝ g z (0, (1, 0)) := by
    have hg : HasFDerivAt g (fderiv ℝ g z) z :=
      (hF.differentiable (by norm_num) z).hasFDerivAt
    simpa only [g, Function.comp_apply, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hg.comp z.2.1 (((hasDerivAt_const (x := z.2.1) z.1).prodMk
        ((hasDerivAt_id z.2.1).prodMk
          (hasDerivAt_const (x := z.2.1) z.2.2))).hasFDerivAt)).hasDerivAt.deriv
  have hp (z : ℝ × ℝ × ℝ) :
      deriv (fun p ↦ F z.1 z.2.1 p) z.2.2 = fderiv ℝ g z (0, (0, 1)) := by
    have hg : HasFDerivAt g (fderiv ℝ g z) z :=
      (hF.differentiable (by norm_num) z).hasFDerivAt
    simpa only [g, Function.comp_apply, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hg.comp z.2.2 (((hasDerivAt_const (x := z.2.2) z.1).prodMk
        ((hasDerivAt_const (x := z.2.2) z.2.1).prodMk
          (hasDerivAt_id z.2.2))).hasFDerivAt)).hasDerivAt.deriv
  constructor
  · convert hqF using 1
    funext z
    exact hq z
  · convert hpF using 1
    funext z
    exact hp z

/-- Along a `C²` curve, both Lagrangian partials in the first-variation
density are continuous (indeed `C¹`). -/
lemma apm_m98J04_contDiff_partials_along_curve
    {F : ℝ → ℝ → ℝ → ℝ} {y : ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 1
        (fun x ↦ deriv (fun q ↦ F x q (deriv y x)) (y x)) ∧
      ContDiff ℝ 1
        (fun x ↦ deriv (fun p ↦ F x (y x) p) (deriv y x)) := by
  have hy1 : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hdy1 : ContDiff ℝ 1 (deriv y) := hy.deriv'
  have hz : ContDiff ℝ 1 (fun x : ℝ ↦ (x, (y x, deriv y x))) :=
    contDiff_id.prodMk (hy1.prodMk hdy1)
  constructor
  · exact (apm_m98J04_contDiff_lagrangian_partials hF).1.comp hz
  · exact (apm_m98J04_contDiff_lagrangian_partials hF).2.comp hz

/-- The first-variation density is continuous and hence interval integrable. -/
lemma apm_m98J04_first_variation_intervalIntegrable
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    IntervalIntegrable
      (fun x ↦ deriv (fun q ↦ F x q (deriv y x)) (y x) * η x +
        deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x)
      MeasureTheory.volume a b := by
  have hp := apm_m98J04_contDiff_partials_along_curve hF hy
  exact ((hp.1.continuous.mul hη.continuous).add
    (hp.2.continuous.mul hη.continuous_deriv_one)).intervalIntegrable a b

/-- The derivative density remains continuous when the variation parameter is
allowed to move. This is the compactness input for domination. -/
lemma apm_m98J04_continuous_first_variation_family
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    Continuous (fun z : ℝ × ℝ ↦
      deriv
          (fun q ↦ F z.2 q (deriv y z.2 + z.1 * deriv η z.2))
          (y z.2 + z.1 * η z.2) * η z.2 +
        deriv
          (fun p ↦ F z.2 (y z.2 + z.1 * η z.2) p)
          (deriv y z.2 + z.1 * deriv η z.2) * deriv η z.2) := by
  have cη : Continuous (fun z : ℝ × ℝ ↦ η z.2) :=
    hη.continuous.comp continuous_snd
  have cdη : Continuous (fun z : ℝ × ℝ ↦ deriv η z.2) :=
    hη.continuous_deriv_one.comp continuous_snd
  have cy : Continuous (fun z : ℝ × ℝ ↦ y z.2) :=
    hy.continuous.comp continuous_snd
  have cdy : Continuous (fun z : ℝ × ℝ ↦ deriv y z.2) :=
    (hy.continuous_deriv (by norm_num)).comp continuous_snd
  have hz : Continuous (fun z : ℝ × ℝ ↦
      (z.2, (y z.2 + z.1 * η z.2,
        deriv y z.2 + z.1 * deriv η z.2))) :=
    continuous_snd.prodMk
      ((cy.add (continuous_fst.mul cη)).prodMk
        (cdy.add (continuous_fst.mul cdη)))
  have hp := apm_m98J04_contDiff_lagrangian_partials hF
  exact (((hp.1.continuous.comp hz).mul cη).add
    ((hp.2.continuous.comp hz).mul cdη))

/-- On a compact parameter strip, the first-variation derivatives have one
uniform bound, suitable as the constant dominating function. -/
lemma apm_m98J04_first_variation_uniform_bound
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    ∃ C : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∈ uIcc a b,
      ‖deriv
            (fun q ↦ F x q (deriv y x + t * deriv η x))
            (y x + t * η x) * η x +
          deriv
            (fun p ↦ F x (y x + t * η x) p)
            (deriv y x + t * deriv η x) * deriv η x‖ ≤ C := by
  let D : ℝ × ℝ → ℝ := fun z ↦
    deriv
        (fun q ↦ F z.2 q (deriv y z.2 + z.1 * deriv η z.2))
        (y z.2 + z.1 * η z.2) * η z.2 +
      deriv
        (fun p ↦ F z.2 (y z.2 + z.1 * η z.2) p)
        (deriv y z.2 + z.1 * deriv η z.2) * deriv η z.2
  have hD : Continuous D :=
    apm_m98J04_continuous_first_variation_family hF hy hη
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    hD.continuousOn
  refine ⟨C, ?_⟩
  intro t ht x hx
  exact hC (t, x) ⟨ht, hx⟩

/-- Pointwise first-variation formula at an arbitrary parameter value. -/
lemma apm_m98J04_hasDerivAt_variation_integrand_at
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (t x : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    HasDerivAt
      (fun s ↦ F x (y x + s * η x)
        (deriv (fun z ↦ y z + s * η z) x))
      (deriv
          (fun q ↦ F x q (deriv y x + t * deriv η x))
          (y x + t * η x) * η x +
        deriv
          (fun p ↦ F x (y x + t * η x) p)
          (deriv y x + t * deriv η x) * deriv η x) t := by
  have hy' : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hη' : Differentiable ℝ η := hη.differentiable (by norm_num)
  let g : ℝ × ℝ → ℝ := fun z ↦ F x z.1 z.2
  have hg : DifferentiableAt ℝ g
      (y x + t * η x, deriv y x + t * deriv η x) :=
    ((apm_m98J04_contDiff_lagrangian_slice x hF).differentiable
      (by norm_num)).differentiableAt
  have hu : HasDerivAt (fun s : ℝ ↦ y x + s * η x) (η x) t :=
    by
      convert (hasDerivAt_const (x := t) (y x)).add
        ((hasDerivAt_id t).mul_const (η x)) using 1
      ring
  have hv : HasDerivAt (fun s : ℝ ↦ deriv y x + s * deriv η x) (deriv η x) t :=
    by
      convert (hasDerivAt_const (x := t) (deriv y x)).add
        ((hasDerivAt_id t).mul_const (deriv η x)) using 1
      ring
  have hpoint := apm_m98J04_hasDerivAt_comp₂ hg hu hv
  convert hpoint using 1
  · funext s
    rw [apm_m98J04_deriv_affine_variation hy' hη' s x]

/-- For every parameter, the varied Lagrangian integrand is continuous in the
spatial variable. -/
lemma apm_m98J04_continuous_variation_integrand
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (t : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    Continuous (fun x ↦
      F x (y x + t * η x) (deriv (fun z ↦ y z + t * η z) x)) := by
  have hy' : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hη' : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hz : Continuous (fun x : ℝ ↦
      (x, (y x + t * η x, deriv y x + t * deriv η x))) :=
    continuous_id.prodMk
      ((hy.continuous.add (continuous_const.mul hη.continuous)).prodMk
        ((hy.continuous_deriv (by norm_num)).add
          (continuous_const.mul hη.continuous_deriv_one)))
  have hc := hF.continuous.comp hz
  convert hc using 1
  funext x
  rw [apm_m98J04_deriv_affine_variation hy' hη' t x]
  rfl

/-- Differentiation of the variational functional under the interval integral. -/
lemma apm_m98J04_hasDerivAt_functional_variation
    {F : ℝ → ℝ → ℝ → ℝ} {y η : ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η) :
    HasDerivAt
      (fun t ↦ apm_m98J04_functional F a b (fun x ↦ y x + t * η x))
      (∫ x in a..b,
        deriv (fun q ↦ F x q (deriv y x)) (y x) * η x +
          deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x) 0 := by
  let V : ℝ → ℝ → ℝ := fun t x ↦
    F x (y x + t * η x) (deriv (fun z ↦ y z + t * η z) x)
  let D : ℝ → ℝ → ℝ := fun t x ↦
    deriv (fun q ↦ F x q (deriv y x + t * deriv η x)) (y x + t * η x) * η x +
      deriv (fun p ↦ F x (y x + t * η x) p)
        (deriv y x + t * deriv η x) * deriv η x
  obtain ⟨C, hC⟩ := apm_m98J04_first_variation_uniform_bound a b hF hy hη
  have hp := apm_m98J04_contDiff_partials_along_curve hF hy
  have hden : Continuous (fun x ↦
      deriv (fun q ↦ F x q (deriv y x)) (y x) * η x +
        deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x) :=
    (hp.1.continuous.mul hη.continuous).add
      (hp.2.continuous.mul hη.continuous_deriv_one)
  have hDmeas : MeasureTheory.AEStronglyMeasurable (D 0)
      (MeasureTheory.volume.restrict (uIoc a b)) := by
    have hD0 : Continuous (D 0) := by simpa [D] using hden
    exact hD0.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := a) (b := b) (F := V) (F' := D)
    (bound := fun _ ↦ C) (x₀ := (0 : ℝ)) (s := Icc (-1 : ℝ) 1)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t ↦
      (apm_m98J04_continuous_variation_integrand t hF hy hη).aestronglyMeasurable)
    ((apm_m98J04_continuous_variation_integrand 0 hF hy hη).intervalIntegrable a b)
    hDmeas
    (Filter.Eventually.of_forall fun x hx t ht ↦ hC t ht x (uIoc_subset_uIcc hx))
    _root_.intervalIntegrable_const
    (Filter.Eventually.of_forall fun x hx t ht ↦
      apm_m98J04_hasDerivAt_variation_integrand_at t x hF hy hη)
  have hder := hmain.2
  simpa [V, D, apm_m98J04_functional] using hder

/-- Stationarity is equivalent, in the direction needed below, to vanishing
of the weak first-variation integral. -/
lemma apm_m98J04_stationary_first_variation_eq_zero
    {F : ℝ → ℝ → ℝ → ℝ} {a b : ℝ} {y : ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y)
    (hstat : apm_m98J04_stationary F a b y)
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (∫ x in a..b,
      deriv (fun q ↦ F x q (deriv y x)) (y x) * η x +
        deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x) = 0 := by
  have hcalc := apm_m98J04_hasDerivAt_functional_variation a b hF hy hη
  have hzero := hstat η hη hηa hηb
  exact hcalc.unique hzero

/-- Integration by parts for the momentum/variation term, with the endpoint
terms eliminated by the admissible variation conditions. -/
lemma apm_m98J04_integral_momentum_mul_deriv
    {F : ℝ → ℝ → ℝ → ℝ} {a b : ℝ} {y η : ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 1 η)
    (hηa : η a = 0) (hηb : η b = 0) :
    (∫ x in a..b,
      deriv (fun p ↦ F x (y x) p) (deriv y x) * deriv η x) =
      -(∫ x in a..b,
        deriv (fun t ↦ deriv (fun p ↦ F t (y t) p) (deriv y t)) x * η x) := by
  let B : ℝ → ℝ := fun x ↦ deriv (fun p ↦ F x (y x) p) (deriv y x)
  have hB : ContDiff ℝ 1 B :=
    (apm_m98J04_contDiff_partials_along_curve hF hy).2
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := b) (u := B) (v := η) (u' := deriv B) (v' := deriv η)
    hB.continuous.continuousOn hη.continuous.continuousOn
    (fun x _ ↦ apm_m98J04_hasDerivAt_deriv_of_contDiff hB x)
    (fun x _ ↦ apm_m98J04_hasDerivAt_deriv_of_contDiff hη x)
    (hB.continuous_deriv_one.intervalIntegrable a b)
    (hη.continuous_deriv_one.intervalIntegrable a b)
  simp [B, hηa, hηb] at hparts ⊢
  exact hparts

/-- Weak Euler–Lagrange equation after integration by parts. -/
lemma apm_m98J04_stationary_residual_integral_eq_zero
    {F : ℝ → ℝ → ℝ → ℝ} {a b : ℝ} {y : ℝ → ℝ}
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y) (hstat : apm_m98J04_stationary F a b y)
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (∫ x in a..b,
      (deriv (fun q ↦ F x q (deriv y x)) (y x) -
        deriv (fun t ↦ deriv (fun p ↦ F t (y t) p) (deriv y t)) x) * η x) = 0 := by
  let A : ℝ → ℝ := fun x ↦ deriv (fun q ↦ F x q (deriv y x)) (y x)
  let B : ℝ → ℝ := fun x ↦ deriv (fun p ↦ F x (y x) p) (deriv y x)
  have hp := apm_m98J04_contDiff_partials_along_curve hF hy
  have hA : ContDiff ℝ 1 A := hp.1
  have hB : ContDiff ℝ 1 B := hp.2
  have hweak := apm_m98J04_stationary_first_variation_eq_zero
    hF hy hstat η hη hηa hηb
  have hip := apm_m98J04_integral_momentum_mul_deriv
    hF hy hη hηa hηb
  have hAη : IntervalIntegrable (fun x ↦ A x * η x)
      MeasureTheory.volume a b :=
    (hA.continuous.mul hη.continuous).intervalIntegrable a b
  have hBη' : IntervalIntegrable (fun x ↦ B x * deriv η x)
      MeasureTheory.volume a b :=
    (hB.continuous.mul hη.continuous_deriv_one).intervalIntegrable a b
  have hdBη : IntervalIntegrable (fun x ↦ deriv B x * η x)
      MeasureTheory.volume a b :=
    (hB.continuous_deriv_one.mul hη.continuous).intervalIntegrable a b
  have hsplit :
      (∫ x in a..b, A x * η x + B x * deriv η x) =
        (∫ x in a..b, A x * η x) + ∫ x in a..b, B x * deriv η x :=
    intervalIntegral.integral_add hAη hBη'
  change (∫ x in a..b, A x * η x + B x * deriv η x) = 0 at hweak
  change (∫ x in a..b, B x * deriv η x) =
    -(∫ x in a..b, deriv B x * η x) at hip
  rw [hsplit, hip] at hweak
  change (∫ x in a..b, (A x - deriv B x) * η x) = 0
  rw [show (fun x ↦ (A x - deriv B x) * η x) =
      (fun x ↦ A x * η x - deriv B x * η x) by funext x; ring]
  rw [intervalIntegral.integral_sub hAη hdBη]
  linarith

/-- A smooth nonnegative bump of prescribed outer radius on the real line. -/
lemma apm_m98J04_exists_test_bump (x r : ℝ) (hr : 0 < r) :
    ∃ η : ℝ → ℝ,
      ContDiff ℝ 1 η ∧ η x = 1 ∧ (∀ z, 0 ≤ η z) ∧
        (∀ z, dist z x < r → 0 < η z) ∧
        ∀ z, r ≤ dist z x → η z = 0 := by
  let φ : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ, φ.contDiff, ?_, ?_, ?_, ?_⟩
  · apply φ.one_of_mem_closedBall
    simpa [φ] using (half_pos hr).le
  · intro z
    exact φ.nonneg
  · intro z hz
    apply φ.pos_of_mem_ball
    simpa [Metric.mem_ball, dist_comm] using hz
  · intro z hz
    exact φ.zero_of_le_dist hz

/-- A bump whose radius fits inside `(a,b)` automatically satisfies the
endpoint-fixing conditions. -/
lemma apm_m98J04_test_bump_endpoints
    {a b x r : ℝ} (hax : a < x) (hxb : x < b) (hr : 0 < r)
    (hra : r ≤ x - a) (hrb : r ≤ b - x) :
    ∃ η : ℝ → ℝ,
      ContDiff ℝ 1 η ∧ η a = 0 ∧ η b = 0 ∧ η x = 1 ∧
        (∀ z, 0 ≤ η z) ∧ (∀ z, dist z x < r → 0 < η z) ∧
        ∀ z, r ≤ dist z x → η z = 0 := by
  obtain ⟨η, hη, hηx, hηnonneg, hηpos, hηzero⟩ :=
    apm_m98J04_exists_test_bump x r hr
  refine ⟨η, hη, ?_, ?_, hηx, hηnonneg, hηpos, hηzero⟩
  · apply hηzero a
    rw [Real.dist_eq]
    rw [abs_of_neg (sub_neg.mpr hax)]
    linarith
  · apply hηzero b
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxb)]
    exact hrb

/-- A continuous function positive at an interior point admits a smooth
endpoint-fixing nonnegative test with strictly positive weighted integral. -/
lemma apm_m98J04_exists_test_integral_pos
    {f : ℝ → ℝ} {a b x : ℝ} (hf : Continuous f)
    (hax : a < x) (hxb : x < b) (hfx : 0 < f x) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ η a = 0 ∧ η b = 0 ∧
      0 < ∫ z in a..b, f z * η z := by
  have hopen : f ⁻¹' Ioi 0 ∈ nhds x :=
    (isOpen_Ioi.preimage hf).mem_nhds hfx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hopen
  let r : ℝ := min (δ / 2) (min ((x - a) / 2) ((b - x) / 2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hδ)
      (lt_min (half_pos (sub_pos.mpr hax)) (half_pos (sub_pos.mpr hxb)))
  have hrδ : r < δ := by
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hra : r ≤ x - a := by
    calc
      r ≤ (x - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ x - a := by linarith
  have hrb : r ≤ b - x := by
    calc
      r ≤ (b - x) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ b - x := by linarith
  obtain ⟨η, hη, hηa, hηb, hηx, hηnonneg, hηpos, hηzero⟩ :=
    apm_m98J04_test_bump_endpoints hax hxb hr hra hrb
  refine ⟨η, hη, hηa, hηb, ?_⟩
  have hfpos : ∀ z, dist z x < r → 0 < f z := by
    intro z hz
    exact hball (by simpa [Metric.mem_ball] using hz.trans hrδ)
  have hnonneg : ∀ z, 0 ≤ f z * η z := by
    intro z
    by_cases hz : dist z x < r
    · exact mul_nonneg (hfpos z hz).le (hηnonneg z)
    · rw [hηzero z (le_of_not_gt hz), mul_zero]
  have hfi : IntervalIntegrable (fun z ↦ f z * η z)
      MeasureTheory.volume a b :=
    (hf.mul hη.continuous).intervalIntegrable a b
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg) hfi]
  refine ⟨hax.trans hxb, ?_⟩
  have hs : Ioo (x - r / 2) (x + r / 2) ⊆
      Function.support (fun z ↦ f z * η z) ∩ Ioc a b := by
    intro z hz
    have hdist : dist z x < r := by
      rw [Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hz.1, hz.2]
    have hzpos : 0 < f z * η z := mul_pos (hfpos z hdist) (hηpos z hdist)
    refine ⟨Function.mem_support.mpr hzpos.ne', ?_⟩
    constructor <;> linarith [hz.1, hz.2, hra, hrb]
  have hinterval : x - r / 2 < x + r / 2 := by linarith
  have hmeasure : 0 < MeasureTheory.volume (Ioo (x - r / 2) (x + r / 2)) :=
    (MeasureTheory.Measure.measure_Ioo_pos MeasureTheory.volume).2 hinterval
  exact hmeasure.trans_le (MeasureTheory.measure_mono hs)

/-- Fundamental lemma of the calculus of variations for continuous real
residuals and globally `C¹`, endpoint-fixing test functions. -/
lemma apm_m98J04_fundamental_lemma
    {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hzero : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      (∫ x in a..b, f x * η x) = 0) :
    ∀ x ∈ Ioo a b, f x = 0 := by
  intro x hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨η, hη, hηa, hηb, hint⟩ :=
      apm_m98J04_exists_test_integral_pos hf.neg hx.1 hx.2 (neg_pos.mpr hneg)
    have hz := hzero η hη hηa hηb
    simp only [neg_mul, intervalIntegral.integral_neg] at hint
    rw [hz, neg_zero] at hint
    exact (lt_irrefl 0 hint)
  · obtain ⟨η, hη, hηa, hηb, hint⟩ :=
      apm_m98J04_exists_test_integral_pos hf hx.1 hx.2 hpos
    rw [hzero η hη hηa hηb] at hint
    exact (lt_irrefl 0 hint)

/-- Smooth stationarity implies the pointwise Euler–Lagrange equation. -/
lemma apm_m98J04_stationary_eulerLagrange
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ)
    (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ ↦ F z.1 z.2.1 z.2.2))
    (hy : ContDiff ℝ 2 y)
    (hstat : apm_m98J04_stationary F a b y) :
    apm_m98J04_eulerLagrange F a b y := by
  let A : ℝ → ℝ := fun x ↦ deriv (fun q ↦ F x q (deriv y x)) (y x)
  let B : ℝ → ℝ := fun x ↦ deriv (fun p ↦ F x (y x) p) (deriv y x)
  have hp := apm_m98J04_contDiff_partials_along_curve hF hy
  have hA : ContDiff ℝ 1 A := hp.1
  have hB : ContDiff ℝ 1 B := hp.2
  have hres : ∀ x ∈ Ioo a b, (A x - deriv B x) = 0 :=
    apm_m98J04_fundamental_lemma
      (hA.continuous.sub hB.continuous_deriv_one) (fun η hη hηa hηb ↦ by
        simpa [A, B] using apm_m98J04_stationary_residual_integral_eq_zero
          hF hy hstat η hη hηa hηb)
  intro x hx
  have hBx : HasDerivAt B (deriv B x) x :=
    apm_m98J04_hasDerivAt_deriv_of_contDiff hB x
  have heq : deriv B x = A x := by linarith [hres x hx]
  simpa [A, B, heq] using hBx

lemma apm_m98J04_deriv_line (a b α β x : ℝ) :
    deriv (apm_m98J04_line a b α β) x = (β - α) / (b - a) := by
  unfold apm_m98J04_line
  have h : HasDerivAt
      (fun t : ℝ => α + ((β - α) / (b - a)) * (t - a))
      ((β - α) / (b - a)) x := by
    simpa using
      (((hasDerivAt_id x).sub_const a).const_mul ((β - α) / (b - a))).const_add α
  exact h.deriv

lemma apm_m98J04_arcLength_line (a b α β : ℝ) (hab : a < b) :
    apm_m98J04_arcLength a b (apm_m98J04_line a b α β) =
      (b - a) * Real.sqrt (1 + ((β - α) / (b - a)) ^ 2) := by
  unfold apm_m98J04_arcLength
  simp_rw [apm_m98J04_deriv_line a b α β]
  simp [intervalIntegral.integral_const]

/-- The computed graph length of the line is the Euclidean endpoint distance. -/
lemma apm_m98J04_arcLength_line_eq_sqrt (a b α β : ℝ) (hab : a < b) :
    apm_m98J04_arcLength a b (apm_m98J04_line a b α β) =
      Real.sqrt ((b - a) ^ 2 + (β - α) ^ 2) := by
  rw [apm_m98J04_arcLength_line a b α β hab]
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [← sq_eq_sq₀ (mul_nonneg hba.le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- The endpoint identity needed for the graph-length lower bound. -/
lemma apm_m98J04_integral_deriv_eq_sub (a b : ℝ) (y : ℝ → ℝ)
    (hy : ContDiff ℝ 1 y) :
    ∫ x in a..b, deriv y x = y b - y a := by
  apply intervalIntegral.integral_deriv_eq_sub
  · intro x hx
    exact hy.differentiable one_ne_zero x
  · exact (hy.continuous_deriv le_rfl).intervalIntegrable a b

/-- The scalar graph arc-length integrand is a complex norm. -/
lemma apm_m98J04_norm_one_add_deriv_mul_I (y : ℝ → ℝ) (x : ℝ) :
    ‖((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I‖ =
      Real.sqrt (1 + (deriv y x) ^ 2) := by
  rw [Complex.norm_add_mul_I]
  norm_num

/-- Integrating the complex graph tangent records the endpoint displacement. -/
lemma apm_m98J04_integral_complex_tangent (a b : ℝ) (y : ℝ → ℝ)
    (hy : ContDiff ℝ 1 y) :
    ∫ x in a..b, (((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I) =
      ((b - a : ℝ) : ℂ) + ((y b - y a : ℝ) : ℂ) * Complex.I := by
  have hderiv : Continuous (deriv y) := hy.continuous_deriv le_rfl
  have h1 : IntervalIntegrable (fun _ : ℝ => ((1 : ℝ) : ℂ))
      MeasureTheory.volume a b := by
    exact continuous_const.intervalIntegrable a b
  have h2 : IntervalIntegrable
      (fun x : ℝ => ((deriv y x : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add h1 h2]
  rw [show (∫ x in a..b, ((deriv y x : ℝ) : ℂ) * Complex.I) =
      (∫ x in a..b, ((deriv y x : ℝ) : ℂ)) * Complex.I from
    intervalIntegral.integral_mul_const Complex.I
      (fun x : ℝ => ((deriv y x : ℝ) : ℂ))]
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_ofReal]
  rw [apm_m98J04_integral_deriv_eq_sub a b y hy]
  simp

/-- The final topological stage of the fundamental lemma: a continuous
function which vanishes almost everywhere on an open interval vanishes at
every point of that interval. -/
lemma apm_m98J04_eq_zero_on_Ioo_of_ae
    (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b))
    (hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ioo a b → f x = 0) :
    ∀ x ∈ Ioo a b, f x = 0 := by
  have hae' : f =ᵐ[MeasureTheory.volume.restrict (Ioo a b)] (0 : ℝ → ℝ) := by
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioo a b), f x = 0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hf
    continuous_zero.continuousOn

/-- Why this unblocks `apm_m98j04`: this is the missing first-variation
assembly theorem.  Its proof differentiates under the frozen interval
integral, integrates the momentum term by parts, converts endpoint-zero
variations to compactly supported smooth tests, applies the distributional
fundamental lemma, and upgrades almost-everywhere vanishing to the pointwise
Euler--Lagrange equation. -/
theorem apm_m98J04_bridge_stationary_imp_eulerLagrange
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ)
    (hab : a < b)
    (hF : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ ↦ F p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y)
    (hstat : apm_m98J04_stationary F a b y) :
    apm_m98J04_eulerLagrange F a b y := by
  exact apm_m98J04_stationary_eulerLagrange F a b y hF hy hstat

theorem apm_m98j04 :
    (∀ (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ),
      a < b →
      ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ ↦ F p.1 p.2.1 p.2.2) →
      ContDiff ℝ 2 y →
      apm_m98J04_stationary F a b y →
      apm_m98J04_eulerLagrange F a b y) ∧
    ∀ (a b α β : ℝ), a < b →
      apm_m98J04_line a b α β ∈ apm_m98J04_admissible a b α β ∧
      ∀ y ∈ apm_m98J04_admissible a b α β,
        apm_m98J04_arcLength a b (apm_m98J04_line a b α β) ≤
          apm_m98J04_arcLength a b y := by
  constructor
  ·
    intro F a b y hab hF hy hstat
    exact apm_m98J04_bridge_stationary_imp_eulerLagrange F a b y hab hF hy hstat
  · intro a b α β hab
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · unfold apm_m98J04_line
        fun_prop
      · simp [apm_m98J04_line]
      · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
        simp [apm_m98J04_line, hba]
    · /-
      The complex number `1 + y' * I` packages the graph tangent without
      needing a custom Euclidean-product norm.  Its norm is the frozen
      arc-length integrand, while its integral is the endpoint displacement.
      -/
      intro y hy
      rw [apm_m98J04_arcLength_line_eq_sqrt a b α β hab]
      unfold apm_m98J04_arcLength
      rw [← Complex.norm_add_mul_I (b - a) (β - α)]
      calc
        ‖((b - a : ℝ) : ℂ) + ((β - α : ℝ) : ℂ) * Complex.I‖ =
            ‖∫ x in a..b,
              (((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I)‖ := by
              rw [apm_m98J04_integral_complex_tangent a b y hy.1]
              simp [hy.2.1, hy.2.2]
        _ ≤ ∫ x in a..b,
              ‖(((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab.le
        _ = ∫ x in a..b, Real.sqrt (1 + (deriv y x) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact apm_m98J04_norm_one_add_deriv_mul_I y x
