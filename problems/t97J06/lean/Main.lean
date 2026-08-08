import Mathlib

/-!
# APM t97J06 — a self-map of the two-torus

The torus is represented concretely as `Circle × Circle`.  Under the usual
covering map `x ↦ exp (2πix)`, the map below is induced by

`(x,y) ↦ (sin (2πx + 4πy), x+y)`.

The degree is recorded by the standard integral of the determinant of the
Jacobian of this lift over a fundamental square.  Non-nullhomotopy is stated
using Mathlib's actual homotopy relation on continuous maps.

## Statement repairs

The printed assertion that the lift is literally periodic is false: translating
`(x,y)` by `(m,n) ∈ ℤ²` changes its second coordinate by `m+n`.  We use the
intended lattice-equivariance statement, equivalently the descended map on
`ℝ²/ℤ²`.
-/

open scoped Real

abbrev T97J06Torus := Circle × Circle

noncomputable def t97J06Map : C(T97J06Torus, T97J06Torus) where
  toFun p :=
    (Circle.exp (2 * Real.pi * Complex.im ((p.1 : ℂ) * (p.2 : ℂ) ^ 2)),
      p.1 * p.2)
  continuous_toFun := by fun_prop

lemma t97J06Map_on_cover (x y : ℝ) :
    t97J06Map
        (Circle.exp (2 * Real.pi * x), Circle.exp (2 * Real.pi * y)) =
      (Circle.exp (2 * Real.pi * Real.sin (2 * Real.pi * x + 4 * Real.pi * y)),
        Circle.exp (2 * Real.pi * (x + y))) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((Circle.exp (2 * Real.pi *
      Complex.im (((Circle.exp (2 * Real.pi * x) : Circle) : ℂ) *
        (((Circle.exp (2 * Real.pi * y) : Circle) : ℂ) ^ 2))) : Circle) : ℂ) =
      (Circle.exp (2 * Real.pi * Real.sin (2 * Real.pi * x + 4 * Real.pi * y)) : ℂ)
    have hprod :
        Circle.exp (2 * Real.pi * x) * (Circle.exp (2 * Real.pi * y)) ^ 2 =
          Circle.exp (2 * Real.pi * x + 2 * Real.pi * y + 2 * Real.pi * y) := by
      rw [pow_two, ← Circle.exp_add, ← Circle.exp_add]
      congr 1
      ring
    have him :
        Complex.im (((Circle.exp (2 * Real.pi * x) : Circle) : ℂ) *
          (((Circle.exp (2 * Real.pi * y) : Circle) : ℂ) ^ 2)) =
          Real.sin (2 * Real.pi * x + 4 * Real.pi * y) := by
      have hprodcoe := congrArg (fun z : Circle ↦ (z : ℂ)) hprod
      change (((Circle.exp (2 * Real.pi * x) : Circle) : ℂ) *
        (((Circle.exp (2 * Real.pi * y) : Circle) : ℂ) ^ 2)) =
          (Circle.exp (2 * Real.pi * x + 2 * Real.pi * y + 2 * Real.pi * y) : ℂ)
        at hprodcoe
      rw [hprodcoe, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
      congr 1
      ring
    rw [him]
  · change Circle.exp (2 * Real.pi * x) * Circle.exp (2 * Real.pi * y) =
      Circle.exp (2 * Real.pi * (x + y))
    simpa [mul_add, add_mul] using
      (Circle.exp_add (2 * Real.pi * x) (2 * Real.pi * y)).symm

lemma t97J06_determinant_integral_zero :
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1,
        Matrix.det !![2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y),
            4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y);
          (1 : ℝ), 1]) = 0 := by
  simp_rw [Matrix.det_fin_two_of, mul_one]
  change (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y) -
      4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y)) = 0
  have hfourpi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcos (x : ℝ) :
      (∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * x + 4 * Real.pi * y)) = 0 := by
    let F : ℝ → ℝ := fun y ↦ Real.sin (2 * Real.pi * x + 4 * Real.pi * y) /
      (4 * Real.pi)
    have hF (y : ℝ) :
        HasDerivAt F (Real.cos (2 * Real.pi * x + 4 * Real.pi * y)) y := by
      have ha : HasDerivAt (fun y : ℝ ↦ 2 * Real.pi * x + 4 * Real.pi * y)
          (4 * Real.pi) y := by
        convert (hasDerivAt_const y (2 * Real.pi * x)).add
          ((hasDerivAt_const y (4 * Real.pi)).mul (hasDerivAt_id y)) using 1 <;>
          simp <;> ring
      dsimp [F]
      convert ha.sin.div_const (4 * Real.pi) using 1 <;> field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hF y)
      ((Real.continuous_cos.comp
        (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    dsimp [F]
    have hperiod :
        Real.sin (2 * Real.pi * x + 4 * Real.pi * 1) =
          Real.sin (2 * Real.pi * x + 4 * Real.pi * 0) := by
      convert Real.sin_add_nat_mul_two_pi (2 * Real.pi * x) 2 using 1 <;> ring
    rw [hperiod]
    ring
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..1,
        2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y) -
          4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y)) = 0 := by
    calc
      _ = (-2 * Real.pi) *
          (∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * x + 4 * Real.pi * y)) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro y _
            ring
      _ = 0 := by rw [hcos x]; ring
  simp_rw [hinner]
  exact intervalIntegral.integral_zero

/-- Any null-homotopy of the torus map would contract the identity map of the
circle: restrict to the first-coordinate meridian and project to the second
coordinate.  This isolates the remaining topological input. -/
lemma t97J06_circle_identity_homotopic_of_map_homotopic_const
    (q : T97J06Torus)
    (h : ContinuousMap.Homotopic t97J06Map
      (ContinuousMap.const T97J06Torus q)) :
    ContinuousMap.Homotopic (ContinuousMap.id Circle)
      (ContinuousMap.const Circle q.2) := by
  let meridian : C(Circle, T97J06Torus) :=
    ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩
  let second : C(T97J06Torus, Circle) :=
    ⟨Prod.snd, continuous_snd⟩
  have hr := ContinuousMap.Homotopic.comp h
    (ContinuousMap.Homotopic.refl meridian)
  have hp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl second) hr
  have hleft : second.comp (t97J06Map.comp meridian) = ContinuousMap.id Circle := by
    ext z
    simp [second, meridian, t97J06Map]
  simpa [hleft, second, meridian] using hp

/-- A null-homotopy of the concrete torus map would make the circle a
contractible space, not merely produce an isolated homotopy statement. -/
lemma t97J06_contractibleCircle_of_map_homotopic_const
    (q : T97J06Torus)
    (h : ContinuousMap.Homotopic t97J06Map
      (ContinuousMap.const T97J06Torus q)) :
    ContractibleSpace Circle := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨q.2, t97J06_circle_identity_homotopic_of_map_homotopic_const q h⟩

/-- The final non-nullhomotopy conjunct follows from the standard
noncontractibility of the circle. -/
lemma t97J06_not_homotopic_const_of_not_contractibleCircle
    (hCircle : ¬ ContractibleSpace Circle) :
    ∀ q : T97J06Torus,
      ¬ ContinuousMap.Homotopic t97J06Map
        (ContinuousMap.const T97J06Torus q) := by
  intro q h
  exact hCircle (t97J06_contractibleCircle_of_map_homotopic_const q h)

theorem apm_t97j06 :
    (∀ x y : ℝ,
      t97J06Map
          (Circle.exp (2 * Real.pi * x), Circle.exp (2 * Real.pi * y)) =
        (Circle.exp (2 * Real.pi * Real.sin (2 * Real.pi * x + 4 * Real.pi * y)),
          Circle.exp (2 * Real.pi * (x + y)))) ∧
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1,
        Matrix.det !![2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y),
            4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y);
          (1 : ℝ), 1]) = 0 ∧
    (∀ q : T97J06Torus,
      ¬ ContinuousMap.Homotopic t97J06Map (ContinuousMap.const T97J06Torus q)) := by
  refine ⟨t97J06Map_on_cover, t97J06_determinant_integral_zero, ?_⟩
  /-
  Boundary (closer hop 3): hop 2 closed the coordinate formula and the
  degree integral.  `t97J06Map_on_cover` uses `Circle.exp_add` and the
  imaginary-part formula for the complex exponential.  The determinant is
  reduced with `Matrix.det_fin_two_of`; its inner integral is the endpoint
  difference of `sin (2πx + 4πy) / (4π)`, and periodicity makes it zero.

  The remaining conjunct was reduced sharply by
  `t97J06_circle_identity_homotopic_of_map_homotopic_const`: restricting the
  alleged null-homotopy to `z ↦ (z,1)` and projecting to the second coordinate
  would make `ContinuousMap.id Circle` homotopic to a constant. Going beyond
  that boundary, hop 3 applies `contractible_iff_id_nullhomotopic` in
  `t97J06_contractibleCircle_of_map_homotopic_const`, turning any alleged
  null-homotopy into an actual `ContractibleSpace Circle` instance.
  `t97J06_not_homotopic_const_of_not_contractibleCircle` then compiles the
  entire final conjunct conditional only on `¬ ContractibleSpace Circle`.

  Renewed searches included `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  `YoungL2.lean`, Mathlib's homotopy, fundamental-group, circle, covering, and
  singular-homology sources, git history, and the topology siblings `t91A05`,
  `t91J02`, `t97J03`, `t01J03`, `t02A03`, and `t97J04`.  Mathlib supplies
  homotopy composition and fundamental-group functoriality, but this snapshot
  has no proof of `¬ ContractibleSpace Circle` or computation of
  `FundamentalGroup Circle`; the siblings independently record the same
  boundary. The frozen statement is unchanged.
  -/
  sorry
