import Mathlib

/-! # APM t95J05: descent and integration of a three-form on `ℝP³`

## Statement repairs

The hint's `vol B⁴ = π⁴ / 2` is a typographical error; the four-ball has
volume `π² / 2`.  Accordingly the requested integral is `-π²` with the
orientation for which `S³ → ℝP³` is orientation-preserving.

## Encoding question

The sphere is the actual unit sphere in `ℝ⁴`, and `ℝP³` is its antipodal
quotient. A projective three-form is represented by its antipodally invariant
pullback density on `S³`. The given ambient form restricts to the explicit
density obtained by contraction with the outward unit normal. Integration on
the quotient is half the Hausdorff-measure integral over the double cover.
-/

open MeasureTheory

noncomputable section

abbrev t95J05R4 := EuclideanSpace ℝ (Fin 4)
abbrev t95J05SphereThree := Metric.sphere (0 : t95J05R4) 1

def t95J05Antipode (x : t95J05SphereThree) : t95J05SphereThree :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

inductive T95J05AntipodalRel :
    t95J05SphereThree → t95J05SphereThree → Prop
  | antipodal (x : t95J05SphereThree) :
      T95J05AntipodalRel x (t95J05Antipode x)

def t95J05RealProjectiveThree :=
  Quotient (Relation.EqvGen.setoid T95J05AntipodalRel)

noncomputable instance : TopologicalSpace t95J05RealProjectiveThree :=
  TopologicalSpace.coinduced
    (fun x : t95J05SphereThree ↦
      Quotient.mk (Relation.EqvGen.setoid T95J05AntipodalRel) x)
    inferInstance

/-- A three-form on `ℝP³`, represented by its invariant density upstairs. -/
def T95J05ProjectiveThreeForm :=
  {ρ : t95J05SphereThree → ℝ //
    ∀ x, ρ (t95J05Antipode x) = ρ x}

/-- The coefficient `x₂³ - 4x₁` of the ambient three-form. -/
def t95J05Omega (x : t95J05R4) : ℝ := x 1 ^ 3 - 4 * x 0

/-- Restriction to the oriented sphere, by contraction with its normal. -/
def t95J05InclusionPullback (x : t95J05SphereThree) : ℝ :=
  t95J05Omega x.1 * x.1 0

/-- Pullback along the antipodal quotient projection. -/
lemma t95J05InclusionPullback_antipodal (x : t95J05SphereThree) :
    t95J05InclusionPullback (t95J05Antipode x) = t95J05InclusionPullback x := by
  simp [t95J05InclusionPullback, t95J05Omega, t95J05Antipode]
  ring

def t95J05ProjectionPullback (η : T95J05ProjectiveThreeForm) :
    t95J05SphereThree → ℝ := η.1

def t95J05Integral (η : T95J05ProjectiveThreeForm) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3

lemma t95J05_existsUnique_projectiveThreeForm :
    ∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback := by
  let η : T95J05ProjectiveThreeForm :=
    ⟨t95J05InclusionPullback, t95J05InclusionPullback_antipodal⟩
  refine ⟨η, rfl, ?_⟩
  intro z hz
  apply Subtype.ext
  exact hz

lemma t95J05InclusionPullback_expand (x : t95J05SphereThree) :
    t95J05InclusionPullback x = x.1 1 ^ 3 * x.1 0 - 4 * x.1 0 ^ 2 := by
  simp [t95J05InclusionPullback, t95J05Omega]
  ring

lemma t95J05Integral_eq_sphereIntegral
    (η : T95J05ProjectiveThreeForm)
    (hη : t95J05ProjectionPullback η = t95J05InclusionPullback) :
    t95J05Integral η =
      (1 / 2 : ℝ) * ∫ x, t95J05InclusionPullback x
        ∂Measure.hausdorffMeasure 3 := by
  unfold t95J05Integral t95J05ProjectionPullback at *
  rw [hη]

lemma t95J05Integral_eq_neg_pi_sq_of_sphereIntegral
    (η : T95J05ProjectiveThreeForm)
    (hη : t95J05ProjectionPullback η = t95J05InclusionPullback)
    (hsphere : (∫ x, t95J05InclusionPullback x
      ∂Measure.hausdorffMeasure 3) = -2 * Real.pi ^ 2) :
    t95J05Integral η = -Real.pi ^ 2 := by
  rw [t95J05Integral_eq_sphereIntegral η hη, hsphere]
  ring

/-- Hausdorff measure is invariant under isometries, so a function negated by
an isometry equivalence has zero integral. This is the measure-theoretic core
of the odd-coordinate cancellation used for the mixed moment. -/
lemma t95J05_hausdorffIntegral_eq_zero_of_isometry_odd
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (d : ℝ) (e : X ≃ᵢ X) (f : X → ℝ) (hodd : ∀ x, f (e x) = -f x) :
    (∫ x, f x ∂Measure.hausdorffMeasure d) = 0 := by
  let em : X ≃ᵐ X := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving em (Measure.hausdorffMeasure d)
      (Measure.hausdorffMeasure d) := e.measurePreserving_hausdorffMeasure d
  have heq := hmp.integral_comp' f
  change (∫ x, f (e x) ∂Measure.hausdorffMeasure d) =
    ∫ x, f x ∂Measure.hausdorffMeasure d at heq
  have hneg : -(∫ x, f x ∂Measure.hausdorffMeasure d) =
      (∫ x, f x ∂Measure.hausdorffMeasure d) := by
    calc
      _ = ∫ x, -f x ∂Measure.hausdorffMeasure d := (integral_neg _).symm
      _ = ∫ x, f (e x) ∂Measure.hausdorffMeasure d := by
        congr 1
        funext x
        exact (hodd x).symm
      _ = _ := heq
  linarith

theorem apm_t95j05 :
    (∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback) ∧
    (∀ η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback →
      t95J05Integral η = -Real.pi ^ 2) := by
  refine ⟨t95J05_existsUnique_projectiveThreeForm, ?_⟩
  intro η hη
  rw [t95J05Integral_eq_sphereIntegral η hη]
  /-
  Boundary (closer hop 1): antipodal invariance is now proved directly in
  `t95J05InclusionPullback_antipodal`, and
  `t95J05_existsUnique_projectiveThreeForm` closes the entire descent and
  uniqueness conjunct using the concrete subtype representation.

  The remaining integral rewrites by `hη` to half the Hausdorff-measure
  integral on the unit `S³` of `(x₁³ - 4x₀) x₀`.  Odd symmetry makes the
  mixed `x₁³ x₀` term vanish, and rotational symmetry gives
  `∫ x₀² = area(S³)/4 = π²/2`, yielding `-π²` after the factor
  `1/2`.  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`, closed radial
  integration artifacts, git history, and Mathlib's Hausdorff sphere measure,
  orthogonal-invariance, sphere-volume, Gaussian, and coordinate-moment APIs
  found no compiled formula for this sphere coordinate moment or a Stokes
  theorem for the encoded density.  Establishing the Hausdorff normalization
  and the coordinate-square moment remains the sole open bridge.

  CLOSER HOP 2: `t95J05Integral_eq_sphereIntegral` now compiles the exact use
  of `hη`, and the main proof rewrites through it before the remaining sorry.
  `t95J05InclusionPullback_expand` compiles the pointwise separation into the
  odd mixed term and coordinate square, while
  `t95J05Integral_eq_neg_pi_sq_of_sphereIntegral` checks the final factor of
  two and sign from the single sphere-integral value `-2π²`.

  Going beyond the prior sphere-API search, I inspected
  `ConstructionTargets.RadialIntegrationR3` and Mathlib's general
  `integral_fun_norm_addHaar`. They compute ambient Lebesgue radial integrals,
  not `hausdorffMeasure 3` on the sphere subtype; no coarea or polar
  disintegration theorem identifies the latter boundary measure. Related
  artifacts `t02A05`, `t01J06`, and `m96J03` independently stop at the same
  subtype-Hausdorff normalization. Thus the remaining sorry is confined to
  the odd-moment cancellation and `∫_{S³} x₀² = π²/2`; the frozen statement
  is unchanged.

  CLOSER HOP 3: the general Hausdorff-measure symmetry mechanism is now
  compiled as `t95J05_hausdorffIntegral_eq_zero_of_isometry_odd`. It uses
  `IsometryEquiv.measurePreserving_hausdorffMeasure` and change of variables
  to prove cancellation for every function negated by an isometry, with no
  separate integrability premise. This removes the analytic change-of-
  variables part of the odd-moment argument. A final search of the Pi-Lp
  coordinate-isometry, subtype-sphere, Hausdorff, and Euclidean-volume APIs
  found no packaged coordinate reflection on the sphere subtype and still no
  formula identifying `∫_{S³} x₀²` with `π²/2`. The live bridge is therefore
  the finite packaging of that coordinate reflection plus the substantive
  Hausdorff-normalized square moment. The frozen statement is unchanged.

  HOP 4 searched the more general inner-product-space reflection API.  It
  provides `Submodule.reflection`, but using it here still requires computing
  the orthogonal projection onto a coordinate line and restricting the result
  to the sphere subtype.  More decisively, no Hausdorff-normalized sphere
  moment or coarea theorem was found.  A precise sufficient missing lemma is:

    let μ := Measure.hausdorffMeasure 3
    MeasureTheory.Integrable
        (fun x : t95J05SphereThree ↦ x.1 1 ^ 3 * x.1 0) μ ∧
      MeasureTheory.Integrable
        (fun x : t95J05SphereThree ↦ x.1 0 ^ 2) μ ∧
      (∫ x : t95J05SphereThree, x.1 1 ^ 3 * x.1 0 ∂μ) = 0 ∧
      (∫ x : t95J05SphereThree, x.1 0 ^ 2 ∂μ) = Real.pi ^ 2 / 2

  The two integrability clauses permit `integral_sub`; the two evaluations,
  together with `t95J05InclusionPullback_expand`, give the required sphere
  integral `-2 * Real.pi ^ 2` by ring arithmetic.  This statement is the
  remaining mathematical content rather than a coercion-only wrapper.
  -/
  sorry
