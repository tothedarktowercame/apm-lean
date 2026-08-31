import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.SimplyConnectedSphereProducts

open CategoryTheory

/-!
# APM t91J02

## Statement repairs

None.

## Encoding questions

None. The torus is the actual product of two circles, the sphere is the unit
two-sphere in Euclidean `ℝ³`, and non-homeomorphism uses Mathlib's native
`Homeomorph` type.
-/

abbrev apm_t91J02_Torus := Circle × Circle
abbrev apm_t91J02_S2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The first circle is a retract of the torus.  This isolates the elementary
part of the usual fundamental-group obstruction to a torus--sphere
homeomorphism. -/
noncomputable def apm_t91J02_circleInclusion :
    C(Circle, apm_t91J02_Torus) :=
  ⟨fun z => (z, 1), continuous_id.prodMk continuous_const⟩

def apm_t91J02_circleProjection :
    C(apm_t91J02_Torus, Circle) :=
  ⟨Prod.fst, continuous_fst⟩

@[simp] theorem apm_t91J02_circleProjection_comp_circleInclusion :
    apm_t91J02_circleProjection.comp apm_t91J02_circleInclusion =
      ContinuousMap.id Circle := by
  ext z
  rfl

/-- Any hypothetical torus--sphere homeomorphism transports the explicit
torus retraction to a circle retraction of the metric sphere. -/
lemma apm_t91J02_circleRetract_of_homeomorph
    (e : apm_t91J02_Torus ≃ₜ apm_t91J02_S2) :
    ∃ i : C(Circle, apm_t91J02_S2),
      ∃ r : C(apm_t91J02_S2, Circle),
        r.comp i = ContinuousMap.id Circle := by
  let i : C(Circle, apm_t91J02_S2) :=
    (⟨e, e.continuous⟩ : C(apm_t91J02_Torus, apm_t91J02_S2)).comp
      apm_t91J02_circleInclusion
  let r : C(apm_t91J02_S2, Circle) :=
    apm_t91J02_circleProjection.comp
      (⟨e.symm, e.symm.continuous⟩ : C(apm_t91J02_S2, apm_t91J02_Torus))
  refine ⟨i, r, ?_⟩
  ext z
  simp [i, r]
  rfl

/-- A no-circle-retract theorem for the metric sphere is exactly sufficient
to rule out the hypothesized homeomorphism. -/
lemma apm_t91J02_not_homeomorph_of_no_circle_retract
    (h : ¬ ∃ i : C(Circle, apm_t91J02_S2),
      ∃ r : C(apm_t91J02_S2, Circle),
        r.comp i = ContinuousMap.id Circle) :
    ¬Nonempty (apm_t91J02_Torus ≃ₜ apm_t91J02_S2) := by
  rintro ⟨e⟩
  exact h (apm_t91J02_circleRetract_of_homeomorph e)

/-- Reused from the functorial argument in sibling `t91A05`: a left inverse
makes the induced fundamental-group map injective. -/
lemma apm_t91J02_fundamentalGroupMap_injective_of_retract
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (r : C(X, A))
    (hr : r.comp i = ContinuousMap.id A) :
    Function.Injective (FundamentalGroup.map i a) := by
  intro x y hxy
  change (FundamentalGroupoid.map i).map x =
    (FundamentalGroupoid.map i).map y at hxy
  have hxy' := congrArg (fun z ↦ (FundamentalGroupoid.map r).map z) hxy
  change ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map x) =
    ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map y) at hxy'
  rw [← FundamentalGroupoid.map_comp, hr, FundamentalGroupoid.map_id] at hxy'
  exact hxy'

/-- The exact invariant obstruction: a space with trivial fundamental groups
at every basepoint cannot admit `Circle` as a retract once the circle's group
is known to be nontrivial. -/
lemma apm_t91J02_no_circle_retract_of_fundamentalGroup
    [Nontrivial (FundamentalGroup Circle (1 : Circle))]
    (hsphere : ∀ x : apm_t91J02_S2,
      Subsingleton (FundamentalGroup apm_t91J02_S2 x)) :
    ¬ ∃ i : C(Circle, apm_t91J02_S2),
      ∃ r : C(apm_t91J02_S2, Circle),
        r.comp i = ContinuousMap.id Circle := by
  rintro ⟨i, r, hr⟩
  letI : Subsingleton (FundamentalGroup apm_t91J02_S2 (i 1)) := hsphere (i 1)
  have hinj := apm_t91J02_fundamentalGroupMap_injective_of_retract i 1 r hr
  obtain ⟨x, hx⟩ := exists_ne (1 : FundamentalGroup Circle (1 : Circle))
  apply hx
  apply hinj
  exact Subsingleton.elim _ _

theorem apm_t91j02 :
    ¬Nonempty (apm_t91J02_Torus ≃ₜ apm_t91J02_S2) := by
  /- Boundary (closer hop 1): the explicit maps above prove that `Circle` is a
  retract of the concrete torus.  Thus a hypothesized homeomorphism would
  transport this to a circle retract of the concrete metric two-sphere.

  I searched `LEMMA-INDEX.md`, Mathlib's fundamental-group, singular-homology,
  sphere, retract, and separation APIs, all `ConstructionTargets/`, git
  history, and the nearby topology artifacts.  Mathlib has functoriality but
  no compiled theorem computing `FundamentalGroup Circle`, the fundamental
  group or integral homology of this metric sphere, or directly ruling out a
  circle retract of it.  The partial siblings `t01J03`, `t91A05`, `t02A06`,
  `t95J04`, and `t01A05` independently stop at those same computations.
  Consequently the remaining bridge is precisely a no-circle-retract theorem
  for `apm_t91J02_S2` (obtainable from π₁ or H₁ once either is computed).

  CLOSER HOP 2: the transport assertion is now fully formal rather than only
  described. `apm_t91J02_circleRetract_of_homeomorph` conjugates the explicit
  torus inclusion and projection across a hypothesized homeomorphism and
  proves their composite is the circle identity.
  `apm_t91J02_not_homeomorph_of_no_circle_retract` then shows that the exact
  no-circle-retract statement immediately closes the frozen conclusion.
  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's
  retract, fundamental-group and singular-homology sources, all topology
  artifacts, and git history found generic functorial no-retraction patterns
  in siblings `t03J01` and `t91A05`, but both still require the unavailable
  nontriviality of `FundamentalGroup Circle` or the `H₁` computations for the
  circle and metric sphere. Thus all transport bookkeeping is closed and only
  the genuine invariant obstruction remains; the frozen statement is
  unchanged.

  CLOSER HOP 3 compiles that invariant obstruction rather than merely naming
  it. Reusing the categorical pattern from sibling `t91A05`,
  `apm_t91J02_fundamentalGroupMap_injective_of_retract` proves that a left
  inverse induces an injection, and
  `apm_t91J02_no_circle_retract_of_fundamentalGroup` derives the exact
  no-circle-retract assertion from a nontrivial circle group and subsingleton
  sphere groups at every basepoint. Thus no functorial or group reasoning
  remains. Searches of covering/lift, winding-number, sphere, and homology
  sources still found neither concrete computation. The sole remaining inputs
  are precisely those foundational instances; the frozen statement is
  unchanged. -/
  letI : Nontrivial (FundamentalGroup Circle (1 : Circle)) :=
    ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.toEquiv.nontrivial
  letI : SimplyConnectedSpace apm_t91J02_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  apply apm_t91J02_not_homeomorph_of_no_circle_retract
  apply apm_t91J02_no_circle_retract_of_fundamentalGroup
  intro x
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance
