import Mathlib

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
  unchanged. -/
  sorry
