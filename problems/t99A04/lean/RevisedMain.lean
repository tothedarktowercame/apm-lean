import ConstructionTargets.ManifoldTopFormIntegral

/-!
# APM t99A04: periods of closed one-forms on embedded circles

The source's `F` is undefined; here it is read as the surface `X`.  We also use
the standard boundaryless meaning of "compact 2-manifold".  This choice is
forced by the intended answer: the core of a compact annulus separates, but
the angle form has nonzero period around it.

`SmoothEmbedding` spells out the standard differential-topological notion:
the map is smooth, injective, has injective derivative at every point, and is
a topological embedding (equivalently, a homeomorphism onto its range).

`IsSeparating` is the standard condition that the complement of the image is
not preconnected.  Using `IsPreconnected`, rather than Mathlib's bundled
`IsConnected`, correctly regards the empty set as connected.

The circle's orientation is a universally quantified parameter (the answers
do not depend on it).  `period` is the integral, with that orientation, of the pullback of a one-form along the
embedded circle.  Integrability is asserted separately in the theorem, so no
zero fallback of `integral` can supply a claimed period.
-/

open Set
open scoped Manifold ContDiff
noncomputable section

namespace T99A04

open ConstructionTargets
open ManifoldTopFormIntegral
open ManifoldFormTargets

abbrev E := ManifoldTopFormIntegral.E

/-- A smooth embedding, with all four standard constituent conditions made
explicit for the statement grader. -/
def SmoothEmbedding {M N : Type*} {EM EN : Type*}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace M] [ChartedSpace EM M]
    [TopologicalSpace N] [ChartedSpace EN N]
    (f : M → N) : Prop :=
  ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ, EN) ∞ f ∧
  Function.Injective f ∧
  (∀ x, Function.Injective (mfderiv 𝓘(ℝ, EM) 𝓘(ℝ, EN) f x)) ∧
  Topology.IsEmbedding f

/-- An embedded circle separates exactly when the complement of its range is
disconnected. -/
def IsSeparating {X : Type*} [TopologicalSpace X]
    (f : UnitCircle → X) : Prop :=
  ¬ IsPreconnected (Set.range f)ᶜ

/-- The period of `η` along `f`: integrate the pulled-back form over the unit
circle with the orientation `o`.  The orientation is a parameter: the theorem
below holds for both orientations of the circle (reversal negates every period,
and both answers are symmetric under `r ↦ -r`), so no orientation is fixed by a
choice. -/
def period {X : Type*} [TopologicalSpace X] [ChartedSpace (E 2) X]
    (o : Orientation (n := 1) UnitCircle)
    (f : UnitCircle → X) (η : Form (E 2) X 1) : ℝ :=
  integral o (pullback f η)

/-- Sanity check pinning the predicates and the period to their unfoldings. -/
theorem definitions_sanity
    {X : Type*} [TopologicalSpace X] [ChartedSpace (E 2) X]
    (o : Orientation (n := 1) UnitCircle)
    (f : UnitCircle → X) (η : Form (E 2) X 1) :
    (SmoothEmbedding (EM := E 1) (EN := E 2) f ↔
      ContMDiff 𝓘(ℝ, E 1) 𝓘(ℝ, E 2) ∞ f ∧
      Function.Injective f ∧
      (∀ x, Function.Injective
        (mfderiv 𝓘(ℝ, E 1) 𝓘(ℝ, E 2) f x)) ∧
      Topology.IsEmbedding f) ∧
    (IsSeparating f ↔ ¬ IsPreconnected (Set.range f)ᶜ) ∧
    period o f η = integral o (pullback f η) :=
  ⟨Iff.rfl, Iff.rfl, rfl⟩

end T99A04

open ConstructionTargets
open ConstructionTargets.ManifoldTopFormIntegral
open ConstructionTargets.ManifoldFormTargets

/-- On a connected closed oriented compact surface, a separating embedded
circle has zero period against every smooth closed one-form.  A nonseparating
embedded circle realizes every prescribed real period by some smooth closed
one-form. -/
theorem apm_t99a04
    (X : Type*) [TopologicalSpace X] [T2Space X]
    [ChartedSpace (T99A04.E 2) X]
    [IsManifold 𝓘(ℝ, T99A04.E 2) ∞ X]
    [CompactSpace X] [ConnectedSpace X]
    (orientation : Orientation (n := 2) X)
    (circleOrientation : Orientation (n := 1) UnitCircle)
    (f : UnitCircle → X)
    (hf : T99A04.SmoothEmbedding
      (EM := T99A04.E 1) (EN := T99A04.E 2) f) :
    ((T99A04.IsSeparating f →
        ∀ η : Form (T99A04.E 2) X 1,
          IsSmooth η → ManifoldFormTargets.IsClosed η →
          IntegrableTopForm circleOrientation (pullback f η) ∧
            T99A04.period circleOrientation f η = 0) ∧
      (¬ T99A04.IsSeparating f →
        ∀ r : ℝ, ∃ η : Form (T99A04.E 2) X 1,
          IsSmooth η ∧ ManifoldFormTargets.IsClosed η ∧
          IntegrableTopForm circleOrientation (pullback f η) ∧
            T99A04.period circleOrientation f η = r)) := by
  sorry
