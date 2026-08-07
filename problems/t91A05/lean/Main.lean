import Mathlib

open CategoryTheory

/-!
# APM t91A05 — no retraction of the disk onto its boundary

## Statement repairs

None.

## Encoding note

The source permits either the smooth or PL category.  We state the stronger
topological no-retraction theorem: a smooth or PL retraction would in
particular be continuous.
-/

abbrev apm_t91a05_Disk := Metric.closedBall (0 : ℂ) 1
abbrev apm_t91a05_Circle := Metric.sphere (0 : ℂ) 1

def apm_t91a05_boundaryInclusion : apm_t91a05_Circle → apm_t91a05_Disk :=
  fun z => ⟨z, by simpa [apm_t91a05_Circle] using z.property.le⟩

/-- A retraction makes the induced map on fundamental groups injective.
This is the route used in the related surface problem `t01A03`. -/
lemma apm_t91a05_fundamentalGroupMap_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (r : C(X, A)) (hr : ∀ x, r (i x) = x) :
    Function.Injective (FundamentalGroup.map i a) := by
  intro p q hpq
  change (FundamentalGroupoid.map i).map p =
    (FundamentalGroupoid.map i).map q at hpq
  have hpq' := congrArg (fun z ↦ (FundamentalGroupoid.map r).map z) hpq
  change ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map p) =
    ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map q) at hpq'
  have hcomp : r.comp i = ContinuousMap.id A := by
    ext x
    exact hr x
  rw [← FundamentalGroupoid.map_comp, hcomp, FundamentalGroupoid.map_id] at hpq'
  exact hpq'

theorem apm_t91a05 :
    ¬∃ g : apm_t91a05_Disk → apm_t91a05_Circle,
      Continuous g ∧
        ∀ z : apm_t91a05_Circle, g (apm_t91a05_boundaryInclusion z) = z := by
  /-
  Boundary (closer hop 1, still open): the functorial retraction step is now
  compiled above as
  `apm_t91a05_fundamentalGroupMap_injective_of_retraction`, adapted from the
  proved helper in sibling `t01A03`. Mathlib also supplies
  `Metric.contractibleSpace_closedBall`, so the disk's fundamental group is
  trivial. A proposed `g` would therefore inject the fundamental group of the
  circle into a trivial group.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, fully closed and
  partial sibling artifacts, Mathlib's `FundamentalGroupoid`, circle,
  singular-homology, contractibility, Brouwer/fixed-point, and retract APIs,
  staging directories, and git history found neither a Brouwer no-retraction
  theorem nor the remaining computation that `FundamentalGroup Circle 1` is
  nontrivial (equivalently isomorphic to `Multiplicative ℤ`). Siblings
  `t01J03`, `t93A03`, and `t02A03` independently record the same missing
  circle computation. Developing winding number or the integral `H₁` of the
  circle is the remaining foundational bridge. No unproved intermediate
  assertion was added, and the frozen statement is unchanged.
  -/
  sorry
