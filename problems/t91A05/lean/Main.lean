import Mathlib
import ConstructionTargets.CircleMetricFundamentalGroup

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
  fun z => ⟨z, z.property.le⟩

lemma apm_t91a05_continuous_boundaryInclusion :
    Continuous apm_t91a05_boundaryInclusion := by
  exact Continuous.subtype_mk continuous_subtype_val _

def apm_t91a05_circleBase : apm_t91a05_Circle :=
  ⟨1, by simp [apm_t91a05_Circle]⟩

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

/-- Once the target fundamental group is trivial and the source fundamental
group is nontrivial, the functorial injectivity lemma rules out a retraction.
This isolates the exact topological computation still missing for the circle. -/
lemma apm_t91a05_no_retraction_of_subsingleton_fundamentalGroup
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A)
    [Subsingleton (FundamentalGroup X (i a))]
    [Nontrivial (FundamentalGroup A a)] :
    ¬∃ r : C(X, A), ∀ x, r (i x) = x := by
  rintro ⟨r, hr⟩
  have hinj :=
    apm_t91a05_fundamentalGroupMap_injective_of_retraction i a r hr
  obtain ⟨p, hp⟩ := exists_ne (1 : FundamentalGroup A a)
  apply hp
  apply hinj
  apply Subsingleton.elim

/-- Concrete reduction for the frozen disk and boundary: Mathlib's
`Metric.contractibleSpace_closedBall` supplies the target-group
subsingleton instance, so only nontriviality of the exact metric circle's
fundamental group remains as an input. -/
lemma apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial
    [Nontrivial
      (FundamentalGroup apm_t91a05_Circle apm_t91a05_circleBase)] :
    ¬∃ g : apm_t91a05_Disk → apm_t91a05_Circle,
      Continuous g ∧
        ∀ z : apm_t91a05_Circle, g (apm_t91a05_boundaryInclusion z) = z := by
  let i : C(apm_t91a05_Circle, apm_t91a05_Disk) :=
    ⟨apm_t91a05_boundaryInclusion, apm_t91a05_continuous_boundaryInclusion⟩
  letI : ContractibleSpace apm_t91a05_Disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : SimplyConnectedSpace apm_t91a05_Disk :=
    SimplyConnectedSpace.ofContractible _
  letI : Subsingleton
      (FundamentalGroup apm_t91a05_Disk (i apm_t91a05_circleBase)) := by
    change Subsingleton
      (Path.Homotopic.Quotient (i apm_t91a05_circleBase)
        (i apm_t91a05_circleBase))
    infer_instance
  rintro ⟨g, hg, hretract⟩
  exact apm_t91a05_no_retraction_of_subsingleton_fundamentalGroup
    i apm_t91a05_circleBase ⟨⟨g, hg⟩, hretract⟩

/-- Why this unblocks `apm_t91a05`: the compiled reduction above proves the
frozen no-retraction theorem from exactly this instance. Mathematically it is
the nontriviality part of `π₁(S¹, 1) ≃ ℤ`. -/
theorem apm_t91A05_bridge_1 :
    Nontrivial
      (FundamentalGroup apm_t91a05_Circle apm_t91a05_circleBase) := by
  simpa [apm_t91a05_Circle, apm_t91a05_circleBase] using
    (ConstructionTargets.CircleMetricFundamentalGroup.metricCircleFundamentalGroupNontrivial :
      Nontrivial (FundamentalGroup
        ConstructionTargets.CircleMetricFundamentalGroup.MetricCircle
        (⟨1, by simp⟩ : ConstructionTargets.CircleMetricFundamentalGroup.MetricCircle)))

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

  CLOSER HOP 2 compiles the complete abstract contradiction as
  `apm_t91a05_no_retraction_of_subsingleton_fundamentalGroup`. It combines
  the hop-1 injectivity theorem with a subsingleton target fundamental group
  and a nontrivial source fundamental group, eliminating all residual group
  reasoning from the final step. A renewed search of `LEMMA-INDEX.md`,
  `ConstructionTargets/`, Mathlib's contractible-space/fundamental-group and
  circle sources, and the no-retraction siblings found no `Nontrivial` instance
  for the circle group or alternative Brouwer theorem. The disk side is
  supplied by `Metric.contractibleSpace_closedBall`; the sole foundational
  bridge remains nontriviality of the circle fundamental group.

  CLOSER HOP 3 compiles the concrete reduction that the earlier boundary only
  described. `apm_t91a05_continuous_boundaryInclusion` bundles the frozen
  subtype inclusion, while
  `apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial` installs
  `Metric.contractibleSpace_closedBall`, obtains the disk's simply-connected
  and fundamental-group subsingleton instances, and applies the hop-2
  contradiction directly to the frozen raw-function statement. Consequently
  no disk-side instance synthesis or statement-shape conversion remains.
  Searches of the native `Circle` definition (which is the same unit metric
  sphere), covering/lift sources, singular homology, winding artifacts,
  `LEMMA-INDEX.md`, `ConstructionTargets/`, and git history still found no
  compiled nontrivial loop or circle fundamental-group instance. The sole
  remaining bridge is exactly `Nontrivial (FundamentalGroup
  apm_t91a05_Circle apm_t91a05_circleBase)`. The frozen statement is
  unchanged.
  -/
  letI : Nontrivial
      (FundamentalGroup apm_t91a05_Circle apm_t91a05_circleBase) := apm_t91A05_bridge_1
  exact apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial
