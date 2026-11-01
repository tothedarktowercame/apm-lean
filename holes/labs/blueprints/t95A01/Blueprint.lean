import Mathlib
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.KleinBottlePiOne
import ConstructionTargets.StandardSurfaceFiniteCover
import ConstructionTargets.t93J03Closure
import ConstructionTargets.CoveringTotalLocPathConnected
import ConstructionTargets.SuppliedCoverAlgebra

/-!
# APM t95A01: examples and obstruction for double covers

The three imperative parts of the printed problem are encoded as one
conjunction giving their answers.

For the first part, the explicit space is the presentation complex
`S¹ ∪_{z ↦ z³} D²`.  Its displayed fundamental group is `ZMod 3`; the
statement separately records path connectedness, failure of simple
connectedness, and the absence of every connected two-sheeted covering.

For the second part, the space is the repository's concrete `aabb` polygon
quotient model of the Klein bottle.  Non-orientability is stated intrinsically,
as vanishing of integral `H₂` of this closed surface (a closed connected orientable
surface has `H₂ = ℤ`), and the asserted self-map is a genuine covering map with
every fibre of cardinal two.  Compactness is included explicitly; “surface” is carried by the
standard disk-polygon quotient construction itself.

For the third part, “finite fundamental group” is expressed by `Finite` on
the actual based fundamental group.  The conclusion universally rules out a
two-sheeted covering self-map of every path-connected space.  No local
path-connectedness or semilocally-simply-connectedness is added: the
nonexistence direction only uses path lifting for the supplied covering map.
-/

open Set
open ConstructionTargets
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APM.T95A01

/-- The degree-three attaching loop used for the explicit `ℤ/3` presentation
complex. -/
def degreeThreeLoop : C(Circle, Circle) where
  toFun z := z ^ (3 : ℕ)
  continuous_toFun := continuous_pow 3

/-- The concrete presentation complex `S¹ ∪_{z ↦ z³} D²`. -/
abbrev ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.Cell degreeThreeLoop

/-- Its canonical basepoint, coming from `1 ∈ S¹`. -/
def threePresentationBasepoint : ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.cellIncl degreeThreeLoop 1

/-- The exact `aabb` polygon pairing whose quotient is the concrete Klein
bottle used below. -/
abbrev KleinPairing := ConstructionTargets.t93J03Closure.kleinPairingData

/-- Compute van Kampen for the degree-three cell attachment.  Apply
`AttachTwoCell.cell_piOne` with its sorry-free cover, contraction, homotopy
equivalence and generator lemmas; identify the normal closure of the cube in
the one-generator free group with `Multiplicative (ZMod 3)`. -/
theorem threePresentationComplex_piOne :
    Nonempty
      (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
        Multiplicative (ZMod 3)) := by
  sorry

/-- A connected two-sheeted cover would have an index-two induced subgroup
of `ZMod 3`.  First use
`IsCoveringMap.totalLocPathConnectedSpace` and connectedness to obtain a
path-connected total space, then `coveringFiberCard_eq_index`; transport the
subgroup through the supplied group equivalence and contradict divisibility
of the order three group. -/
theorem threePresentationComplex_no_connected_double_cover
    (hpi : Nonempty
      (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
        Multiplicative (ZMod 3))) :
    ∀ (E : Type) [TopologicalSpace E] [ConnectedSpace E]
        (p : E → ThreePresentationComplex),
      ¬ (IsCoveringMap p ∧
        ∀ x : ThreePresentationComplex,
          Nat.card {e : E // p e = x} = 2) := by
  sorry

/-- The degree-two singular homology of the `aabb` polygon vanishes.  Use
`PolygonSurfaceHomology.lowDegreeHomology`, compute its `BoundaryKernel` as
bottom from the two `-2` attaching coordinates, and transport through
`t93J03Closure.kleinPairingSpaceHomeomorph`. -/
theorem kleinBottle_h2_isZero :
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of KleinBottle)) := by
  sorry

/-- Construct the double self-cover on the affine-plane orbit model.  Use
`(x,y) ↦ (2*x,y)`, equivariant for the injective Klein-group endomorphism
`(m,n) ↦ (2*m,n)` of index two; descend it and use properly discontinuous
orbit charts plus the two cosets to prove the covering and fibre count. -/
theorem kleinPlaneQuotient_double_self_cover :
    ∃ p : ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient →
        ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient,
      IsCoveringMap p ∧
      ∀ x, Nat.card {y // p y = x} = 2 := by
  sorry

/-- Conjugating a finite-sheeted self-cover by a homeomorphism preserves both
`IsCoveringMap` and the exact fibre cardinality.  Use
`IsCoveringMap.homeomorph_comp`, `Homeomorph.isCoveringMap`, and the induced
equivalence between corresponding fibres. -/
theorem double_self_cover_conjugate_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X → X) (hp : IsCoveringMap p)
    (hcard : ∀ x : X, Nat.card {y : X // p y = x} = 2) :
    ∃ q : Y → Y, IsCoveringMap q ∧
      ∀ y : Y, Nat.card {z : Y // q z = y} = 2 := by
  sorry

/-- Assembly of the affine quotient cover and the banked homeomorphism to the
disk-polygon Klein bottle. -/
theorem kleinBottle_double_self_cover :
    ∃ p : KleinBottle → KleinBottle,
      IsCoveringMap p ∧
      ∀ x : KleinBottle, Nat.card {y : KleinBottle // p y = x} = 2 := by
  obtain ⟨p, hp, hcard⟩ := kleinPlaneQuotient_double_self_cover
  obtain ⟨e⟩ :=
    ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_homeomorph
  exact double_self_cover_conjugate_homeomorph e p hp hcard

/-- A finite fundamental group cannot contain an isomorphic index-two copy of
itself.  Use `coveringInducedFundamentalGroupMap_injective` and
`coveringFiberCard_eq_index`; path-connectedness supplies the coset/fibre
equivalence without any local hypotheses.  Compare finite cardinalities of
the domain group and the induced range. -/
theorem finite_piOne_no_double_self_cover :
    ∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
      Finite (FundamentalGroup X x) →
      ∀ p : X → X,
        ¬ (IsCoveringMap p ∧
          ∀ z : X, Nat.card {y : X // p y = z} = 2) := by
  sorry

end APM.T95A01

open APM.T95A01

#check ConstructionTargets.AttachTwoCell.cell_piOne
#check ConstructionTargets.coveringInducedFundamentalGroupMap_injective
#check ConstructionTargets.coveringFiberCard_eq_index
#check ConstructionTargets.CoveringTotalLocPathConnected.IsCoveringMap.totalLocPathConnectedSpace
#check ConstructionTargets.PolygonSurfaceHomology.lowDegreeHomology
#check ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_homeomorph

/-- APM t95A01.  The answers are respectively the degree-three presentation
complex, the Klein bottle, and nonexistence in the finite-fundamental-group
case. -/
theorem apm_t95a01 :
    (Nonempty ThreePresentationComplex ∧
      IsPathConnected (Set.univ : Set ThreePresentationComplex) ∧
      Nonempty
        (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
          Multiplicative (ZMod 3)) ∧
      ¬ SimplyConnectedSpace ThreePresentationComplex ∧
      ∀ (E : Type) [TopologicalSpace E] [ConnectedSpace E]
          (p : E → ThreePresentationComplex),
        ¬ (IsCoveringMap p ∧
          ∀ x : ThreePresentationComplex,
            Nat.card {e : E // p e = x} = 2)) ∧
    (CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of KleinBottle)) ∧
      IsCompact (Set.univ : Set KleinBottle) ∧
      ∃ p : KleinBottle → KleinBottle,
        IsCoveringMap p ∧
        ∀ x : KleinBottle, Nat.card {y : KleinBottle // p y = x} = 2) ∧
    (∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
      Finite (FundamentalGroup X x) →
      ∀ p : X → X,
        ¬ (IsCoveringMap p ∧
          ∀ z : X, Nat.card {y : X // p y = z} = 2)) := by
  have hpath : PathConnectedSpace ThreePresentationComplex :=
    (ConstructionTargets.AttachTwoCell.cell_pathConnected degreeThreeLoop
      (ConstructionTargets.AttachTwoCell.cell_overlap_hequiv degreeThreeLoop)
      (ConstructionTargets.AttachTwoCell.cell_outer_hequiv degreeThreeLoop)).2.2
  have hpi := threePresentationComplex_piOne
  have hnotsc : ¬ SimplyConnectedSpace ThreePresentationComplex := by
    intro hsc
    letI : SimplyConnectedSpace ThreePresentationComplex := hsc
    obtain ⟨e⟩ := hpi
    have htriv : Subsingleton (Path.Homotopic.Quotient
        threePresentationBasepoint threePresentationBasepoint) :=
      inferInstance
    have heq : e.symm (Multiplicative.ofAdd (0 : ZMod 3)) =
        e.symm (Multiplicative.ofAdd (1 : ZMod 3)) := htriv.elim _ _
    have hzero : (Multiplicative.ofAdd (0 : ZMod 3)) =
        Multiplicative.ofAdd (1 : ZMod 3) :=
      e.symm.injective heq
    have := congrArg Multiplicative.toAdd hzero
    norm_num at this
  have hcompact : IsCompact (Set.univ : Set KleinBottle) := by
    rw [← Set.image_univ_of_surjective
      (ConstructionTargets.Surfaces.surjective_surfaceQuotient false 2)]
    exact isCompact_univ.image
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 2)
  refine ⟨?_, ?_, finite_piOne_no_double_self_cover⟩
  · exact ⟨⟨threePresentationBasepoint⟩,
      pathConnectedSpace_iff_univ.mp hpath, hpi, hnotsc,
      threePresentationComplex_no_connected_double_cover hpi⟩
  · exact ⟨kleinBottle_h2_isZero, hcompact,
      kleinBottle_double_self_cover⟩
