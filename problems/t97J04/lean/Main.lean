import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup

/-!
# APM t97J04

## Statement repairs

The spelling `meridinal` is corrected to `meridional`. No mathematical
hypothesis or conclusion is changed.

## Encoding questions

The given decomposition deformation retracts to a torus wedged with the
remaining longitude circle. Following `t02A03`, this is retained as an actual
topological quotient rather than a numerical surrogate. Its fundamental group
is the actual presented group `<a,b,d | [a,b]>`, and its homology groups are
integral singular homology objects in `ModuleCat ℤ`.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97J04_Torus := Circle × Circle

/-- Glue the remaining longitude circle to the torus at their basepoints. -/
inductive apm_t97J04_WedgeRel :
    Sum apm_t97J04_Torus Circle → Sum apm_t97J04_Torus Circle → Prop
  | base : apm_t97J04_WedgeRel (.inl (1, 1)) (.inr 1)

/-- The concrete deformation-retract model `T² ∨ S¹` of the specified finite
complex. -/
def apm_t97J04_X :=
  Quotient (Relation.EqvGen.setoid apm_t97J04_WedgeRel)

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97J04_Torus Circle ↦ Quotient.mk _ x) inferInstance

def apm_t97J04_basepoint : apm_t97J04_X :=
  Quotient.mk _ (.inl (1, 1))

/-- The two chosen basepoints are identified in the concrete wedge quotient. -/
lemma apm_t97J04_inl_base_eq_inr_base :
    (Quotient.mk _ (.inl (1, 1)) : apm_t97J04_X) =
      Quotient.mk _ (.inr 1) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ apm_t97J04_WedgeRel.base

/-- Canonical quotient map from the disjoint union to the wedge. -/
def apm_t97J04_wedgeQuotient :
    Sum apm_t97J04_Torus Circle → apm_t97J04_X :=
  fun x ↦ Quotient.mk _ x

lemma apm_t97J04_continuous_wedgeQuotient :
    Continuous apm_t97J04_wedgeQuotient := by
  exact continuous_coinduced_rng

lemma apm_t97J04_surjective_wedgeQuotient :
    Function.Surjective apm_t97J04_wedgeQuotient := by
  exact Quotient.mk_surjective

def apm_t97J04_torusInclusion : apm_t97J04_Torus → apm_t97J04_X :=
  fun x ↦ apm_t97J04_wedgeQuotient (.inl x)

def apm_t97J04_circleInclusion : Circle → apm_t97J04_X :=
  fun z ↦ apm_t97J04_wedgeQuotient (.inr z)

lemma apm_t97J04_continuous_torusInclusion :
    Continuous apm_t97J04_torusInclusion := by
  exact apm_t97J04_continuous_wedgeQuotient.comp continuous_inl

lemma apm_t97J04_continuous_circleInclusion :
    Continuous apm_t97J04_circleInclusion := by
  exact apm_t97J04_continuous_wedgeQuotient.comp continuous_inr

/-- Compatible maps out of the two summands respect the generated relation. -/
lemma apm_t97J04_wedgeDesc_respects
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) {x y}
    (hxy : Relation.EqvGen apm_t97J04_WedgeRel x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | base => exact hbase
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous pushout eliminator for the concrete wedge quotient. -/
noncomputable def apm_t97J04_wedgeDesc
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) : C(apm_t97J04_X, Z) := by
  let raw : Sum apm_t97J04_Torus Circle → Z := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy ↦
      apm_t97J04_wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift (fun _ _ hxy ↦
      apm_t97J04_wedgeDesc_respects f g hbase hxy)⟩

@[simp] lemma apm_t97J04_wedgeDesc_torusInclusion
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (x : apm_t97J04_Torus) :
    apm_t97J04_wedgeDesc f g hbase (apm_t97J04_torusInclusion x) = f x := rfl

@[simp] lemma apm_t97J04_wedgeDesc_circleInclusion
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (z : Circle) :
    apm_t97J04_wedgeDesc f g hbase (apm_t97J04_circleInclusion z) = g z := rfl

/-- The descended map is uniquely determined by its two restrictions. -/
lemma apm_t97J04_wedgeDesc_unique
    {Z : Type*} [TopologicalSpace Z]
    (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z))
    (hbase : f (1, 1) = g 1) (u : C(apm_t97J04_X, Z))
    (huT : ∀ x, u (apm_t97J04_torusInclusion x) = f x)
    (huC : ∀ z, u (apm_t97J04_circleInclusion z) = g z) :
    u = apm_t97J04_wedgeDesc f g hbase := by
  ext y
  obtain ⟨x, rfl⟩ := apm_t97J04_surjective_wedgeQuotient y
  cases x with
  | inl x => exact huT x
  | inr z => exact huC z

/-- Collapse the circle summand to the wedge point, giving a continuous
retraction onto the torus summand. -/
noncomputable def apm_t97J04_torusRetraction :
    C(apm_t97J04_X, apm_t97J04_Torus) :=
  apm_t97J04_wedgeDesc (ContinuousMap.id apm_t97J04_Torus)
    (ContinuousMap.const Circle (1, 1)) rfl

@[simp] lemma apm_t97J04_torusRetraction_torusInclusion
    (x : apm_t97J04_Torus) :
    apm_t97J04_torusRetraction (apm_t97J04_torusInclusion x) = x := rfl

/-- Collapse the torus summand to the wedge point, giving a continuous
retraction onto the circle summand. -/
noncomputable def apm_t97J04_circleRetraction : C(apm_t97J04_X, Circle) :=
  apm_t97J04_wedgeDesc (ContinuousMap.const apm_t97J04_Torus 1)
    (ContinuousMap.id Circle) rfl

@[simp] lemma apm_t97J04_circleRetraction_circleInclusion (z : Circle) :
    apm_t97J04_circleRetraction (apm_t97J04_circleInclusion z) = z := rfl

/-- Both canonical summand maps are injective, witnessed by the compiled
retractions rather than by analysis of the generated equivalence relation. -/
lemma apm_t97J04_summandInclusions_injective :
    Function.Injective apm_t97J04_torusInclusion ∧
      Function.Injective apm_t97J04_circleInclusion := by
  constructor
  · exact Function.LeftInverse.injective
      apm_t97J04_torusRetraction_torusInclusion
  · exact Function.LeftInverse.injective
      apm_t97J04_circleRetraction_circleInclusion

/-- The relation `[a,b]` in the requested three-generator presentation. -/
def apm_t97J04_relator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 *
    (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

abbrev apm_t97J04_piOne :=
  PresentedGroup ({apm_t97J04_relator} : Set (FreeGroup (Fin 3)))

/-- Integral singular homology of the specified complex. -/
abbrev apm_t97J04_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_X))

/-- Why this unblocks the fundamental-group conjunct of `apm_t97j04`: this
is Seifert--van Kampen for the concrete pushout `T² ∨ S¹`, including the
basepoint identification already proved above. The torus contributes the
single commutator relation and the extra circle contributes the third free
generator. -/
theorem apm_t97J04_bridge_1 :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) := by
  sorry

/-- Why this unblocks the four homology conjuncts of `apm_t97j04`: this is
the singular Mayer--Vietoris (equivalently cellular-to-singular) computation
for the actual wedge quotient `T² ∨ S¹`, stated simultaneously in every
degree needed by the frozen theorem. -/
theorem apm_t97J04_bridge_2 :
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  sorry

theorem apm_t97j04 :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  /-
  PARTIAL boundary (closer hop 1).

  The concrete quotient bookkeeping now has a compiled basepoint bridge:
  `apm_t97J04_inl_base_eq_inr_base` proves that the torus and circle
  basepoints agree in `apm_t97J04_X` directly from the generating relation.

  The remaining proof needs Seifert--van Kampen for this EqvGen quotient to
  identify its fundamental group with the frozen presentation, and singular
  Mayer--Vietoris (or a cellular-to-singular comparison) to compute all four
  homology claims.  `t02A03` uses the identical `T² ∨ S¹` quotient and records
  the same boundary.  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  closed topology artifacts, Mathlib's fundamental-groupoid product/pushout
  sources, singular homology, exact-sequence and CW-complex sources, and git
  history found product preservation but no circle fundamental-group
  computation, van Kampen theorem, singular Mayer--Vietoris sequence, or
  cellular comparison theorem capable of closing these frozen conjuncts.

  CLOSER HOP 2: following the compiled quotient-eliminator pattern in sibling
  `t02A03`, the full topological pushout interface is now explicit.
  `apm_t97J04_wedgeQuotient` is continuous and surjective; the torus and
  circle inclusions are continuous; and `apm_t97J04_wedgeDesc`, its two
  computation lemmas, and `apm_t97J04_wedgeDesc_unique` prove the continuous
  universal property for compatible maps. Thus quotient bookkeeping and the
  point-set pushout eliminator are closed. Searches beyond hop 1 also checked
  Mathlib's categorical `IsVanKampenColimit` and sheaf-cohomology
  Mayer--Vietoris developments. The former is a general stability property of
  colimits, not Seifert--van Kampen for fundamental groups, and the latter
  does not compute singular homology. No circle/torus fundamental-group
  computation, singular Mayer--Vietoris sequence, or cellular comparison was
  found, so the five frozen invariant claims remain open.

  CLOSER HOP 3: the pushout eliminator now constructs explicit continuous
  retractions onto both summands. `apm_t97J04_torusRetraction` collapses the
  circle and is definitionally a left inverse to the torus inclusion;
  `apm_t97J04_circleRetraction` does the converse. The compiled theorem
  `apm_t97J04_summandInclusions_injective` consequently proves both canonical
  inclusions injective without analyzing `Relation.EqvGen`. This supplies
  split summand data that a future functorial homology or fundamental-group
  argument can consume. Renewed searches of `LEMMA-INDEX.md`,
  `ConstructionTargets/`, wedge siblings, Mathlib's singular-homology,
  fundamental-groupoid, van Kampen, and Mayer--Vietoris sources, and git
  history still found no theorem computing the circle/torus invariants or
  assembling them across this wedge. The five frozen invariant claims remain
  open and the statement is unchanged.
  -/
  sorry
