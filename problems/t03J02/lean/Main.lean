import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup

/-!
# APM t03J02: two tori glued along null-homotopic circles

## Statement repairs

None.

## Encoding questions

Each simple closed curve is encoded by a topological embedding of the actual
circle into the standard torus, together with null-homotopy of that map.  The
two parameterizations encode the specified homeomorphism between the curves.
The glued space is the genuine quotient, and the free product of two copies
of `ℤ²` is given by its four-generator, two-commutator presentation.
-/

open CategoryTheory

noncomputable section

abbrev apm_t03J02_Torus := Circle × Circle

inductive apm_t03J02_glueRel
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus →
      Sum apm_t03J02_Torus apm_t03J02_Torus → Prop
  | glue (z : Circle) :
      apm_t03J02_glueRel j₁ j₂ (Sum.inl (j₁ z)) (Sum.inr (j₂ z))

def apm_t03J02_space (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :=
  Quotient (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂))

noncomputable instance (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    TopologicalSpace (apm_t03J02_space j₁ j₂) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t03J02_Torus apm_t03J02_Torus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂)) z)
    inferInstance

def apm_t03J02_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus → apm_t03J02_space j₁ j₂ :=
  fun z => Quotient.mk _ z

lemma apm_t03J02_continuous_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Continuous (apm_t03J02_quotientMap j₁ j₂) := by
  exact continuous_coinduced_rng

lemma apm_t03J02_surjective_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Function.Surjective (apm_t03J02_quotientMap j₁ j₂) := by
  exact Quotient.mk_surjective

lemma apm_t03J02_glue_eq
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z : Circle) :
    apm_t03J02_quotientMap j₁ j₂ (Sum.inl (j₁ z)) =
      apm_t03J02_quotientMap j₁ j₂ (Sum.inr (j₂ z)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t03J02_glueRel.glue z)

def apm_t03J02_basepoint
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z₀ : Circle) :
    apm_t03J02_space j₁ j₂ :=
  Quotient.mk _ (Sum.inl (j₁ z₀))

abbrev apm_t03J02_generator := Fin 2 × Fin 2

def apm_t03J02_commutatorRelation (i : Fin 2) :
    FreeGroup apm_t03J02_generator :=
  FreeGroup.of (i, 0) * FreeGroup.of (i, 1) *
    (FreeGroup.of (i, 0))⁻¹ * (FreeGroup.of (i, 1))⁻¹

abbrev apm_t03J02_freeProductZ2Z2 :=
  PresentedGroup (Set.range apm_t03J02_commutatorRelation)

abbrev apm_t03J02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem apm_t03j02
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂)
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (z₀ : Circle) :
    let X := apm_t03J02_space j₁ j₂
    let x₀ := apm_t03J02_basepoint j₁ j₂ z₀
    Nonempty (FundamentalGroup X x₀ ≃* apm_t03J02_freeProductZ2Z2) ∧
    Nonempty (apm_t03J02_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t03J02_H 1 X ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
    Nonempty (apm_t03J02_H 2 X ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t03J02_H k X) := by
  /-
  Closer hop 1 packages the quotient data explicitly:
  `apm_t03J02_quotientMap` is proved continuous and surjective, and
  `apm_t03J02_glue_eq` proves the two circle parameterizations have identical
  images pointwise in the quotient. This follows the useful quotient-map layer
  extracted in siblings `t02A03` and `t00A01`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all topology siblings,
  Mathlib's `FundamentalGroupoid`, `TopCat` limits, singular homology, pushout,
  and Mayer--Vietoris sources, plus git history, found no theorem promoting
  this `EqvGen` quotient to a topological pushout with a van Kampen computation,
  and no singular Mayer--Vietoris sequence. Mathlib also lacks the required
  concrete computations of the torus fundamental group and homology in this
  encoding. Thus the remaining bridge is substantial algebraic-topology
  infrastructure, not quotient bookkeeping; the frozen statement is unchanged.
  -/
  sorry
