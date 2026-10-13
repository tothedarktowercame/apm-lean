import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SingularHomologyConcrete

/-! # Blueprint for APM t03J02 -/

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

/-- LIBRARY: the common collar/open-cover comparison for the concrete quotient.
It packages exactly the shared geometric input needed by both invariant computations. -/
theorem apm_t03J02_pushout_openCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) :
    ∃ U V : Set (apm_t03J02_space j₁ j₂),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
      Nonempty (ContinuousMap.HomotopyEquiv U apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv V apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv
        (U ∩ V : Set (apm_t03J02_space j₁ j₂)) Circle) := by
  sorry

/-- LIBRARY: van Kampen plus the algebraic identification of the two trivial
attaching legs.  The open-cover conclusion is supplied as a hypothesis so this
program can run in parallel with the homology program after the geometry lands. -/
theorem apm_t03J02_fundamentalGroup_of_openCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (z₀ : Circle)
    (hcover : ∃ U V : Set (apm_t03J02_space j₁ j₂),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
      Nonempty (ContinuousMap.HomotopyEquiv U apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv V apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv
        (U ∩ V : Set (apm_t03J02_space j₁ j₂)) Circle)) :
    Nonempty
      (FundamentalGroup (apm_t03J02_space j₁ j₂)
        (apm_t03J02_basepoint j₁ j₂ z₀) ≃*
          apm_t03J02_freeProductZ2Z2) := by
  sorry

/-- LIBRARY: singular Mayer--Vietoris and the resulting integer-module
calculation.  It consumes the same geometric conclusion as the π₁ program. -/
theorem apm_t03J02_homology_of_openCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (hcover : ∃ U V : Set (apm_t03J02_space j₁ j₂),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
      Nonempty (ContinuousMap.HomotopyEquiv U apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv V apm_t03J02_Torus) ∧
      Nonempty (ContinuousMap.HomotopyEquiv
        (U ∩ V : Set (apm_t03J02_space j₁ j₂)) Circle)) :
    Nonempty (apm_t03J02_H 0 (apm_t03J02_space j₁ j₂) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t03J02_H 1 (apm_t03J02_space j₁ j₂) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
    Nonempty (apm_t03J02_H 2 (apm_t03J02_space j₁ j₂) ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    ∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (apm_t03J02_H k (apm_t03J02_space j₁ j₂)) := by
  sorry

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
  have hcover := apm_t03J02_pushout_openCover j₁ j₂ hj₁ hj₂
  have hπ := apm_t03J02_fundamentalGroup_of_openCover
    j₁ j₂ hnull₁ hnull₂ z₀ hcover
  obtain ⟨h0, h1, h2, hhi⟩ :=
    apm_t03J02_homology_of_openCover j₁ j₂ hnull₁ hnull₂ hcover
  exact ⟨hπ, h0, h1, h2, hhi⟩

#print axioms apm_t03j02
