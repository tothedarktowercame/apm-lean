import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.Surfaces
import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.TorusCircleWedgeMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters

open CategoryTheory Set

noncomputable section

abbrev apm_t97J04_Disk := ConstructionTargets.Surfaces.Disk

def apm_t97J04_edgePoint (n : ℕ) (j : Fin n)
    (t : Set.Icc (0 : ℝ) 1) : apm_t97J04_Disk :=
  ConstructionTargets.Surfaces.edgePoint n j t

inductive apm_t97J04_ComplexRel :
    Sum apm_t97J04_Disk apm_t97J04_Disk →
      Sum apm_t97J04_Disk apm_t97J04_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 0 t))
        (.inl (apm_t97J04_edgePoint 8 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 1 t))
        (.inl (apm_t97J04_edgePoint 8 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inl (apm_t97J04_edgePoint 8 6 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | d (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 5 t))
        (.inl (apm_t97J04_edgePoint 8 7 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩))
  | meridian (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inr (apm_t97J04_edgePoint 1 0 t))

def apm_t97J04_X := Quotient (Relation.EqvGen.setoid apm_t97J04_ComplexRel)

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97J04_Disk apm_t97J04_Disk ↦ Quotient.mk _ x)
    inferInstance

def apm_t97J04_basepoint : apm_t97J04_X :=
  Quotient.mk _ (.inl (0 : apm_t97J04_Disk))

def apm_t97J04_relator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

abbrev apm_t97J04_piOne :=
  PresentedGroup ({apm_t97J04_relator} : Set (FreeGroup (Fin 3)))

abbrev apm_t97J04_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_X))

abbrev apm_t97J04_W :=
  ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge

def apm_t97J04_wedgeBase : apm_t97J04_W :=
  ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase

abbrev apm_t97J04_WH (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_W))

/-- LIBRARY: collapse the meridian-capped genus-two polygon quotient to the
torus-circle wedge, with the based fundamental-group and all-degree singular
homology transports needed by the two independent invariant computations. -/
theorem apm_t97J04_complex_to_wedge :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        FundamentalGroup apm_t97J04_W apm_t97J04_wedgeBase) ∧
    (∀ k : ℕ, Nonempty (apm_t97J04_H k ≅ apm_t97J04_WH k)) := by
  sorry

/-- Pure group-presentation simplification: `ℤ² * ℤ` is the three-generator
presentation with the single commutator relation on the first two generators. -/
theorem apm_t97J04_coprod_equiv_presentation :
    Nonempty
      (Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) ≃*
        apm_t97J04_piOne) := by
  sorry

/-- Transport the already-computed torus-circle wedge invariants across the
geometric comparison.  The comparison is an explicit hypothesis so this
lemma can be proved in parallel with the library construction. -/
theorem apm_t97J04_invariants_of_comparison
    (hπ : Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        FundamentalGroup apm_t97J04_W apm_t97J04_wedgeBase))
    (hH : ∀ k : ℕ, Nonempty (apm_t97J04_H k ≅ apm_t97J04_WH k))
    (hpres : Nonempty
      (Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ) ≃*
        apm_t97J04_piOne)) :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
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
  rcases apm_t97J04_complex_to_wedge with ⟨hπ, hH⟩
  exact apm_t97J04_invariants_of_comparison hπ hH
    apm_t97J04_coprod_equiv_presentation

#print axioms apm_t97j04
