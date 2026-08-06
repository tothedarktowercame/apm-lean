import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01J03: A twice-wound gluing of solid tori

## Statement repairs

None.

## Encoding questions

The informal "spirals twice" curve is encoded algebraically in genuine
fundamental groups. Boundary coordinates are required to be compatible with
the inclusions into the solid tori: the meridian is killed and the longitude
maps to the core generator. The glued space is the actual topological quotient.
-/

open CategoryTheory

noncomputable section

abbrev apm_t01J03_Torus := Circle × Circle
abbrev apm_t01J03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J03_Disk2 := Metric.closedBall (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_BoundaryCircle := Metric.sphere (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_SolidTorus := Circle × apm_t01J03_Disk2
abbrev apm_t01J03_BoundaryTorus := Circle × apm_t01J03_BoundaryCircle

def apm_t01J03_boundaryInclusion :
    apm_t01J03_BoundaryTorus → apm_t01J03_SolidTorus :=
  fun z ↦ (z.1, ⟨z.2.1, le_of_eq z.2.2⟩)

inductive apm_t01J03_glueRel (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus →
      Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus → Prop
  | glue (z : apm_t01J03_BoundaryTorus) :
      apm_t01J03_glueRel h
        (Sum.inl (apm_t01J03_boundaryInclusion z))
        (Sum.inr (apm_t01J03_boundaryInclusion (h z)))

def apm_t01J03_gluedSpace (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :=
  Quotient (Relation.EqvGen.setoid (apm_t01J03_glueRel h))

noncomputable instance (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) : TopologicalSpace (apm_t01J03_gluedSpace h) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t01J03_glueRel h)) z)
    inferInstance

def apm_t01J03_gluedBasepoint (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) (z₀ : apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedSpace h :=
  Quotient.mk _ (Sum.inl (apm_t01J03_boundaryInclusion z₀))

abbrev apm_t01J03_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01J03_hasTwiceSpiral
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ) : Prop :=
  (∀ g, c₁ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ z₀) g) =
      Multiplicative.ofAdd (e₁ g).toAdd.2) ∧
  (∀ g, c₂ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ (h z₀)) g) =
      Multiplicative.ofAdd (e₂ g).toAdd.2) ∧
  e₂ ((FundamentalGroup.map ⟨h, h.continuous⟩ z₀)
    (e₁.symm (Multiplicative.ofAdd (1, 0)))) =
      Multiplicative.ofAdd (1, 2)

theorem apm_t01j03 :
    Nonempty
      (FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus)) ∧
    (∀ (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
        (z₀ : apm_t01J03_BoundaryTorus)
        (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
          Multiplicative (ℤ × ℤ))
        (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
          Multiplicative (ℤ × ℤ))
        (c₁ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
        (c₂ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ),
      apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂ →
      let M := apm_t01J03_gluedSpace h
      let m₀ := apm_t01J03_gluedBasepoint h z₀
      Nonempty (FundamentalGroup M m₀ ≃* Multiplicative (ZMod 2)) ∧
      Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
      Limits.IsZero (apm_t01J03_H 2 M) ∧
      Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M)) := by
  sorry
