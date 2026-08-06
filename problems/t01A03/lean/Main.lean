import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01A03 — three retraction problems for surfaces

## Statement repairs

None.

## Encoding note

The source specifies the inclusions pictorially.  The repaired statement uses
actual spaces and continuous inclusions, with the algebraic features visible
in those pictures stated concretely: the middle separating circle induces zero
on `H₁`, the standard circle wedge in the torus has a noninjective induced
fundamental-group map, and the final subset is the actual disjoint union of two
circles inside a connected genus-two surface.  The genus is pinned by integral
singular homology.  This replaces nine `sorry`-typed placeholder definitions.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t01a03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01a03_I2 := 𝓘(ℝ, apm_t01a03_E2)
abbrev apm_t01a03_Torus := Circle × Circle
abbrev apm_t01a03_TwoCircles := Sum Circle Circle

inductive apm_t01a03_wedgeRel :
    Sum Circle Circle → Sum Circle Circle → Prop
  | base : apm_t01a03_wedgeRel (.inl 1) (.inr 1)

def apm_t01a03_Wedge :=
  Quotient (Relation.EqvGen.setoid apm_t01a03_wedgeRel)

noncomputable instance : TopologicalSpace apm_t01a03_Wedge :=
  TopologicalSpace.coinduced
    (fun x : Sum Circle Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a03_wedgeRel) x)
    inferInstance

def apm_t01a03_wedgeBase : apm_t01a03_Wedge :=
  Quotient.mk _ (.inl 1)

abbrev apm_t01a03_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01a03_H1map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t01a03_hasGenusTwo (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01a03_H1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅ ModuleCat.of ℤ ℤ)

def apm_t01a03_HasRetraction {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) : Prop :=
  ∃ r : C(X, A), ∀ a, r (i a) = a

theorem apm_t01a03 :
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
      [PathConnectedSpace S] [ChartedSpace apm_t01a03_E2 S]
      [IsManifold apm_t01a03_I2 ∞ S],
      apm_t01a03_hasGenusTwo S →
      ∀ (middle : C(Circle, S))
        (wedgeInTorus : C(apm_t01a03_Wedge, apm_t01a03_Torus))
        (twoCircles : C(apm_t01a03_TwoCircles, S)),
        Topology.IsEmbedding middle → apm_t01a03_H1map middle = 0 →
        Topology.IsEmbedding wedgeInTorus →
        ¬Function.Injective
          (FundamentalGroup.map wedgeInTorus apm_t01a03_wedgeBase) →
        Topology.IsEmbedding twoCircles →
        ¬apm_t01a03_HasRetraction middle ∧
        ¬apm_t01a03_HasRetraction wedgeInTorus ∧
        ¬apm_t01a03_HasRetraction twoCircles := by
  sorry
