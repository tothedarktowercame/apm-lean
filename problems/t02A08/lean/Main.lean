import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t02A08

## Statement repairs

The printed target `Z = {p} × S²` has dimension two. Its intersection with
the image of `f : S² → S¹ × S²` is therefore one-dimensional, so the stated
integer-valued oriented intersection number is not defined. Following the
supplied solution, `Z` is minimally replaced by the complementary-dimensional
circle `S¹ × {q}`. The constructed maps still land in the fiber `{p} × S²`
named in the source and wrap that fiber with degree `n`.

The notation `I_X` is corrected to `I_Y`, since the ambient manifold is `Y`.

## Encoding questions

Degree is encoded through the actual map induced on integral second singular
homology, after choosing the sphere's orientation isomorphism with `ℤ`.
Intersection with the repaired cycle `S¹ × {q}` is the degree of the second
projection, with the cycle pinned by an equality rather than hidden behind an
opaque integer-valued operation.
-/

open CategoryTheory

noncomputable section

abbrev apm_t02a08_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a08_S2 := Metric.sphere (0 : apm_t02a08_E3) 1
abbrev apm_t02a08_Y := Circle × apm_t02a08_S2

def apm_t02a08_Z (q : apm_t02a08_S2) : Set apm_t02a08_Y :=
  {y | y.2 = q}

def apm_t02a08_fiberMap
    (p : Circle) (g : C(apm_t02a08_S2, apm_t02a08_S2)) :
    C(apm_t02a08_S2, apm_t02a08_Y) :=
  (ContinuousMap.const apm_t02a08_S2 p).prodMk g

abbrev apm_t02a08_H2 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a08_S2))

def apm_t02a08_H2Map (g : C(apm_t02a08_S2, apm_t02a08_S2)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)

def apm_t02a08_HasDegree
    (g : C(apm_t02a08_S2, apm_t02a08_S2)) (n : ℤ) : Prop :=
  ∃ orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ,
    ∀ a : apm_t02a08_H2,
      orientation.hom (apm_t02a08_H2Map g a) = n * orientation.hom a

def apm_t02a08_secondProjection : C(apm_t02a08_Y, apm_t02a08_S2) :=
  ⟨Prod.snd, continuous_snd⟩

def apm_t02a08_HasOrientedIntersection
    (f : C(apm_t02a08_S2, apm_t02a08_Y))
    (Z : Set apm_t02a08_Y) (n : ℤ) : Prop :=
  ∃ q : apm_t02a08_S2,
    Z = apm_t02a08_Z q ∧
    apm_t02a08_HasDegree (apm_t02a08_secondProjection.comp f) n

theorem apm_t02a08
    (p : Circle) (q : apm_t02a08_S2) :
    ∀ n : ℤ,
      ∃ g : C(apm_t02a08_S2, apm_t02a08_S2),
        apm_t02a08_HasDegree g n ∧
        apm_t02a08_HasOrientedIntersection
          (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) n := by
  sorry
