import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t02A06

## Statement repairs

For part (a), the two great circles are required to be distinct; otherwise
their oriented intersection number is not defined by transverse point-counting.
In part (c), “a degree map” is read as “a map of nonzero degree”. Without
“nonzero”, every continuous map between the stated oriented manifolds has a
degree and the assertion would be vacuous rather than the intended question.

## Encoding questions

The intersection is the actual subtype of the two great circles, with local
sign determined by the cross product of their oriented normals. Part (b) is
strengthened to the nonexistence of a homeomorphism. In part (c), degree zero
is expressed without a placeholder as vanishing of the actual induced map on
integral third singular homology.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t02a06_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t02a06_S1 := apm_t02a06_Sphere 1
abbrev apm_t02a06_S2 := apm_t02a06_Sphere 2
abbrev apm_t02a06_S3 := apm_t02a06_Sphere 3
abbrev apm_t02a06_S4 := apm_t02a06_Sphere 4
abbrev apm_t02a06_T3 := apm_t02a06_S1 × apm_t02a06_S1 × apm_t02a06_S1

def apm_t02a06_greatCircle (normal : apm_t02a06_S2) : Set apm_t02a06_S2 :=
  {x | inner ℝ (x : EuclideanSpace ℝ (Fin 3)) normal = 0}

abbrev apm_t02a06_intersection (normal₁ normal₂ : apm_t02a06_S2) :=
  {x : apm_t02a06_S2 //
    x ∈ apm_t02a06_greatCircle normal₁ ∩ apm_t02a06_greatCircle normal₂}

def apm_t02a06_localSign {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) : ℤ :=
  if 0 < dotProduct
      (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
      (x.1 : Fin 3 → ℝ) then 1 else -1

def apm_t02a06_signedIntersection {normal₁ normal₂ : apm_t02a06_S2}
    (e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂) : ℤ :=
  ∑ i : Fin 2, apm_t02a06_localSign (e i)

abbrev apm_t02a06_H3 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t02a06_H3Map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

theorem apm_t02a06 :
    (∀ normal₁ normal₂ : apm_t02a06_S2,
      apm_t02a06_greatCircle normal₁ ≠ apm_t02a06_greatCircle normal₂ →
        ∃ e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂,
          apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1) ∧
          apm_t02a06_signedIntersection e = 0) ∧
    (¬Nonempty ((apm_t02a06_S2 × apm_t02a06_S2) ≃ₜ apm_t02a06_S4)) ∧
    (∀ f : C(apm_t02a06_S3, apm_t02a06_T3),
      apm_t02a06_H3Map f = 0) := by
  sorry
