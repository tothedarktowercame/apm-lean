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

lemma apm_t02a06_localSign_eq_one_or_neg_one
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) :
    apm_t02a06_localSign x = 1 ∨ apm_t02a06_localSign x = -1 := by
  unfold apm_t02a06_localSign
  split_ifs <;> simp

/-- Reuses the two-term cancellation pattern proved in sibling `t01A07`. -/
lemma apm_t02a06_signedIntersection_eq_zero_of_opposite
    {normal₁ normal₂ : apm_t02a06_S2}
    (e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂)
    (h : apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1)) :
    apm_t02a06_signedIntersection e = 0 := by
  rw [apm_t02a06_signedIntersection, Fin.sum_univ_two, h]
  omega

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
  /-
  CLOSER HOP 1 boundary. Following the compiled sibling `t01A07`, the local-
  sign dichotomy and the final two-term cancellation are now proved above as
  `apm_t02a06_localSign_eq_one_or_neg_one` and
  `apm_t02a06_signedIntersection_eq_zero_of_opposite`.

  For the first conjunct, distinct great-circle sets must be converted into
  linear independence of their unit normals. Then their cross product is
  nonzero, its normalization and negative give the two intersection points,
  and orthogonal-complement dimension one proves exhaustiveness. Mathlib has
  `crossProduct` identities and finite-dimensional orthogonal-complement
  theory, but no theorem assembling this subtype equivalence or converting
  equality of the two great-circle zero sets into proportional normals.

  The second and third conjuncts are homological. The intended proofs use
  `H₂(S² × S²) ≅ ℤ²` versus `H₂(S⁴) = 0`, and `H₃(T³) = 0`, respectively.
  Mathlib's singular-homology functor is present, but searches found neither
  integral homology computations for metric spheres nor a Künneth theorem
  yielding the required product groups. Without those computations,
  homeomorphism invariance and functoriality alone cannot close either claim.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/` modules,
  closed sphere/homology/intersection artifacts (including `t01A07`),
  Mathlib's cross-product, orthogonal-complement, singular-homology, Künneth,
  and sphere sources, and git history. Only the elementary signed-sum pattern
  was reusable; the geometric classification and homology bridges remain.
  -/
  sorry
