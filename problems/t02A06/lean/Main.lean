import Mathlib

/-!
# APM t02A06

## Statement repairs

For part (a), the two great circles are required to be distinct; otherwise
their oriented intersection number is not defined by transverse point-counting.
In part (c), “a degree map” is read as “a map of nonzero degree”. Without
“nonzero”, every continuous map between the stated oriented manifolds has a
degree and the assertion would be vacuous rather than the intended question.

## Encoding questions

Mathlib has no unified API for oriented intersection numbers, smooth
diffeomorphisms of these sphere subtypes, or mapping degree. These three
operations are isolated as typed placeholders. The spheres, great circles,
product spaces, maps, and the three negative answers remain explicit.
-/

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

opaque apm_t02a06_orientedGreatCircleIntersection
    (normal₁ normal₂ : apm_t02a06_S2) : ℤ

opaque apm_t02a06_IsDiffeomorphism
    (f : apm_t02a06_S2 × apm_t02a06_S2 ≃ apm_t02a06_S4) : Prop

opaque apm_t02a06_degree (f : C(apm_t02a06_S3, apm_t02a06_T3)) : ℤ

theorem apm_t02a06 :
    (∀ normal₁ normal₂ : apm_t02a06_S2,
      apm_t02a06_greatCircle normal₁ ≠ apm_t02a06_greatCircle normal₂ →
        apm_t02a06_orientedGreatCircleIntersection normal₁ normal₂ = 0) ∧
    (¬∃ f : apm_t02a06_S2 × apm_t02a06_S2 ≃ apm_t02a06_S4,
      apm_t02a06_IsDiffeomorphism f) ∧
    (∀ f : C(apm_t02a06_S3, apm_t02a06_T3),
      apm_t02a06_degree f = 0) := by
  sorry
