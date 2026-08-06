import Mathlib

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

Mathlib does not package mapping degree and oriented map-submanifold
intersection number for these sphere subtypes. Both integer-valued operations
are opaque and fully typed below. The spheres, product manifold, repaired
submanifold, continuous maps, fiber construction, and degree/intersection
equalities remain explicit.
-/

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

opaque apm_t02a08_degree (g : C(apm_t02a08_S2, apm_t02a08_S2)) : ℤ

opaque apm_t02a08_orientedIntersection
    (f : C(apm_t02a08_S2, apm_t02a08_Y)) (Z : Set apm_t02a08_Y) : ℤ

theorem apm_t02a08
    (p : Circle) (q : apm_t02a08_S2) :
    ∀ n : ℤ,
      ∃ g : C(apm_t02a08_S2, apm_t02a08_S2),
        apm_t02a08_degree g = n ∧
        apm_t02a08_orientedIntersection
          (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) = n := by
  sorry
