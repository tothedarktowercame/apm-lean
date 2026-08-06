import Mathlib

/-!
# APM t91J03

## Statement repairs

None.

## Encoding questions

The annulus is the actual product `Circle × [0,1]`, and a simple closed curve
is a native continuous embedding of `Circle`. Mathlib has no packaged winding
number for annulus-valued loops, so that integer-valued homotopy invariant is
isolated as a typed function on the genuine loop.
-/

open Set

abbrev apm_t91J03_Annulus := Circle × Set.Icc (0 : ℝ) 1

/-- Winding number of a closed curve around the core of the annulus. -/
opaque apm_t91J03_windingNumber
    (gamma : C(Circle, apm_t91J03_Annulus)) : ℤ

theorem apm_t91j03
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus)) :
    (apm_t91J03_windingNumber gamma).natAbs ≠ 2 := by
  sorry
