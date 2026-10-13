import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz

/-! # Rational homology interface for the t99J05 closure

This file fixes the exact output required from the `CP n` homology computation.
It deliberately contains no numerical Lefschetz assertion: the trace
calculation consumes this data in the next milestone.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.t99J05Closure

/-- The rational singular-homology data of `CP n` needed by the Lefschetz
calculation: finite dimensionality in every degree, vanishing above the top
degree and in odd degrees, and one chosen generator in each surviving even
degree. -/
structure ComplexProjectiveRationalHomologyData (n : ℕ) where
  finiteDimensional : ∀ k, FiniteDimensional ℚ (Homology (CP n) k)
  vanishesAbove : ∀ k, 2 * n < k → Subsingleton (Homology (CP n) k)
  vanishesOdd : ∀ k, Odd k → Subsingleton (Homology (CP n) k)
  evenEquiv (i : Fin (n + 1)) : Homology (CP n) (2 * i.val) ≃ₗ[ℚ] ℚ

/-- Install the finite-dimensional instance recorded by the homology data. -/
theorem ComplexProjectiveRationalHomologyData.finiteDimensionalAt
    {n : ℕ} (h : ComplexProjectiveRationalHomologyData n) (k : ℕ) :
    FiniteDimensional ℚ (Homology (CP n) k) :=
  h.finiteDimensional k

/-- Degrees above `2n` contribute no trace term. -/
theorem ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
    {n k : ℕ} (h : ComplexProjectiveRationalHomologyData n)
    (hk : 2 * n < k) : Subsingleton (Homology (CP n) k) :=
  h.vanishesAbove k hk

/-- Odd degrees contribute no trace term. -/
theorem ComplexProjectiveRationalHomologyData.subsingleton_of_odd
    {n k : ℕ} (h : ComplexProjectiveRationalHomologyData n) (hk : Odd k) :
    Subsingleton (Homology (CP n) k) :=
  h.vanishesOdd k hk

/-- The exact successor interface for the projective filtration.  Its proof is
the Mayer--Vietoris step adjoining the single cell in real dimension
`2 * (n + 1)`. -/
def ComplexProjectiveRationalHomologyStep :=
  ∀ n, ComplexProjectiveRationalHomologyData n →
    ComplexProjectiveRationalHomologyData (n + 1)

/-- A base computation for `CP 0` and the successor Mayer--Vietoris step
assemble the rational homology data in every finite projective dimension. -/
noncomputable def complexProjectiveRationalHomologyData_of_zero_of_step
    (hzero : ComplexProjectiveRationalHomologyData 0)
    (hstep : ComplexProjectiveRationalHomologyStep) :
    ∀ n, ComplexProjectiveRationalHomologyData n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      simpa only [Nat.succ_eq_add_one] using hstep n ih

#print axioms ComplexProjectiveRationalHomologyData.finiteDimensionalAt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_odd
#print axioms complexProjectiveRationalHomologyData_of_zero_of_step

end ConstructionTargets.t99J05Closure
