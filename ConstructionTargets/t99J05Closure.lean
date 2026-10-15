import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.CoefficientH0

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

/-- The literal quotient model `CP 0` has exactly one projective point.  This
is the geometric base of the projective filtration, proved directly from the
fixed affine-chart representation rather than replacing `CP 0` by a model. -/
theorem cp_zero_subsingleton : Subsingleton (CP 0) := by
  constructor
  intro x y
  let i : Fin 1 := 0
  have hrep (p : CP 0) : Projectivization.rep p i ≠ 0 := by
    intro hi
    apply Projectivization.rep_nonzero p
    funext j
    have hj : j = i := Fin.ext (by omega)
    simpa [hj] using hi
  rw [← chartInverse_coordinates i x (hrep x)]
  rw [← chartInverse_coordinates i y (hrep y)]
  apply congrArg (chartInverse i)
  funext j
  exact (j.2 (Fin.ext (by omega))).elim

/-- The rational singular-homology data of `CP n` needed by the Lefschetz
calculation: finite dimensionality in every degree, vanishing above the top
degree and in odd degrees, and one chosen generator in each surviving even
degree. -/
structure ComplexProjectiveRationalHomologyData (n : ℕ) where
  finiteDimensional : ∀ k, FiniteDimensional ℚ (Homology (CP n) k)
  vanishesAbove : ∀ k, 2 * n < k → Subsingleton (Homology (CP n) k)
  vanishesOdd : ∀ k, Odd k → Subsingleton (Homology (CP n) k)
  evenEquiv (i : Fin (n + 1)) : Homology (CP n) (2 * i.val) ≃ₗ[ℚ] ℚ

/-- The exact singular-homology output needed for a nonempty one-point space.
The chain-level computation will construct this structure; it contains no
projective-space-specific data. -/
structure NonemptySubsingletonRationalHomologyData (X : Type)
    [TopologicalSpace X] where
  finiteDimensional : ∀ k, FiniteDimensional ℚ (Homology X k)
  vanishesPositive : ∀ k, 0 < k → Subsingleton (Homology X k)
  zeroEquiv : Homology X 0 ≃ₗ[ℚ] ℚ

/-- A nonempty subsingleton is contractible, so its rational singular
homology is `ℚ` in degree zero and vanishes in every positive degree. -/
noncomputable def t99J05_subsingleton_rational_homology
    (X : Type) [TopologicalSpace X] [Nonempty X] [Subsingleton X] :
    NonemptySubsingletonRationalHomologyData X where
  finiteDimensional k := by
    by_cases hk : k = 0
    · subst k
      exact (ConstructionTargets.CoefficientH0.h0Iso ℚ
        (Classical.choice inferInstance)).toLinearEquiv.symm.finiteDimensional
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
        ℚ X k hk
      letI : Subsingleton (Homology X k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact FiniteDimensional.of_injective
        (0 : Homology X k →ₗ[ℚ] ℚ)
        (Function.injective_of_subsingleton _)
  vanishesPositive k hk :=
    ModuleCat.isZero_iff_subsingleton.mp
      (ConstructionTargets.CoefficientContractiblePair.higher_zero
        ℚ X k (Nat.ne_of_gt hk))
  zeroEquiv := (ConstructionTargets.CoefficientH0.h0Iso ℚ
    (Classical.choice inferInstance)).toLinearEquiv

/-- The generic one-point homology calculation, once supplied, gives the full
base datum for the literal `CP 0` quotient. -/
noncomputable def cpZeroHomologyDataOfSubsingletonData
    (h : NonemptySubsingletonRationalHomologyData (CP 0)) :
    ComplexProjectiveRationalHomologyData 0 where
  finiteDimensional := h.finiteDimensional
  vanishesAbove k hk := h.vanishesPositive k (by simpa using hk)
  vanishesOdd k hk := h.vanishesPositive k hk.pos
  evenEquiv i := by
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa using h.zeroEquiv

/-- The complete rational homology datum for the literal quotient model
`CP 0`, obtained from its proved singleton property. -/
noncomputable def t99J05_cp_zero_rational_homology :
    ComplexProjectiveRationalHomologyData 0 := by
  let p : CP 0 := chartInverse (0 : Fin 1)
    (0 : AffineCoordinates (0 : Fin 1))
  letI : Nonempty (CP 0) := ⟨p⟩
  letI : Subsingleton (CP 0) := cp_zero_subsingleton
  exact cpZeroHomologyDataOfSubsingletonData
    (t99J05_subsingleton_rational_homology (CP 0))

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
#print axioms cp_zero_subsingleton
#print axioms cpZeroHomologyDataOfSubsingletonData
#print axioms t99J05_subsingleton_rational_homology
#print axioms t99J05_cp_zero_rational_homology
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_odd
#print axioms complexProjectiveRationalHomologyData_of_zero_of_step

end ConstructionTargets.t99J05Closure
