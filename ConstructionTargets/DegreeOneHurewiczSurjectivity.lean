import ConstructionTargets.DegreeOneHurewiczMap

/-!
# Finite coefficient infrastructure for degree-one Hurewicz surjectivity

This file exposes the production degree-one chain group as the genuine direct
sum of its singular-simplex coefficients and transports the differential to
that direct-sum presentation.  It does not assume or prove Hurewicz
surjectivity.
-/

noncomputable section

namespace ConstructionTargets.DegreeOneHurewiczSurjectivity

open CategoryTheory
open ConstructionTargets.SingularSubdivision

abbrev OneSimplex (X : Type) [TopologicalSpace X] :=
  SingularSimplex (TopCat.of X) 1

abbrev ZeroSimplex (X : Type) [TopologicalSpace X] :=
  SingularSimplex (TopCat.of X) 0

abbrev OneCoefficientGroup (X : Type) [TopologicalSpace X] :=
  AddCommGrpCat.of (DirectSum (OneSimplex X) (fun _ ↦ ℤ))

abbrev ZeroCoefficientGroup (X : Type) [TopologicalSpace X] :=
  AddCommGrpCat.of (DirectSum (ZeroSimplex X) (fun _ ↦ ℤ))

/-- The canonical production-chain/direct-sum coordinate isomorphism in
degree one. -/
def oneChainCoefficientsIso (X : Type) [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).X 1 ≅ OneCoefficientGroup X :=
  by
    letI := Classical.decEq (OneSimplex X)
    exact addCommGrpCoproductIsoDirectSum (OneSimplex X)

/-- The analogous coordinate isomorphism in degree zero. -/
def zeroChainCoefficientsIso (X : Type) [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).X 0 ≅ ZeroCoefficientGroup X :=
  by
    letI := Classical.decEq (ZeroSimplex X)
    exact addCommGrpCoproductIsoDirectSum (ZeroSimplex X)

def oneChainCoefficients {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) : OneCoefficientGroup X :=
  (oneChainCoefficientsIso X).hom z

def oneChainOfCoefficients {X : Type} [TopologicalSpace X]
    (a : OneCoefficientGroup X) : (SingularChains (TopCat.of X)).X 1 :=
  (oneChainCoefficientsIso X).inv a

@[simp] theorem oneChainOfCoefficients_coefficients
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) :
    oneChainOfCoefficients (oneChainCoefficients z) = z := by
  exact (oneChainCoefficientsIso X).hom_inv_id_apply z

@[simp] theorem oneChainCoefficients_ofCoefficients
    {X : Type} [TopologicalSpace X] (a : OneCoefficientGroup X) :
    oneChainCoefficients (oneChainOfCoefficients a) = a := by
  exact (oneChainCoefficientsIso X).inv_hom_id_apply a

/-- The simplex support of every production one-chain is finite. -/
theorem oneChainCoefficients_finite {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) :
    Set.Finite {σ | oneChainCoefficients z σ ≠ 0} := by
  exact DFinsupp.finite_support _

/-- The production differential conjugated into the two direct-sum
coefficient presentations. -/
def degreeOneCoefficientBoundary (X : Type) [TopologicalSpace X] :
    OneCoefficientGroup X ⟶ ZeroCoefficientGroup X :=
  (oneChainCoefficientsIso X).inv ≫
    (SingularChains (TopCat.of X)).d 1 0 ≫
      (zeroChainCoefficientsIso X).hom

theorem degreeOneCoefficientBoundary_apply
    {X : Type} [TopologicalSpace X] (z : (SingularChains (TopCat.of X)).X 1) :
    degreeOneCoefficientBoundary X (oneChainCoefficients z) =
      (zeroChainCoefficientsIso X).hom
        ((SingularChains (TopCat.of X)).d 1 0 z) := by
  simp [degreeOneCoefficientBoundary, oneChainCoefficients]

/-- A production cycle has zero boundary after transport to the actual finite
coefficient presentation. -/
theorem degreeOneCoefficientBoundary_eq_zero_of_cycle
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    degreeOneCoefficientBoundary X (oneChainCoefficients z) = 0 := by
  rw [degreeOneCoefficientBoundary_apply, hz]
  exact map_zero _

#print axioms oneChainOfCoefficients_coefficients
#print axioms oneChainCoefficients_finite
#print axioms degreeOneCoefficientBoundary_eq_zero_of_cycle

end ConstructionTargets.DegreeOneHurewiczSurjectivity
