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

/-! ## Coherent coefficient generators -/

/-- The degree-one coefficient generator owned by the same coordinate
isomorphism as `oneChainCoefficients`. -/
def oneCoefficientGenerator {X : Type} [TopologicalSpace X]
    (σ : OneSimplex X) : AddCommGrpCat.of ℤ ⟶ OneCoefficientGroup X :=
  singularGenerator (TopCat.of X) 1 σ ≫ (oneChainCoefficientsIso X).hom

/-- The degree-zero coefficient generator owned by the same coordinate
isomorphism as the zero-chain presentation. -/
def zeroCoefficientGenerator {X : Type} [TopologicalSpace X]
    (v : ZeroSimplex X) : AddCommGrpCat.of ℤ ⟶ ZeroCoefficientGroup X :=
  singularGenerator (TopCat.of X) 0 v ≫ (zeroChainCoefficientsIso X).hom

@[simp] theorem oneCoefficientGenerator_iso_inv
    {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    oneCoefficientGenerator σ ≫ (oneChainCoefficientsIso X).inv =
      singularGenerator (TopCat.of X) 1 σ := by
  simp [oneCoefficientGenerator]

@[simp] theorem zeroCoefficientGenerator_iso_inv
    {X : Type} [TopologicalSpace X] (v : ZeroSimplex X) :
    zeroCoefficientGenerator v ≫ (zeroChainCoefficientsIso X).inv =
      singularGenerator (TopCat.of X) 0 v := by
  simp [zeroCoefficientGenerator]

/-- The owned generator still has the expected direct-sum coordinate.  This
is the sole theorem that unfolds the coordinate isomorphism's classical
choice. -/
theorem oneCoefficientGenerator_eq_directSumOf
    {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    oneCoefficientGenerator σ =
      AddCommGrpCat.ofHom (by
        letI := Classical.decEq (OneSimplex X)
        exact DirectSum.of (fun _ : OneSimplex X ↦ ℤ) σ) := by
  letI := Classical.decEq (OneSimplex X)
  change singularGenerator (TopCat.of X) 1 σ ≫
      (addCommGrpCoproductIsoDirectSum (OneSimplex X)).hom = _
  exact addCommGrpCoproductIsoDirectSum_generator σ

theorem zeroCoefficientGenerator_eq_directSumOf
    {X : Type} [TopologicalSpace X] (v : ZeroSimplex X) :
    zeroCoefficientGenerator v =
      AddCommGrpCat.ofHom (by
        letI := Classical.decEq (ZeroSimplex X)
        exact DirectSum.of (fun _ : ZeroSimplex X ↦ ℤ) v) := by
  letI := Classical.decEq (ZeroSimplex X)
  change singularGenerator (TopCat.of X) 0 v ≫
      (addCommGrpCoproductIsoDirectSum (ZeroSimplex X)).hom = _
  exact addCommGrpCoproductIsoDirectSum_generator v

/-- Terminal and initial zero-simplices in the production face convention. -/
def terminalZeroSimplex {X : Type} [TopologicalSpace X]
    (σ : OneSimplex X) : ZeroSimplex X :=
  (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 2) σ

def initialZeroSimplex {X : Type} [TopologicalSpace X]
    (σ : OneSimplex X) : ZeroSimplex X :=
  (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 2) σ

theorem terminalZeroSimplex_ofContinuousMap {X : Type} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    terminalZeroSimplex
        (singularSimplexOfContinuousMap (TopCat.of X) 1 σ) =
      singularSimplexOfContinuousMap (TopCat.of X) 0
        (σ.comp (faceAffine 0 0)) :=
  singularSimplexOfContinuousMap_face σ 0

theorem initialZeroSimplex_ofContinuousMap {X : Type} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    initialZeroSimplex
        (singularSimplexOfContinuousMap (TopCat.of X) 1 σ) =
      singularSimplexOfContinuousMap (TopCat.of X) 0
        (σ.comp (faceAffine 0 1)) :=
  singularSimplexOfContinuousMap_face σ 1

/-- The production differential in coherent coefficient coordinates is
terminal minus initial. -/
theorem degreeOneCoefficientBoundary_generator
    {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    oneCoefficientGenerator σ ≫ degreeOneCoefficientBoundary X =
      zeroCoefficientGenerator (terminalZeroSimplex σ) -
        zeroCoefficientGenerator (initialZeroSimplex σ) := by
  simp only [oneCoefficientGenerator, degreeOneCoefficientBoundary,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Category.assoc]
  rw [singularGenerator_boundary, Fin.sum_univ_two]
  simp [zeroCoefficientGenerator, terminalZeroSimplex, initialZeroSimplex,
    sub_eq_add_neg]

#print axioms oneChainOfCoefficients_coefficients
#print axioms oneChainCoefficients_finite
#print axioms degreeOneCoefficientBoundary_eq_zero_of_cycle
#print axioms oneCoefficientGenerator_eq_directSumOf
#print axioms zeroCoefficientGenerator_eq_directSumOf
#print axioms degreeOneCoefficientBoundary_generator

end ConstructionTargets.DegreeOneHurewiczSurjectivity
