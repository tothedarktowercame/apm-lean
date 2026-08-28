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

/-! ## Finite reconstruction and vertex balance -/

/-- The finite support of a one-chain in the owned coefficient coordinates. -/
noncomputable def oneChainSupport {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) : Finset (OneSimplex X) := by
  letI := Classical.decEq (OneSimplex X)
  exact (DFinsupp.toFinsupp (oneChainCoefficients z)).support

/-- Every production one-chain coefficient family is the finite sum of its
actual supported simplex generators. -/
theorem oneChainCoefficients_eq_sum_support
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) :
    oneChainCoefficients z =
      ∑ σ ∈ oneChainSupport z,
        oneCoefficientGenerator σ (oneChainCoefficients z σ) := by
  classical
  ext τ
  simp [oneChainSupport, oneCoefficientGenerator_eq_directSumOf,
    DirectSum.of_apply]

/-- Transporting the boundary through the finite reconstruction gives the
finite endpoint-difference formula. -/
theorem degreeOneCoefficientBoundary_eq_sum_endpoints
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) :
    degreeOneCoefficientBoundary X (oneChainCoefficients z) =
      ∑ σ ∈ oneChainSupport z,
        zeroCoefficientGenerator (terminalZeroSimplex σ)
          (oneChainCoefficients z σ) -
      ∑ σ ∈ oneChainSupport z,
        zeroCoefficientGenerator (initialZeroSimplex σ)
          (oneChainCoefficients z σ) := by
  conv_lhs => rw [oneChainCoefficients_eq_sum_support]
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← CategoryTheory.comp_apply, degreeOneCoefficientBoundary_generator]
  rfl

/-- Evaluation of a zero-chain coefficient at one production zero-simplex.
This definition is independent of every `DecidableEq` choice used to package
the direct sum. -/
def zeroCoefficientAt {X : Type} [TopologicalSpace X]
    (v : ZeroSimplex X) : ZeroCoefficientGroup X →+ ℤ where
  toFun a := a v
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def zeroCoefficientIndicator {X : Type} [TopologicalSpace X]
    (p v : ZeroSimplex X) (n : ℤ) : ℤ := by
  classical
  exact if v = p then n else 0

@[simp] theorem zeroCoefficientAt_generator
    {X : Type} [TopologicalSpace X] (p v : ZeroSimplex X) (n : ℤ) :
    zeroCoefficientAt p (zeroCoefficientGenerator v n) =
      zeroCoefficientIndicator p v n := by
  classical
  rw [zeroCoefficientGenerator_eq_directSumOf]
  simp [zeroCoefficientAt, zeroCoefficientIndicator, DirectSum.of_apply]

noncomputable def incomingSupport {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) (p : ZeroSimplex X) :
    Finset (OneSimplex X) := by
  classical
  exact (oneChainSupport z).filter (terminalZeroSimplex · = p)

noncomputable def outgoingSupport {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) (p : ZeroSimplex X) :
    Finset (OneSimplex X) := by
  classical
  exact (oneChainSupport z).filter (initialZeroSimplex · = p)

/-- At every zero-simplex, a cycle has equal total incoming and outgoing
coefficients among the finitely many simplices in its actual support. -/
theorem cycle_vertex_balance
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0)
    (p : ZeroSimplex X) :
    ∑ σ ∈ incomingSupport z p,
        oneChainCoefficients z σ =
      ∑ σ ∈ outgoingSupport z p,
        oneChainCoefficients z σ := by
  classical
  have hb := congrArg (zeroCoefficientAt p)
    (degreeOneCoefficientBoundary_eq_sum_endpoints z)
  rw [degreeOneCoefficientBoundary_eq_zero_of_cycle z hz] at hb
  simp only [map_zero, map_sub, map_sum] at hb
  have hin :
      ∑ σ ∈ oneChainSupport z,
          zeroCoefficientAt p
            (zeroCoefficientGenerator (terminalZeroSimplex σ)
              (oneChainCoefficients z σ)) =
        ∑ σ ∈ oneChainSupport z,
          zeroCoefficientIndicator p (terminalZeroSimplex σ)
            (oneChainCoefficients z σ) := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact zeroCoefficientAt_generator p _ _
  have hout :
      ∑ σ ∈ oneChainSupport z,
          zeroCoefficientAt p
            (zeroCoefficientGenerator (initialZeroSimplex σ)
              (oneChainCoefficients z σ)) =
        ∑ σ ∈ oneChainSupport z,
          zeroCoefficientIndicator p (initialZeroSimplex σ)
            (oneChainCoefficients z σ) := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact zeroCoefficientAt_generator p _ _
  rw [hin, hout] at hb
  have hbalance := sub_eq_zero.mp hb.symm
  simpa [incomingSupport, outgoingSupport, zeroCoefficientIndicator,
    Finset.sum_filter] using hbalance

#print axioms oneChainOfCoefficients_coefficients
#print axioms oneChainCoefficients_finite
#print axioms degreeOneCoefficientBoundary_eq_zero_of_cycle
#print axioms oneCoefficientGenerator_eq_directSumOf
#print axioms zeroCoefficientGenerator_eq_directSumOf
#print axioms degreeOneCoefficientBoundary_generator
#print axioms oneChainCoefficients_eq_sum_support
#print axioms degreeOneCoefficientBoundary_eq_sum_endpoints
#print axioms zeroCoefficientAt_generator
#print axioms cycle_vertex_balance

end ConstructionTargets.DegreeOneHurewiczSurjectivity
