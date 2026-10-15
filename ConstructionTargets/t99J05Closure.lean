import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.CoefficientH0
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

/-! # Rational homology interface for the t99J05 closure

This file fixes the exact output required from the `CP n` homology computation.
It deliberately contains no numerical Lefschetz assertion: the trace
calculation consumes this data in the next milestone.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.ProjectiveQuotientDescent
open Set Topology
open scoped ContinuousMap

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

/-- The last-coordinate affine chart in `CP (n+1)`, which supplies the open
cell in the projective-filtration Mayer--Vietoris step. -/
def cpSuccessorTopPatch (n : ℕ) : Set (CP (n + 1)) :=
  {p | Projectivization.rep p (Fin.last (n + 1)) ≠ 0}

/-- The union of all affine charts except the last-coordinate chart.  This is
the open neighborhood of the embedded lower projective space used by the
successor step. -/
def cpSuccessorLowerPatch (n : ℕ) : Set (CP (n + 1)) :=
  {p | ∃ i : Fin (n + 2), i ≠ Fin.last (n + 1) ∧
    Projectivization.rep p i ≠ 0}

theorem cpSuccessorTopPatch_isOpen (n : ℕ) :
    IsOpen (cpSuccessorTopPatch n) := by
  simpa [cpSuccessorTopPatch] using
    (affineSource_isOpen (Fin.last (n + 1)))

theorem cpSuccessorLowerPatch_isOpen (n : ℕ) :
    IsOpen (cpSuccessorLowerPatch n) := by
  rw [show cpSuccessorLowerPatch n =
      ⋃ i : {i : Fin (n + 2) // i ≠ Fin.last (n + 1)},
        {p : CP (n + 1) | Projectivization.rep p i.1 ≠ 0} by
    ext p
    simp [cpSuccessorLowerPatch]]
  exact isOpen_iUnion (fun i ↦ affineSource_isOpen i.1)

/-- The two filtration patches cover the literal quotient model
`CP (n+1)`. -/
theorem cpSuccessor_openCover (n : ℕ) :
    IsOpen (cpSuccessorLowerPatch n) ∧
      IsOpen (cpSuccessorTopPatch n) ∧
      cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n = Set.univ := by
  refine ⟨cpSuccessorLowerPatch_isOpen n, cpSuccessorTopPatch_isOpen n, ?_⟩
  apply Set.eq_univ_of_forall
  intro p
  by_cases hlast : Projectivization.rep p (Fin.last (n + 1)) ≠ 0
  · exact Or.inr hlast
  · left
    change ∃ i : Fin (n + 2), i ≠ Fin.last (n + 1) ∧
      Projectivization.rep p i ≠ 0
    by_contra h
    push_neg at h
    apply Projectivization.rep_nonzero p
    funext i
    by_cases hi : i = Fin.last (n + 1)
    · subst i
      exact not_ne_iff.mp hlast
    · exact h i hi

/-- In the last affine chart, the overlap with the lower filtration patch is
exactly the punctured affine coordinate space. -/
theorem cpSuccessor_overlap_topCoordinates_ne_zero (n : ℕ)
    (p : CP (n + 1))
    (htop : p ∈ cpSuccessorTopPatch n) :
    p ∈ cpSuccessorLowerPatch n ↔
      coordinates (Fin.last (n + 1)) p ≠ 0 := by
  constructor
  · rintro ⟨i, hi, hrep⟩ hzero
    have hcoord := congrFun hzero
      (⟨i, hi⟩ : {j : Fin (n + 2) // j ≠ Fin.last (n + 1)})
    change Projectivization.rep p i /
        Projectivization.rep p (Fin.last (n + 1)) = 0 at hcoord
    exact hrep ((div_eq_zero_iff.mp hcoord).resolve_right htop)
  · intro hcoord
    by_contra hlower
    have hz : ∀ i : Fin (n + 2), i ≠ Fin.last (n + 1) →
        Projectivization.rep p i = 0 := by
      intro i hi
      by_contra hrep
      exact hlower ⟨i, hi, hrep⟩
    apply hcoord
    funext j
    change Projectivization.rep p j.1 /
      Projectivization.rep p (Fin.last (n + 1)) = 0
    rw [hz j.1 j.2]
    exact zero_div _

theorem t99J05_coordinates_continuousOn_exact {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (coordinates i)
      {x : CP n | Projectivization.rep x i ≠ 0} := by
  let s : Set (CP n) := {x | Projectivization.rep x i ≠ 0}
  let q : NonzeroVectors ℂ n → CP n := quotientMap ℂ n
  let qr := s.restrictPreimage q
  have hqr : IsOpenQuotientMap qr := by
    refine ⟨?_, continuous_quotientMap ℂ n |>.restrictPreimage, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n x
      exact ⟨⟨v, hx⟩, rfl⟩
    · exact (projectiveQuotientMap_isOpen ℂ n).restrictPreimage s
  rw [continuousOn_iff_continuous_restrict]
  apply hqr.isQuotientMap.continuous_iff.mpr
  apply continuous_pi
  intro j
  have hnum : Continuous (fun v : q ⁻¹' s => v.1.1 j.1) :=
    (continuous_apply j.1).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden : Continuous (fun v : q ⁻¹' s => v.1.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden0 : ∀ v : q ⁻¹' s, v.1.1 i ≠ 0 := by
    intro v
    exact (Set.ext_iff.mp (affineSource_preimage i) v.1).mp v.2
  convert hnum.div hden hden0 using 1
  funext v
  change (Projectivization.mk ℂ v.1.1 v.1.2).rep j.1 /
      (Projectivization.mk ℂ v.1.1 v.1.2).rep i = _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 v.1.2
  rw [← ha]
  change (a.1 * v.1.1 j.1) / (a.1 * v.1.1 i) = _
  field_simp
  rfl

theorem t99J05_chartInverse_continuous_exact {n : ℕ} (i : Fin (n + 1)) :
    Continuous (chartInverse i) := by
  apply (continuous_quotientMap ℂ n).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simpa only [dif_pos] using
      (continuous_const : Continuous (fun _ : AffineCoordinates i => (1 : ℂ)))
  · simpa only [dif_neg h] using
      (continuous_apply (⟨j, h⟩ : {k : Fin (n + 1) // k ≠ i}) :
        Continuous (fun z : AffineCoordinates i => z ⟨j, h⟩))

/-- Every literal affine patch of `CP n` is homeomorphic to its full affine
coordinate space, with the exact coordinate and inverse maps. -/
theorem t99J05_affineChartConstruction_all (n : ℕ) :
    AffineChartConstruction n := by
  intro i
  have hinvMem (z : AffineCoordinates i) :
      Projectivization.rep (chartInverse i z) i ≠ 0 := by
    unfold chartInverse
    let v : NonzeroVectors ℂ n :=
      ⟨fun j => if h : j = i then 1 else z ⟨j, h⟩, by
        intro hz
        have hi := congrFun hz i
        simp at hi⟩
    have hv : v ∈ {w : NonzeroVectors ℂ n | w.1 i ≠ 0} := by simp [v]
    have hp : v ∈ quotientMap ℂ n ⁻¹'
        {x : CP n | Projectivization.rep x i ≠ 0} := by
      rw [affineSource_preimage i]
      exact hv
    exact hp
  have hzero : chartInverse i 0 = coordinateLine ℂ n i := by
    unfold chartInverse coordinateLine
    congr 1
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  have hlineMem : Projectivization.rep (coordinateLine ℂ n i) i ≠ 0 := by
    rw [← hzero]
    exact hinvMem 0
  have hlineCoord : coordinates i (coordinateLine ℂ n i) = 0 := by
    rw [← hzero]
    exact coordinates_chartInverse i 0
  let e : OpenPartialHomeomorph (CP n) (AffineCoordinates i) := {
    toPartialEquiv := {
      toFun := coordinates i
      invFun := chartInverse i
      source := {x : CP n | Projectivization.rep x i ≠ 0}
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun z _ => hinvMem z
      left_inv' := fun x hx => chartInverse_coordinates i x hx
      right_inv' := fun z _ => coordinates_chartInverse i z }
    open_source := affineSource_isOpen i
    open_target := isOpen_univ
    continuousOn_toFun := t99J05_coordinates_continuousOn_exact i
    continuousOn_invFun := (t99J05_chartInverse_continuous_exact i).continuousOn }
  refine ⟨e, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx; rfl
  · exact hlineMem
  · exact hlineCoord
  · exact hzero

/-- The overlap of the two successor patches is exactly punctured affine
space in the last-coordinate chart. -/
noncomputable def t99J05_cp_successor_overlap_homeomorph_puncturedAffine
    (n : ℕ) :
    ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} : Set (CP (n + 1))) ≃ₜ
      ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
        Set (AffineCoordinates (Fin.last (n + 1)))) := by
  have hinvMem (z : AffineCoordinates (Fin.last (n + 1))) :
      Projectivization.rep
          (chartInverse (Fin.last (n + 1)) z) (Fin.last (n + 1)) ≠ 0 := by
    unfold chartInverse
    let v : NonzeroVectors ℂ (n + 1) :=
      ⟨fun j => if h : j = Fin.last (n + 1) then 1 else z ⟨j, h⟩, by
        intro hz
        have hi := congrFun hz (Fin.last (n + 1))
        simp at hi⟩
    have hv : v ∈ {w : NonzeroVectors ℂ (n + 1) |
        w.1 (Fin.last (n + 1)) ≠ 0} := by simp [v]
    exact (Set.ext_iff.mp (affineSource_preimage (Fin.last (n + 1))) v).mpr hv
  refine
    { toFun := fun p =>
        ⟨coordinates (Fin.last (n + 1)) p.1,
          (cpSuccessor_overlap_topCoordinates_ne_zero n p.1 p.2.2).mp p.2.1⟩
      invFun := fun z =>
        ⟨chartInverse (Fin.last (n + 1)) z.1,
          ⟨(cpSuccessor_overlap_topCoordinates_ne_zero n _ (hinvMem z.1)).mpr
              (by simpa only [coordinates_chartInverse] using z.2),
            hinvMem z.1⟩⟩
      left_inv := fun p => by
        apply Subtype.ext
        exact chartInverse_coordinates (Fin.last (n + 1)) p.1 p.2.2
      right_inv := fun z => by
        apply Subtype.ext
        exact coordinates_chartInverse (Fin.last (n + 1)) z.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (t99J05_coordinates_continuousOn_exact (Fin.last (n + 1))).comp_continuous
          continuous_subtype_val (fun p => p.2.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (t99J05_chartInverse_continuous_exact (Fin.last (n + 1))).comp
          continuous_subtype_val }

/-- Rational singular homology of the successor overlap is transported to
the punctured affine-coordinate model by the literal chart homeomorphism. -/
noncomputable def t99J05_cp_successor_overlap_homologyIso_puncturedAffine
    (n k : ℕ) :
    Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k ≅
      Homology
        ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
          Set (AffineCoordinates (Fin.last (n + 1)))) k :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ))).mapIso
    (TopCat.isoOfHomeo
      (t99J05_cp_successor_overlap_homeomorph_puncturedAffine n))

/-- The successor overlap has the homotopy type of the unit sphere in its
affine coordinate space: first use the exact chart, then normalize radially. -/
noncomputable def t99J05_cp_successor_overlap_homotopyEquiv_unitSphere
    (n : ℕ) :
    ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) ≃ₕ
      Metric.sphere
        (0 : AffineCoordinates (Fin.last (n + 1))) 1 :=
  (t99J05_cp_successor_overlap_homeomorph_puncturedAffine n).toHomotopyEquiv.trans
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
        (AffineCoordinates (Fin.last (n + 1)))).symm

/-- The corresponding rational-homology isomorphism from the overlap to its
unit-sphere model. -/
noncomputable def t99J05_cp_successor_overlap_homologyIso_unitSphere
    (n k : ℕ) :
    Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k ≅
      Homology
        (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) k :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      (t99J05_cp_successor_overlap_homotopyEquiv_unitSphere n) k

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
#print axioms cpSuccessorTopPatch_isOpen
#print axioms cpSuccessorLowerPatch_isOpen
#print axioms cpSuccessor_openCover
#print axioms cpSuccessor_overlap_topCoordinates_ne_zero
#print axioms t99J05_affineChartConstruction_all
#print axioms t99J05_cp_successor_overlap_homeomorph_puncturedAffine
#print axioms t99J05_cp_successor_overlap_homologyIso_puncturedAffine
#print axioms t99J05_cp_successor_overlap_homotopyEquiv_unitSphere
#print axioms t99J05_cp_successor_overlap_homologyIso_unitSphere
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_odd
#print axioms complexProjectiveRationalHomologyData_of_zero_of_step

end ConstructionTargets.t99J05Closure
