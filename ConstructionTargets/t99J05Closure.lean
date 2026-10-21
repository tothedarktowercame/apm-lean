import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.CoefficientH0
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.CoefficientSubcomplexMayerVietoris
import ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
import ConstructionTargets.CoefficientIntersectionRangeComparison
import ConstructionTargets.CoefficientIntersectionRangeNaturality
import ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence
import ConstructionTargets.HomologyBiprodIso
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Rational homology interface for the t99J05 closure

This file fixes the exact output required from the `CP n` homology computation.
It deliberately contains no numerical Lefschetz assertion: the trace
calculation consumes this data in the next milestone.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.ProjectiveQuotientDescent
open CategoryTheory.Limits
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

/-- Nonzero homogeneous representatives of the lower filtration patch. -/
abbrev CPSuccessorLowerVectors (n : ℕ) :=
  {v : NonzeroVectors ℂ (n + 1) //
    quotientMap ℂ (n + 1) v ∈ cpSuccessorLowerPatch n}

/-- Zero the last homogeneous coordinate of a representative in the lower
patch.  The result remains nonzero because some earlier coordinate is
nonzero.  This is the endpoint used by the lower-patch deformation retract. -/
def cpSuccessorZeroLastVector (n : ℕ) (v : CPSuccessorLowerVectors n) :
    NonzeroVectors ℂ (n + 1) :=
  ⟨fun j => if j = Fin.last (n + 1) then 0 else v.1.1 j, by
    obtain ⟨i, hi, hrep⟩ := v.2
    have hvi : v.1.1 i ≠ 0 := by
      have hmem : v.1 ∈ quotientMap ℂ (n + 1) ⁻¹'
          {p : CP (n + 1) | Projectivization.rep p i ≠ 0} := hrep
      exact (Set.ext_iff.mp (affineSource_preimage i) v.1).mp hmem
    intro hz
    have := congrFun hz i
    simp [hi, hvi] at this⟩

@[simp] theorem cpSuccessorZeroLastVector_last (n : ℕ)
    (v : CPSuccessorLowerVectors n) :
    (cpSuccessorZeroLastVector n v).1 (Fin.last (n + 1)) = 0 := by
  simp [cpSuccessorZeroLastVector]

@[simp] theorem cpSuccessorZeroLastVector_castSucc (n : ℕ)
    (v : CPSuccessorLowerVectors n) (i : Fin (n + 1)) :
    (cpSuccessorZeroLastVector n v).1 i.castSucc = v.1.1 i.castSucc := by
  simp [cpSuccessorZeroLastVector, Fin.castSucc_ne_last]

/-- Scale only the last homogeneous coordinate toward zero.  An earlier
coordinate supplied by lower-patch membership stays unchanged, so the whole
path consists of nonzero vectors. -/
def cpSuccessorLowerVectorHomotopy (n : ℕ) (v : CPSuccessorLowerVectors n)
    (s : Set.Icc (0 : ℝ) 1) : NonzeroVectors ℂ (n + 1) :=
  ⟨fun j => if j = Fin.last (n + 1)
      then ((1 - s.1 : ℝ) : ℂ) * v.1.1 j else v.1.1 j, by
    obtain ⟨i, hi, hrep⟩ := v.2
    have hvi : v.1.1 i ≠ 0 := by
      have hmem : v.1 ∈ quotientMap ℂ (n + 1) ⁻¹'
          {p : CP (n + 1) | Projectivization.rep p i ≠ 0} := hrep
      exact (Set.ext_iff.mp (affineSource_preimage i) v.1).mp hmem
    intro hz
    have := congrFun hz i
    simp [hi, hvi] at this⟩

@[simp] theorem cpSuccessorLowerVectorHomotopy_zero (n : ℕ)
    (v : CPSuccessorLowerVectors n) :
    cpSuccessorLowerVectorHomotopy n v ⟨0, by simp⟩ = v.1 := by
  apply Subtype.ext
  funext j
  by_cases hj : j = Fin.last (n + 1)
  · simp [cpSuccessorLowerVectorHomotopy, hj]
  · simp [cpSuccessorLowerVectorHomotopy, hj]

@[simp] theorem cpSuccessorLowerVectorHomotopy_one (n : ℕ)
    (v : CPSuccessorLowerVectors n) :
    cpSuccessorLowerVectorHomotopy n v ⟨1, by simp⟩ =
      cpSuccessorZeroLastVector n v := by
  apply Subtype.ext
  funext j
  by_cases hj : j = Fin.last (n + 1)
  · simp [cpSuccessorLowerVectorHomotopy, cpSuccessorZeroLastVector, hj]
  · simp [cpSuccessorLowerVectorHomotopy, cpSuccessorZeroLastVector, hj]

/-- The vector homotopy is homogeneous, which is the algebraic condition
needed for descent through the projective quotient. -/
theorem cpSuccessorLowerVectorHomotopy_smul (n : ℕ)
    (v w : CPSuccessorLowerVectors n) (s : Set.Icc (0 : ℝ) 1) (a : ℂ)
    (hvw : v.1.1 = a • w.1.1) :
    (cpSuccessorLowerVectorHomotopy n v s).1 =
      a • (cpSuccessorLowerVectorHomotopy n w s).1 := by
  funext j
  have hj := congrFun hvw j
  by_cases hlast : j = Fin.last (n + 1)
  · subst j
    have hcoord := congrFun hvw (Fin.last (n + 1))
    change v.1.1 (Fin.last (n + 1)) =
      a * w.1.1 (Fin.last (n + 1)) at hcoord
    simp only [cpSuccessorLowerVectorHomotopy, if_pos, Pi.smul_apply,
      smul_eq_mul]
    rw [hcoord]
    ring
  · simp [cpSuccessorLowerVectorHomotopy, hlast, hj]

/-- The homogeneous vector homotopy is jointly continuous in the lower-patch
representative and the interval parameter. -/
theorem cpSuccessorLowerVectorHomotopy_continuous (n : ℕ) :
    Continuous (fun z : CPSuccessorLowerVectors n × Set.Icc (0 : ℝ) 1 =>
      cpSuccessorLowerVectorHomotopy n z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  have hv : Continuous (fun z : CPSuccessorLowerVectors n × Set.Icc (0 : ℝ) 1 =>
      z.1.1.1 j) :=
    (continuous_apply j).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    simp only [cpSuccessorLowerVectorHomotopy, if_pos]
    exact (Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).mul hv
  · simp only [cpSuccessorLowerVectorHomotopy, if_neg hj]
    exact hv

/-- Every point of the vector homotopy still represents a point of the lower
projective patch, since one non-last coordinate remains unchanged and nonzero. -/
theorem cpSuccessorLowerVectorHomotopy_mem_lowerPatch (n : ℕ)
    (v : CPSuccessorLowerVectors n) (s : Set.Icc (0 : ℝ) 1) :
    quotientMap ℂ (n + 1) (cpSuccessorLowerVectorHomotopy n v s) ∈
      cpSuccessorLowerPatch n := by
  obtain ⟨i, hi, hrep⟩ := v.2
  refine ⟨i, hi, ?_⟩
  have hvi : v.1.1 i ≠ 0 := by
    have hmem : v.1 ∈ quotientMap ℂ (n + 1) ⁻¹'
        {p : CP (n + 1) | Projectivization.rep p i ≠ 0} := hrep
    exact (Set.ext_iff.mp (affineSource_preimage i) v.1).mp hmem
  have hcoord : (cpSuccessorLowerVectorHomotopy n v s).1 i ≠ 0 := by
    simpa [cpSuccessorLowerVectorHomotopy, hi] using hvi
  exact (Set.ext_iff.mp (affineSource_preimage i)
    (cpSuccessorLowerVectorHomotopy n v s)).mpr hcoord

/-- The continuous vector homotopy, bundled with its proved lower-patch
membership so it can be descended through the restricted quotient. -/
def cpSuccessorLowerVectorHomotopyInPatch (n : ℕ)
    (z : CPSuccessorLowerVectors n × Set.Icc (0 : ℝ) 1) :
    CPSuccessorLowerVectors n :=
  ⟨cpSuccessorLowerVectorHomotopy n z.1 z.2,
    cpSuccessorLowerVectorHomotopy_mem_lowerPatch n z.1 z.2⟩

theorem cpSuccessorLowerVectorHomotopyInPatch_continuous (n : ℕ) :
    Continuous (cpSuccessorLowerVectorHomotopyInPatch n) :=
  (cpSuccessorLowerVectorHomotopy_continuous n).subtype_mk _

/-- The projective quotient restricted over the lower patch. -/
def cpSuccessorLowerQuotientMap (n : ℕ) :
    CPSuccessorLowerVectors n → {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n} :=
  fun v => ⟨quotientMap ℂ (n + 1) v.1, v.2⟩

/-- The restricted projective quotient is still an open quotient map. -/
theorem cpSuccessorLowerQuotientMap_isOpenQuotient (n : ℕ) :
    IsOpenQuotientMap (cpSuccessorLowerQuotientMap n) := by
  let s := cpSuccessorLowerPatch n
  let q : NonzeroVectors ℂ (n + 1) → CP (n + 1) := quotientMap ℂ (n + 1)
  change IsOpenQuotientMap (s.restrictPreimage q)
  refine ⟨?_, (continuous_quotientMap ℂ (n + 1)).restrictPreimage, ?_⟩
  · rintro ⟨p, hp⟩
    obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ (n + 1) p
    exact ⟨⟨v, hp⟩, rfl⟩
  · exact (projectiveQuotientMap_isOpen ℂ (n + 1)).restrictPreimage s

/-- A fixed representative of each point in the lower projective patch. -/
noncomputable def cpSuccessorLowerRepresentative (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    CPSuccessorLowerVectors n :=
  Classical.choose ((cpSuccessorLowerQuotientMap_isOpenQuotient n).surjective p)

@[simp] theorem cpSuccessorLowerRepresentative_quotient (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    cpSuccessorLowerQuotientMap n (cpSuccessorLowerRepresentative n p) = p :=
  Classical.choose_spec ((cpSuccessorLowerQuotientMap_isOpenQuotient n).surjective p)

/-- The lower-patch vector homotopy descended through the restricted
projective quotient. -/
noncomputable def cpSuccessorLowerPatchHomotopy (n : ℕ)
    (z : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n} × Set.Icc (0 : ℝ) 1) :
    {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n} :=
  cpSuccessorLowerQuotientMap n
    (cpSuccessorLowerVectorHomotopyInPatch n
      (cpSuccessorLowerRepresentative n z.1, z.2))

/-- Pulling the descended homotopy back to a lower-patch representative
recovers the original homogeneous vector homotopy. -/
theorem cpSuccessorLowerPatchHomotopy_quotient (n : ℕ)
    (v : CPSuccessorLowerVectors n) (s : Set.Icc (0 : ℝ) 1) :
    cpSuccessorLowerPatchHomotopy n (cpSuccessorLowerQuotientMap n v, s) =
      cpSuccessorLowerQuotientMap n
        (cpSuccessorLowerVectorHomotopyInPatch n (v, s)) := by
  let w := cpSuccessorLowerRepresentative n (cpSuccessorLowerQuotientMap n v)
  have hq : quotientMap ℂ (n + 1) w.1 = quotientMap ℂ (n + 1) v.1 := by
    exact congrArg Subtype.val
      (cpSuccessorLowerRepresentative_quotient n
        (cpSuccessorLowerQuotientMap n v))
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ w.1.1 v.1.1 w.1.2 v.1.2).mp hq
  apply Subtype.ext
  change quotientMap ℂ (n + 1)
      (cpSuccessorLowerVectorHomotopy n w s) =
    quotientMap ℂ (n + 1) (cpSuccessorLowerVectorHomotopy n v s)
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
  refine ⟨a, ?_⟩
  exact (cpSuccessorLowerVectorHomotopy_smul n w v s a ha.symm).symm

/-- The descended lower-patch homotopy is jointly continuous. -/
theorem cpSuccessorLowerPatchHomotopy_continuous (n : ℕ) :
    Continuous (cpSuccessorLowerPatchHomotopy n) := by
  have hq := (cpSuccessorLowerQuotientMap_isOpenQuotient n).prodMap
    (IsOpenQuotientMap.id : IsOpenQuotientMap
      (fun s : Set.Icc (0 : ℝ) 1 => s))
  refine hq.isQuotientMap.continuous_iff.mpr ?_
  have hcomp : cpSuccessorLowerPatchHomotopy n ∘
      Prod.map (cpSuccessorLowerQuotientMap n) id =
      cpSuccessorLowerQuotientMap n ∘
        cpSuccessorLowerVectorHomotopyInPatch n := by
    funext z
    exact cpSuccessorLowerPatchHomotopy_quotient n z.1 z.2
  rw [hcomp]
  exact (cpSuccessorLowerQuotientMap_isOpenQuotient n).continuous.comp
    (cpSuccessorLowerVectorHomotopyInPatch_continuous n)

@[simp] theorem cpSuccessorLowerPatchHomotopy_zero (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    cpSuccessorLowerPatchHomotopy n (p, ⟨0, by simp⟩) = p := by
  let w := cpSuccessorLowerRepresentative n p
  calc
    cpSuccessorLowerPatchHomotopy n (p, ⟨0, by simp⟩) =
        cpSuccessorLowerPatchHomotopy n
          (cpSuccessorLowerQuotientMap n w, ⟨0, by simp⟩) := by
            rw [cpSuccessorLowerRepresentative_quotient n p]
    _ = cpSuccessorLowerQuotientMap n
        (cpSuccessorLowerVectorHomotopyInPatch n (w, ⟨0, by simp⟩)) :=
      cpSuccessorLowerPatchHomotopy_quotient n w ⟨0, by simp⟩
    _ = cpSuccessorLowerQuotientMap n w := by
      congr 1
      apply Subtype.ext
      exact cpSuccessorLowerVectorHomotopy_zero n w
    _ = p := cpSuccessorLowerRepresentative_quotient n p

@[simp] theorem cpSuccessorLowerPatchHomotopy_one (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    cpSuccessorLowerPatchHomotopy n (p, ⟨1, by simp⟩) =
      cpSuccessorLowerQuotientMap n
        ⟨cpSuccessorZeroLastVector n (cpSuccessorLowerRepresentative n p),
          by
            have h := cpSuccessorLowerVectorHomotopy_mem_lowerPatch n
              (cpSuccessorLowerRepresentative n p) ⟨1, by simp⟩
            rw [cpSuccessorLowerVectorHomotopy_one] at h
            exact h⟩ := by
  let w := cpSuccessorLowerRepresentative n p
  calc
    cpSuccessorLowerPatchHomotopy n (p, ⟨1, by simp⟩) =
        cpSuccessorLowerPatchHomotopy n
          (cpSuccessorLowerQuotientMap n w, ⟨1, by simp⟩) := by
            rw [cpSuccessorLowerRepresentative_quotient n p]
    _ = cpSuccessorLowerQuotientMap n
        (cpSuccessorLowerVectorHomotopyInPatch n (w, ⟨1, by simp⟩)) :=
      cpSuccessorLowerPatchHomotopy_quotient n w ⟨1, by simp⟩
    _ = cpSuccessorLowerQuotientMap n
        ⟨cpSuccessorZeroLastVector n w, by
          have h := cpSuccessorLowerVectorHomotopy_mem_lowerPatch n w ⟨1, by simp⟩
          rw [cpSuccessorLowerVectorHomotopy_one] at h
          exact h⟩ := by
      congr 1
      apply Subtype.ext
      exact cpSuccessorLowerVectorHomotopy_one n w

/-- Append a zero last coordinate to a nonzero homogeneous vector. -/
def cpSuccessorZeroLastIncludeVector (n : ℕ) (v : NonzeroVectors ℂ n) :
    NonzeroVectors ℂ (n + 1) :=
  ⟨fun j => if h : j = Fin.last (n + 1) then 0 else v.1 (j.castPred h), by
    intro hz
    apply v.2
    funext i
    have hi := congrFun hz i.castSucc
    simpa [Fin.castSucc_ne_last] using hi⟩

@[simp] theorem cpSuccessorZeroLastIncludeVector_castSucc (n : ℕ)
    (v : NonzeroVectors ℂ n) (i : Fin (n + 1)) :
    (cpSuccessorZeroLastIncludeVector n v).1 i.castSucc = v.1 i := by
  simp [cpSuccessorZeroLastIncludeVector, Fin.castSucc_ne_last]

@[simp] theorem cpSuccessorZeroLastIncludeVector_last (n : ℕ)
    (v : NonzeroVectors ℂ n) :
    (cpSuccessorZeroLastIncludeVector n v).1 (Fin.last (n + 1)) = 0 := by
  simp [cpSuccessorZeroLastIncludeVector]

theorem cpSuccessorZeroLastIncludeVector_continuous (n : ℕ) :
    Continuous (cpSuccessorZeroLastIncludeVector n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases hj : j = Fin.last (n + 1)
  · simp only [dif_pos hj]
    exact continuous_const
  · simp only [cpSuccessorZeroLastIncludeVector, dif_neg hj]
    exact (continuous_apply (j.castPred hj)).comp continuous_subtype_val

theorem cpSuccessorZeroLastIncludeVector_mem_lowerPatch (n : ℕ)
    (v : NonzeroVectors ℂ n) :
    quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n v) ∈
      cpSuccessorLowerPatch n := by
  have hex : ∃ i : Fin (n + 1), v.1 i ≠ 0 := by
    by_contra h
    push_neg at h
    apply v.2
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i.castSucc, Fin.castSucc_ne_last i, ?_⟩
  apply (Set.ext_iff.mp (affineSource_preimage i.castSucc)
    (cpSuccessorZeroLastIncludeVector n v)).mpr
  simpa using hi

/-- The zero-last-coordinate vector inclusion, with its image bundled in the
lower successor patch. -/
def cpSuccessorZeroLastIncludeVectorInPatch (n : ℕ) (v : NonzeroVectors ℂ n) :
    {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n} :=
  ⟨quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n v),
    cpSuccessorZeroLastIncludeVector_mem_lowerPatch n v⟩

theorem cpSuccessorZeroLastIncludeVectorInPatch_continuous (n : ℕ) :
    Continuous (cpSuccessorZeroLastIncludeVectorInPatch n) :=
  ((continuous_quotientMap ℂ (n + 1)).comp
    (cpSuccessorZeroLastIncludeVector_continuous n)).subtype_mk _

/-- The canonical continuous inclusion of `CP n` as the zero-last-coordinate
projective subspace of the lower successor patch. -/
noncomputable def cpSuccessorZeroLastInclusion (n : ℕ) :
    C(CP n, {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :=
  Classical.choose (projectiveHomogeneousMapDescent ℂ
    (cpSuccessorZeroLastIncludeVectorInPatch n)
    (cpSuccessorZeroLastIncludeVectorInPatch_continuous n)
    (by
      intro a b t hab
      apply Subtype.ext
      change quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n a) =
        quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n b)
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        rw [hab, ht]
        simp
      refine ⟨Units.mk0 t ht, ?_⟩
      funext j
      by_cases hj : j = Fin.last (n + 1)
      · simp [cpSuccessorZeroLastIncludeVector, hj]
      · have hcoord := congrFun hab (j.castPred hj)
        simpa [cpSuccessorZeroLastIncludeVector, hj] using hcoord.symm))

@[simp] theorem cpSuccessorZeroLastInclusion_quotient (n : ℕ)
    (v : NonzeroVectors ℂ n) :
    cpSuccessorZeroLastInclusion n (quotientMap ℂ n v) =
      cpSuccessorZeroLastIncludeVectorInPatch n v :=
  Classical.choose_spec (projectiveHomogeneousMapDescent ℂ
    (cpSuccessorZeroLastIncludeVectorInPatch n)
    (cpSuccessorZeroLastIncludeVectorInPatch_continuous n)
    (by
      intro a b t hab
      apply Subtype.ext
      change quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n a) =
        quotientMap ℂ (n + 1) (cpSuccessorZeroLastIncludeVector n b)
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        rw [hab, ht]
        simp
      refine ⟨Units.mk0 t ht, ?_⟩
      funext j
      by_cases hj : j = Fin.last (n + 1)
      · simp [cpSuccessorZeroLastIncludeVector, hj]
      · have hcoord := congrFun hab (j.castPred hj)
        simpa [cpSuccessorZeroLastIncludeVector, hj] using hcoord.symm)) v

/-- Forget the last coordinate of a lower-patch representative.  A non-last
coordinate is nonzero by lower-patch membership. -/
def cpSuccessorLowerTruncateVector (n : ℕ) (v : CPSuccessorLowerVectors n) :
    NonzeroVectors ℂ n :=
  ⟨fun i => v.1.1 i.castSucc, by
    obtain ⟨j, hj, hrep⟩ := v.2
    have hvj : v.1.1 j ≠ 0 := by
      have hmem : v.1 ∈ quotientMap ℂ (n + 1) ⁻¹'
          {p : CP (n + 1) | Projectivization.rep p j ≠ 0} := hrep
      exact (Set.ext_iff.mp (affineSource_preimage j) v.1).mp hmem
    intro hz
    have hcoord := congrFun hz (j.castPred hj)
    rw [Fin.castSucc_castPred j hj] at hcoord
    exact hvj hcoord⟩

theorem cpSuccessorZeroLastInclude_truncate (n : ℕ)
    (v : CPSuccessorLowerVectors n) :
    cpSuccessorZeroLastIncludeVector n (cpSuccessorLowerTruncateVector n v) =
      cpSuccessorZeroLastVector n v := by
  apply Subtype.ext
  funext j
  by_cases hj : j = Fin.last (n + 1)
  · simp [hj]
  · simp [cpSuccessorZeroLastIncludeVector, cpSuccessorLowerTruncateVector,
      cpSuccessorZeroLastVector, hj, Fin.castSucc_castPred]

/-- The time-one endpoint of the lower-patch homotopy factors through the
canonical zero-last inclusion of `CP n`. -/
theorem cpSuccessorLowerPatchHomotopy_one_eq_inclusion (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    cpSuccessorLowerPatchHomotopy n (p, ⟨1, by simp⟩) =
      cpSuccessorZeroLastInclusion n
        (quotientMap ℂ n
          (cpSuccessorLowerTruncateVector n
            (cpSuccessorLowerRepresentative n p))) := by
  rw [cpSuccessorLowerPatchHomotopy_one,
    cpSuccessorZeroLastInclusion_quotient]
  apply Subtype.ext
  change quotientMap ℂ (n + 1)
      (cpSuccessorZeroLastVector n (cpSuccessorLowerRepresentative n p)) =
    quotientMap ℂ (n + 1)
      (cpSuccessorZeroLastIncludeVector n
        (cpSuccessorLowerTruncateVector n
          (cpSuccessorLowerRepresentative n p)))
  rw [cpSuccessorZeroLastInclude_truncate]

theorem cpSuccessorLowerTruncateVector_continuous (n : ℕ) :
    Continuous (cpSuccessorLowerTruncateVector n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply i.castSucc).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- Truncation respects homogeneous scalar multiplication. -/
theorem cpSuccessorLowerTruncateVector_smul (n : ℕ)
    (v w : CPSuccessorLowerVectors n) (a : ℂ)
    (hvw : v.1.1 = a • w.1.1) :
    (cpSuccessorLowerTruncateVector n v).1 =
      a • (cpSuccessorLowerTruncateVector n w).1 := by
  funext i
  exact congrFun hvw i.castSucc

/-- Truncate a lower-patch representative and pass to `CP n`. -/
def cpSuccessorLowerTruncationOnVectors (n : ℕ)
    (v : CPSuccessorLowerVectors n) : CP n :=
  quotientMap ℂ n (cpSuccessorLowerTruncateVector n v)

theorem cpSuccessorLowerTruncationOnVectors_continuous (n : ℕ) :
    Continuous (cpSuccessorLowerTruncationOnVectors n) :=
  (continuous_quotientMap ℂ n).comp
    (cpSuccessorLowerTruncateVector_continuous n)

/-- The projective truncation map from the lower successor patch to `CP n`. -/
noncomputable def cpSuccessorLowerRetraction (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) : CP n :=
  cpSuccessorLowerTruncationOnVectors n
    (cpSuccessorLowerRepresentative n p)

/-- Pulling the projective truncation back to any lower-patch representative
recovers its literal truncated projective class. -/
theorem cpSuccessorLowerRetraction_quotient (n : ℕ)
    (v : CPSuccessorLowerVectors n) :
    cpSuccessorLowerRetraction n (cpSuccessorLowerQuotientMap n v) =
      cpSuccessorLowerTruncationOnVectors n v := by
  let w := cpSuccessorLowerRepresentative n (cpSuccessorLowerQuotientMap n v)
  have hq : quotientMap ℂ (n + 1) w.1 = quotientMap ℂ (n + 1) v.1 := by
    exact congrArg Subtype.val
      (cpSuccessorLowerRepresentative_quotient n
        (cpSuccessorLowerQuotientMap n v))
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ w.1.1 v.1.1 w.1.2 v.1.2).mp hq
  change quotientMap ℂ n (cpSuccessorLowerTruncateVector n w) =
    quotientMap ℂ n (cpSuccessorLowerTruncateVector n v)
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
  refine ⟨a, ?_⟩
  exact (cpSuccessorLowerTruncateVector_smul n w v a ha.symm).symm

theorem cpSuccessorLowerRetraction_continuous (n : ℕ) :
    Continuous (cpSuccessorLowerRetraction n) := by
  apply (cpSuccessorLowerQuotientMap_isOpenQuotient n).isQuotientMap.continuous_iff.mpr
  have hcomp : cpSuccessorLowerRetraction n ∘ cpSuccessorLowerQuotientMap n =
      cpSuccessorLowerTruncationOnVectors n := by
    funext v
    exact cpSuccessorLowerRetraction_quotient n v
  rw [hcomp]
  exact cpSuccessorLowerTruncationOnVectors_continuous n

@[simp] theorem cpSuccessorLowerTruncate_include (n : ℕ)
    (v : NonzeroVectors ℂ n) :
    cpSuccessorLowerTruncateVector n
        ⟨cpSuccessorZeroLastIncludeVector n v,
          cpSuccessorZeroLastIncludeVector_mem_lowerPatch n v⟩ = v := by
  apply Subtype.ext
  funext i
  simp [cpSuccessorLowerTruncateVector, cpSuccessorZeroLastIncludeVector]

/-- Projective truncation is a left inverse to the zero-last-coordinate
inclusion. -/
@[simp] theorem cpSuccessorLowerRetraction_inclusion (n : ℕ) (x : CP n) :
    cpSuccessorLowerRetraction n (cpSuccessorZeroLastInclusion n x) = x := by
  obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n x
  rw [cpSuccessorZeroLastInclusion_quotient]
  change cpSuccessorLowerRetraction n
      (cpSuccessorLowerQuotientMap n
        ⟨cpSuccessorZeroLastIncludeVector n v,
          cpSuccessorZeroLastIncludeVector_mem_lowerPatch n v⟩) =
    quotientMap ℂ n v
  rw [cpSuccessorLowerRetraction_quotient]
  change quotientMap ℂ n
      (cpSuccessorLowerTruncateVector n
        ⟨cpSuccessorZeroLastIncludeVector n v,
          cpSuccessorZeroLastIncludeVector_mem_lowerPatch n v⟩) = _
  rw [cpSuccessorLowerTruncate_include]

/-- The time-one endpoint is literally inclusion after the descended
truncation retraction. -/
theorem cpSuccessorLowerPatchHomotopy_one_eq_inclusion_retraction (n : ℕ)
    (p : {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}) :
    cpSuccessorLowerPatchHomotopy n (p, ⟨1, by simp⟩) =
      cpSuccessorZeroLastInclusion n (cpSuccessorLowerRetraction n p) := by
  rw [cpSuccessorLowerPatchHomotopy_one_eq_inclusion]
  rfl

def cpSuccessorLowerRetractionContinuousMap (n : ℕ) :
    C({p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n}, CP n) :=
  ⟨cpSuccessorLowerRetraction n, cpSuccessorLowerRetraction_continuous n⟩

/-- The descended quotient homotopy, bundled in Mathlib's time-first
homotopy interface. -/
noncomputable def cpSuccessorLowerPatchDeformationHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (ContinuousMap.id {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n})
      ((cpSuccessorZeroLastInclusion n).comp
        (cpSuccessorLowerRetractionContinuousMap n)) where
  toFun z := cpSuccessorLowerPatchHomotopy n (z.2, z.1)
  continuous_toFun := (cpSuccessorLowerPatchHomotopy_continuous n).comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left p := cpSuccessorLowerPatchHomotopy_zero n p
  map_one_left p :=
    cpSuccessorLowerPatchHomotopy_one_eq_inclusion_retraction n p

/-- The lower affine-filtration patch is homotopy equivalent to `CP n`,
with the concrete zero-last inclusion and truncation retraction. -/
noncomputable def t99J05_cp_successor_lowerPatch_deformationRetract (n : ℕ) :
    CP n ≃ₕ {p : CP (n + 1) // p ∈ cpSuccessorLowerPatch n} where
  toFun := cpSuccessorZeroLastInclusion n
  invFun := cpSuccessorLowerRetractionContinuousMap n
  left_inv := by
    have h : (cpSuccessorLowerRetractionContinuousMap n).comp
        (cpSuccessorZeroLastInclusion n) = ContinuousMap.id (CP n) := by
      apply ContinuousMap.ext
      exact cpSuccessorLowerRetraction_inclusion n
    rw [h]
  right_inv := ⟨(cpSuccessorLowerPatchDeformationHomotopy n).symm⟩

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

/-- Punctured affine coordinates are path connected, including the first
successor step where the affine space has one complex coordinate. -/
theorem t99J05_puncturedAffine_isPathConnected (n : ℕ) :
    IsPathConnected
      ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
        Set (AffineCoordinates (Fin.last (n + 1)))) := by
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank']
  norm_cast
  rw [Module.finrank_pi_fintype]
  simp [AffineCoordinates]
  omega

/-- The overlap has rational zeroth homology `ℚ`. -/
noncomputable def t99J05_cp_successor_overlap_rational_H0 (n : ℕ) :
    Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) 0 ≅ ModuleCat.of ℚ ℚ := by
  letI : PathConnectedSpace
      ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
        Set (AffineCoordinates (Fin.last (n + 1)))) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (t99J05_puncturedAffine_isPathConnected n)
  let e := t99J05_cp_successor_overlap_homeomorph_puncturedAffine n
  letI : PathConnectedSpace
      ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact ConstructionTargets.CoefficientH0.h0Iso ℚ
    (Classical.choice inferInstance)

/-- Finite dimensionality of the unit-sphere model transports back to the
successor overlap. -/
theorem t99J05_cp_successor_overlap_finiteDimensional_of_unitSphere
    (n k : ℕ)
    [FiniteDimensional ℚ
      (Homology
        (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) k)] :
    FiniteDimensional ℚ
      (Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k) :=
  (t99J05_cp_successor_overlap_homologyIso_unitSphere n k).symm.toLinearEquiv.finiteDimensional

/-- Off-degree vanishing of the unit-sphere model transports back to the
exact successor overlap. -/
theorem t99J05_cp_successor_overlap_subsingleton_of_unitSphere
    (n k : ℕ)
    [Subsingleton
      (Homology
        (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) k)] :
    Subsingleton
      (Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k) := by
  constructor
  intro x y
  apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (t99J05_cp_successor_overlap_homologyIso_unitSphere n k).hom).1
  exact Subsingleton.elim _ _

/-- A top-degree computation for the unit-sphere model transports back to the
exact successor overlap.  This isolates the remaining sphere-model comparison
from the Mayer--Vietoris argument. -/
noncomputable def t99J05_cp_successor_overlap_topIso_of_unitSphere
    (n : ℕ)
    (e : Homology
          (Metric.sphere
            (0 : AffineCoordinates (Fin.last (n + 1))) 1) (2 * n + 1) ≅
        ModuleCat.of ℚ ℚ) :
    Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) (2 * n + 1) ≅ ModuleCat.of ℚ ℚ :=
  t99J05_cp_successor_overlap_homologyIso_unitSphere n (2 * n + 1) ≪≫ e

/-- A finite-dimensional real-linear coordinate equivalence from the complex
affine chart to the Euclidean model used by the sphere-homology computation. -/
noncomputable def t99J05_affineCoordinatesEuclideanEquiv (n : ℕ) :
    AffineCoordinates (Fin.last (n + 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n + 2)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [AffineCoordinates, Module.finrank_pi_fintype,
      Fintype.card_subtype_compl]
    omega)

/-- The coordinate equivalence restricts to the complements of the origins. -/
noncomputable def t99J05_puncturedAffineCoordinatesEuclideanHomeomorph (n : ℕ) :
    ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
      Set (AffineCoordinates (Fin.last (n + 1)))) ≃ₜ
    ({x : EuclideanSpace ℝ (Fin (2 * n + 2)) | x ≠ 0} :
      Set (EuclideanSpace ℝ (Fin (2 * n + 2)))) where
  toFun z := ⟨t99J05_affineCoordinatesEuclideanEquiv n z.1, by
    intro hz
    apply z.2
    exact (t99J05_affineCoordinatesEuclideanEquiv n).injective (by simpa using hz)⟩
  invFun x := ⟨(t99J05_affineCoordinatesEuclideanEquiv n).symm x.1, by
    intro hz
    apply x.2
    exact (t99J05_affineCoordinatesEuclideanEquiv n).symm.injective (by simpa using hz)⟩
  left_inv z := by ext; simp
  right_inv x := by ext; simp
  continuous_toFun :=
    (t99J05_affineCoordinatesEuclideanEquiv n).continuous.comp
      continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (t99J05_affineCoordinatesEuclideanEquiv n).symm.continuous.comp
      continuous_subtype_val |>.subtype_mk _

/-- The affine unit sphere is homotopy equivalent to the standard Euclidean
sphere of real dimension `2n+1`. -/
noncomputable def t99J05_affineUnitSphereHomotopyEquivEuclidean (n : ℕ) :
    Metric.sphere (0 : AffineCoordinates (Fin.last (n + 1))) 1 ≃ₕ
      T02A06.euclideanUnitSphere (2 * n + 2) :=
  (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
      (AffineCoordinates (Fin.last (n + 1)))).trans
    ((t99J05_puncturedAffineCoordinatesEuclideanHomeomorph n).toHomotopyEquiv.trans
      (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
        (EuclideanSpace ℝ (Fin (2 * n + 2)))).symm)

/-- Rational top homology of the exact affine unit-sphere model is `ℚ`. -/
noncomputable def t99J05_affineUnitSphere_topHomologyIso (n : ℕ) :
    Homology
        (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) (2 * n + 1) ≅
      ModuleCat.of ℚ ℚ :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      (t99J05_affineUnitSphereHomotopyEquivEuclidean n) (2 * n + 1) ≪≫
    ConstructionTargets.CoefficientFirstReflection.topIso ℚ (2 * n)

/-- Rational first homology of every Euclidean unit sphere of dimension at
least two vanishes; this is the endpoint for the sphere-shift induction. -/
theorem t99J05_euclideanUnitSphere_H1_isZero
    (m : ℕ) (hm : 2 < m) :
    IsZero (Homology (T02A06.euclideanUnitSphere m) 1) := by
  have hd : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  letI : ContractibleSpace (T02A06.euclideanClosedDisk (m - 1)) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace (T02A06.euclideanUnitSphere (m - 1)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        simp
        omega) 0 (by norm_num))
  letI : PathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet (m - 1)) :=
    (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph (m - 1)).symm.surjective.pathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph (m - 1)).symm.continuous
  have hz :=
    (ConstructionTargets.CoefficientSphereShift.sphereH1KernelIso ℚ (m - 1)).isZero_iff.mpr
      (ConstructionTargets.CoefficientConnectedH0Map.inclusion_kernel_zero ℚ _)
  change IsZero
    (Homology (T02A06.euclideanUnitSphere (m - 1 + 1)) 1) at hz
  rw [hd] at hz
  exact hz

/-- Rational homology vanishes in every positive degree strictly below the
top dimension of a Euclidean unit sphere. -/
theorem t99J05_euclideanUnitSphere_positiveHomology_isZero_of_lt
    (m k : ℕ) (hk : 0 < k) (hkm : k < m - 1) :
    IsZero (Homology (T02A06.euclideanUnitSphere m) k) := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              exact t99J05_euclideanUnitSphere_H1_isZero (m + 1) (by omega)
          | succ k =>
              have hz :
                  IsZero
                    (Homology (T02A06.euclideanUnitSphere m) (k + 1)) :=
                ih (k + 1) (by omega) (by omega)
              have e :
                  Homology (T02A06.euclideanUnitSphere (m + 1)) (k + 2) ≅
                    Homology (T02A06.euclideanUnitSphere m) (k + 1) := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  ConstructionTargets.CoefficientSphereShift.sphereShift
                    ℚ m (k + 1) (by omega)
              exact hz.of_iso e

/-- Rational homology vanishes strictly above the top dimension of every
nonempty Euclidean unit sphere. -/
theorem t99J05_euclideanUnitSphere_homology_isZero_of_gt
    (m k : ℕ) (hk : m < k) :
    IsZero (Homology (T02A06.euclideanUnitSphere (m + 1)) k) := by
  induction m generalizing k with
  | zero =>
      change IsZero
        (ConstructionTargets.SphereZeroCoefficients.H ℚ k)
      exact ConstructionTargets.SphereZeroCoefficients.positive_vanishing
        ℚ k (by omega)
  | succ m ih =>
      have hk0 : k - 1 ≠ 0 := by omega
      have hdeg : k - 1 + 1 = k := by omega
      have e :
          Homology (T02A06.euclideanUnitSphere (m + 2)) k ≅
            Homology (T02A06.euclideanUnitSphere (m + 1)) (k - 1) := by
        simpa only [Nat.add_assoc, hdeg] using
          ConstructionTargets.CoefficientSphereShift.sphereShift
            ℚ (m + 1) (k - 1) hk0
      exact (ih (k - 1) (by omega)).of_iso e

/-- Above its top degree, the exact affine unit-sphere model also has zero
rational homology. -/
theorem t99J05_affineUnitSphere_homology_isZero_of_gt
    (n k : ℕ) (hk : 2 * n + 1 < k) :
    IsZero
      (Homology
        (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) k) := by
  have hz :
      IsZero
        (Homology (T02A06.euclideanUnitSphere (2 * n + 1 + 1)) k) :=
    t99J05_euclideanUnitSphere_homology_isZero_of_gt (2 * n + 1) k hk
  exact hz.of_iso
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      (t99J05_affineUnitSphereHomotopyEquivEuclidean n) k)

/-- The successor overlap inherits the same above-top vanishing from its
affine unit-sphere model. -/
theorem t99J05_cp_successor_overlap_homology_isZero_of_gt
    (n k : ℕ) (hk : 2 * n + 1 < k) :
    IsZero
      (Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k) := by
  exact (t99J05_affineUnitSphere_homology_isZero_of_gt n k hk).of_iso
    (t99J05_cp_successor_overlap_homologyIso_unitSphere n k)

/-- Consequently, the successor overlap has one-dimensional rational homology
in its unique positive top degree. -/
noncomputable def t99J05_cp_successor_overlap_rational_topHomology (n : ℕ) :
    Homology
        ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) (2 * n + 1) ≅ ModuleCat.of ℚ ℚ :=
  t99J05_cp_successor_overlap_topIso_of_unitSphere n
    (t99J05_affineUnitSphere_topHomologyIso n)

/-- The successor overlap is finite-dimensional in every degree: degree zero
and the sphere top degree are one-dimensional, and all other degrees vanish. -/
theorem t99J05_cp_successor_overlap_finiteDimensional (n k : ℕ) :
    FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k) := by
  by_cases hk0 : k = 0
  · subst k
    exact (t99J05_cp_successor_overlap_rational_H0 n).symm.toLinearEquiv.finiteDimensional
  rcases lt_trichotomy k (2 * n + 1) with hlt | heq | hgt
  · have hzEuclidean :
        IsZero (Homology (T02A06.euclideanUnitSphere (2 * n + 2)) k) :=
      t99J05_euclideanUnitSphere_positiveHomology_isZero_of_lt
        (2 * n + 2) k (Nat.pos_of_ne_zero hk0) (by omega)
    have hzAffine : IsZero
        (Homology (Metric.sphere
          (0 : AffineCoordinates (Fin.last (n + 1))) 1) k) :=
      hzEuclidean.of_iso
        (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
          (t99J05_affineUnitSphereHomotopyEquivEuclidean n) k)
    letI : Subsingleton
        (Homology ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (hzAffine.of_iso (t99J05_cp_successor_overlap_homologyIso_unitSphere n k))
    exact FiniteDimensional.of_injective (0 : _ →ₗ[ℚ] ℚ)
      (Function.injective_of_subsingleton _)
  · subst k
    exact (t99J05_cp_successor_overlap_rational_topHomology n).symm.toLinearEquiv.finiteDimensional
  · letI : Subsingleton
        (Homology ({p : CP (n + 1) |
          p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) k) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (t99J05_cp_successor_overlap_homology_isZero_of_gt n k hgt)
    exact FiniteDimensional.of_injective (0 : _ →ₗ[ℚ] ℚ)
      (Function.injective_of_subsingleton _)

#print axioms t99J05_cp_successor_overlap_finiteDimensional

/-- The rational chain-level Mayer--Vietoris sequence for the two literal
projective patches is short exact before transport from small simplices. -/
theorem t99J05_cp_successor_subcomplexMayerVietoris_shortExact (n : ℕ) :
    (ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex ℚ
      (ConstructionTargets.SingularExcision.ambientSubspaceRange
        (cpSuccessorLowerPatch n))
      (ConstructionTargets.SingularExcision.ambientSubspaceRange
        (cpSuccessorTopPatch n))).ShortExact := by
  exact ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortExact ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n))

/-- The specialized chain sequence, named so its three homology exactness
positions can be transported to the literal patch homology groups. -/
noncomputable def t99J05_cp_successor_mayerVietorisShortComplex (n : ℕ) :=
  ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n))

/-- Exactness at the direct sum of the two patch homology groups in the
specialized projective Mayer--Vietoris sequence. -/
theorem t99J05_cp_successor_mayerVietoris_exact_pieces (n k : ℕ) :
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).f k)
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).g k)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [(t99J05_cp_successor_mayerVietorisShortComplex n).zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact ConstructionTargets.CoefficientSubcomplexMayerVietoris.exact_pieces ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n)) k

/-- The connecting map of the specialized successor sequence, retaining the
degree shift from ambient degree `k+1` to overlap degree `k`. -/
noncomputable def t99J05_cp_successor_mayerVietorisConnecting (n k : ℕ) :=
  ConstructionTargets.CoefficientSubcomplexMayerVietoris.connecting ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n)) k

/-- Exactness at the overlap homology term in the specialized projective
Mayer--Vietoris sequence. -/
noncomputable def t99J05_cp_successor_mayerVietoris_exact_overlap (n k : ℕ) :=
  ConstructionTargets.CoefficientSubcomplexMayerVietoris.exact_intersection ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n)) k

/-- Exactness at ambient homology in degree `k + 1`, between the two-patch
map and the degree-lowering connecting morphism. -/
noncomputable def t99J05_cp_successor_mayerVietoris_exact_ambient (n k : ℕ) :=
  ConstructionTargets.CoefficientSubcomplexMayerVietoris.exact_union ℚ
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorLowerPatch n))
    (ConstructionTargets.SingularExcision.ambientSubspaceRange
      (cpSuccessorTopPatch n)) k

/-- The union term of the successor Mayer--Vietoris sequence computes the
homology of the literal union of the two open projective patches. -/
theorem t99J05_cp_successor_unionRange_homologyMap_isIso (n k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSubspaceUnionRangeInclusion.unionRangeChainsInclusion
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n)) k) := by
  exact
    ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence.unionRange_homologyMap_isIso
      ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n)
      (cpSuccessorLowerPatch_isOpen n) (cpSuccessorTopPatch_isOpen n) k

#print axioms t99J05_cp_successor_unionRange_homologyMap_isIso

/-- Rational chains on an ambient subspace range are canonically the literal
singular chains of that subspace. -/
noncomputable def t99J05_ambientSubspaceRangeChainsIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange A : SSet) ≅
      (ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (TopCat.toSSet.obj (TopCat.of A)) :=
  ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility.ambientSubspaceRangeChainsIso ℚ A

/-- Homology-level rational transport from an ambient range presentation to
the corresponding literal topological subspace. -/
noncomputable def t99J05_ambientSubspaceRangeHomologyIso
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) :
    ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange A : SSet)).homology k ≅
      Homology A k :=
  ConstructionTargets.CoefficientAmbientSubspaceRangeComparison.rangeHomologyIso ℚ A k

/-- Degreewise transport from the union term of the successor
Mayer--Vietoris complex to homology of the literal union of its patches. -/
noncomputable def t99J05_cp_successor_unionRangeHomologyIso (n k : ℕ) :
    ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
      ((ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) ⊔
        ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) :
        (TopCat.toSSet.obj (TopCat.of (CP (n + 1)))).Subcomplex) : SSet)).homology k ≅
      Homology ((cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n :
        Set (CP (n + 1)))) k := by
  letI := t99J05_cp_successor_unionRange_homologyMap_isIso n k
  exact
    (CategoryTheory.asIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSubspaceUnionRangeInclusion.unionRangeChainsInclusion
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n)) k)).trans
      (t99J05_ambientSubspaceRangeHomologyIso
        (cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n) k)

#print axioms t99J05_cp_successor_unionRangeHomologyIso

/-- The literal target of the transported union term is the whole successor. -/
theorem t99J05_cp_successor_patch_union_eq_univ (n : ℕ) :
    cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n = Set.univ :=
  (cpSuccessor_openCover n).2.2

#print axioms t99J05_cp_successor_patch_union_eq_univ

/-- The literal patch union is homeomorphic to the ambient successor space. -/
noncomputable def t99J05_cp_successor_patchUnionHomeomorph (n : ℕ) :
    ((cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n : Set (CP (n + 1)))) ≃ₜ
      CP (n + 1) :=
  (Homeomorph.setCongr (t99J05_cp_successor_patch_union_eq_univ n)).trans
    (Homeomorph.Set.univ (CP (n + 1)))

/-- Homology transport from the literal patch union to the successor. -/
noncomputable def t99J05_cp_successor_patchUnionHomologyIso (n k : ℕ) :
    Homology ((cpSuccessorLowerPatch n ∪ cpSuccessorTopPatch n :
      Set (CP (n + 1)))) k ≅ Homology (CP (n + 1)) k :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ))).mapIso
      (TopCat.isoOfHomeo (t99J05_cp_successor_patchUnionHomeomorph n))

#print axioms t99J05_cp_successor_patchUnionHomologyIso

/-- The union object in the transported Mayer--Vietoris complex is identified
degreewise with rational homology of the literal projective successor. -/
noncomputable def t99J05_cp_successor_unionRangeToSuccessorHomologyIso
    (n k : ℕ) :
    ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
      ((ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) ⊔
        ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) :
        (TopCat.toSSet.obj (TopCat.of (CP (n + 1)))).Subcomplex) : SSet)).homology k ≅
      Homology (CP (n + 1)) k :=
  t99J05_cp_successor_unionRangeHomologyIso n k ≪≫
    t99J05_cp_successor_patchUnionHomologyIso n k

#print axioms t99J05_cp_successor_unionRangeToSuccessorHomologyIso

/-- The range-to-literal homology isomorphism commutes with inclusion into
ambient singular homology. -/
theorem t99J05_ambientSubspaceRangeHomologyIso_hom_comp_subspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          (t99J05_ambientSubspaceRangeChainsIso A).hom k)
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A) k) =
      HomologicalComplex.homologyMap
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
          (ConstructionTargets.SingularExcision.ambientSubspaceRange A).ι) k := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f k)
      (ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility.ambientSubspaceRangeChainsIso_hom_comp_subspaceMap
        ℚ A)

/-- Range-to-literal homology transport is natural for every inclusion of
literal subspaces. -/
theorem t99J05_ambientSubspaceRangeHomologyIso_naturality
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (t99J05_ambientSubspaceRangeHomologyIso A k).hom
        (HomologicalComplex.homologyMap
          ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
            (TopCat.toSSet.map
              (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion h))) k) =
      CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
            (ConstructionTargets.SingularExcision.ambientSubspaceRangeInclusion h)) k)
        (t99J05_ambientSubspaceRangeHomologyIso B k).hom := by
  have hchain :
      CategoryTheory.CategoryStruct.comp
        (t99J05_ambientSubspaceRangeChainsIso A).hom
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
          (TopCat.toSSet.map
            (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion h))) =
      CategoryTheory.CategoryStruct.comp
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
          (ConstructionTargets.SingularExcision.ambientSubspaceRangeInclusion h))
        (t99J05_ambientSubspaceRangeChainsIso B).hom := by
    change
      CategoryTheory.CategoryStruct.comp
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map _)
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map _) =
      CategoryTheory.CategoryStruct.comp
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map _)
        ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map _)
    simpa only [← CategoryTheory.Functor.map_comp] using congrArg
      (ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
      (ConstructionTargets.SingularExcision.ambientSubspaceRangeInclusion_square h)
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f k) hchain

#print axioms t99J05_ambientSubspaceRangeHomologyIso_naturality

/-- Naturality specialized to the overlap inclusion into the lower successor
patch. -/
def t99J05_cp_successor_mayerVietoris_overlap_lower_naturality
    (n k : ℕ) :=
  t99J05_ambientSubspaceRangeHomologyIso_naturality
    (A := cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n)
    (B := cpSuccessorLowerPatch n) Set.inter_subset_left k

#print axioms t99J05_cp_successor_mayerVietoris_overlap_lower_naturality

/-- Naturality specialized to the overlap inclusion into the top successor
patch. -/
def t99J05_cp_successor_mayerVietoris_overlap_top_naturality
    (n k : ℕ) :=
  t99J05_ambientSubspaceRangeHomologyIso_naturality
    (A := cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n)
    (B := cpSuccessorTopPatch n) Set.inter_subset_right k

#print axioms t99J05_cp_successor_mayerVietoris_overlap_top_naturality

/-- The canonical rational-module comparison from homology of a binary
biproduct of chain complexes to the biproduct of their homologies. -/
noncomputable def t99J05_rationalHomologyBiprodIso
    (K L : ChainComplex (ModuleCat ℚ) ℕ) (k : ℕ) :
    (K ⊞ L).homology k ≅ K.homology k ⊞ L.homology k := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) k
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L

/-- Its hom is the lift of the two canonical homology projections. -/
theorem t99J05_rationalHomologyBiprodIso_hom
    (K L : ChainComplex (ModuleCat ℚ) ℕ) (k : ℕ) :
    (t99J05_rationalHomologyBiprodIso K L k).hom =
      biprod.lift
        (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) k)
        (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) k) := by
  rfl

#print axioms t99J05_rationalHomologyBiprodIso_hom

/-- The homology biproduct comparison carries a chain-level lift to the lift
of the induced homology maps. -/
@[reassoc]
theorem t99J05_homologyMap_lift_comp_rationalHomologyBiprodIso_hom
    {M K L : ChainComplex (ModuleCat ℚ) ℕ} (f : M ⟶ K) (g : M ⟶ L) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (biprod.lift f g) k)
        (t99J05_rationalHomologyBiprodIso K L k).hom =
      biprod.lift (HomologicalComplex.homologyMap f k)
        (HomologicalComplex.homologyMap g k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) k
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact biprod.map_lift_mapBiprod F K L f g

#print axioms t99J05_homologyMap_lift_comp_rationalHomologyBiprodIso_hom

/-- Cancel an isomorphism comparison on the source of a commuting triangle. -/
theorem t99J05_iso_inv_comp_of_hom_comp_eq
    {C : Type*} [CategoryTheory.Category C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (h : CategoryTheory.CategoryStruct.comp e.hom f = g) :
    CategoryTheory.CategoryStruct.comp e.inv g = f := by
  rw [← h, ← CategoryTheory.Category.assoc, e.inv_hom_id,
    CategoryTheory.Category.id_comp]

#print axioms t99J05_iso_inv_comp_of_hom_comp_eq

/-- The literal overlap-to-patches arrow, with the Mayer--Vietoris sign on
the top-patch component. -/
noncomputable def t99J05_cp_successor_literalOverlapToPieces (n k : ℕ) :
    Homology ({p : CP (n + 1) |
      p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} : Set (CP (n + 1))) k ⟶
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} : Set (CP (n + 1))) k ⊞
        Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} : Set (CP (n + 1))) k) :=
  biprod.lift
    (HomologicalComplex.homologyMap
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
        (TopCat.toSSet.map
          (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
            (Set.inter_subset_left : cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n ⊆
              cpSuccessorLowerPatch n)))) k)
    (-HomologicalComplex.homologyMap
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
        (TopCat.toSSet.map
          (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
            (Set.inter_subset_right : cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n ⊆
              cpSuccessorTopPatch n)))) k)

/-- The first component of the literal successor overlap map is the lower
patch inclusion on homology. -/
theorem t99J05_cp_successor_literalOverlapToPieces_fst (n k : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (t99J05_cp_successor_literalOverlapToPieces n k) biprod.fst =
    HomologicalComplex.homologyMap
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
        (TopCat.toSSet.map
          (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
            (Set.inter_subset_left : cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n ⊆
              cpSuccessorLowerPatch n)))) k := by
  simp [t99J05_cp_successor_literalOverlapToPieces]

/-- The second component of the literal successor overlap map is the negated
top-patch inclusion on homology. -/
theorem t99J05_cp_successor_literalOverlapToPieces_snd (n k : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (t99J05_cp_successor_literalOverlapToPieces n k) biprod.snd =
    -HomologicalComplex.homologyMap
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
        (TopCat.toSSet.map
          (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
            (Set.inter_subset_right : cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n ⊆
              cpSuccessorTopPatch n)))) k := by
  simp [t99J05_cp_successor_literalOverlapToPieces]

#print axioms t99J05_cp_successor_literalOverlapToPieces_fst
#print axioms t99J05_cp_successor_literalOverlapToPieces_snd

/-- The three range-presented terms in the successor Mayer--Vietoris sequence
transport to the literal overlap and two patches. -/
noncomputable def t99J05_cp_successor_mayerVietoris_rangeHomologyIsos
    (n k : ℕ) :=
  (t99J05_ambientSubspaceRangeHomologyIso
      (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k,
    t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) k,
    t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) k)

/-- The first Mayer--Vietoris homology arrow transported from ambient-range
chains to the literal overlap and patch homology groups. -/
noncomputable def t99J05_cp_successor_mayerVietoris_f_transport
    (n k : ℕ) :
    Homology ({p : CP (n + 1) |
      p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} : Set (CP (n + 1))) k ⟶
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} : Set (CP (n + 1))) k ⊞
        Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} : Set (CP (n + 1))) k) := by
  dsimp [t99J05_cp_successor_mayerVietorisShortComplex,
    ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex]
  exact CategoryTheory.CategoryStruct.comp
    (t99J05_ambientSubspaceRangeHomologyIso
      (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k).inv
    (CategoryTheory.CategoryStruct.comp
      (ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).hom
      (CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap
          (t99J05_cp_successor_mayerVietorisShortComplex n).f k)
        (CategoryTheory.CategoryStruct.comp
          (t99J05_rationalHomologyBiprodIso
            ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
              (ConstructionTargets.SingularExcision.ambientSubspaceRange
                (cpSuccessorLowerPatch n) : SSet))
            ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
              (ConstructionTargets.SingularExcision.ambientSubspaceRange
                (cpSuccessorTopPatch n) : SSet)) k).hom
          (biprod.map
            (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) k).hom
            (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) k).hom))))

#print axioms t99J05_cp_successor_mayerVietoris_f_transport

/-- The homology Mayer--Vietoris segment at the two pieces, transported to the
literal overlap and literal patch homology groups.  The ambient union term is
left in its original presentation because exactness is asserted at the middle
object. -/
noncomputable def t99J05_cp_successor_mayerVietoris_piecesTransport
    (n k : ℕ) : CategoryTheory.ShortComplex (ModuleCat ℚ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).f k)
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).g k)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [(t99J05_cp_successor_mayerVietorisShortComplex n).zero,
          HomologicalComplex.homologyMap_zero]))
    ((ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
      ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).symm.trans
        (t99J05_ambientSubspaceRangeHomologyIso
          (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k))
    ((t99J05_rationalHomologyBiprodIso
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) : SSet))
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) : SSet)) k).trans
      (biprod.mapIso
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) k)
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) k)))
    (CategoryTheory.Iso.refl _)

/-- Exactness at the literal biproduct of the two successor patches. -/
theorem t99J05_cp_successor_mayerVietoris_exact_pieces_transport (n k : ℕ) :
    (t99J05_cp_successor_mayerVietoris_piecesTransport n k).Exact := by
  apply ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
  exact t99J05_cp_successor_mayerVietoris_exact_pieces n k

#print axioms t99J05_cp_successor_mayerVietoris_exact_pieces_transport

/-- The same Mayer--Vietoris segment with its union term transported all the
way to homology of the literal projective successor. -/
noncomputable def t99J05_cp_successor_mayerVietoris_unionTransport
    (n k : ℕ) : CategoryTheory.ShortComplex (ModuleCat ℚ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).f k)
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).g k)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [(t99J05_cp_successor_mayerVietorisShortComplex n).zero,
          HomologicalComplex.homologyMap_zero]))
    ((ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
      ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).symm.trans
        (t99J05_ambientSubspaceRangeHomologyIso
          (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k))
    ((t99J05_rationalHomologyBiprodIso
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) : SSet))
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) : SSet)) k).trans
      (biprod.mapIso
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) k)
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) k)))
    (t99J05_cp_successor_unionRangeToSuccessorHomologyIso n k)

/-- Exactness survives the full transport to the successor union term. -/
theorem t99J05_cp_successor_mayerVietoris_union_transport (n k : ℕ) :
    (t99J05_cp_successor_mayerVietoris_unionTransport n k).Exact := by
  apply ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
  exact t99J05_cp_successor_mayerVietoris_exact_pieces n k

#print axioms t99J05_cp_successor_mayerVietoris_union_transport

/-- The adjacent long-exact-sequence segment, transported so exactness is
asserted at homology of the literal projective successor. -/
noncomputable def t99J05_cp_successor_mayerVietoris_ambientTransport
    (n k : ℕ) : CategoryTheory.ShortComplex (ModuleCat ℚ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex
    (CategoryTheory.ShortComplex.mk
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).g (k + 1))
      (t99J05_cp_successor_mayerVietorisConnecting n k)
      ((t99J05_cp_successor_subcomplexMayerVietoris_shortExact n).comp_δ
        (k + 1) k rfl))
    ((t99J05_rationalHomologyBiprodIso
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) : SSet))
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) : SSet)) (k + 1)).trans
      (biprod.mapIso
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) (k + 1))
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) (k + 1))))
    (t99J05_cp_successor_unionRangeToSuccessorHomologyIso n (k + 1))
    ((ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
      ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).symm.trans
        (t99J05_ambientSubspaceRangeHomologyIso
          (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k))

/-- Exactness at successor homology in the fully transported adjacent segment. -/
theorem t99J05_cp_successor_mayerVietoris_exact_ambient_transport
    (n k : ℕ) :
    (t99J05_cp_successor_mayerVietoris_ambientTransport n k).Exact := by
  apply ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
  exact t99J05_cp_successor_mayerVietoris_exact_ambient n k

#print axioms t99J05_cp_successor_mayerVietoris_exact_ambient_transport

/-- The next adjacent segment, transported so exactness is asserted at the
literal overlap homology term. -/
noncomputable def t99J05_cp_successor_mayerVietoris_overlapTransport
    (n k : ℕ) : CategoryTheory.ShortComplex (ModuleCat ℚ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex
    (CategoryTheory.ShortComplex.mk
      (t99J05_cp_successor_mayerVietorisConnecting n k)
      (HomologicalComplex.homologyMap
        (t99J05_cp_successor_mayerVietorisShortComplex n).f k)
      ((t99J05_cp_successor_subcomplexMayerVietoris_shortExact n).δ_comp
        (k + 1) k rfl))
    (t99J05_cp_successor_unionRangeToSuccessorHomologyIso n (k + 1))
    ((ConstructionTargets.CoefficientIntersectionRangeComparison.intersectionHomologyIso
      ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).symm.trans
        (t99J05_ambientSubspaceRangeHomologyIso
          (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n) k))
    ((t99J05_rationalHomologyBiprodIso
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorLowerPatch n) : SSet))
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).obj
        (ConstructionTargets.SingularExcision.ambientSubspaceRange
          (cpSuccessorTopPatch n) : SSet)) k).trans
      (biprod.mapIso
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorLowerPatch n) k)
        (t99J05_ambientSubspaceRangeHomologyIso (cpSuccessorTopPatch n) k)))

/-- Exactness at the literal overlap term survives transport. -/
theorem t99J05_cp_successor_mayerVietoris_exact_overlap_transport
    (n k : ℕ) :
    (t99J05_cp_successor_mayerVietoris_overlapTransport n k).Exact := by
  apply ConstructionTargets.ProductionOpenCoverMayerVietoris.transportShortComplex_exact
  exact t99J05_cp_successor_mayerVietoris_exact_overlap n k

#print axioms t99J05_cp_successor_mayerVietoris_exact_overlap_transport

/-- Two adjacent exact segments with zero outer terms make their common
middle arrow bijective. -/
theorem t99J05_bijective_of_adjacent_exact_of_subsingleton
    {W X Y Z : ModuleCat ℚ} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : LinearMap.range f.hom = LinearMap.ker g.hom)
    (hgh : LinearMap.range g.hom = LinearMap.ker h.hom)
    [Subsingleton W] [Subsingleton Z] : Function.Bijective g.hom := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    rw [← hfg]
    apply LinearMap.range_eq_bot.mpr
    ext x
    rw [Subsingleton.elim x 0]
    simp
  · rw [← LinearMap.range_eq_top, hgh]
    apply LinearMap.ker_eq_top.mpr
    ext x
    exact Subsingleton.elim _ _

#print axioms t99J05_bijective_of_adjacent_exact_of_subsingleton

/-- A finite-dimensional extraction lemma for the surjective end of an exact
three-term segment.  This is the algebraic step used degreewise after the
Mayer--Vietoris outer terms have been identified. -/
theorem t99J05_finiteDimensional_middle_of_exact_of_surjective
    {X Y Z : ModuleCat ℚ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfun : Function.Exact f.hom g.hom)
    [FiniteDimensional ℚ X] [FiniteDimensional ℚ Z]
    (hg : Function.Surjective g.hom) : FiniteDimensional ℚ Y := by
  letI : Module.Finite ℚ Y := Module.Finite.of_exact
    (R := ℚ) (M := X) (N := Y) (P := Z)
    (f := f.hom) (g := g.hom) hfun hg
  exact inferInstance

#print axioms t99J05_finiteDimensional_middle_of_exact_of_surjective

/-- A linear map into a zero module is automatically surjective. -/
theorem t99J05_surjective_of_subsingleton
    {X Y : ModuleCat ℚ} [Subsingleton Y] (f : X ⟶ Y) :
    Function.Surjective f.hom := by
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

/-- Finite-dimensionality of the middle term of an exact segment when the
right-hand term vanishes. -/
theorem t99J05_finiteDimensional_middle_of_exact_of_subsingleton
    {X Y Z : ModuleCat ℚ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfun : Function.Exact f.hom g.hom)
    [FiniteDimensional ℚ X] [FiniteDimensional ℚ Z] [Subsingleton Z] :
    FiniteDimensional ℚ Y :=
  t99J05_finiteDimensional_middle_of_exact_of_surjective f g hfun
    (t99J05_surjective_of_subsingleton g)

#print axioms t99J05_surjective_of_subsingleton
#print axioms t99J05_finiteDimensional_middle_of_exact_of_subsingleton

/-- The categorical `ShortComplex.Exact` form of the vanishing-term finite
extraction, ready for direct use on transported Mayer--Vietoris segments. -/
theorem t99J05_shortComplex_finiteDimensional_middle_of_subsingleton
    (S : CategoryTheory.ShortComplex (ModuleCat ℚ)) (hS : S.Exact)
    [FiniteDimensional ℚ S.X₁] [FiniteDimensional ℚ S.X₃]
    [Subsingleton S.X₃] : FiniteDimensional ℚ S.X₂ := by
  apply t99J05_finiteDimensional_middle_of_exact_of_subsingleton S.f S.g
  rw [LinearMap.exact_iff]
  exact hS.moduleCat_range_eq_ker.symm

#print axioms t99J05_shortComplex_finiteDimensional_middle_of_subsingleton

/-- In an exact three-term segment, finite-dimensional outer terms force the
middle term to be finite-dimensional; surjectivity is recovered by restricting
the second arrow to its range. -/
theorem t99J05_shortComplex_finiteDimensional_middle
    (S : CategoryTheory.ShortComplex (ModuleCat ℚ)) (hS : S.Exact)
    [FiniteDimensional ℚ S.X₁] [FiniteDimensional ℚ S.X₃] :
    FiniteDimensional ℚ S.X₂ := by
  letI : FiniteDimensional ℚ (LinearMap.range S.g.hom) := inferInstance
  let g' : S.X₂ ⟶ ModuleCat.of ℚ (LinearMap.range S.g.hom) :=
    ModuleCat.ofHom S.g.hom.rangeRestrict
  apply t99J05_finiteDimensional_middle_of_exact_of_surjective
    S.f g'
  · rw [LinearMap.exact_iff]
    change LinearMap.ker S.g.hom.rangeRestrict = LinearMap.range S.f.hom
    rw [LinearMap.ker_rangeRestrict]
    exact hS.moduleCat_range_eq_ker.symm
  · change Function.Surjective S.g.hom.rangeRestrict
    exact S.g.hom.surjective_rangeRestrict

#print axioms t99J05_shortComplex_finiteDimensional_middle

/-- The lower successor patch has the same rational homology as `CP n`, via
the previously constructed deformation-retract equivalence. -/
noncomputable def t99J05_cp_successor_lowerPatch_homologyIso
    (n k : ℕ) :
    Homology (CP n) k ≅
      Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) k :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
    (t99J05_cp_successor_lowerPatch_deformationRetract n) k

/-- Finite-dimensionality from the induction datum transports to the literal
lower successor patch in every degree. -/
theorem t99J05_cp_successor_lowerPatch_finiteDimensional
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) k) := by
  letI : FiniteDimensional ℚ (Homology (CP n) k) := h.finiteDimensional k
  exact (t99J05_cp_successor_lowerPatch_homologyIso n k).toLinearEquiv.finiteDimensional

#print axioms t99J05_cp_successor_lowerPatch_homologyIso
#print axioms t99J05_cp_successor_lowerPatch_finiteDimensional

/-- The last-coordinate affine patch is contractible, via the exact full-target
chart already constructed for the fixed quotient model. -/
theorem t99J05_cp_successor_topPatch_contractible (n : ℕ) :
    ContractibleSpace
      ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} : Set (CP (n + 1))) := by
  obtain ⟨e, hsource, htarget, _⟩ :=
    t99J05_affineChartConstruction_all (n + 1) (Fin.last (n + 1))
  let h : ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) ≃ₜ AffineCoordinates (Fin.last (n + 1)) :=
    (Homeomorph.setCongr (by simpa [cpSuccessorTopPatch] using hsource.symm)).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _)))
  exact h.contractibleSpace

/-- Rational homology of the contractible top affine patch is
finite-dimensional in every degree. -/
theorem t99J05_cp_successor_topPatch_finiteDimensional (n k : ℕ) :
    FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k) := by
  let X := ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
    Set (CP (n + 1)))
  letI : ContractibleSpace X := t99J05_cp_successor_topPatch_contractible n
  letI : Nonempty X :=
    ⟨(Classical.choice (ContractibleSpace.hequiv_unit X)).invFun ()⟩
  by_cases hk : k = 0
  · subst k
    exact (ConstructionTargets.CoefficientH0.h0Iso ℚ
      (Classical.choice inferInstance)).toLinearEquiv.symm.finiteDimensional
  · letI : Subsingleton (Homology X k) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ X k hk)
    exact FiniteDimensional.of_injective (0 : Homology X k →ₗ[ℚ] ℚ)
      (Function.injective_of_subsingleton _)

#print axioms t99J05_cp_successor_topPatch_contractible
#print axioms t99J05_cp_successor_topPatch_finiteDimensional

/-- The lower patch vanishes above the old projective top degree. -/
theorem t99J05_cp_successor_lowerPatch_subsingleton_above
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n)
    (hk : 2 * n < k) :
    Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) k) := by
  letI : Subsingleton (Homology (CP n) k) := h.vanishesAbove k hk
  exact (t99J05_cp_successor_lowerPatch_homologyIso n k).symm.toLinearEquiv.injective.subsingleton

/-- Positive-degree homology of the contractible top patch vanishes. -/
theorem t99J05_cp_successor_topPatch_subsingleton_positive
    (n k : ℕ) (hk : 0 < k) :
    Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k) := by
  letI : ContractibleSpace
      ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} : Set (CP (n + 1))) :=
    t99J05_cp_successor_topPatch_contractible n
  exact ModuleCat.isZero_iff_subsingleton.mp
    (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ _ k
      (Nat.ne_of_gt hk))

#print axioms t99J05_cp_successor_lowerPatch_subsingleton_above
#print axioms t99J05_cp_successor_topPatch_subsingleton_positive

/-- At the new top degree, the transported Mayer--Vietoris connecting map is
bijective because both adjacent patch terms vanish. -/
theorem t99J05_cp_successor_top_connecting_bijective
    (n : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    Function.Bijective
      (t99J05_cp_successor_mayerVietoris_ambientTransport n (2 * n + 1)).g.hom := by
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n (2 * n + 1)
  let T := t99J05_cp_successor_mayerVietoris_overlapTransport n (2 * n + 1)
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) (2 * n + 2)) :=
    t99J05_cp_successor_lowerPatch_subsingleton_above n (2 * n + 2) h (by omega)
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) (2 * n + 2)) :=
    t99J05_cp_successor_topPatch_subsingleton_positive n (2 * n + 2) (by omega)
  letI : Subsingleton S.X₁ := by
    apply ModuleCat.subsingleton_of_isZero
    change CategoryTheory.Limits.IsZero
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
          Set (CP (n + 1))) (2 * n + 2) ⊞
        Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) (2 * n + 2))
    rw [CategoryTheory.Limits.biprod_isZero_iff]
    exact ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) (2 * n + 1)) :=
    t99J05_cp_successor_lowerPatch_subsingleton_above n (2 * n + 1) h (by omega)
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) (2 * n + 1)) :=
    t99J05_cp_successor_topPatch_subsingleton_positive n (2 * n + 1) (by omega)
  letI : Subsingleton T.X₃ := by
    apply ModuleCat.subsingleton_of_isZero
    change CategoryTheory.Limits.IsZero
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
          Set (CP (n + 1))) (2 * n + 1) ⊞
        Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
          Set (CP (n + 1))) (2 * n + 1))
    rw [CategoryTheory.Limits.biprod_isZero_iff]
    exact ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  have hS := t99J05_cp_successor_mayerVietoris_exact_ambient_transport n (2 * n + 1)
  have hT := t99J05_cp_successor_mayerVietoris_exact_overlap_transport n (2 * n + 1)
  have hshared : S.g = T.f := by rfl
  apply t99J05_bijective_of_adjacent_exact_of_subsingleton S.f S.g T.g
  · exact hS.moduleCat_range_eq_ker
  · rw [hshared]
    exact hT.moduleCat_range_eq_ker

#print axioms t99J05_cp_successor_top_connecting_bijective

/-- The top connecting morphism identifies successor top homology with the
top homology of the affine overlap. -/
noncomputable def t99J05_cp_successor_top_connecting_iso
    (n : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    Homology (CP (n + 1)) (2 * n + 2) ≃ₗ[ℚ]
      Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) (2 * n + 1) :=
  LinearEquiv.ofBijective
    (t99J05_cp_successor_mayerVietoris_ambientTransport n (2 * n + 1)).g.hom
    (t99J05_cp_successor_top_connecting_bijective n h)

#print axioms t99J05_cp_successor_top_connecting_iso

/-- Positive overlap homology below the sphere top degree vanishes. -/
theorem t99J05_cp_successor_overlap_subsingleton_of_pos_of_lt
    (n k : ℕ) (hk0 : 0 < k) (hktop : k < 2 * n + 1) :
    Subsingleton
      (Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) k) := by
  have hzEuclidean :
      CategoryTheory.Limits.IsZero
        (Homology (T02A06.euclideanUnitSphere (2 * n + 2)) k) :=
    t99J05_euclideanUnitSphere_positiveHomology_isZero_of_lt
      (2 * n + 2) k hk0 (by omega)
  have hzAffine : CategoryTheory.Limits.IsZero
      (Homology (Metric.sphere
        (0 : AffineCoordinates (Fin.last (n + 1))) 1) k) :=
    hzEuclidean.of_iso
      (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
        (t99J05_affineUnitSphereHomotopyEquivEuclidean n) k)
  exact ModuleCat.isZero_iff_subsingleton.mp
    (hzAffine.of_iso (t99J05_cp_successor_overlap_homologyIso_unitSphere n k))

#print axioms t99J05_cp_successor_overlap_subsingleton_of_pos_of_lt

/-- In every old positive even degree, the patch-to-successor map is
bijective: the two neighboring overlap groups vanish. -/
theorem t99J05_cp_successor_middle_even_bijective
    (n : ℕ) (i : Fin (n + 1)) (hi : 0 < i.val) :
    Function.Bijective
      (t99J05_cp_successor_mayerVietoris_unionTransport n (2 * i.val)).g.hom := by
  have hitop := i.isLt
  rw [show 2 * i.val = (2 * i.val - 1) + 1 by omega]
  let S := t99J05_cp_successor_mayerVietoris_unionTransport n
    ((2 * i.val - 1) + 1)
  let T := t99J05_cp_successor_mayerVietoris_ambientTransport n (2 * i.val - 1)
  letI : Subsingleton S.X₁ := by
    change Subsingleton
      (Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) ((2 * i.val - 1) + 1))
    exact t99J05_cp_successor_overlap_subsingleton_of_pos_of_lt
      n ((2 * i.val - 1) + 1) (by omega) (by omega)
  letI : Subsingleton T.X₃ := by
    change Subsingleton
      (Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) (2 * i.val - 1))
    exact t99J05_cp_successor_overlap_subsingleton_of_pos_of_lt
      n (2 * i.val - 1) (by omega) (by omega)
  have hS := t99J05_cp_successor_mayerVietoris_union_transport n
    ((2 * i.val - 1) + 1)
  have hT := t99J05_cp_successor_mayerVietoris_exact_ambient_transport
    n (2 * i.val - 1)
  have hshared : S.g = T.f := by
    rfl
  apply t99J05_bijective_of_adjacent_exact_of_subsingleton S.f S.g T.g
  · exact hS.moduleCat_range_eq_ker
  · rw [hshared]
    exact hT.moduleCat_range_eq_ker

#print axioms t99J05_cp_successor_middle_even_bijective

/-- The old positive even homology groups survive unchanged in the successor. -/
noncomputable def t99J05_cp_successor_middle_even_iso
    (n : ℕ) (i : Fin (n + 1)) (hi : 0 < i.val) :
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) (2 * i.val) ≃ₗ[ℚ]
      Homology (CP (n + 1)) (2 * i.val) := by
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) (2 * i.val)
  let T : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) (2 * i.val)
  letI : Subsingleton T :=
    t99J05_cp_successor_topPatch_subsingleton_positive n (2 * i.val) (by omega)
  letI : Unique T :=
    { default := 0
      uniq := fun x => Subsingleton.elim x 0 }
  exact ((ModuleCat.biprodIsoProd L T).toLinearEquiv.trans
      (LinearEquiv.prodUnique (R := ℚ) (M := L) (M₂ := T))).symm.trans
    (LinearEquiv.ofBijective
      (t99J05_cp_successor_mayerVietoris_unionTransport n (2 * i.val)).g.hom
      (t99J05_cp_successor_middle_even_bijective n i hi))

#print axioms t99J05_cp_successor_middle_even_iso

/-- Degree-zero homology of every projective successor is canonically
one-dimensional. -/
noncomputable def t99J05_cp_successor_zero_equiv (n : ℕ) :
    Homology (CP (n + 1)) 0 ≃ₗ[ℚ] ℚ := by
  letI : PathConnectedSpace (NonzeroVectors ℂ (n + 1)) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    change IsPathConnected ({0}ᶜ : Set (Fin (n + 2) → ℂ))
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank']
    norm_cast
    rw [Module.finrank_pi_fintype]
    simp
    omega
  letI : PathConnectedSpace (CP (n + 1)) :=
    (surjective_quotientMap ℂ (n + 1)).pathConnectedSpace
      (continuous_quotientMap ℂ (n + 1))
  let p : CP (n + 1) := chartInverse (Fin.last (n + 1))
    (0 : AffineCoordinates (Fin.last (n + 1)))
  exact (ConstructionTargets.CoefficientH0.h0Iso ℚ p).toLinearEquiv

#print axioms t99J05_cp_successor_zero_equiv

/-- All successor even groups, including degree zero and the new top degree,
are one-dimensional. -/
noncomputable def t99J05_cp_successor_even_equiv
    (n : ℕ) (h : ComplexProjectiveRationalHomologyData n)
    (i : Fin (n + 2)) : Homology (CP (n + 1)) (2 * i.val) ≃ₗ[ℚ] ℚ := by
  have hibound := i.isLt
  by_cases hi0 : i.val = 0
  · rw [hi0]
    exact t99J05_cp_successor_zero_equiv n
  by_cases hitop : i.val = n + 1
  · rw [hitop]
    convert (t99J05_cp_successor_top_connecting_iso n h).trans
      (t99J05_cp_successor_overlap_rational_topHomology n).toLinearEquiv using 1 <;>
      omega
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
    let j : Fin (n + 1) := ⟨i.val, by omega⟩
    exact (t99J05_cp_successor_middle_even_iso n j hipos).symm.trans
      ((t99J05_cp_successor_lowerPatch_homologyIso n (2 * j.val)).symm.toLinearEquiv.trans
        (h.evenEquiv j))

#print axioms t99J05_cp_successor_even_equiv

/-- In an exact segment, zero outer terms force the middle term to vanish. -/
theorem t99J05_subsingleton_middle_of_exact
    {X Y Z : ModuleCat ℚ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hex : LinearMap.range f.hom = LinearMap.ker g.hom)
    [Subsingleton X] [Subsingleton Z] : Subsingleton Y := by
  constructor
  intro y₁ y₂
  have hy : y₁ - y₂ ∈ LinearMap.ker g.hom := by
    change g.hom (y₁ - y₂) = 0
    exact Subsingleton.elim _ _
  rw [← hex] at hy
  obtain ⟨x, hx⟩ := hy
  have hfx : f.hom x = 0 := by
    rw [Subsingleton.elim x 0]
    exact map_zero f.hom
  rw [hfx] at hx
  exact sub_eq_zero.mp hx.symm

#print axioms t99J05_subsingleton_middle_of_exact

/-- Successor homology vanishes above its new top degree. -/
theorem t99J05_cp_successor_subsingleton_above
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n)
    (hk : 2 * (n + 1) < k) :
    Subsingleton (Homology (CP (n + 1)) k) := by
  rw [show k = (k - 1) + 1 by omega]
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) ((k - 1) + 1)
  let T : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) ((k - 1) + 1)
  let P : ModuleCat ℚ := L ⊞ T
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n (k - 1)
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) ((k - 1) + 1)) :=
    t99J05_cp_successor_lowerPatch_subsingleton_above n ((k - 1) + 1) h (by omega)
  letI : Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) ((k - 1) + 1)) :=
    t99J05_cp_successor_topPatch_subsingleton_positive n ((k - 1) + 1) (by omega)
  letI : Subsingleton S.X₁ := by
    apply ModuleCat.subsingleton_of_isZero
    change CategoryTheory.Limits.IsZero P
    rw [CategoryTheory.Limits.biprod_isZero_iff]
    exact ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  letI : Subsingleton S.X₃ := by
    change Subsingleton
      (Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) (k - 1))
    exact ModuleCat.isZero_iff_subsingleton.mp
      (t99J05_cp_successor_overlap_homology_isZero_of_gt n (k - 1) (by omega))
  exact t99J05_subsingleton_middle_of_exact S.f S.g
    (t99J05_cp_successor_mayerVietoris_exact_ambient_transport n (k - 1)).moduleCat_range_eq_ker

#print axioms t99J05_cp_successor_subsingleton_above

/-- Odd homology of the lower patch vanishes by the induction datum. -/
theorem t99J05_cp_successor_lowerPatch_subsingleton_odd
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n) (hk : Odd k) :
    Subsingleton
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) k) := by
  letI : Subsingleton (Homology (CP n) k) := h.vanishesOdd k hk
  exact (t99J05_cp_successor_lowerPatch_homologyIso n k).symm.toLinearEquiv.injective.subsingleton

/-- Successor homology vanishes in every odd degree strictly above one. -/
theorem t99J05_cp_successor_subsingleton_odd_gt_one
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n)
    (hk : Odd k) (hk1 : 1 < k) :
    Subsingleton (Homology (CP (n + 1)) k) := by
  obtain ⟨j, hkj⟩ := hk
  by_cases hktop : 2 * (n + 1) < k
  · exact t99J05_cp_successor_subsingleton_above n k h hktop
  rw [show k = (k - 1) + 1 by omega]
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) ((k - 1) + 1)
  let T : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) ((k - 1) + 1)
  let P : ModuleCat ℚ := L ⊞ T
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n (k - 1)
  have hk' : Odd ((k - 1) + 1) := ⟨j, by omega⟩
  letI : Subsingleton L :=
    t99J05_cp_successor_lowerPatch_subsingleton_odd n ((k - 1) + 1) h hk'
  letI : Subsingleton T :=
    t99J05_cp_successor_topPatch_subsingleton_positive n ((k - 1) + 1) (by omega)
  letI : Subsingleton S.X₁ := by
    apply ModuleCat.subsingleton_of_isZero
    change CategoryTheory.Limits.IsZero P
    rw [CategoryTheory.Limits.biprod_isZero_iff]
    exact ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  letI : Subsingleton S.X₃ := by
    change Subsingleton
      (Homology (cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n :
        Set (CP (n + 1))) (k - 1))
    exact t99J05_cp_successor_overlap_subsingleton_of_pos_of_lt n (k - 1)
      (by omega) (by omega)
  exact t99J05_subsingleton_middle_of_exact S.f S.g
    (t99J05_cp_successor_mayerVietoris_exact_ambient_transport n (k - 1)).moduleCat_range_eq_ker

#print axioms t99J05_cp_successor_lowerPatch_subsingleton_odd
#print axioms t99J05_cp_successor_subsingleton_odd_gt_one

/-- A continuous map out of a path-connected space is injective on rational
zeroth homology. -/
theorem t99J05_h0_map_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(X, Y)) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℚ f) 0).hom := by
  intro a b hab
  apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (ConstructionTargets.CoefficientH0.h0Iso ℚ
      (Classical.choice (inferInstance : Nonempty X))).hom).1
  change (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom a =
    (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom b
  apply_fun (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom at hab
  have hn := ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ f
  have hna := congrArg (fun g => g.hom a) hn
  have hnb := congrArg (fun g => g.hom b) hn
  simp only [CategoryTheory.comp_apply] at hna hnb
  exact hna.symm.trans (hab.trans hnb)

/-- The degree-zero overlap-to-patches arrow is injective. -/
theorem t99J05_cp_successor_literalOverlapToPieces_zero_injective (n : ℕ) :
    Function.Injective (t99J05_cp_successor_literalOverlapToPieces n 0).hom := by
  let O := ({p : CP (n + 1) |
    p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} : Set (CP (n + 1)))
  let L := ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} : Set (CP (n + 1)))
  letI : PathConnectedSpace O := by
    letI : PathConnectedSpace
        ({z : AffineCoordinates (Fin.last (n + 1)) | z ≠ 0} :
          Set (AffineCoordinates (Fin.last (n + 1)))) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (t99J05_puncturedAffine_isPathConnected n)
    let e := t99J05_cp_successor_overlap_homeomorph_puncturedAffine n
    exact e.symm.surjective.pathConnectedSpace e.symm.continuous
  let f : C(O, L) :=
    ⟨fun p => ⟨p.1, p.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  have hincl := t99J05_h0_map_injective f
  change Function.Injective
    (HomologicalComplex.homologyMap
      ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.chains ℚ).map
        (TopCat.toSSet.map
          (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
            (Set.inter_subset_left : cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n ⊆
              cpSuccessorLowerPatch n)))) 0).hom at hincl
  intro a b hab
  apply hincl
  have hc := congrArg (fun z => (biprod.fst :
    Homology L 0 ⊞ Homology
      ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} : Set (CP (n + 1))) 0 ⟶
        Homology L 0).hom z) hab
  change
    (CategoryTheory.CategoryStruct.comp
      (t99J05_cp_successor_literalOverlapToPieces n 0) biprod.fst).hom a =
      (CategoryTheory.CategoryStruct.comp
        (t99J05_cp_successor_literalOverlapToPieces n 0) biprod.fst).hom b at hc
  rw [t99J05_cp_successor_literalOverlapToPieces_fst] at hc
  exact hc

#print axioms t99J05_h0_map_injective
#print axioms t99J05_cp_successor_literalOverlapToPieces_zero_injective

/-- Degreewise finite-dimensionality of successor homology in every degree
whose overlap term vanishes.  The two patch terms are the left object of the
transported adjacent Mayer--Vietoris segment. -/
theorem t99J05_cp_successor_finiteDimensional_of_overlap_subsingleton
    (n k : ℕ)
    [FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) (k + 1))]
    [FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) (k + 1))]
    [FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k)]
    [Subsingleton
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k)] :
    FiniteDimensional ℚ (Homology (CP (n + 1)) (k + 1)) := by
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) (k + 1)
  let T : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) (k + 1)
  let P : ModuleCat ℚ := L ⊞ T
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n k
  letI : FiniteDimensional ℚ S.X₁ := by
    change FiniteDimensional ℚ P
    exact LinearEquiv.finiteDimensional
      (ModuleCat.biprodIsoProd L T).symm.toLinearEquiv
  letI : FiniteDimensional ℚ S.X₃ := by
    change FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k)
    infer_instance
  letI : Subsingleton S.X₃ := by
    change Subsingleton
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k)
    infer_instance
  exact t99J05_shortComplex_finiteDimensional_middle_of_subsingleton
    S
    (t99J05_cp_successor_mayerVietoris_exact_ambient_transport n k)

#print axioms t99J05_cp_successor_finiteDimensional_of_overlap_subsingleton

/-- Above the overlap's top degree, its existing sphere vanishing theorem
supplies both zero and finite-dimensional instances to the degreewise
Mayer--Vietoris extraction. -/
theorem t99J05_cp_successor_finiteDimensional_of_overlap_gt
    (n k : ℕ) (hk : 2 * n + 1 < k)
    [FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
        Set (CP (n + 1))) (k + 1))]
    [FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) (k + 1))] :
    FiniteDimensional ℚ (Homology (CP (n + 1)) (k + 1)) := by
  let O := Homology ({p : CP (n + 1) |
    p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
    Set (CP (n + 1))) k
  letI : Subsingleton O :=
    ModuleCat.isZero_iff_subsingleton.mp
      (t99J05_cp_successor_overlap_homology_isZero_of_gt n k hk)
  letI : FiniteDimensional ℚ O :=
    FiniteDimensional.of_injective (0 : O →ₗ[ℚ] ℚ)
      (Function.injective_of_subsingleton _)
  exact t99J05_cp_successor_finiteDimensional_of_overlap_subsingleton n k

#print axioms t99J05_cp_successor_finiteDimensional_of_overlap_gt

/-- The Mayer--Vietoris segment and the three already-computed patch terms
give finite-dimensional successor homology in every positive degree. -/
theorem t99J05_cp_successor_finiteDimensional_positive
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) (k + 1)) := by
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) (k + 1)
  let T : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) (k + 1)
  let P : ModuleCat ℚ := L ⊞ T
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n k
  letI : FiniteDimensional ℚ L :=
    t99J05_cp_successor_lowerPatch_finiteDimensional n (k + 1) h
  letI : FiniteDimensional ℚ T :=
    t99J05_cp_successor_topPatch_finiteDimensional n (k + 1)
  letI : FiniteDimensional ℚ S.X₁ := by
    change FiniteDimensional ℚ P
    exact LinearEquiv.finiteDimensional
      (ModuleCat.biprodIsoProd L T).symm.toLinearEquiv
  letI : FiniteDimensional ℚ S.X₃ := by
    change FiniteDimensional ℚ
      (Homology ({p : CP (n + 1) |
        p ∈ cpSuccessorLowerPatch n ∩ cpSuccessorTopPatch n} :
        Set (CP (n + 1))) k)
    exact t99J05_cp_successor_overlap_finiteDimensional n k
  exact t99J05_shortComplex_finiteDimensional_middle S
    (t99J05_cp_successor_mayerVietoris_exact_ambient_transport n k)

#print axioms t99J05_cp_successor_finiteDimensional_positive

/-- Degree-zero rational homology of the projective successor is
one-dimensional, by its canonical path-connected-space `H₀` comparison. -/
theorem t99J05_cp_successor_finiteDimensional_zero (n : ℕ) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) 0) := by
  letI : PathConnectedSpace (NonzeroVectors ℂ (n + 1)) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    change IsPathConnected ({0}ᶜ : Set (Fin (n + 2) → ℂ))
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank']
    norm_cast
    rw [Module.finrank_pi_fintype]
    simp
    omega
  letI : PathConnectedSpace (CP (n + 1)) :=
    (surjective_quotientMap ℂ (n + 1)).pathConnectedSpace
      (continuous_quotientMap ℂ (n + 1))
  let p : CP (n + 1) := chartInverse (Fin.last (n + 1))
    (0 : AffineCoordinates (Fin.last (n + 1)))
  exact (ConstructionTargets.CoefficientH0.h0Iso ℚ p).toLinearEquiv.symm.finiteDimensional

/-- All-degree finite-dimensionality for the successor, combining the
canonical degree-zero calculation with Mayer--Vietoris in positive degrees. -/
theorem t99J05_cp_successor_finiteDimensional
    (n k : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) k) := by
  rcases k with _ | k
  · exact t99J05_cp_successor_finiteDimensional_zero n
  · exact t99J05_cp_successor_finiteDimensional_positive n k h

#print axioms t99J05_cp_successor_finiteDimensional_zero
#print axioms t99J05_cp_successor_finiteDimensional

/-- The separately named transported arrow is exactly the first arrow of the
transported short complex whose exactness was established above. -/
theorem t99J05_cp_successor_mayerVietoris_f_transport_eq_piecesTransport_f
    (n k : ℕ) :
    t99J05_cp_successor_mayerVietoris_f_transport n k =
      (t99J05_cp_successor_mayerVietoris_piecesTransport n k).f := by
  rfl

#print axioms t99J05_cp_successor_mayerVietoris_f_transport_eq_piecesTransport_f

/-- Transporting the first Mayer--Vietoris arrow through the range and
biproduct comparisons gives the literal signed overlap-to-pieces arrow. -/
theorem t99J05_cp_successor_mayerVietoris_f_transport_eq_literal
    (n k : ℕ) :
    t99J05_cp_successor_mayerVietoris_f_transport n k =
      t99J05_cp_successor_literalOverlapToPieces n k := by
  apply biprod.hom_ext
  · simp [t99J05_cp_successor_mayerVietoris_f_transport,
      t99J05_cp_successor_literalOverlapToPieces,
      t99J05_cp_successor_mayerVietorisShortComplex,
      ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex,
      t99J05_homologyMap_lift_comp_rationalHomologyBiprodIso_hom_assoc,
      CategoryTheory.Category.assoc]
    rw [← CategoryTheory.Category.assoc]
    change CategoryTheory.CategoryStruct.comp
      (ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).inv _ = _
    apply t99J05_iso_inv_comp_of_hom_comp_eq
      (e := ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k)
    simpa [ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso_hom,
      t99J05_ambientSubspaceRangeHomologyIso,
      HomologicalComplex.homologyMap_comp] using
      ConstructionTargets.CoefficientIntersectionRangeNaturality.homology_square_left
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k
  · simp [t99J05_cp_successor_mayerVietoris_f_transport,
      t99J05_cp_successor_literalOverlapToPieces,
      t99J05_cp_successor_mayerVietorisShortComplex,
      ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex,
      t99J05_homologyMap_lift_comp_rationalHomologyBiprodIso_hom_assoc,
      CategoryTheory.Category.assoc]
    congr 1
    rw [← CategoryTheory.Category.assoc]
    change CategoryTheory.CategoryStruct.comp
      (ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k).inv _ = _
    apply t99J05_iso_inv_comp_of_hom_comp_eq
      (e := ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k)
    simpa [ConstructionTargets.CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso_hom,
      t99J05_ambientSubspaceRangeHomologyIso,
      HomologicalComplex.homologyMap_comp] using
      ConstructionTargets.CoefficientIntersectionRangeNaturality.homology_square_right
        ℚ (cpSuccessorLowerPatch n) (cpSuccessorTopPatch n) k

#print axioms t99J05_cp_successor_mayerVietoris_f_transport_eq_literal

/-- The remaining degree-one successor homology vanishes: exactness embeds it
in overlap H0, while the overlap-to-patches H0 arrow is injective. -/
theorem t99J05_cp_successor_subsingleton_one
    (n : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    Subsingleton (Homology (CP (n + 1)) 1) := by
  let S := t99J05_cp_successor_mayerVietoris_ambientTransport n 0
  let T := t99J05_cp_successor_mayerVietoris_overlapTransport n 0
  let L : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorLowerPatch n} :
      Set (CP (n + 1))) 1
  let U : ModuleCat ℚ :=
    Homology ({p : CP (n + 1) | p ∈ cpSuccessorTopPatch n} :
      Set (CP (n + 1))) 1
  let P : ModuleCat ℚ := L ⊞ U
  letI : Subsingleton L :=
    t99J05_cp_successor_lowerPatch_subsingleton_odd n 1 h (by norm_num)
  letI : Subsingleton U :=
    t99J05_cp_successor_topPatch_subsingleton_positive n 1 (by omega)
  letI : Subsingleton S.X₁ := by
    apply ModuleCat.subsingleton_of_isZero
    change CategoryTheory.Limits.IsZero P
    rw [CategoryTheory.Limits.biprod_isZero_iff]
    exact ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  have hS := t99J05_cp_successor_mayerVietoris_exact_ambient_transport n 0
  have hconn : Function.Injective S.g.hom := by
    rw [← LinearMap.ker_eq_bot, ← hS.moduleCat_range_eq_ker]
    apply LinearMap.range_eq_bot.mpr
    ext x
    rw [Subsingleton.elim x 0]
    simp
  have hT := t99J05_cp_successor_mayerVietoris_exact_overlap_transport n 0
  have hTg : Function.Injective T.g.hom := by
    change Function.Injective (t99J05_cp_successor_mayerVietoris_f_transport n 0).hom
    rw [t99J05_cp_successor_mayerVietoris_f_transport_eq_literal]
    exact t99J05_cp_successor_literalOverlapToPieces_zero_injective n
  have hrange : LinearMap.range S.g.hom = ⊥ := by
    rw [show S.g = T.f by rfl]
    have hTex := hT.moduleCat_range_eq_ker
    change LinearMap.range T.f.hom = LinearMap.ker T.g.hom at hTex
    exact hTex.trans (LinearMap.ker_eq_bot.mpr hTg)
  have hgzero : S.g.hom = 0 := LinearMap.range_eq_bot.mp hrange
  change Subsingleton S.X₂
  constructor
  intro a b
  apply hconn
  have ha : S.g.hom a = 0 := by rw [hgzero]; rfl
  have hb : S.g.hom b = 0 := by rw [hgzero]; rfl
  exact ha.trans hb.symm

#print axioms t99J05_cp_successor_subsingleton_one

/-- Assemble the degreewise successor calculations into the rational homology
datum required by the projective-space induction. -/
noncomputable def t99J05_cp_successor_rational_homology
    (n : ℕ) (h : ComplexProjectiveRationalHomologyData n) :
    ComplexProjectiveRationalHomologyData (n + 1) where
  finiteDimensional k :=
    t99J05_cp_successor_finiteDimensional n k h
  vanishesAbove k hk :=
    t99J05_cp_successor_subsingleton_above n k h hk
  vanishesOdd k hk := by
    by_cases hk1 : k = 1
    · subst k
      exact t99J05_cp_successor_subsingleton_one n h
    · obtain ⟨j, hj⟩ := hk
      exact t99J05_cp_successor_subsingleton_odd_gt_one n k h ⟨j, hj⟩
          (by omega)
  evenEquiv i :=
    t99J05_cp_successor_even_equiv n h i

#print axioms t99J05_cp_successor_rational_homology

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

/-- Rational singular-homology data for every finite-dimensional complex
projective space, assembled from the literal `CP 0` computation and the
Mayer--Vietoris successor step. -/
noncomputable def t99J05_cp_homology
    (n : ℕ) : ComplexProjectiveRationalHomologyData n :=
  complexProjectiveRationalHomologyData_of_zero_of_step
    t99J05_cp_zero_rational_homology
    t99J05_cp_successor_rational_homology n

#print axioms t99J05_cp_homology

/-- The assembled homology data gives the numerical rational Betti profile:
one generator in the even degrees through `2n`, and zero otherwise. -/
theorem t99J05_cp_homology_finrank (n k : ℕ) :
    Module.finrank ℚ (Homology (CP n) k) =
      if Even k ∧ k ≤ 2 * n then 1 else 0 := by
  let h := t99J05_cp_homology n
  letI : FiniteDimensional ℚ (Homology (CP n) k) := h.finiteDimensional k
  by_cases hk : k ≤ 2 * n
  · by_cases he : Even k
    · obtain ⟨i, hi⟩ := he
      let j : Fin (n + 1) := ⟨i, by omega⟩
      have hdeg : k = 2 * j.val := by
        change k = 2 * i
        omega
      rw [if_pos ⟨⟨i, hi⟩, hk⟩, hdeg]
      simpa using LinearEquiv.finrank_eq (h.evenEquiv j)
    · letI : Subsingleton (Homology (CP n) k) :=
        h.vanishesOdd k (Nat.not_even_iff_odd.mp he)
      rw [Module.finrank_zero_of_subsingleton]
      simp [he]
  · letI : Subsingleton (Homology (CP n) k) :=
      h.vanishesAbove k (by omega)
    rw [Module.finrank_zero_of_subsingleton]
    simp [hk]

#print axioms t99J05_cp_homology_finrank

/-- The alternating sum of the rational Betti profile of `CP n` is `n+1`. -/
theorem t99J05_cp_alternating_betti_sum (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1),
      (-1 : ℚ)^k * (if Even k ∧ k ≤ 2 * n then 1 else 0)) =
        (n : ℚ) + 1 := by
  induction n with
  | zero => norm_num [Even]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have he : Even (2 * n + 2) := by exact ⟨n + 1, by omega⟩
    have ho : ¬ Even (2 * n + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨n, by omega⟩
    simp only [ho, false_and, if_false, mul_zero, add_zero, he, true_and]
    rw [show (∑ k ∈ Finset.range (2 * n + 1),
        (-1 : ℚ) ^ k * (if Even k ∧ k ≤ 2 * (n + 1) then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * n + 1),
        (-1 : ℚ) ^ k * (if Even k ∧ k ≤ 2 * n then 1 else 0) by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < 2 * n + 1 := Finset.mem_range.mp hk
      have hkbound : k ≤ 2 * n := by omega
      have hkbound' : k ≤ 2 * (n + 1) := by omega
      by_cases hke : Even k <;> simp [hke, hkbound, hkbound']]
    rw [ih]
    rw [if_pos (by omega)]
    rw [Even.neg_one_pow he]
    norm_num

#print axioms t99J05_cp_alternating_betti_sum

open CategoryTheory CategoryTheory.MonoidalCategory

/-- Convert a topological cylinder homotopy into the simplicial homotopy used
by the singular-chain homotopy-invariance theorem. -/
private noncomputable def t99J05_induced_eq_of_homotopic_sset
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) :
    SSet.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h := (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map h
  h₀ := by
    change _ = TopCat.toSSet.map f
    simp only [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₀]
  h₁ := by
    change _ = TopCat.toSSet.map g
    simp only [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₁]
  rel := by
    ext m x
    exact x.1.property.elim

/-- Homotopic continuous maps induce equal maps on rational singular homology
in every degree. -/
theorem t99J05_induced_eq_of_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopic f g) (k : ℕ) :
    induced f k = induced g k := by
  rcases H with ⟨H⟩
  let h : TopCat.of X ⊗ TopCat.I ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
      H.continuous.comp
        ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  have h₀ : TopCat.ι₀ ≫ h = TopCat.ofHom f := by
    ext x
    change H (0, x) = f x
    simp
  have h₁ : TopCat.ι₁ ≫ h = TopCat.ofHom g := by
    ext x
    change H (1, x) = g x
    simp
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
      (f := TopCat.toSSet.map (TopCat.ofHom f))
      (g := TopCat.toSSet.map (TopCat.ofHom g))
      (t99J05_induced_eq_of_homotopic_sset h h₀ h₁).toSimplicialObjectHomotopy k

#print axioms t99J05_induced_eq_of_homotopic

#print axioms ComplexProjectiveRationalHomologyData.finiteDimensionalAt
#print axioms cp_zero_subsingleton
#print axioms cpZeroHomologyDataOfSubsingletonData
#print axioms t99J05_subsingleton_rational_homology
#print axioms t99J05_cp_zero_rational_homology
#print axioms cpSuccessorTopPatch_isOpen
#print axioms cpSuccessorLowerPatch_isOpen
#print axioms cpSuccessor_openCover
#print axioms cpSuccessorZeroLastVector
#print axioms cpSuccessorZeroLastVector_last
#print axioms cpSuccessorZeroLastVector_castSucc
#print axioms cpSuccessorLowerVectorHomotopy_continuous
#print axioms cpSuccessorLowerVectorHomotopy_mem_lowerPatch
#print axioms cpSuccessorLowerVectorHomotopyInPatch_continuous
#print axioms cpSuccessorLowerQuotientMap_isOpenQuotient
#print axioms cpSuccessorLowerPatchHomotopy_quotient
#print axioms cpSuccessorLowerPatchHomotopy_continuous
#print axioms cpSuccessorLowerPatchHomotopy_zero
#print axioms cpSuccessorLowerPatchHomotopy_one
#print axioms cpSuccessorZeroLastIncludeVector_continuous
#print axioms cpSuccessorZeroLastIncludeVector_mem_lowerPatch
#print axioms cpSuccessorZeroLastIncludeVectorInPatch_continuous
#print axioms cpSuccessorZeroLastInclusion
#print axioms cpSuccessorZeroLastInclusion_quotient
#print axioms cpSuccessorLowerTruncateVector
#print axioms cpSuccessorZeroLastInclude_truncate
#print axioms cpSuccessorLowerPatchHomotopy_one_eq_inclusion
#print axioms cpSuccessorLowerTruncateVector_continuous
#print axioms cpSuccessorLowerTruncateVector_smul
#print axioms cpSuccessorLowerTruncationOnVectors_continuous
#print axioms cpSuccessorLowerRetraction_quotient
#print axioms cpSuccessorLowerRetraction_continuous
#print axioms cpSuccessorLowerTruncate_include
#print axioms cpSuccessorLowerRetraction_inclusion
#print axioms cpSuccessorLowerPatchHomotopy_one_eq_inclusion_retraction
#print axioms cpSuccessorLowerPatchDeformationHomotopy
#print axioms t99J05_cp_successor_lowerPatch_deformationRetract
#print axioms cpSuccessor_overlap_topCoordinates_ne_zero
#print axioms t99J05_affineChartConstruction_all
#print axioms t99J05_cp_successor_overlap_homeomorph_puncturedAffine
#print axioms t99J05_cp_successor_overlap_homologyIso_puncturedAffine
#print axioms t99J05_cp_successor_overlap_homotopyEquiv_unitSphere
#print axioms t99J05_cp_successor_overlap_homologyIso_unitSphere
#print axioms t99J05_puncturedAffine_isPathConnected
#print axioms t99J05_cp_successor_overlap_rational_H0
#print axioms t99J05_cp_successor_overlap_finiteDimensional_of_unitSphere
#print axioms t99J05_cp_successor_overlap_subsingleton_of_unitSphere
#print axioms t99J05_cp_successor_overlap_topIso_of_unitSphere
#print axioms t99J05_affineCoordinatesEuclideanEquiv
#print axioms t99J05_puncturedAffineCoordinatesEuclideanHomeomorph
#print axioms t99J05_affineUnitSphereHomotopyEquivEuclidean
#print axioms t99J05_affineUnitSphere_topHomologyIso
#print axioms t99J05_euclideanUnitSphere_H1_isZero
#print axioms t99J05_euclideanUnitSphere_positiveHomology_isZero_of_lt
#print axioms t99J05_euclideanUnitSphere_homology_isZero_of_gt
#print axioms t99J05_affineUnitSphere_homology_isZero_of_gt
#print axioms t99J05_cp_successor_overlap_homology_isZero_of_gt
#print axioms t99J05_cp_successor_overlap_rational_topHomology
#print axioms t99J05_cp_successor_subcomplexMayerVietoris_shortExact
#print axioms t99J05_cp_successor_mayerVietorisShortComplex
#print axioms t99J05_cp_successor_mayerVietoris_exact_pieces
#print axioms t99J05_cp_successor_mayerVietorisConnecting
#print axioms t99J05_cp_successor_mayerVietoris_exact_overlap
#print axioms t99J05_cp_successor_mayerVietoris_exact_ambient
#print axioms t99J05_ambientSubspaceRangeChainsIso
#print axioms t99J05_ambientSubspaceRangeHomologyIso
#print axioms t99J05_ambientSubspaceRangeHomologyIso_hom_comp_subspaceMap
#print axioms t99J05_cp_successor_mayerVietoris_rangeHomologyIsos
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_odd
#print axioms complexProjectiveRationalHomologyData_of_zero_of_step

end ConstructionTargets.t99J05Closure
