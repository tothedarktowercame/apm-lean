import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.CoefficientH0
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
import ConstructionTargets.CoefficientFirstReflection
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
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_two_mul_lt
#print axioms ComplexProjectiveRationalHomologyData.subsingleton_of_odd
#print axioms complexProjectiveRationalHomologyData_of_zero_of_step

end ConstructionTargets.t99J05Closure
