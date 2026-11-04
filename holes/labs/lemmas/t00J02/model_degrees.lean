import Mathlib
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator

open CategoryTheory Set

noncomputable section

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def horizontal (u : ℝ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then u else 0)

lemma horizontal_zero : horizontal 0 = 0 := by
  ext i
  simp [horizontal]

def horizontalSlice (U : Set E2) : Set ℝ := {u | horizontal u ∈ U}

def productMap (g : C(E2, ℝ)) : C(E2, E2) where
  toFun p := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if i = 0 then g p else p 1)
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa using g.continuous
    · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

def splitProductMap (g : C(E2, ℝ)) : C(E2, E2) :=
  productMap ⟨fun p => g (horizontal (p 0)),
    g.continuous.comp (by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi; intro i; fin_cases i
      · simpa [horizontal] using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
      · exact continuous_const)⟩

def sliceMap (U : Set E2) (g : C(E2, ℝ)) : C(horizontalSlice U, ℝ) where
  toFun u := g (horizontal u)
  continuous_toFun := g.continuous.comp <| by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa [horizontal] using
        (continuous_subtype_val : Continuous (fun u : horizontalSlice U => (u : ℝ)))
    · exact continuous_const

def restrictedMap (U : Set E2) (F : C(E2, E2)) : C(U, E2) :=
  F.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The degree of a map from an open neighborhood of the origin, expressed
exactly as in `t00J02_IsLocalDegree`: a neighborhood class restricts to the
standard ambient local generator and its pushforward is `n` times the target
generator. -/
def IsLocalDegreeTwo (U : Set E2) (F : C(E2, E2))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains (neighborhoodDeletedPoint U (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion U)
          (neighborhoodInclusion_mapsTo U 0)) 2 a =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (restrictedMap U F) (by
            intro p hp hFp
            exact hp ((hzero p).mp hFp))) 2 a =
      n • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2)

def identityScalar : C(E2, ℝ) where
  toFun p := p 0
  continuous_toFun := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0

def reflectionScalar : C(E2, ℝ) where
  toFun p := -(p 0)
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).neg

def positiveFoldScalar : C(E2, ℝ) where
  toFun p := (p 0) ^ 2
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2

def negativeFoldScalar : C(E2, ℝ) where
  toFun p := -((p 0) ^ 2)
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2).neg

lemma identity_productMap_zero_iff (U : Set E2) (p : U) :
    productMap identityScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 0) h
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, identityScalar]

lemma reflection_productMap_zero_iff (U : Set E2) (p : U) :
    productMap reflectionScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) h
      simpa [productMap, reflectionScalar] using neg_eq_zero.mp h0
    · simpa [productMap, reflectionScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, reflectionScalar]

lemma positiveFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap positiveFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : (p.1 0) ^ 2 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 0) h
    have hp0 : p.1 0 = 0 := eq_zero_of_pow_eq_zero h0
    have hp1 : p.1 1 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i
    fin_cases i <;> simp [hp0, hp1]
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, positiveFoldScalar]

lemma negativeFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap negativeFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : -((p.1 0) ^ 2) = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 0) h
    have hp0 : p.1 0 = 0 := eq_zero_of_pow_eq_zero (neg_eq_zero.mp h0)
    have hp1 : p.1 1 = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i
    fin_cases i <;> simp [hp0, hp1]
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, negativeFoldScalar]

/-- The identity map carries the ambient local generator to itself.  The
neighborhood generator is obtained by inverting the neighborhood-inclusion
isomorphism.  Estimated size: 35--60 lines. -/
theorem identity_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap identityScalar)
      (identity_productMap_zero_iff U) 1 := by
  sorry

/-- Reflection in the first coordinate acts by `-1` on two-dimensional local
homology.  This follows by transporting `all_reflections_negative` through
the radial local-homology isomorphism.  Estimated size: 70--110 lines. -/
theorem reflection_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap reflectionScalar)
      (reflection_productMap_zero_iff U) (-1) := by
  sorry

/-- The positive fold has zero local degree.  Its image lies in the closed
right half-plane; the relative `H₂` of that half-plane at the origin vanishes
because the half-plane and its puncture are contractible.  Estimated size:
90--150 lines. -/
theorem positiveFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap positiveFoldScalar)
      (positiveFold_productMap_zero_iff U) 0 := by
  sorry

/-- The negative fold has zero local degree by the identical half-plane
factorization through the closed left half-plane.  Estimated size: 25--45
lines once the positive half-plane calculation is available. -/
theorem negativeFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap negativeFoldScalar)
      (negativeFold_productMap_zero_iff U) 0 := by
  sorry

end t00J02_ModelProduct
