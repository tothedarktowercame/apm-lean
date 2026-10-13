import Mathlib
import ConstructionTargets.T94A08AffineChartHomeomorph
import ConstructionTargets.T94A08AffineSmoothConicParametrization

/-!
# APM t94A08 — blueprint for a smooth and a nodal projective conic

The projective affine charts and the affine smooth-conic parametrization are
already available in the imported, sorry-free `ConstructionTargets` modules.
The two remaining topological conclusions are deliberately independent
top-level contracts, so they can be proved in parallel.
-/

open Set
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t94a08_C3 := Fin 3 → ℂ
abbrev apm_t94a08_CP2 := Projectivization ℂ apm_t94a08_C3

noncomputable instance apm_t94a08_projectiveTopology :
    TopologicalSpace apm_t94a08_CP2 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

def apm_t94a08_quadratic1 (z : apm_t94a08_C3) : ℂ :=
  z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_quadratic2 (z : apm_t94a08_C3) : ℂ :=
  z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_sigma1 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic1 (Projectivization.rep p) = 0}

def apm_t94a08_sigma2 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic2 (Projectivization.rep p) = 0}

def apm_t94a08_IsRegularLevelSet
    (q : apm_t94a08_C3 → ℂ) (S : Set apm_t94a08_CP2) : Prop :=
  S = {p | q (Projectivization.rep p) = 0} ∧
    ∀ z : apm_t94a08_C3, z ≠ 0 → q z = 0 → fderiv ℂ q z ≠ 0

def apm_t94a08_IsRealTwoManifoldAt
    (S : Set apm_t94a08_CP2) (p : apm_t94a08_CP2) : Prop :=
  ∃ U : Set apm_t94a08_CP2,
    IsOpen U ∧ p ∈ U ∧
      ∃ W : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen W ∧ Nonempty (↥(U ∩ S) ≃ₜ ↥W)

def apm_t94a08_IsRealTwoManifold (S : Set apm_t94a08_CP2) : Prop :=
  ∀ p ∈ S, apm_t94a08_IsRealTwoManifoldAt S p

private def apm_t94a08_dquadratic1 (z : apm_t94a08_C3) :
    apm_t94a08_C3 →L[ℂ] ℂ :=
  (2 * z 0) • ContinuousLinearMap.proj 0 +
    (2 * z 1) • ContinuousLinearMap.proj 1 +
      (2 * z 2) • ContinuousLinearMap.proj 2

set_option maxHeartbeats 800000 in
private lemma apm_t94a08_hasFDerivAt_quadratic1 (z : apm_t94a08_C3) :
    HasFDerivAt apm_t94a08_quadratic1 (apm_t94a08_dquadratic1 z) z := by
  unfold apm_t94a08_quadratic1 apm_t94a08_dquadratic1
  convert ((((ContinuousLinearMap.proj 0 : apm_t94a08_C3 →L[ℂ] ℂ)).hasFDerivAt.pow 2).add
    ((ContinuousLinearMap.proj 1 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt.pow 2)).add
      ((ContinuousLinearMap.proj 2 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt.pow 2) using 1 <;>
    ext x <;> simp [mul_comm]

private lemma apm_t94a08_dquadratic1_ne_zero {z : apm_t94a08_C3} (hz : z ≠ 0) :
    apm_t94a08_dquadratic1 z ≠ 0 := by
  intro hd
  apply hz
  funext i
  fin_cases i
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 0 1)) hd
    simpa [apm_t94a08_dquadratic1] using h
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 1 1)) hd
    simpa [apm_t94a08_dquadratic1] using h
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 2 1)) hd
    simpa [apm_t94a08_dquadratic1] using h

lemma apm_t94a08_regularLevelSet_quadratic1 :
    apm_t94a08_IsRegularLevelSet apm_t94a08_quadratic1 apm_t94a08_sigma1 := by
  refine ⟨rfl, ?_⟩
  intro z hz _
  rw [(apm_t94a08_hasFDerivAt_quadratic1 z).fderiv]
  exact apm_t94a08_dquadratic1_ne_zero hz

private lemma apm_t94a08_e0_ne_zero : (Pi.single 0 1 : apm_t94a08_C3) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa using h0

def apm_t94a08_node : apm_t94a08_CP2 :=
  Projectivization.mk ℂ (Pi.single 0 1) apm_t94a08_e0_ne_zero

lemma apm_t94a08_node_mem_sigma2 : apm_t94a08_node ∈ apm_t94a08_sigma2 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep
    (K := ℂ) (Pi.single 0 1 : apm_t94a08_C3) apm_t94a08_e0_ne_zero
  rw [apm_t94a08_sigma2, mem_setOf_eq, apm_t94a08_quadratic2]
  change (Projectivization.mk ℂ (Pi.single 0 1) apm_t94a08_e0_ne_zero).rep 1 ^ 2 +
    (Projectivization.mk ℂ (Pi.single 0 1) apm_t94a08_e0_ne_zero).rep 2 ^ 2 = 0
  rw [← ha]
  simp

lemma apm_t94a08_quadratic2_factor (z : apm_t94a08_C3) :
    apm_t94a08_quadratic2 z =
      (z 1 + Complex.I * z 2) * (z 1 - Complex.I * z 2) := by
  unfold apm_t94a08_quadratic2
  calc
    z 1 ^ 2 + z 2 ^ 2 = z 1 ^ 2 - Complex.I ^ 2 * z 2 ^ 2 := by
      rw [pow_two Complex.I, Complex.I_mul_I]
      ring
    _ = (z 1 + Complex.I * z 2) * (z 1 - Complex.I * z 2) := by ring

def apm_t94a08_sigma2BranchPlus : Set apm_t94a08_CP2 :=
  {p | Projectivization.rep p 1 + Complex.I * Projectivization.rep p 2 = 0}

def apm_t94a08_sigma2BranchMinus : Set apm_t94a08_CP2 :=
  {p | Projectivization.rep p 1 - Complex.I * Projectivization.rep p 2 = 0}

lemma apm_t94a08_sigma2_eq_branches :
    apm_t94a08_sigma2 =
      apm_t94a08_sigma2BranchPlus ∪ apm_t94a08_sigma2BranchMinus := by
  ext p
  rw [apm_t94a08_sigma2, mem_setOf_eq,
    apm_t94a08_quadratic2_factor, mul_eq_zero]
  rfl

lemma apm_t94a08_node_mem_both_branches :
    apm_t94a08_node ∈ apm_t94a08_sigma2BranchPlus ∩
      apm_t94a08_sigma2BranchMinus := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep
    (K := ℂ) (Pi.single 0 1 : apm_t94a08_C3) apm_t94a08_e0_ne_zero
  constructor
  · change apm_t94a08_node.rep 1 + Complex.I * apm_t94a08_node.rep 2 = 0
    unfold apm_t94a08_node
    rw [← ha]
    simp
  · change apm_t94a08_node.rep 1 - Complex.I * apm_t94a08_node.rep 2 = 0
    unfold apm_t94a08_node
    rw [← ha]
    simp

/-- LIBRARY: construct local Euclidean charts for the smooth projective conic,
using the imported projective affine charts and affine-conic parametrization. -/
theorem apm_t94a08_sigma1_isRealTwoManifold :
    apm_t94a08_IsRealTwoManifold apm_t94a08_sigma1 := by
  sorry

/-- LIBRARY: the union of the two distinct complex projective lines is not
locally Euclidean at their common node. -/
theorem apm_t94a08_nodal_not_manifold_at :
    ¬apm_t94a08_IsRealTwoManifoldAt apm_t94a08_sigma2 apm_t94a08_node := by
  sorry

theorem apm_t94a08 :
    apm_t94a08_IsRegularLevelSet
        apm_t94a08_quadratic1 apm_t94a08_sigma1 ∧
      apm_t94a08_IsRealTwoManifold apm_t94a08_sigma1 ∧
      ¬apm_t94a08_IsRealTwoManifold apm_t94a08_sigma2 := by
  refine ⟨apm_t94a08_regularLevelSet_quadratic1,
    apm_t94a08_sigma1_isRealTwoManifold, ?_⟩
  intro hman
  exact apm_t94a08_nodal_not_manifold_at
    (hman apm_t94a08_node apm_t94a08_node_mem_sigma2)

#print axioms apm_t94a08
