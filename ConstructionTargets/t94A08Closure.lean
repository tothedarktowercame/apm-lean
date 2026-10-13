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
private def apm_t94a08_sigma1_isRealTwoManifold_aux_complexReal :
    ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm).toHomeomorph

private def apm_t94a08_sigma1_isRealTwoManifold_aux_W :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | (apm_t94a08_sigma1_isRealTwoManifold_aux_complexReal.symm x) ≠ 0}

private lemma apm_t94a08_sigma1_isRealTwoManifold_aux_W_open :
    IsOpen apm_t94a08_sigma1_isRealTwoManifold_aux_W := by
  exact isOpen_compl_singleton.preimage
    apm_t94a08_sigma1_isRealTwoManifold_aux_complexReal.symm.continuous

private def apm_t94a08_sigma1_isRealTwoManifold_aux_cstarReal :
    T94A08AffineSmoothConicParam.Cstar ≃ₜ
      ↑apm_t94a08_sigma1_isRealTwoManifold_aux_W :=
  apm_t94a08_sigma1_isRealTwoManifold_aux_complexReal.subtype (fun z => by
    rfl)

private def apm_t94a08_sigma1_isRealTwoManifold_aux_affineConicReal :
    T94A08AffineSmoothConicParam.AffineConic ≃ₜ
      ↑apm_t94a08_sigma1_isRealTwoManifold_aux_W :=
  T94A08AffineSmoothConicParam.affineConicHomeomorphCstar.trans
    apm_t94a08_sigma1_isRealTwoManifold_aux_cstarReal

private theorem apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_zero :
    Nonempty
      (↑({p : apm_t94a08_CP2 | Projectivization.rep p (0 : Fin 3) ≠ 0} ∩
          apm_t94a08_sigma1) ≃ₜ
        T94A08AffineSmoothConicParam.AffineConic) := by
  open ConstructionTargets.ComplexProjectiveChartTargets in
      let a : Fin 3 := 0
      let j : {j : Fin 3 // j ≠ a} := ⟨1, by decide⟩
      let k : {j : Fin 3 // j ≠ a} := ⟨2, by decide⟩
      let f : ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
          apm_t94a08_sigma1) → T94A08AffineSmoothConicParam.AffineConic :=
        fun p ↦ ⟨(coordinates a p.1 j, coordinates a p.1 k), by
          have ha : Projectivization.rep p.1 a ≠ 0 := p.2.1
          have hq : apm_t94a08_quadratic1 (Projectivization.rep p.1) = 0 := p.2.2
          unfold apm_t94a08_quadratic1 at hq
          dsimp [coordinates, a, j, k]
          rw [div_pow, div_pow]
          calc
            1 + Projectivization.rep p.1 1 ^ 2 / Projectivization.rep p.1 0 ^ 2 +
                Projectivization.rep p.1 2 ^ 2 / Projectivization.rep p.1 0 ^ 2 =
                (Projectivization.rep p.1 0 ^ 2 + Projectivization.rep p.1 1 ^ 2 +
                  Projectivization.rep p.1 2 ^ 2) / Projectivization.rep p.1 0 ^ 2 := by
                    rw [← div_self (pow_ne_zero 2 ha)]
                    ring
            _ = 0 := by rw [hq]; simp⟩
      let g : T94A08AffineSmoothConicParam.AffineConic →
          ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
            apm_t94a08_sigma1) := fun z ↦
        ⟨chartInverse a (fun q ↦ if q.1 = 1 then z.1.1 else z.1.2), by
          constructor
          · exact ConstructionTargets.T94A08ProjectiveConic.chartInverse_mem_affineSource _ _
          · rw [apm_t94a08_sigma1, mem_setOf_eq, apm_t94a08_quadratic1]
            let v : Fin 3 → ℂ := fun q ↦ if h : q = a then 1 else
              (fun q : {q : Fin 3 // q ≠ a} ↦ if q.1 = 1 then z.1.1 else z.1.2) ⟨q, h⟩
            have hv : v ≠ 0 := by
              intro h
              have := congrFun h a
              simpa [v, a] using this
            obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
            change apm_t94a08_quadratic1
              (Projectivization.rep (Projectivization.mk ℂ v hv)) = 0
            rw [← hc]
            dsimp [apm_t94a08_quadratic1, v, a]
            have hz := z.2
            simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
            ring_nf at hz ⊢
            linear_combination c.1 ^ 2 * hz⟩
      refine ⟨Homeomorph.mk (Equiv.mk f g ?_ ?_) ?_ ?_⟩
      · intro p
        apply Subtype.ext
        dsimp [f, g]
        have heq : (fun q : {q : Fin 3 // q ≠ a} =>
            if q.1 = 1 then coordinates a p.1 j else coordinates a p.1 k) =
            coordinates a p.1 := by
          funext q
          fin_cases q <;> simp [a, j, k]
        rw [heq, ConstructionTargets.T94A08ProjectiveConic.chartInverse_coordinates]
        exact p.2.1
      · intro z
        apply Subtype.ext
        apply Prod.ext <;>
          simp [f, g, j, k,
            ConstructionTargets.T94A08ProjectiveConic.coordinates_chartInverse]
      · apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact (continuous_apply j).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
        · exact (continuous_apply k).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
      · apply Continuous.subtype_mk
        exact (ConstructionTargets.T94A08ProjectiveConic.continuous_chartInverse a).comp
          (continuous_pi fun q ↦ by
            fin_cases q <;> simp [a] <;> fun_prop)

private theorem apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_one :
    Nonempty
      (↑({p : apm_t94a08_CP2 | Projectivization.rep p (1 : Fin 3) ≠ 0} ∩
          apm_t94a08_sigma1) ≃ₜ
        T94A08AffineSmoothConicParam.AffineConic) := by
  open ConstructionTargets.ComplexProjectiveChartTargets in
      let a : Fin 3 := 1
      let j : {j : Fin 3 // j ≠ a} := ⟨0, by decide⟩
      let k : {j : Fin 3 // j ≠ a} := ⟨2, by decide⟩
      let f : ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
          apm_t94a08_sigma1) → T94A08AffineSmoothConicParam.AffineConic :=
        fun p ↦ ⟨(coordinates a p.1 j, coordinates a p.1 k), by
          have ha : Projectivization.rep p.1 a ≠ 0 := p.2.1
          have hq : apm_t94a08_quadratic1 (Projectivization.rep p.1) = 0 := p.2.2
          unfold apm_t94a08_quadratic1 at hq
          dsimp [coordinates, a, j, k]
          rw [div_pow, div_pow]
          calc
            1 + Projectivization.rep p.1 0 ^ 2 / Projectivization.rep p.1 1 ^ 2 +
                Projectivization.rep p.1 2 ^ 2 / Projectivization.rep p.1 1 ^ 2 =
                (Projectivization.rep p.1 0 ^ 2 + Projectivization.rep p.1 1 ^ 2 +
                  Projectivization.rep p.1 2 ^ 2) / Projectivization.rep p.1 1 ^ 2 := by
                    rw [← div_self (pow_ne_zero 2 ha)]
                    ring
            _ = 0 := by rw [hq]; simp⟩
      let g : T94A08AffineSmoothConicParam.AffineConic →
          ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
            apm_t94a08_sigma1) := fun z ↦
        ⟨chartInverse a (fun q ↦ if q.1 = 0 then z.1.1 else z.1.2), by
          constructor
          · exact ConstructionTargets.T94A08ProjectiveConic.chartInverse_mem_affineSource _ _
          · rw [apm_t94a08_sigma1, mem_setOf_eq, apm_t94a08_quadratic1]
            let v : Fin 3 → ℂ := fun q ↦ if h : q = a then 1 else
              (fun q : {q : Fin 3 // q ≠ a} ↦ if q.1 = 0 then z.1.1 else z.1.2) ⟨q, h⟩
            have hv : v ≠ 0 := by
              intro h
              have := congrFun h a
              simpa [v, a] using this
            obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
            change apm_t94a08_quadratic1
              (Projectivization.rep (Projectivization.mk ℂ v hv)) = 0
            rw [← hc]
            dsimp [apm_t94a08_quadratic1, v, a]
            have hz := z.2
            simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
            ring_nf at hz ⊢
            linear_combination c.1 ^ 2 * hz⟩
      refine ⟨Homeomorph.mk (Equiv.mk f g ?_ ?_) ?_ ?_⟩
      · intro p
        apply Subtype.ext
        dsimp [f, g]
        have heq : (fun q : {q : Fin 3 // q ≠ a} =>
            if q.1 = 0 then coordinates a p.1 j else coordinates a p.1 k) =
            coordinates a p.1 := by
          funext q
          fin_cases q <;> simp [a, j, k]
        rw [heq, ConstructionTargets.T94A08ProjectiveConic.chartInverse_coordinates]
        exact p.2.1
      · intro z
        apply Subtype.ext
        apply Prod.ext <;>
          simp [f, g, j, k,
            ConstructionTargets.T94A08ProjectiveConic.coordinates_chartInverse]
      · apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact (continuous_apply j).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
        · exact (continuous_apply k).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
      · apply Continuous.subtype_mk
        exact (ConstructionTargets.T94A08ProjectiveConic.continuous_chartInverse a).comp
          (continuous_pi fun q ↦ by
            fin_cases q <;> simp [a] <;> fun_prop)

private theorem apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_two :
    Nonempty
      (↑({p : apm_t94a08_CP2 | Projectivization.rep p (2 : Fin 3) ≠ 0} ∩
          apm_t94a08_sigma1) ≃ₜ
        T94A08AffineSmoothConicParam.AffineConic) := by
  open ConstructionTargets.ComplexProjectiveChartTargets in
      let a : Fin 3 := 2
      let j : {j : Fin 3 // j ≠ a} := ⟨0, by decide⟩
      let k : {j : Fin 3 // j ≠ a} := ⟨1, by decide⟩
      let f : ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
          apm_t94a08_sigma1) → T94A08AffineSmoothConicParam.AffineConic :=
        fun p ↦ ⟨(coordinates a p.1 j, coordinates a p.1 k), by
          have ha : Projectivization.rep p.1 a ≠ 0 := p.2.1
          have hq : apm_t94a08_quadratic1 (Projectivization.rep p.1) = 0 := p.2.2
          unfold apm_t94a08_quadratic1 at hq
          dsimp [coordinates, a, j, k]
          rw [div_pow, div_pow]
          calc
            1 + Projectivization.rep p.1 0 ^ 2 / Projectivization.rep p.1 2 ^ 2 +
                Projectivization.rep p.1 1 ^ 2 / Projectivization.rep p.1 2 ^ 2 =
                (Projectivization.rep p.1 0 ^ 2 + Projectivization.rep p.1 1 ^ 2 +
                  Projectivization.rep p.1 2 ^ 2) / Projectivization.rep p.1 2 ^ 2 := by
                    rw [← div_self (pow_ne_zero 2 ha)]
                    ring
            _ = 0 := by rw [hq]; simp⟩
      let g : T94A08AffineSmoothConicParam.AffineConic →
          ↑({p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} ∩
            apm_t94a08_sigma1) := fun z ↦
        ⟨chartInverse a (fun q ↦ if q.1 = 0 then z.1.1 else z.1.2), by
          constructor
          · exact ConstructionTargets.T94A08ProjectiveConic.chartInverse_mem_affineSource _ _
          · rw [apm_t94a08_sigma1, mem_setOf_eq, apm_t94a08_quadratic1]
            let v : Fin 3 → ℂ := fun q ↦ if h : q = a then 1 else
              (fun q : {q : Fin 3 // q ≠ a} ↦ if q.1 = 0 then z.1.1 else z.1.2) ⟨q, h⟩
            have hv : v ≠ 0 := by
              intro h
              have := congrFun h a
              simpa [v, a] using this
            obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
            change apm_t94a08_quadratic1
              (Projectivization.rep (Projectivization.mk ℂ v hv)) = 0
            rw [← hc]
            dsimp [apm_t94a08_quadratic1, v, a]
            have hz := z.2
            simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
            ring_nf at hz ⊢
            linear_combination c.1 ^ 2 * hz⟩
      refine ⟨Homeomorph.mk (Equiv.mk f g ?_ ?_) ?_ ?_⟩
      · intro p
        apply Subtype.ext
        dsimp [f, g]
        have heq : (fun q : {q : Fin 3 // q ≠ a} =>
            if q.1 = 0 then coordinates a p.1 j else coordinates a p.1 k) =
            coordinates a p.1 := by
          funext q
          fin_cases q <;> simp [a, j, k]
        rw [heq, ConstructionTargets.T94A08ProjectiveConic.chartInverse_coordinates]
        exact p.2.1
      · intro z
        apply Subtype.ext
        apply Prod.ext <;>
          simp [f, g, j, k,
            ConstructionTargets.T94A08ProjectiveConic.coordinates_chartInverse]
      · apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact (continuous_apply j).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
        · exact (continuous_apply k).comp
            ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
              continuous_subtype_val (fun p ↦ p.2.1))
      · apply Continuous.subtype_mk
        exact (ConstructionTargets.T94A08ProjectiveConic.continuous_chartInverse a).comp
          (continuous_pi fun q ↦ by
            fin_cases q <;> simp [a] <;> fun_prop)

theorem apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice (i : Fin 3) :
    Nonempty
      (↑({p : apm_t94a08_CP2 | Projectivization.rep p i ≠ 0} ∩
          apm_t94a08_sigma1) ≃ₜ
        T94A08AffineSmoothConicParam.AffineConic) := by
  fin_cases i
  · exact apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_zero
  · exact apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_one
  · exact apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice_aux_two

theorem apm_t94a08_sigma1_isRealTwoManifold :
    apm_t94a08_IsRealTwoManifold apm_t94a08_sigma1 := by
  intro p hp
  have hex : ∃ i : Fin 3, Projectivization.rep p i ≠ 0 := by
    by_contra h
    push_neg at h
    apply Projectivization.rep_nonzero p
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let U : Set apm_t94a08_CP2 :=
    {q | Projectivization.rep q i ≠ 0}
  refine ⟨U, ?_, hi, apm_t94a08_sigma1_isRealTwoManifold_aux_W,
    apm_t94a08_sigma1_isRealTwoManifold_aux_W_open, ?_⟩
  · exact ConstructionTargets.ComplexProjectiveChartTargets.affineSource_isOpen i
  · obtain ⟨e⟩ := apm_t94a08_sigma1_isRealTwoManifold_aux_chartSlice i
    exact ⟨e.trans apm_t94a08_sigma1_isRealTwoManifold_aux_affineConicReal⟩

/-! ## Affine algebra for the nodal obstruction

In the chart where the zeroth homogeneous coordinate is nonzero, the two
projective branches are the following two complex lines.  The next lemmas
isolate the algebraic fact used by the punctured-neighborhood argument: the
branches meet only at the origin.
-/

def apm_t94a08_affineBranchPlus : Set (ℂ × ℂ) :=
  {z | z.1 + Complex.I * z.2 = 0}

def apm_t94a08_affineBranchMinus : Set (ℂ × ℂ) :=
  {z | z.1 - Complex.I * z.2 = 0}

lemma apm_t94a08_affineBranch_common_zero
    {u v : ℂ} (hplus : u + Complex.I * v = 0)
    (hminus : u - Complex.I * v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (hplus + hminus) / 2
  · have hiv : Complex.I * v = 0 := by
      linear_combination (hplus - hminus) / 2
    exact (mul_eq_zero.mp hiv).resolve_left Complex.I_ne_zero

lemma apm_t94a08_affineBranches_inter :
    apm_t94a08_affineBranchPlus ∩ apm_t94a08_affineBranchMinus = {(0, 0)} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hplus, hminus⟩
    have hzero := apm_t94a08_affineBranch_common_zero hplus hminus
    simpa [Prod.ext_iff] using hzero
  · intro hz
    have hz0 : z = (0, 0) := by simpa using hz
    subst z
    simp [apm_t94a08_affineBranchPlus, apm_t94a08_affineBranchMinus]

def apm_t94a08_puncturedAffineCross : Set (ℂ × ℂ) :=
  (apm_t94a08_affineBranchPlus ∪ apm_t94a08_affineBranchMinus) \ {(0, 0)}

lemma apm_t94a08_affineBranchPlus_isClosed :
    IsClosed apm_t94a08_affineBranchPlus := by
  exact isClosed_singleton.preimage
    (continuous_fst.add (continuous_const.mul continuous_snd))

lemma apm_t94a08_affineBranchMinus_isClosed :
    IsClosed apm_t94a08_affineBranchMinus := by
  exact isClosed_singleton.preimage
    (continuous_fst.sub (continuous_const.mul continuous_snd))

lemma apm_t94a08_puncturedAffineCross_not_isPreconnected :
    ¬ IsPreconnected apm_t94a08_puncturedAffineCross := by
  intro hconn
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hconn
  have hcover : apm_t94a08_puncturedAffineCross ⊆
      apm_t94a08_affineBranchPlus ∪ apm_t94a08_affineBranchMinus :=
    fun _ hz ↦ hz.1
  have hinter : apm_t94a08_puncturedAffineCross ∩
      (apm_t94a08_affineBranchPlus ∩ apm_t94a08_affineBranchMinus) = ∅ := by
    ext z
    constructor
    · intro hz
      have hzero : z = (0, 0) := by
        rw [apm_t94a08_affineBranches_inter] at hz
        simpa using hz.2
      exact (hz.1.2 (by simpa [hzero])).elim
    · intro hz
      exact hz.elim
  rcases hconn _ _ apm_t94a08_affineBranchPlus_isClosed
      apm_t94a08_affineBranchMinus_isClosed hcover hinter with hplus | hminus
  · have hm : (1, -Complex.I) ∈ apm_t94a08_puncturedAffineCross := by
      constructor
      · right
        simp [apm_t94a08_affineBranchMinus]
      · simp [Complex.I_ne_zero]
    have := hplus hm
    simpa [apm_t94a08_affineBranchPlus] using this
  · have hp : (1, Complex.I) ∈ apm_t94a08_puncturedAffineCross := by
      constructor
      · left
        simp [apm_t94a08_affineBranchPlus]
      · simp [Complex.I_ne_zero]
    have := hminus hp
    simpa [apm_t94a08_affineBranchMinus] using this

lemma apm_t94a08_puncturedAffineCross_homeomorph_image_not_isPreconnected
    {X : Type*} [TopologicalSpace X] (e : (ℂ × ℂ) ≃ₜ X) :
    ¬ IsPreconnected (e '' apm_t94a08_puncturedAffineCross) := by
  intro himage
  exact apm_t94a08_puncturedAffineCross_not_isPreconnected
    (e.isInducing.isPreconnected_image.mp himage)

/-! The zeroth projective chart carries `sigma2` exactly to the affine cross. -/

lemma apm_t94a08_sigma2_zeroChart_mem_iff (p : apm_t94a08_CP2)
    (hp : Projectivization.rep p (0 : Fin 3) ≠ 0) :
    let z :=
      (ConstructionTargets.ComplexProjectiveChartTargets.coordinates (0 : Fin 3) p
          ⟨1, by decide⟩,
        ConstructionTargets.ComplexProjectiveChartTargets.coordinates (0 : Fin 3) p
          ⟨2, by decide⟩)
    p ∈ apm_t94a08_sigma2 ↔
      z ∈ apm_t94a08_affineBranchPlus ∪ apm_t94a08_affineBranchMinus := by
  dsimp only
  rw [apm_t94a08_sigma2, mem_setOf_eq, apm_t94a08_quadratic2_factor]
  change _ ↔
    Projectivization.rep p 1 / Projectivization.rep p 0 +
          Complex.I * (Projectivization.rep p 2 / Projectivization.rep p 0) = 0 ∨
      Projectivization.rep p 1 / Projectivization.rep p 0 -
          Complex.I * (Projectivization.rep p 2 / Projectivization.rep p 0) = 0
  rw [mul_eq_zero]
  constructor
  · rintro (hplus | hminus)
    · left
      field_simp
      simpa using hplus
    · right
      field_simp
      simpa using hminus
  · rintro (hplus | hminus)
    · left
      field_simp [hp] at hplus
      simpa using hplus
    · right
      field_simp [hp] at hminus
      simpa using hminus

def apm_t94a08_zeroChartHomeomorph :
    ↑{p : apm_t94a08_CP2 | Projectivization.rep p (0 : Fin 3) ≠ 0} ≃ₜ
      (ℂ × ℂ) := by
  open ConstructionTargets.ComplexProjectiveChartTargets in
    let a : Fin 3 := 0
    let j : {q : Fin 3 // q ≠ a} := ⟨1, by decide⟩
    let k : {q : Fin 3 // q ≠ a} := ⟨2, by decide⟩
    let f : ↑{p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} → ℂ × ℂ :=
      fun p ↦ (coordinates a p.1 j, coordinates a p.1 k)
    let g : ℂ × ℂ →
        ↑{p : apm_t94a08_CP2 | Projectivization.rep p a ≠ 0} :=
      fun z ↦ ⟨chartInverse a (fun q ↦ if q.1 = 1 then z.1 else z.2),
        ConstructionTargets.T94A08ProjectiveConic.chartInverse_mem_affineSource _ _⟩
    exact Homeomorph.mk (Equiv.mk f g (by
      intro p
      apply Subtype.ext
      dsimp [f, g]
      have heq : (fun q : {q : Fin 3 // q ≠ a} ↦
          if q.1 = 1 then coordinates a p.1 j else coordinates a p.1 k) =
          coordinates a p.1 := by
        funext q
        fin_cases q <;> simp [a, j, k]
      rw [heq, ConstructionTargets.T94A08ProjectiveConic.chartInverse_coordinates]
      exact p.2) (by
      intro z
      apply Prod.ext <;>
        simp [f, g, j, k,
          ConstructionTargets.T94A08ProjectiveConic.coordinates_chartInverse])) (by
      apply Continuous.prodMk
      · exact (continuous_apply j).comp
          ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
            continuous_subtype_val (fun p ↦ p.2))
      · exact (continuous_apply k).comp
          ((ConstructionTargets.T94A08ProjectiveConic.continuous_coordinates a).comp_continuous
            continuous_subtype_val (fun p ↦ p.2))) (by
      apply Continuous.subtype_mk
      exact (ConstructionTargets.T94A08ProjectiveConic.continuous_chartInverse a).comp
        (continuous_pi fun q ↦ by
          fin_cases q <;> simp [a] <;> fun_prop))

lemma apm_t94a08_node_mem_zeroChart :
    Projectivization.rep apm_t94a08_node (0 : Fin 3) ≠ 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep
    (K := ℂ) (Pi.single 0 1 : apm_t94a08_C3) apm_t94a08_e0_ne_zero
  change Projectivization.rep
      (Projectivization.mk ℂ (Pi.single 0 1) apm_t94a08_e0_ne_zero) 0 ≠ 0
  rw [← hc]
  simpa [Pi.smul_apply, Units.smul_def] using c.ne_zero

lemma apm_t94a08_zeroChartHomeomorph_node :
    apm_t94a08_zeroChartHomeomorph
      ⟨apm_t94a08_node, apm_t94a08_node_mem_zeroChart⟩ = (0, 0) := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep
    (K := ℂ) (Pi.single 0 1 : apm_t94a08_C3) apm_t94a08_e0_ne_zero
  apply Prod.ext <;>
    change Projectivization.rep apm_t94a08_node _ /
      Projectivization.rep apm_t94a08_node 0 = 0 <;>
    rw [show apm_t94a08_node =
      Projectivization.mk ℂ (Pi.single 0 1) apm_t94a08_e0_ne_zero by rfl, ← hc] <;>
    simp

def apm_t94a08_puncturedSigma2ZeroChart :
    Set ↑{p : apm_t94a08_CP2 | Projectivization.rep p (0 : Fin 3) ≠ 0} :=
  {p | p.1 ∈ apm_t94a08_sigma2 ∧ p.1 ≠ apm_t94a08_node}

def apm_t94a08_puncturedSigma2ZeroChartHomeomorph :
    ↑apm_t94a08_puncturedSigma2ZeroChart ≃ₜ ↑apm_t94a08_puncturedAffineCross :=
  apm_t94a08_zeroChartHomeomorph.subtype (fun p ↦ by
    rw [apm_t94a08_puncturedSigma2ZeroChart,
      apm_t94a08_puncturedAffineCross]
    have hmem := apm_t94a08_sigma2_zeroChart_mem_iff p.1 p.2
    dsimp only at hmem
    change (p.1 ∈ apm_t94a08_sigma2 ∧ p.1 ≠ apm_t94a08_node) ↔
      (apm_t94a08_zeroChartHomeomorph p ∈
          apm_t94a08_affineBranchPlus ∪ apm_t94a08_affineBranchMinus ∧
        apm_t94a08_zeroChartHomeomorph p ∉ {(0, 0)})
    rw [hmem]
    constructor <;> rintro ⟨hcross, hne⟩ <;> refine ⟨hcross, ?_⟩
    · intro himem
      have himage : apm_t94a08_zeroChartHomeomorph p = (0, 0) := by
        simpa using himem
      apply hne
      have hp : p = ⟨apm_t94a08_node, apm_t94a08_node_mem_zeroChart⟩ :=
        apm_t94a08_zeroChartHomeomorph.injective
          (himage.trans apm_t94a08_zeroChartHomeomorph_node.symm)
      exact congrArg Subtype.val hp
    · intro hpnode
      apply hne
      rw [Set.mem_singleton_iff]
      have hp : p = ⟨apm_t94a08_node, apm_t94a08_node_mem_zeroChart⟩ :=
        Subtype.ext hpnode
      rw [hp]
      exact apm_t94a08_zeroChartHomeomorph_node)

lemma apm_t94a08_puncturedSigma2ZeroChart_not_isPreconnected :
    ¬ IsPreconnected apm_t94a08_puncturedSigma2ZeroChart := by
  intro hsource
  letI : PreconnectedSpace ↑apm_t94a08_puncturedSigma2ZeroChart :=
    isPreconnected_iff_preconnectedSpace.mp hsource
  have htarget_univ : IsPreconnected
      (Set.univ : Set ↑apm_t94a08_puncturedAffineCross) := by
    simpa only [Set.image_univ,
      apm_t94a08_puncturedSigma2ZeroChartHomeomorph.surjective.range_eq] using
      apm_t94a08_puncturedSigma2ZeroChartHomeomorph.isPreconnected_image.mpr
        isPreconnected_univ
  have htarget_space : PreconnectedSpace ↑apm_t94a08_puncturedAffineCross :=
    ⟨htarget_univ⟩
  exact apm_t94a08_puncturedAffineCross_not_isPreconnected
    (isPreconnected_iff_preconnectedSpace.mpr htarget_space)
