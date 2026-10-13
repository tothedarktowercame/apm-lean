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

/-- A local connectedness test used to separate a plane point from a node. -/
def apm_t94a08_HasConnectedPuncturedNeighborhood
    {X : Type*} [TopologicalSpace X] (S : Set X) (p : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
    IsPreconnected ((U ∩ S) \ {p})

/-- LIBRARY: a point of an open subset of the real plane has a smaller open
neighborhood whose puncture is preconnected. -/
lemma apm_t94a08_plane_punctured_neighborhood
    (W : Set (EuclideanSpace ℝ (Fin 2))) (hW : IsOpen W) {x} (hx : x ∈ W) :
    ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ IsPreconnected (V \ {x}) := by
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hx
  refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrW, ?_⟩
  let A : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    Set.Ioo 0 r ×ˢ Metric.sphere 0 1
  let f : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun q => x + q.1 • q.2
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hA : IsPreconnected A := by
    exact (ordConnected_Ioo.isPreconnected.prod
      (isPathConnected_sphere hrank 0 (r := 1) (by norm_num)).isConnected.isPreconnected)
  have hf : Continuous f := by
    exact continuous_const.add (continuous_fst.smul continuous_snd)
  have himage : f '' A = Metric.ball x r \ {x} := by
    ext y
    constructor
    · rintro ⟨q, ⟨hq, hu⟩, rfl⟩
      have hq0 : 0 < q.1 := hq.1
      have hu_norm : ‖q.2‖ = 1 := by
        simpa [Metric.mem_sphere] using hu
      constructor
      · rw [Metric.mem_ball, dist_eq_norm]
        rw [add_sub_cancel_left, norm_smul, hu_norm, mul_one]
        simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq.2
      · simp only [mem_singleton_iff]
        intro heq
        have : q.1 • q.2 = 0 := by
          simpa [f] using congrArg (fun z => z - x) heq
        exact hq0.ne' (smul_eq_zero.mp this |>.resolve_right (by
          intro hz
          simpa [hz] using hu_norm))
    · rintro ⟨hyball, hyx⟩
      let ρ : ℝ := ‖y - x‖
      let u : EuclideanSpace ℝ (Fin 2) := ρ⁻¹ • (y - x)
      have hρ : 0 < ρ := by
        rw [show ρ = dist y x by simp [ρ, dist_eq_norm]]
        exact dist_pos.mpr (by simpa [mem_singleton_iff] using hyx)
      have hρr : ρ < r := by
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hyball
        simpa [ρ, norm_sub_rev] using hyball
      have hu : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        rw [show ‖u‖ = |ρ⁻¹| * ‖y - x‖ by simp [u, norm_smul]]
        rw [abs_of_pos (inv_pos.mpr hρ)]
        exact inv_mul_cancel₀ hρ.ne'
      refine ⟨(ρ, u), ⟨⟨hρ, hρr⟩, hu⟩, ?_⟩
      simp [f, u, hρ.ne']
  rw [← himage]
  exact hA.image _ hf.continuousOn

/-- LIBRARY: transport a connected punctured neighborhood through a local
chart.  The plane-side conclusion is an explicit hypothesis so this lemma is
independent of `apm_t94a08_plane_punctured_neighborhood`. -/
lemma apm_t94a08_chart_transport_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] {S U : Set X} {p : X}
    {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hpU : p ∈ U) (hpS : p ∈ S)
    (e : ↥(U ∩ S) ≃ₜ ↥W)
    (hplane : ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ (e ⟨p, hpU, hpS⟩ : EuclideanSpace ℝ (Fin 2)) ∈ V ∧
      V ⊆ W ∧ IsPreconnected (V \ {(e ⟨p, hpU, hpS⟩ :
        EuclideanSpace ℝ (Fin 2))})) :
    apm_t94a08_HasConnectedPuncturedNeighborhood S p := by
  obtain ⟨V, hVopen, hxV, hVW, hVconn⟩ := hplane
  let q : ↑(U ∩ S) := ⟨p, hpU, hpS⟩
  let A : Set (↑(U ∩ S)) :=
    e ⁻¹' ((↑) ⁻¹' V)
  have hAopen : IsOpen A := by
    exact (hVopen.preimage continuous_subtype_val).preimage e.continuous
  obtain ⟨O, hOopen, hOA⟩ := isOpen_induced_iff.mp hAopen
  refine ⟨O ∩ U, hOopen.inter hU, ?_, ?_⟩
  · constructor
    · have hqA : q ∈ A := by
        exact hxV
      have : p ∈ O := by
        have := congrArg (fun T : Set (↑(U ∩ S)) => q ∈ T) hOA
        exact this.mpr hqA
      exact this
    · exact hpU
  · let D : Set (↑V) := {y | (y : EuclideanSpace ℝ (Fin 2)) ≠ e q}
    let f : ↑V → X := fun y =>
      (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ : ↑(U ∩ S))
    have hDconn : IsPreconnected D := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have hval : Subtype.val '' D =
          V \ {(e q : EuclideanSpace ℝ (Fin 2))} := by
        ext y
        simp [D, and_comm]
      rw [hval]
      exact hVconn
    have hfcont : Continuous f := by
      exact continuous_subtype_val.comp
        (e.symm.continuous.comp
          (Continuous.subtype_mk continuous_subtype_val (fun y => hVW y.2)))
    have himage : f '' D = (((O ∩ U) ∩ S) \ {p}) := by
      ext z
      constructor
      · rintro ⟨y, hyD, rfl⟩
        have hyA : e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ ∈ A := by
          simp [A]
        have hyO : (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ :
            ↑(U ∩ S)).1 ∈ O := by
          have h := congrArg
            (fun T : Set (↑(U ∩ S)) =>
              e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ ∈ T) hOA
          exact h.mpr hyA
        refine ⟨⟨⟨hyO, (e.symm ⟨y, hVW y.2⟩).2.1⟩,
          (e.symm ⟨y, hVW y.2⟩).2.2⟩, ?_⟩
        intro hz
        have hzq : e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ = q := by
          apply Subtype.ext
          exact hz
        apply hyD
        change (y : EuclideanSpace ℝ (Fin 2)) = e q
        simpa using congrArg (fun r : ↑(U ∩ S) =>
          (e r : EuclideanSpace ℝ (Fin 2))) hzq
      · rintro ⟨⟨⟨hzO, hzU⟩, hzS⟩, hzp⟩
        let r : ↑(U ∩ S) := ⟨z, hzU, hzS⟩
        have hrA : r ∈ A := by
          have h := congrArg (fun T : Set (↑(U ∩ S)) => r ∈ T) hOA
          exact h.mp hzO
        have herV : (e r : EuclideanSpace ℝ (Fin 2)) ∈ V := hrA
        let y : ↑V := ⟨(e r : EuclideanSpace ℝ (Fin 2)), herV⟩
        refine ⟨y, ?_, ?_⟩
        · change (y : EuclideanSpace ℝ (Fin 2)) ≠ e q
          intro heq
          apply hzp
          have : r = q := e.injective (Subtype.ext heq)
          exact congrArg Subtype.val this
        · change (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ :
            ↑(U ∩ S)).1 = z
          simp [y, r]
    rw [← himage]
    exact hDconn.image f hfcont.continuousOn

/-- The affine nodal model: two complex coordinate axes crossing at zero. -/
def apm_t94a08_complexCross : Set (ℂ × ℂ) :=
  {z | z.1 = 0 ∨ z.2 = 0}

/-- LIBRARY: every ambient-open neighborhood of the origin in the complex
cross becomes disconnected after deleting the origin. -/
lemma apm_t94a08_complexCross_punctured_not_preconnected
    (V : Set (ℂ × ℂ)) (hV : IsOpen V) (h0 : (0, 0) ∈ V) :
    ¬ IsPreconnected ((V ∩ apm_t94a08_complexCross) \ {(0, 0)}) := by
  intro hpre
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (0, 0) h0
  let a : ℂ := (r / 2 : ℝ)
  have ha : a ≠ 0 := by
    simp [a, ne_of_gt hr]
  have haV : (a, 0) ∈ V := by
    apply hrV
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [a, abs_of_pos hr, hr]
  have hbV : (0, a) ∈ V := by
    apply hrV
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [a, abs_of_pos hr, hr]
  let A : Set (ℂ × ℂ) := Prod.fst ⁻¹' ({0} : Set ℂ)ᶜ
  let B : Set (ℂ × ℂ) := Prod.snd ⁻¹' ({0} : Set ℂ)ᶜ
  have hA : IsOpen A := by
    exact isClosed_singleton.isOpen_compl.preimage continuous_fst
  have hB : IsOpen B := by
    exact isClosed_singleton.isOpen_compl.preimage continuous_snd
  have hcover : ((V ∩ apm_t94a08_complexCross) \ {(0, 0)}) ⊆ A ∪ B := by
    rintro z ⟨⟨hzV, hz⟩, hz0⟩
    change z.1 = 0 ∨ z.2 = 0 at hz
    change z ∈ A ∨ z ∈ B
    rcases hz with hfst | hsnd
    · right
      change z.2 ≠ 0
      intro h
      apply hz0
      simp only [mem_singleton_iff]
      apply Prod.ext <;> assumption
    · left
      change z.1 ≠ 0
      intro h
      apply hz0
      simp only [mem_singleton_iff]
      apply Prod.ext <;> assumption
  have hdisj :
      ((V ∩ apm_t94a08_complexCross) \ {(0, 0)}) ∩ (A ∩ B) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, ⟨⟨⟨_, hcross⟩, _⟩, hzA, hzB⟩⟩
    change z.1 ≠ 0 at hzA
    change z.2 ≠ 0 at hzB
    change z.1 = 0 ∨ z.2 = 0 at hcross
    exact hcross.elim hzA hzB
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre A B hA hB hcover hdisj) with
    hsub | hsub
  · have hmem : (0, a) ∈ ((V ∩ apm_t94a08_complexCross) \ {(0, 0)}) := by
      refine ⟨⟨hbV, ?_⟩, ?_⟩
      · exact Or.inl rfl
      · simpa [Prod.ext_iff] using ha
    exact (hsub hmem) rfl
  · have hmem : (a, 0) ∈ ((V ∩ apm_t94a08_complexCross) \ {(0, 0)}) := by
      refine ⟨⟨haV, ?_⟩, ?_⟩
      · exact Or.inr rfl
      · simpa [Prod.ext_iff] using ha
    exact (hsub hmem) rfl

/-- Seat (claude-14 split): both branches are closed in `CP²` (zero sets of a
linear form in homogeneous coordinates; closed in the quotient topology because
their preimage in `C³ ∖ 0` is closed). -/
lemma apm_t94a08_branches_closed :
    IsClosed apm_t94a08_sigma2BranchPlus ∧ IsClosed apm_t94a08_sigma2BranchMinus := by
  sorry

/-- Seat: the branches meet only at the node (`y + i z = 0 = y - i z` forces
`y = z = 0`, so the point is `[1 : 0 : 0]`). -/
lemma apm_t94a08_branches_inter :
    apm_t94a08_sigma2BranchPlus ∩ apm_t94a08_sigma2BranchMinus ⊆
      {apm_t94a08_node} := by
  intro p hp
  rcases hp with ⟨hplus, hminus⟩
  change p.rep 1 + Complex.I * p.rep 2 = 0 at hplus
  change p.rep 1 - Complex.I * p.rep 2 = 0 at hminus
  have h1 : p.rep 1 = 0 := by
    linear_combination (hplus + hminus) / 2
  have h2 : p.rep 2 = 0 := by
    have hI : Complex.I * p.rep 2 = 0 := by
      linear_combination (hplus - hminus) / 2
    exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
  rw [mem_singleton_iff, ← Projectivization.mk_rep p]
  unfold apm_t94a08_node
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _
    (Projectivization.rep_nonzero p) apm_t94a08_e0_ne_zero).2
  refine ⟨p.rep 0, ?_⟩
  funext i
  fin_cases i <;> simp [h1, h2]

/-- Seat: every open neighbourhood of the node contains other points of each
branch: `[1 : t : ∓ i t] → [1 : 0 : 0]` as `t → 0`, and these differ from the
node for `t ≠ 0`. -/
lemma apm_t94a08_branches_accumulate (U : Set apm_t94a08_CP2) (hU : IsOpen U)
    (hnode : apm_t94a08_node ∈ U) :
    ((U ∩ apm_t94a08_sigma2BranchPlus) \ {apm_t94a08_node}).Nonempty ∧
      ((U ∩ apm_t94a08_sigma2BranchMinus) \ {apm_t94a08_node}).Nonempty := by
  sorry

/-- Seat (general topology): if `A, B` are closed, meet at most in `p`, and an
open-set slice meets both away from `p`, then the punctured slice of `A ∪ B` is
not preconnected (`isPreconnected_iff_subset_of_disjoint_closed`). -/
lemma apm_t94a08_union_closed_punctured_not_preconnected {X : Type*}
    [TopologicalSpace X] {A B U : Set X} {p : X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∩ B ⊆ {p})
    (hUA : ((U ∩ A) \ {p}).Nonempty) (hUB : ((U ∩ B) \ {p}).Nonempty) :
    ¬ IsPreconnected ((U ∩ (A ∪ B)) \ {p}) := by
  sorry

/-- The node has no connected punctured neighbourhood in the nodal conic
(claude-14 restatement: global two-branch argument; `hcross` is no longer used). -/
lemma apm_t94a08_node_has_no_connected_punctured_neighborhood
    (hcross : ∀ V : Set (ℂ × ℂ), IsOpen V → (0, 0) ∈ V →
      ¬ IsPreconnected ((V ∩ apm_t94a08_complexCross) \ {(0, 0)})) :
    ¬ apm_t94a08_HasConnectedPuncturedNeighborhood
      apm_t94a08_sigma2 apm_t94a08_node := by
  rintro ⟨U, hU, hnode, hpre⟩
  rw [apm_t94a08_sigma2_eq_branches] at hpre
  have hacc := apm_t94a08_branches_accumulate U hU hnode
  exact apm_t94a08_union_closed_punctured_not_preconnected
    apm_t94a08_branches_closed.1 apm_t94a08_branches_closed.2
    apm_t94a08_branches_inter hacc.1 hacc.2 hpre

/-- The union of the two distinct complex projective lines is not locally
Euclidean at their common node. -/
theorem apm_t94a08_nodal_not_manifold_at :
    ¬apm_t94a08_IsRealTwoManifoldAt apm_t94a08_sigma2 apm_t94a08_node := by
  intro hman
  obtain ⟨U, hU, hpU, W, hW, ⟨e⟩⟩ := hman
  have hpS : apm_t94a08_node ∈ apm_t94a08_sigma2 :=
    apm_t94a08_node_mem_sigma2
  have hplane := apm_t94a08_plane_punctured_neighborhood W hW
    (show (e ⟨apm_t94a08_node, hpU, hpS⟩ :
      EuclideanSpace ℝ (Fin 2)) ∈ W from (e ⟨apm_t94a08_node, hpU, hpS⟩).2)
  have hconnected := apm_t94a08_chart_transport_punctured_neighborhood
    hU hpU hpS e hplane
  exact apm_t94a08_node_has_no_connected_punctured_neighborhood
    apm_t94a08_complexCross_punctured_not_preconnected hconnected

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
