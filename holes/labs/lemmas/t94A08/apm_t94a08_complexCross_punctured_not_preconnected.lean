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
  sorry

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
  sorry

/-- The affine nodal model: two complex coordinate axes crossing at zero. -/
def apm_t94a08_complexCross : Set (ℂ × ℂ) :=
  {z | z.1 = 0 ∨ z.2 = 0}

/-- LIBRARY: every ambient-open neighborhood of the origin in the complex
cross becomes disconnected after deleting the origin. -/
-- BEGIN SEAT AREA
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
-- END SEAT AREA

/-- LIBRARY: the projective affine chart at the node transports the complex
cross obstruction to `sigma2`.  The obstruction is supplied explicitly so
this proof is independent of the preceding lemma. -/
lemma apm_t94a08_node_has_no_connected_punctured_neighborhood
    (hcross : ∀ V : Set (ℂ × ℂ), IsOpen V → (0, 0) ∈ V →
      ¬ IsPreconnected ((V ∩ apm_t94a08_complexCross) \ {(0, 0)})) :
    ¬ apm_t94a08_HasConnectedPuncturedNeighborhood
      apm_t94a08_sigma2 apm_t94a08_node := by
  sorry

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
