import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.T99J05ArbitraryAffineChartContinuity

/-! # t99J05 blueprint

The quotient descent and arbitrary-dimensional affine charts are already in the
sorry-free construction bank.  The three admitted declarations isolate the
fixed-point calculation, the local calculation, and the global rational
homology/Lefschetz calculation.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
open ConstructionTargets.T99J05ArbitraryAffineChartContinuity
noncomputable section

def T99J05Diagonal (n : ℕ) (v : Vectors ℂ n) : Vectors ℂ n :=
  fun i => ((i.val + 1 : ℕ) : ℂ) * v i

lemma T99J05Diagonal_eq_consumerDiagonal (n : ℕ) (v : Vectors ℂ n) :
    T99J05Diagonal n v = t99J05Diagonal n v := by
  rfl

theorem T99J05Diagonal_homotopy_descends (n : ℕ) :
    ∃ H : C(CP n × Set.Icc (0 : ℝ) 1, CP n),
      (∀ z : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1,
        H (quotientMap ℂ n z.1, z.2) = quotientMap ℂ n
          ⟨t99J05DiagonalHomotopy n (z.1.1, z.2),
            t99J05DiagonalHomotopy_nonzero z.1 z.2⟩) ∧
      (∀ v, H (quotientMap ℂ n v, ⟨0, by norm_num⟩) = quotientMap ℂ n v) ∧
      (∀ v, H (quotientMap ℂ n v, ⟨1, by norm_num⟩) = quotientMap ℂ n
        ⟨T99J05Diagonal n v.1, by
          rw [T99J05Diagonal_eq_consumerDiagonal]
          exact t99J05Diagonal_nonzero v⟩) := by
  simpa only [T99J05Diagonal_eq_consumerDiagonal] using
    t99J05DiagonalHomotopy_descends n

theorem T99J05_affineChartConstruction (n : ℕ) :
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
    continuousOn_toFun := t99J05_coordinates_continuousOn i
    continuousOn_invFun := (t99J05_chartInverse_continuous i).continuousOn }
  refine ⟨e, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx; rfl
  · exact hlineMem
  · exact hlineCoord
  · exact hzero

/-- Construct the diagonal projective map and identify its fixed points. -/
theorem t99J05_map_fixedPoints (n : ℕ) :
    ∃ f : ContinuousMap (CP n) (CP n),
      (∀ v : NonzeroVectors ℂ n, ∃ hv : T99J05Diagonal n v.val ≠ 0,
        f (quotientMap ℂ n v) = quotientMap ℂ n ⟨T99J05Diagonal n v.val, hv⟩) ∧
      ContinuousMap.Homotopic f (ContinuousMap.id (CP n)) ∧
      (∀ p : CP n, f p = p ↔
        ∃ i : Fin (n + 1), p = coordinateLine ℂ n i) := by
  sorry

/-- The affine-coordinate calculation, stated conditionally on the quotient
formula so that it can be proved independently of `t99J05_map_fixedPoints`. -/
-- BEGIN SEAT AREA
private def t99J05_localIndices_one_aux_r {n : ℕ} (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) : ℝ :=
  ((j.1.val + 1 : ℕ) : ℝ) / ((i.val + 1 : ℕ) : ℝ)

private def t99J05_localIndices_one_aux_L {n : ℕ} (i : Fin (n + 1)) :
    AffineCoordinates i →L[ℝ] AffineCoordinates i :=
  ContinuousLinearMap.pi fun j =>
    (t99J05_localIndices_one_aux_r i j) •
      (ContinuousLinearMap.proj j : AffineCoordinates i →L[ℝ] ℂ)

private lemma t99J05_localIndices_one_aux_L_apply {n : ℕ} (i : Fin (n + 1))
    (z : AffineCoordinates i) (j) :
    t99J05_localIndices_one_aux_L i z j =
      (t99J05_localIndices_one_aux_r i j : ℂ) * z j := by
  simp only [t99J05_localIndices_one_aux_L, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply]
  rfl

private lemma t99J05_localIndices_one_aux_formula (n : ℕ)
    (f : ContinuousMap (CP n) (CP n))
    (hformula : ∀ v : NonzeroVectors ℂ n,
      ∃ hv : T99J05Diagonal n v.val ≠ 0,
        f (quotientMap ℂ n v) =
          quotientMap ℂ n ⟨T99J05Diagonal n v.val, hv⟩)
    (i : Fin (n + 1)) :
    localMap f i = t99J05_localIndices_one_aux_L i := by
  funext z
  have hinj : Function.Injective (chartInverse i) := fun x y h => by
    have hh := congrArg (coordinates i) h
    simpa using hh
  apply hinj
  change chartInverse i (coordinates i (f (chartInverse i z))) = _
  let v : NonzeroVectors ℂ n :=
    ⟨fun k => if h : k = i then 1 else z ⟨k, h⟩, by
      intro hz
      have := congrFun hz i
      simp at this⟩
  have hci : chartInverse i z = quotientMap ℂ n v := by rfl
  obtain ⟨hv, hf⟩ := hformula v
  have hout : Projectivization.rep (f (chartInverse i z)) i ≠ 0 := by
    rw [hci, hf]
    have hm : (⟨T99J05Diagonal n v.val, hv⟩ : NonzeroVectors ℂ n) ∈
        {w : NonzeroVectors ℂ n | w.1 i ≠ 0} := by
      simp [T99J05Diagonal, v]
      exact_mod_cast Nat.succ_ne_zero i.val
    have hp : (⟨T99J05Diagonal n v.val, hv⟩ : NonzeroVectors ℂ n) ∈
        quotientMap ℂ n ⁻¹' {x : CP n | Projectivization.rep x i ≠ 0} := by
      rw [affineSource_preimage i]
      exact hm
    exact hp
  rw [chartInverse_coordinates i _ hout, hci, hf]
  unfold chartInverse
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(((i.val + 1 : ℕ) : ℂ)), ?_⟩
  funext k
  by_cases hk : k = i
  · subst k
    simp [T99J05Diagonal, v]
  · simp [T99J05Diagonal, v, hk, t99J05_localIndices_one_aux_L_apply,
      t99J05_localIndices_one_aux_r, div_eq_inv_mul]
    field_simp

private lemma t99J05_localIndices_one_aux_det (n : ℕ) (i : Fin (n + 1)) :
    0 < (ContinuousLinearMap.id ℝ (AffineCoordinates i) -
      t99J05_localIndices_one_aux_L i).toLinearMap.det := by
  let a : {j : Fin (n + 1) // j ≠ i} → ℝ := fun j =>
    1 - t99J05_localIndices_one_aux_r i j
  have heq : (ContinuousLinearMap.id ℝ (AffineCoordinates i) -
      t99J05_localIndices_one_aux_L i).toLinearMap =
      LinearMap.pi (fun j => ((a j) • LinearMap.id : ℂ →ₗ[ℝ] ℂ) ∘ₗ
        (LinearMap.proj j : AffineCoordinates i →ₗ[ℝ] ℂ)) := by
    apply LinearMap.ext
    intro z
    funext j
    simp [a, t99J05_localIndices_one_aux_L_apply]
    change z j - (t99J05_localIndices_one_aux_r i j : ℂ) * z j =
      ((1 - t99J05_localIndices_one_aux_r i j : ℝ) : ℂ) * z j
    push_cast
    ring
  rw [heq, LinearMap.det_pi]
  apply Finset.prod_pos
  intro j hj
  rw [LinearMap.det_smul]
  simp only [Complex.finrank_real_complex, pow_two, LinearMap.det_id, mul_one]
  have hane : a j ≠ 0 := by
    apply sub_ne_zero.mpr
    dsimp [a, t99J05_localIndices_one_aux_r]
    intro h
    have hi : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by positivity
    have := (div_eq_one_iff_eq (ne_of_gt hi)).mp h.symm
    norm_cast at this
    exact j.2 (Fin.ext (Nat.succ.inj this))
  exact mul_self_pos.mpr hane

theorem t99J05_localIndices_one (n : ℕ) (f : ContinuousMap (CP n) (CP n))
    (hformula : ∀ v : NonzeroVectors ℂ n,
      ∃ hv : T99J05Diagonal n v.val ≠ 0,
        f (quotientMap ℂ n v) =
          quotientMap ℂ n ⟨T99J05Diagonal n v.val, hv⟩) :
    ∀ i : Fin (n + 1), ContDiffAt ℝ 1 (localMap f i) 0 ∧
      fixedPointDeterminant f i ≠ 0 ∧ localIndex f i = 1 := by
  intro i
  have hmap := t99J05_localIndices_one_aux_formula n f hformula i
  have hdet := t99J05_localIndices_one_aux_det n i
  have hfd : fderiv ℝ (localMap f i) 0 = t99J05_localIndices_one_aux_L i := by
    rw [hmap]
    exact (t99J05_localIndices_one_aux_L i).hasFDerivAt.fderiv
  have hd : 0 < fixedPointDeterminant f i := by
    simpa [fixedPointDeterminant, hfd] using hdet
  refine ⟨?_, ne_of_gt hd, ?_⟩
  · rw [hmap]
    exact (t99J05_localIndices_one_aux_L i).contDiff.contDiffAt
  · simp [localIndex, hd]
-- END SEAT AREA

/-- **LIBRARY:** rational homology of `CP n`, homotopy invariance of induced
maps, and the resulting finite alternating-trace calculation. -/
theorem t99J05_lefschetz_euler (n : ℕ) (f : ContinuousMap (CP n) (CP n))
    (hhom : ContinuousMap.Homotopic f (ContinuousMap.id (CP n))) :
    HasLefschetzNumber f ((n : ℚ) + 1) ∧
      HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  sorry

theorem apm_t99j05 :
    ∀ n : ℕ, AffineChartConstruction n ∧
      ∃ f : ContinuousMap (CP n) (CP n),
        (∀ v : NonzeroVectors ℂ n, ∃ hv : T99J05Diagonal n v.val ≠ 0,
          f (quotientMap ℂ n v) = quotientMap ℂ n ⟨T99J05Diagonal n v.val,hv⟩) ∧
        ContinuousMap.Homotopic f (ContinuousMap.id (CP n)) ∧
        (∀ p : CP n, f p = p ↔ ∃ i : Fin (n + 1), p = coordinateLine ℂ n i) ∧
        (∀ i : Fin (n + 1), ContDiffAt ℝ 1 (localMap f i) 0 ∧
          fixedPointDeterminant f i ≠ 0 ∧ localIndex f i = 1) ∧
        HasLefschetzNumber f (∑ i : Fin (n + 1), (localIndex f i : ℚ)) ∧
        HasEulerCharacteristic (CP n) (∑ i : Fin (n + 1), (localIndex f i : ℚ)) ∧
        HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  intro n
  refine ⟨T99J05_affineChartConstruction n, ?_⟩
  obtain ⟨f, hformula, hhom, hfixed⟩ := t99J05_map_fixedPoints n
  have hlocal := t99J05_localIndices_one n f hformula
  obtain ⟨hlef, heuler⟩ := t99J05_lefschetz_euler n f hhom
  have hsum : (∑ i : Fin (n + 1), (localIndex f i : ℚ)) = (n : ℚ) + 1 := by
    simp_rw [(hlocal _).2.2]
    simp
  refine ⟨f, hformula, hhom, hfixed, hlocal, ?_, ?_, heuler⟩
  · simpa [hsum] using hlef
  · simpa [hsum] using heuler

#print axioms apm_t99j05
