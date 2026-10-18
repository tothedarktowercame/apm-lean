import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.T99J05ArbitraryAffineChartContinuity
import ConstructionTargets.CP2RationalHomology
import ConstructionTargets.t99J05Closure

/-! # t99J05 blueprint

The quotient descent and arbitrary-dimensional affine charts are already in the
sorry-free construction bank.  The seven admitted `t99J05_lefschetz_euler_*` leaves isolate the
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
  obtain ⟨H, hHformula, hHzero, hHone⟩ :=
    T99J05Diagonal_homotopy_descends n
  let one : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let zero : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let f : C(CP n, CP n) := H.comp
    ⟨fun p => (p, one), continuous_id.prodMk continuous_const⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v
    refine ⟨by
      rw [T99J05Diagonal_eq_consumerDiagonal]
      exact t99J05Diagonal_nonzero v, ?_⟩
    exact hHone v
  · apply ContinuousMap.Homotopic.symm
    refine ⟨{
      toContinuousMap := H.comp
        ⟨fun z : Set.Icc (0 : ℝ) 1 × CP n => (z.2, z.1),
          continuous_snd.prodMk continuous_fst⟩
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro p
      obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n p
      exact hHzero v
    · intro p
      obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n p
      simpa [f, one] using hHone v
  · intro p
    obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n p
    constructor
    · intro hfix
      have heq : quotientMap ℂ n
          ⟨T99J05Diagonal n v.1, by
            rw [T99J05Diagonal_eq_consumerDiagonal]
            exact t99J05Diagonal_nonzero v⟩ = quotientMap ℂ n v := by
        rw [← hfix]
        exact (hHone v).symm
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp heq
      obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ 0 := by
        by_contra h
        apply v.2
        funext i
        exact not_ne_iff.mp (not_exists.mp h i)
      have hweight_i : (a : ℂ) = (((i.val + 1 : ℕ) : ℂ)) := by
        have hai := congrFun ha i
        simp only [Pi.smul_apply, Units.smul_def, T99J05Diagonal] at hai
        exact (mul_right_cancel₀ hi) hai
      have hjzero (j : Fin (n + 1)) (hji : j ≠ i) : v.1 j = 0 := by
        by_contra hj
        have haj := congrFun ha j
        simp only [Pi.smul_apply, Units.smul_def, T99J05Diagonal] at haj
        have hweight_j : (a : ℂ) = (((j.val + 1 : ℕ) : ℂ)) :=
          (mul_right_cancel₀ hj) haj
        have hw : (((i.val + 1 : ℕ) : ℂ)) = (((j.val + 1 : ℕ) : ℂ)) := by
          rw [← hweight_i, ← hweight_j]
        have hij : i.val = j.val := by
          have : i.val + 1 = j.val + 1 := by exact_mod_cast hw
          omega
        exact hji (Fin.ext hij.symm)
      refine ⟨i, ?_⟩
      unfold coordinateLine
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      refine ⟨Units.mk0 (v.1 i) hi, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hjzero j hji, Pi.single_apply, hji]
    · rintro ⟨i, hi⟩
      let e : NonzeroVectors ℂ n := ⟨Pi.single i 1, by
        intro h
        have := congrFun h i
        simp at this⟩
      have he : coordinateLine ℂ n i = quotientMap ℂ n e := rfl
      rw [hi, he]
      calc
        f (quotientMap ℂ n e) = quotientMap ℂ n
            ⟨T99J05Diagonal n e.1, by
              rw [T99J05Diagonal_eq_consumerDiagonal]
              exact t99J05Diagonal_nonzero e⟩ := by
          simpa [f, one] using hHone e
        _ = quotientMap ℂ n e := by
          apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
          let w : ℂ := ((i.val + 1 : ℕ) : ℂ)
          have hw : w ≠ 0 := by
            dsimp [w]
            exact_mod_cast (Nat.succ_ne_zero i.val)
          refine ⟨Units.mk0 w hw, ?_⟩
          funext j
          by_cases hji : j = i
          · subst j
            simp [T99J05Diagonal, e, w]
          · simp [T99J05Diagonal, e, Pi.single_apply, hji]

/-- The affine-coordinate calculation, stated conditionally on the quotient
formula so that it can be proved independently of `t99J05_map_fixedPoints`. -/
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

/-- Rational homology has one generator in each even degree through `2 * n`. -/
def T99J05CPHomologyProfile (n : ℕ) (X : Type) [TopologicalSpace X] : Prop :=
  (∀ k, FiniteDimensional ℚ (Homology X k)) ∧
    ∀ k, Module.finrank ℚ (Homology X k) =
      if Even k ∧ k ≤ 2 * n then 1 else 0

/-- `CP (n+1)` minus its last coordinate point and its last affine chart. -/
def t99J05U (n : ℕ) : Set (CP (n + 1)) :=
  {x | ∃ i : Fin (n + 1), x.rep i.castSucc ≠ 0}

def t99J05V (n : ℕ) : Set (CP (n + 1)) :=
  {x | x.rep (Fin.last (n + 1)) ≠ 0}

/-- The two standard subsets are an open cover. -/
theorem t99J05_lefschetz_euler_cover (n : ℕ) :
    IsOpen (t99J05U n) ∧ IsOpen (t99J05V n) ∧
      t99J05U n ∪ t99J05V n = Set.univ := by
  have hopen (i : Fin (n + 2)) :
      IsOpen {x : CP (n + 1) | x.rep i ≠ 0} :=
    affineSource_isOpen i
  refine ⟨?_, hopen (Fin.last (n + 1)), ?_⟩
  · rw [show t99J05U n =
        ⋃ i : Fin (n + 1), {x : CP (n + 1) | x.rep i.castSucc ≠ 0} by
      ext x
      simp [t99J05U]]
    exact isOpen_iUnion fun i => hopen i.castSucc
  · ext x
    simp only [t99J05U, t99J05V, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_univ, iff_true]
    by_contra h
    push_neg at h
    apply Projectivization.rep_nonzero x
    funext i
    refine Fin.lastCases h.2 (fun j => ?_) i
    exact h.1 j

/-- The last affine chart is contractible and has the rational homology of a point. -/
theorem t99J05_lefschetz_euler_V (n : ℕ) :
    Nonempty (t99J05V n ≃ₜ ({j : Fin (n + 2) // j ≠ Fin.last (n + 1)} → ℂ)) ∧
      T99J05CPHomologyProfile 0 (t99J05V n) := by
  let i : Fin (n + 2) := Fin.last (n + 1)
  obtain ⟨e, hs, ht, _⟩ := T99J05_affineChartConstruction (n + 1) i
  have hV : t99J05V n = e.source := by
    rw [hs]
    rfl
  let h : t99J05V n ≃ₜ AffineCoordinates i :=
    (Homeomorph.setCongr hV).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  have hi : AffineCoordinates i =
      ({j : Fin (n + 2) // j ≠ Fin.last (n + 1)} → ℂ) := by
    rfl
  have h' : t99J05V n ≃ₜ
      ({j : Fin (n + 2) // j ≠ Fin.last (n + 1)} → ℂ) := by
    simpa [hi] using h
  refine ⟨⟨h'⟩, ?_⟩
  letI : ContractibleSpace (t99J05V n) := h.contractibleSpace
  constructor
  · intro k
    by_cases hk : k = 0
    · subst k
      exact (ConstructionTargets.CoefficientH0.h0Iso ℚ
        (Classical.choice inferInstance)).toLinearEquiv.symm.finiteDimensional
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
          ℚ (t99J05V n) k hk
      letI : Subsingleton (Homology (t99J05V n) k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact FiniteDimensional.of_injective
        (0 : Homology (t99J05V n) k →ₗ[ℚ] ℚ)
        (Function.injective_of_subsingleton _)
  · intro k
    by_cases hk : k = 0
    · subst k
      simpa [Even] using LinearEquiv.finrank_eq
        (ConstructionTargets.CoefficientH0.h0Iso ℚ
          (Classical.choice inferInstance)).toLinearEquiv
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
          ℚ (t99J05V n) k hk
      letI : Subsingleton (Homology (t99J05V n) k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      rw [Module.finrank_zero_of_subsingleton]
      simp [hk]

/-- LEAF U-hequiv (split 2026-10-18).  `t99J05U n` is `CP (n+1)` minus the
point `[0:…:0:1]` (some coordinate `i < n+1` is nonzero).  It deformation
retracts onto `CP n`, embedded as the hyperplane `z_{n+1} = 0`: the homotopy
`[z₀:…:zₙ:w] ↦ [z₀:…:zₙ:t·w]`, `t ∈ [0,1]`, is well defined because some
`zᵢ ≠ 0`.  Construct the homotopy equivalence (inclusion and the `t = 0` map). -/
theorem t99J05_lefschetz_euler_U_aux_hequiv (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (t99J05U n) (CP n)) := by
  have hU : t99J05U n =
      ConstructionTargets.t99J05Closure.cpSuccessorLowerPatch n := by
    ext p
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.castSucc, Fin.castSucc_ne_last i, hi⟩
    · rintro ⟨i, hi, hrep⟩
      obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hi
      exact ⟨j, hj ▸ hrep⟩
  exact ⟨(Homeomorph.setCongr hU).toHomotopyEquiv.trans
    (ConstructionTargets.t99J05Closure.t99J05_cp_successor_lowerPatch_deformationRetract n).symm⟩

theorem t99J05_lefschetz_euler_U_aux_transport (n : ℕ)
    (e : ContinuousMap.HomotopyEquiv (t99J05U n) (CP n))
    (h : T99J05CPHomologyProfile n (CP n)) :
    T99J05CPHomologyProfile n (t99J05U n) := by
  constructor
  · intro k
    letI := h.1 k
    let E := ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℚ e k
    exact FiniteDimensional.of_injective E.toLinearEquiv.toLinearMap E.toLinearEquiv.injective
  · intro k
    let E := ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℚ e k
    rw [LinearEquiv.finrank_eq E.toLinearEquiv]
    exact h.2 k

/-- Deleting the last coordinate point deformation retracts onto `CP n`. -/
theorem t99J05_lefschetz_euler_U (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (t99J05U n) (CP n)) ∧
      (T99J05CPHomologyProfile n (CP n) →
        T99J05CPHomologyProfile n (t99J05U n)) := by
  obtain ⟨e⟩ := t99J05_lefschetz_euler_U_aux_hequiv n
  exact ⟨⟨e⟩, t99J05_lefschetz_euler_U_aux_transport n e⟩

/-- The overlap is a punctured complex affine space and hence an odd sphere.
The final conjunct is the degree-zero input needed by Mayer–Vietoris. -/
private lemma t99J05_lefschetz_euler_inter_aux_ne_zero (n : ℕ)
    (p : CP (n + 1)) (hv : p ∈ t99J05V n) :
    p ∈ t99J05U n ↔ coordinates (Fin.last (n + 1)) p ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ hz
    have h := congrFun hz
      (⟨i.castSucc, by simp⟩ : {j : Fin (n + 2) // j ≠ Fin.last (n + 1)})
    change p.rep i.castSucc / p.rep (Fin.last (n + 1)) = 0 at h
    exact hi ((div_eq_zero_iff.mp h).resolve_right hv)
  · intro hz
    by_contra hu
    apply hz
    funext j
    change p.rep j.1 / p.rep (Fin.last (n + 1)) = 0
    have hj : ∃ i : Fin (n + 1), i.castSucc = j.1 := by
      exact Fin.exists_castSucc_eq.mpr j.2
    obtain ⟨i, hi⟩ := hj
    rw [← hi]
    rw [show p.rep i.castSucc = 0 by
      by_contra hi
      exact hu ⟨i, hi⟩]
    exact zero_div _

private noncomputable def t99J05_lefschetz_euler_inter_aux_homeo (n : ℕ) :
    ↑(t99J05U n ∩ t99J05V n) ≃ₜ
      {z : AffineCoordinates (Fin.last (n + 1)) // z ≠ 0} := by
  have hinv (z : AffineCoordinates (Fin.last (n + 1))) :
      (chartInverse (Fin.last (n + 1)) z).rep (Fin.last (n + 1)) ≠ 0 := by
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
    { toFun := fun p => ⟨coordinates (Fin.last (n + 1)) p.1,
        (t99J05_lefschetz_euler_inter_aux_ne_zero n p.1 p.2.2).mp p.2.1⟩
      invFun := fun z => ⟨chartInverse (Fin.last (n + 1)) z.1, by
        constructor
        · apply (t99J05_lefschetz_euler_inter_aux_ne_zero n _ (hinv z.1)).mpr
          rw [coordinates_chartInverse]
          exact z.2
        · exact hinv z.1⟩
      left_inv := fun p => by
        apply Subtype.ext
        exact chartInverse_coordinates (Fin.last (n + 1)) p.1 p.2.2
      right_inv := fun z => by
        apply Subtype.ext
        exact coordinates_chartInverse (Fin.last (n + 1)) z.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (t99J05_coordinates_continuousOn (Fin.last (n + 1))).comp_continuous
          continuous_subtype_val (fun p => p.2.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (t99J05_chartInverse_continuous (Fin.last (n + 1))).comp continuous_subtype_val }

private noncomputable def t99J05_lefschetz_euler_inter_aux_affine_euclidean (n : ℕ) :
    AffineCoordinates (Fin.last (n + 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n + 2)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [AffineCoordinates, Module.finrank_pi_fintype,
      Fintype.card_subtype_compl]
    omega)

private noncomputable def t99J05_lefschetz_euler_inter_aux_punctured_euclidean
    (n : ℕ) :
    {z : AffineCoordinates (Fin.last (n + 1)) // z ≠ 0} ≃ₜ
      {x : EuclideanSpace ℝ (Fin (2 * n + 2)) // x ≠ 0} where
  toFun z := ⟨t99J05_lefschetz_euler_inter_aux_affine_euclidean n z.1, by
    intro h
    apply z.2
    exact (t99J05_lefschetz_euler_inter_aux_affine_euclidean n).injective (by simpa using h)⟩
  invFun x := ⟨(t99J05_lefschetz_euler_inter_aux_affine_euclidean n).symm x.1, by
    intro h
    apply x.2
    exact (t99J05_lefschetz_euler_inter_aux_affine_euclidean n).symm.injective
      (by simpa using h)⟩
  left_inv z := by ext; simp
  right_inv x := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def t99J05_lefschetz_euler_inter_aux_equivSphere (n : ℕ) :
    ContinuousMap.HomotopyEquiv ↑(t99J05U n ∩ t99J05V n)
      (T02A06.euclideanUnitSphere (2 * n + 2)) :=
  (t99J05_lefschetz_euler_inter_aux_homeo n).toHomotopyEquiv |>.trans
    ((t99J05_lefschetz_euler_inter_aux_punctured_euclidean n).toHomotopyEquiv |>.trans
      (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
        (EuclideanSpace ℝ (Fin (2 * n + 2)))).symm)

private lemma t99J05_lefschetz_euler_inter_aux_sphere_H1_zero
    (m : ℕ) (hm : 2 < m) :
    CategoryTheory.Limits.IsZero (Homology (T02A06.euclideanUnitSphere m) 1) := by
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
  change CategoryTheory.Limits.IsZero (Homology (T02A06.euclideanUnitSphere (m - 1 + 1)) 1) at hz
  rwa [hd] at hz

private lemma t99J05_lefschetz_euler_inter_aux_sphere_low_zero
    (m k : ℕ) (hk : 0 < k) (hkm : k < m - 1) :
    CategoryTheory.Limits.IsZero (Homology (T02A06.euclideanUnitSphere m) k) := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              exact t99J05_lefschetz_euler_inter_aux_sphere_H1_zero (m + 1) (by omega)
          | succ k =>
              have hz := ih (k + 1) (by omega) (by omega)
              have e :
                  Homology (T02A06.euclideanUnitSphere (m + 1)) (k + 2) ≅
                    Homology (T02A06.euclideanUnitSphere m) (k + 1) := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  ConstructionTargets.CoefficientSphereShift.sphereShift ℚ m (k + 1) (by omega)
              exact hz.of_iso e

private lemma t99J05_lefschetz_euler_inter_aux_sphere_high_zero
    (m k : ℕ) (hk : m < k) :
    CategoryTheory.Limits.IsZero (Homology (T02A06.euclideanUnitSphere (m + 1)) k) := by
  induction m generalizing k with
  | zero =>
      change CategoryTheory.Limits.IsZero (ConstructionTargets.SphereZeroCoefficients.H ℚ k)
      exact ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ k (by omega)
  | succ m ih =>
      have e :
          Homology (T02A06.euclideanUnitSphere (m + 2)) k ≅
            Homology (T02A06.euclideanUnitSphere (m + 1)) (k - 1) := by
        simpa only [Nat.add_assoc, show k - 1 + 1 = k by omega] using
          ConstructionTargets.CoefficientSphereShift.sphereShift ℚ (m + 1) (k - 1) (by omega)
      exact (ih (k - 1) (by omega)).of_iso e

private lemma t99J05_lefschetz_euler_inter_aux_sphere_zero
    (n k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 1) :
    CategoryTheory.Limits.IsZero (Homology (T02A06.euclideanUnitSphere (2 * n + 2)) k) := by
  rcases lt_or_gt_of_ne hktop with h | h
  · exact t99J05_lefschetz_euler_inter_aux_sphere_low_zero
      (2 * n + 2) k (Nat.pos_of_ne_zero hk0) (by omega)
  · exact t99J05_lefschetz_euler_inter_aux_sphere_high_zero
      (2 * n + 1) k (by omega)

private lemma t99J05_lefschetz_euler_inter_aux_pathConnected (n : ℕ) :
    PathConnectedSpace ↑(t99J05U n ∩ t99J05V n) := by
  let A := AffineCoordinates (Fin.last (n + 1))
  have hA : PathConnectedSpace {z : A // z ≠ 0} := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    change IsPathConnected ({0}ᶜ : Set A)
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank']
    norm_cast
    rw [Module.finrank_pi_fintype]
    simp [A, AffineCoordinates, Fintype.card_subtype_compl]
    omega
  exact (t99J05_lefschetz_euler_inter_aux_homeo n).symm.surjective.pathConnectedSpace
    (t99J05_lefschetz_euler_inter_aux_homeo n).symm.continuous

theorem t99J05_lefschetz_euler_inter (n : ℕ) :
    (∀ k, FiniteDimensional ℚ (Homology (↑(t99J05U n ∩ t99J05V n)) k)) ∧
    (∀ k, Module.finrank ℚ (Homology (↑(t99J05U n ∩ t99J05V n)) k) =
      if k = 0 ∨ k = 2 * n + 1 then 1 else 0) ∧
    Function.Injective (RP3Homology.mvI (t99J05U n) (t99J05V n) 0).hom := by
  let e (k : ℕ) :=
    ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ
      (t99J05_lefschetz_euler_inter_aux_equivSphere n) k
  have h0 : Nonempty
      (Homology (↑(t99J05U n ∩ t99J05V n)) 0 ≅ ModuleCat.of ℚ ℚ) := by
    letI := t99J05_lefschetz_euler_inter_aux_pathConnected n
    exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℚ (Classical.choice inferInstance)⟩
  have htop : Nonempty
      (Homology (↑(t99J05U n ∩ t99J05V n)) (2 * n + 1) ≅ ModuleCat.of ℚ ℚ) :=
    ⟨e (2 * n + 1) ≪≫
      ConstructionTargets.CoefficientFirstReflection.topIso ℚ (2 * n)⟩
  have hz (k : ℕ) (hk0 : k ≠ 0) (hkt : k ≠ 2 * n + 1) :
      CategoryTheory.Limits.IsZero (Homology (↑(t99J05U n ∩ t99J05V n)) k) :=
    (t99J05_lefschetz_euler_inter_aux_sphere_zero n k hk0 hkt).of_iso (e k)
  have hfd (k : ℕ) : FiniteDimensional ℚ
      (Homology (↑(t99J05U n ∩ t99J05V n)) k) := by
    by_cases hk0 : k = 0
    · subst k
      exact (Classical.choice h0).symm.toLinearEquiv.finiteDimensional
    by_cases hkt : k = 2 * n + 1
    · subst k
      exact (Classical.choice htop).symm.toLinearEquiv.finiteDimensional
    · letI := ModuleCat.isZero_iff_subsingleton.mp (hz k hk0 hkt)
      apply FiniteDimensional.of_surjective
        (0 : ℚ →ₗ[ℚ] (Homology (↑(t99J05U n ∩ t99J05V n)) k))
      intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine ⟨hfd, ?_, ?_⟩
  · intro k
    by_cases hk0 : k = 0
    · subst k
      simpa using (Classical.choice h0).toLinearEquiv.finrank_eq
    by_cases hkt : k = 2 * n + 1
    · subst k
      simpa using (Classical.choice htop).toLinearEquiv.finrank_eq
    · letI := ModuleCat.isZero_iff_subsingleton.mp (hz k hk0 hkt)
      simp [hk0, hkt]
  · letI := t99J05_lefschetz_euler_inter_aux_pathConnected n
    intro a b hab
    have h := congrArg (fun z =>
      (CategoryTheory.Limits.biprod.fst :
        RP3Homology.HQ 0 (t99J05U n) ⊞ RP3Homology.HQ 0 (t99J05V n) ⟶
          RP3Homology.HQ 0 (t99J05U n)).hom z) hab
    simp only [RP3Homology.mvI] at h
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      CategoryTheory.Limits.biprod.lift_fst] at h
    exact RP3Homology.cp_mvI_zero_injective_aux_h0_map _ h

/-- Banked from lemma-1's round-2 partial (2026-10-18): in an exact sequence
`B → C → A` of rational vector spaces, `C` is finite-dimensional when `B` and `A` are. -/
lemma t99J05_lefschetz_euler_step_aux_finite
    {A B C : Type} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C]
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (g : B →ₗ[ℚ] C) (h : C →ₗ[ℚ] A)
    (hex : LinearMap.range g = LinearMap.ker h) :
    FiniteDimensional ℚ C := by
  let hr : C →ₗ[ℚ] LinearMap.range h := h.rangeRestrict
  obtain ⟨s, hs⟩ := hr.exists_rightInverse_of_surjective h.range_rangeRestrict
  let F : B × LinearMap.range h →ₗ[ℚ] C := g.coprod s
  apply FiniteDimensional.of_surjective F
  intro x
  let y : LinearMap.range h := ⟨h x, ⟨x, rfl⟩⟩
  have hy : h (x - s y) = 0 := by
    have hs' := LinearMap.congr_fun hs y
    have hs'' : h (s y) = y.1 := congrArg Subtype.val hs'
    simp [y, hs'']
  have hm : x - s y ∈ LinearMap.range g := by
    rw [hex]
    exact hy
  obtain ⟨b, hb⟩ := hm
  refine ⟨(b, y), ?_⟩
  change g b + s y = x
  rw [hb]
  abel

/-- LEAF step-h0 (split 2026-10-18).  `CP (n+1)` is path connected (quotient of
the nonzero vectors, `isPathConnected_compl_singleton_of_one_lt_rank`), so
`H₀ ≅ ℚ` by `CoefficientH0.h0Iso`.  Template: `RP3Homology.cp2_h0`. -/
theorem t99J05_lefschetz_euler_step_aux_h0 (n : ℕ) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) 0) ∧
      Module.finrank ℚ (Homology (CP (n + 1)) 0) = 1 := by
  letI : PathConnectedSpace (NonzeroVectors ℂ (n + 1)) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    change IsPathConnected ({0}ᶜ : Set (Fin (n + 2) → ℂ))
    apply isPathConnected_compl_singleton_of_one_lt_rank
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change 1 < (n + 2) * 2
    omega
  letI : PathConnectedSpace (CP (n + 1)) :=
    (surjective_quotientMap ℂ (n + 1)).pathConnectedSpace
      (continuous_quotientMap ℂ (n + 1))
  let e := ConstructionTargets.CoefficientH0.h0Iso ℚ
    (coordinateLine ℂ (n + 1) 0)
  constructor
  · exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective
  · simpa using e.toLinearEquiv.finrank_eq

/-- LEAF step-top (split 2026-10-18).  Degree `2n+2` of Mayer–Vietoris
(`RP3Homology.rationalMayerVietoris`): `H_{2n+2}(U) ⊕ H_{2n+2}(V) = 0` makes the
connecting map `δ (2n+1)` injective, and `H_{2n+1}(U) ⊕ H_{2n+1}(V) = 0` (odd
degree) makes it surjective onto `H_{2n+1}(U ∩ V)`, which has rank one.
Template: the `h4` step of `RP3Homology.cp2_homology_of_mv`. -/
theorem t99J05_lefschetz_euler_step_aux_top (n : ℕ)
    (hcover : IsOpen (t99J05U n) ∧ IsOpen (t99J05V n) ∧
      t99J05U n ∪ t99J05V n = Set.univ)
    (hU : T99J05CPHomologyProfile n (t99J05U n))
    (hV : T99J05CPHomologyProfile 0 (t99J05V n))
    (hinter : (∀ k, FiniteDimensional ℚ
        (Homology (↑(t99J05U n ∩ t99J05V n)) k)) ∧
      (∀ k, Module.finrank ℚ (Homology (↑(t99J05U n ∩ t99J05V n)) k) =
        if k = 0 ∨ k = 2 * n + 1 then 1 else 0) ∧
      Function.Injective (RP3Homology.mvI (t99J05U n) (t99J05V n) 0).hom) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) (2 * n + 2)) ∧
      Module.finrank ℚ (Homology (CP (n + 1)) (2 * n + 2)) = 1 := by
  sorry

/-- LEAF step-mid (split 2026-10-18).  Degrees `1 ≤ k`, `k ≠ 2n+2` of
Mayer–Vietoris.  `mvI k = 0` (for `k ≠ 2n+1` its source is zero, for `k = 2n+1`
its target `H_{2n+1}(U) ⊕ H_{2n+1}(V)` is zero), so `mvJ k` is injective;
`δ (k-1) = 0` (for `k = 1` by injectivity of `mvI 0`, otherwise its target is zero
because `k - 1 ≠ 2n+1`), so `mvJ k` is surjective.  Hence
`H_k(CP (n+1)) ≅ H_k(U) ⊕ H_k(V) ≅ H_k(U)` (`H_k(V) = 0` for `k ≥ 1`), and the
`U` profile gives the rank: for `k ≠ 2n+2`, `Even k ∧ k ≤ 2n ↔ Even k ∧ k ≤ 2(n+1)`.
Template: the `h2` step of `RP3Homology.cp2_homology_of_mv`;
`t99J05_lefschetz_euler_step_aux_finite` gives finite-dimensionality. -/
-- BEGIN SEAT AREA
theorem t99J05_lefschetz_euler_step_aux_mid (n : ℕ)
    (hcover : IsOpen (t99J05U n) ∧ IsOpen (t99J05V n) ∧
      t99J05U n ∪ t99J05V n = Set.univ)
    (hU : T99J05CPHomologyProfile n (t99J05U n))
    (hV : T99J05CPHomologyProfile 0 (t99J05V n))
    (hinter : (∀ k, FiniteDimensional ℚ
        (Homology (↑(t99J05U n ∩ t99J05V n)) k)) ∧
      (∀ k, Module.finrank ℚ (Homology (↑(t99J05U n ∩ t99J05V n)) k) =
        if k = 0 ∨ k = 2 * n + 1 then 1 else 0) ∧
      Function.Injective (RP3Homology.mvI (t99J05U n) (t99J05V n) 0).hom)
    (k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 2) :
    FiniteDimensional ℚ (Homology (CP (n + 1)) k) ∧
      Module.finrank ℚ (Homology (CP (n + 1)) k) =
        if Even k ∧ k ≤ 2 * (n + 1) then 1 else 0 := by
  obtain ⟨δ, e1, e2, e3⟩ :=
    RP3Homology.rationalMayerVietoris (t99J05U n) (t99J05V n)
      hcover.1 hcover.2.1 hcover.2.2
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hVrank : Module.finrank ℚ (Homology (↑(t99J05V n)) k) = 0 := by
    rw [hV.2]
    simp [hk0]
  have hVzero : CategoryTheory.Limits.IsZero
      (Homology (↑(t99J05V n)) k) := by
    letI := hV.1 k
    letI : Subsingleton (Homology (↑(t99J05V n)) k) :=
      Module.finrank_zero_iff.mp hVrank
    exact ModuleCat.isZero_of_subsingleton _
  have hJinj : Function.Injective
      (RP3Homology.mvJ (t99J05U n) (t99J05V n) k).hom := by
    rw [← LinearMap.ker_eq_bot, ← e1 k, LinearMap.range_eq_bot]
    by_cases hki : k = 2 * n + 1
    · have hodd : ¬ Even k := by
        rw [hki]
        rintro ⟨a, ha⟩
        omega
      have hUrank : Module.finrank ℚ
          (Homology (↑(t99J05U n)) k) = 0 := by
        rw [hU.2]
        simp [hodd]
      have hUzero : CategoryTheory.Limits.IsZero
          (Homology (↑(t99J05U n)) k) := by
        letI := hU.1 k
        letI : Subsingleton (Homology (↑(t99J05U n)) k) :=
          Module.finrank_zero_iff.mp hUrank
        exact ModuleCat.isZero_of_subsingleton _
      have hz := RP3Homology.cp2_homology_of_mv_aux_biprod_zero hUzero hVzero
      exact congrArg ModuleCat.Hom.hom (hz.eq_of_tgt _ 0)
    · have hirank : Module.finrank ℚ
          (Homology (↑(t99J05U n ∩ t99J05V n)) k) = 0 := by
        rw [hinter.2.1]
        simp [hk0, hki]
      have hizero : CategoryTheory.Limits.IsZero
          (Homology (↑(t99J05U n ∩ t99J05V n)) k) := by
        letI := hinter.1 k
        letI : Subsingleton
            (Homology (↑(t99J05U n ∩ t99J05V n)) k) :=
          Module.finrank_zero_iff.mp hirank
        exact ModuleCat.isZero_of_subsingleton _
      exact congrArg ModuleCat.Hom.hom (hizero.eq_of_src _ 0)
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hJsurj : Function.Surjective
      (RP3Homology.mvJ (t99J05U n) (t99J05V n) k).hom := by
    rw [← LinearMap.range_eq_top]
    rw [← hkpred, e2 (k - 1), LinearMap.ker_eq_top]
    by_cases hk1 : k = 1
    · subst k
      have hrange : LinearMap.range (δ 0).hom = ⊥ := by
        rw [e3 0, LinearMap.ker_eq_bot]
        exact hinter.2.2
      exact LinearMap.range_eq_bot.mp hrange
    · have hp0 : k - 1 ≠ 0 := by omega
      have hptop : k - 1 ≠ 2 * n + 1 := by omega
      have hprank : Module.finrank ℚ
          (Homology (↑(t99J05U n ∩ t99J05V n)) (k - 1)) = 0 := by
        rw [hinter.2.1]
        simp [hp0, hptop]
      have hpzero : CategoryTheory.Limits.IsZero
          (Homology (↑(t99J05U n ∩ t99J05V n)) (k - 1)) := by
        letI := hinter.1 (k - 1)
        letI : Subsingleton
            (Homology (↑(t99J05U n ∩ t99J05V n)) (k - 1)) :=
          Module.finrank_zero_iff.mp hprank
        exact ModuleCat.isZero_of_subsingleton _
      exact congrArg ModuleCat.Hom.hom (hpzero.eq_of_tgt _ 0)
  let EJ := LinearEquiv.ofBijective
    (RP3Homology.mvJ (t99J05U n) (t99J05V n) k).hom ⟨hJinj, hJsurj⟩
  let EF := LinearEquiv.ofBijective
    (CategoryTheory.Limits.biprod.fst :
      (Homology (↑(t99J05U n)) k ⊞ Homology (↑(t99J05V n)) k ⟶
        Homology (↑(t99J05U n)) k)).hom
    (RP3Homology.cp2_homology_of_mv_aux_fst_bijective hVzero)
  let E : Homology (CP (n + 1)) k ≃ₗ[ℚ]
      Homology (↑(t99J05U n)) k := EJ.symm.trans EF
  letI := hU.1 k
  have hfd : FiniteDimensional ℚ (Homology (CP (n + 1)) k) :=
    E.symm.finiteDimensional
  refine ⟨hfd, ?_⟩
  rw [E.finrank_eq, hU.2]
  congr 1
  apply propext
  constructor
  · rintro ⟨he, hle⟩
    exact ⟨he, by omega⟩
  · rintro ⟨he, hle⟩
    refine ⟨he, ?_⟩
    by_contra hnle
    have : k = 2 * n + 2 := by
      obtain ⟨a, ha⟩ := he
      omega
    exact hktop this
-- END SEAT AREA

/-- The dimension-counting step in the rational Mayer–Vietoris sequence. -/
theorem t99J05_lefschetz_euler_step (n : ℕ)
    (hCP : T99J05CPHomologyProfile n (CP n))
    (hcover : IsOpen (t99J05U n) ∧ IsOpen (t99J05V n) ∧
      t99J05U n ∪ t99J05V n = Set.univ)
    (hU : T99J05CPHomologyProfile n (t99J05U n))
    (hV : T99J05CPHomologyProfile 0 (t99J05V n))
    (hinter : (∀ k, FiniteDimensional ℚ
        (Homology (↑(t99J05U n ∩ t99J05V n)) k)) ∧
      (∀ k, Module.finrank ℚ (Homology (↑(t99J05U n ∩ t99J05V n)) k) =
        if k = 0 ∨ k = 2 * n + 1 then 1 else 0) ∧
      Function.Injective (RP3Homology.mvI (t99J05U n) (t99J05V n) 0).hom) :
    T99J05CPHomologyProfile (n + 1) (CP (n + 1)) := by
  have hk : ∀ k, FiniteDimensional ℚ (Homology (CP (n + 1)) k) ∧
      Module.finrank ℚ (Homology (CP (n + 1)) k) =
        if Even k ∧ k ≤ 2 * (n + 1) then 1 else 0 := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨hf, hr⟩ := t99J05_lefschetz_euler_step_aux_h0 n
      exact ⟨hf, by rw [hr]; simp⟩
    by_cases hktop : k = 2 * n + 2
    · subst hktop
      obtain ⟨hf, hr⟩ := t99J05_lefschetz_euler_step_aux_top n hcover hU hV hinter
      refine ⟨hf, ?_⟩
      rw [hr, if_pos]
      exact ⟨⟨n + 1, by ring⟩, by omega⟩
    exact t99J05_lefschetz_euler_step_aux_mid n hcover hU hV hinter k hk0 hktop
  exact ⟨fun k => (hk k).1, fun k => (hk k).2⟩

/-- `CP 0` is a point. -/
private lemma t99J05_lefschetz_euler_base_aux_subsingleton :
    Subsingleton (CP 0) := by
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

theorem t99J05_lefschetz_euler_base : T99J05CPHomologyProfile 0 (CP 0) := by
  let p : CP 0 := chartInverse (0 : Fin 1)
    (0 : AffineCoordinates (0 : Fin 1))
  letI : Nonempty (CP 0) := ⟨p⟩
  letI : Subsingleton (CP 0) :=
    t99J05_lefschetz_euler_base_aux_subsingleton
  constructor
  · intro k
    by_cases hk : k = 0
    · subst k
      exact (ConstructionTargets.CoefficientH0.h0Iso ℚ p).toLinearEquiv.symm.finiteDimensional
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
          ℚ (CP 0) k hk
      letI : Subsingleton (Homology (CP 0) k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact FiniteDimensional.of_injective
        (0 : Homology (CP 0) k →ₗ[ℚ] ℚ)
        (Function.injective_of_subsingleton _)
  · intro k
    by_cases hk : k = 0
    · subst k
      simpa [Even] using LinearEquiv.finrank_eq
        (ConstructionTargets.CoefficientH0.h0Iso ℚ p).toLinearEquiv
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
          ℚ (CP 0) k hk
      letI : Subsingleton (Homology (CP 0) k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      rw [Module.finrank_zero_of_subsingleton]
      simp [hk]

/-- Homotopy invariance turns the homology profile into the required trace sums. -/
private lemma t99J05_lefschetz_euler_trace_aux_sum (n : ℕ) :
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
      by_cases hke : Even k <;> simp [hke, hkbound, hkbound']
      ]
    rw [ih]
    rw [if_pos (by omega)]
    rw [Even.neg_one_pow he]
    norm_num

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

private noncomputable def t99J05_lefschetz_euler_trace_aux_sset
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

private lemma t99J05_lefschetz_euler_trace_aux_homotopy
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
      (t99J05_lefschetz_euler_trace_aux_sset h h₀ h₁).toSimplicialObjectHomotopy k

theorem t99J05_lefschetz_euler_trace (n : ℕ)
    (f : ContinuousMap (CP n) (CP n))
    (hprofile : T99J05CPHomologyProfile n (CP n))
    (hhom : ContinuousMap.Homotopic f (ContinuousMap.id (CP n))) :
    HasLefschetzNumber f ((n : ℚ) + 1) ∧
      HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  rcases hprofile with ⟨hfinite, hrank⟩
  have hid (k : ℕ) :
      (induced f k).hom = LinearMap.id := by
    have h := t99J05_lefschetz_euler_trace_aux_homotopy hhom k
    unfold induced at h
    rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id] at h
    exact congrArg ModuleCat.Hom.hom h
  have hvalue :
      (∑ k ∈ Finset.range (2 * n + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ (Homology (CP n) k)
          (induced (ContinuousMap.id (CP n)) k).hom) = (n : ℚ) + 1 := by
    rw [← t99J05_lefschetz_euler_trace_aux_sum n]
    apply Finset.sum_congr rfl
    intro k hk
    unfold induced
    rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id]
    change (-1 : ℚ) ^ k *
      (LinearMap.trace ℚ (Homology (CP n) k) LinearMap.id) = _
    rw [LinearMap.trace_id, hrank]
    norm_num
  have hvanish : ∀ k, 2 * n < k → Subsingleton (Homology (CP n) k) := by
    intro k hk
    have hz : Module.finrank ℚ (Homology (CP n) k) = 0 := by
      rw [hrank]
      simp [show ¬k ≤ 2 * n by omega]
    exact Module.finrank_zero_iff.mp hz
  constructor
  · refine ⟨hfinite, 2 * n, hvanish, ?_⟩
    rw [show (∑ k ∈ Finset.range (2 * n + 1),
        (-1 : ℚ) ^ k * LinearMap.trace ℚ (Homology (CP n) k)
          (induced f k).hom) =
      ∑ k ∈ Finset.range (2 * n + 1),
        (-1 : ℚ) ^ k * LinearMap.trace ℚ (Homology (CP n) k)
          (induced (ContinuousMap.id (CP n)) k).hom by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hid]
      have hi : (induced (ContinuousMap.id (CP n)) k).hom = LinearMap.id := by
        unfold induced
        rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id]
        rfl
      rw [hi]]
    exact hvalue
  · exact ⟨hfinite, 2 * n, hvanish, hvalue⟩

/-- Assembly of the induction and trace calculation. -/
theorem t99J05_lefschetz_euler (n : ℕ) (f : ContinuousMap (CP n) (CP n))
    (hhom : ContinuousMap.Homotopic f (ContinuousMap.id (CP n))) :
    HasLefschetzNumber f ((n : ℚ) + 1) ∧
      HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  have allProfiles : ∀ m, T99J05CPHomologyProfile m (CP m) := by
    intro m
    induction m with
    | zero => exact t99J05_lefschetz_euler_base
    | succ m ih =>
      exact t99J05_lefschetz_euler_step m ih
        (t99J05_lefschetz_euler_cover m)
        ((t99J05_lefschetz_euler_U m).2 ih)
        (t99J05_lefschetz_euler_V m).2
        (t99J05_lefschetz_euler_inter m)
  exact t99J05_lefschetz_euler_trace n f (allProfiles n) hhom

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
