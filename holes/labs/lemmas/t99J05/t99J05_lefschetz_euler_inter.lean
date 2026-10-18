import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.T99J05ArbitraryAffineChartContinuity
import ConstructionTargets.CP2RationalHomology

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
  sorry

/-- The last affine chart is contractible and has the rational homology of a point. -/
theorem t99J05_lefschetz_euler_V (n : ℕ) :
    Nonempty (t99J05V n ≃ₜ ({j : Fin (n + 2) // j ≠ Fin.last (n + 1)} → ℂ)) ∧
      T99J05CPHomologyProfile 0 (t99J05V n) := by
  sorry

/-- Deleting the last coordinate point deformation retracts onto `CP n`. -/
theorem t99J05_lefschetz_euler_U (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (t99J05U n) (CP n)) ∧
      (T99J05CPHomologyProfile n (CP n) →
        T99J05CPHomologyProfile n (t99J05U n)) := by
  sorry

/-- The overlap is a punctured complex affine space and hence an odd sphere.
The final conjunct is the degree-zero input needed by Mayer–Vietoris. -/
-- BEGIN SEAT AREA
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
  sorry

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
theorem t99J05_lefschetz_euler_trace (n : ℕ)
    (f : ContinuousMap (CP n) (CP n))
    (hprofile : T99J05CPHomologyProfile n (CP n))
    (hhom : ContinuousMap.Homotopic f (ContinuousMap.id (CP n))) :
    HasLefschetzNumber f ((n : ℚ) + 1) ∧
      HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  sorry

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
