import ConstructionTargets.T02A06HemisphereCoordinates
import Mathlib.Topology.Maps.Basic

/-!
# Open cover of two Euclidean spheres glued along their equators

This target constructs the geometric open cover before any singular-homology
or Mayer--Vietoris argument.  It is dimension-generic and uses the final
Euclidean coordinate as height.
-/

open Set Topology
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.SphereEquatorGluingOpenCover

open T02A06

/-- The standard Euclidean sphere with final-coordinate height. -/
abbrev AmbientSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Final-coordinate height on the standard sphere. -/
def sphereHeight (n : ℕ) (x : AmbientSphere n) : ℝ :=
  x.1 (Fin.last n)

theorem continuous_sphereHeight (n : ℕ) : Continuous (sphereHeight n) := by
  exact (PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val

/-- The fixed open equatorial band `|height| < 1/2`. -/
def equatorialBand (n : ℕ) : Set (AmbientSphere n) :=
  {x | |sphereHeight n x| < (1 / 2 : ℝ)}

theorem equatorialBand_isOpen (n : ℕ) : IsOpen (equatorialBand n) := by
  exact (continuous_abs.comp (continuous_sphereHeight n)).isOpen_preimage _ isOpen_Iio

/-- Include the coordinate equator into the ambient sphere. -/
def equatorInclusion (n : ℕ) (x : sphereEquator n) : AmbientSphere n :=
  ⟨x.1, x.property.1⟩

theorem equatorInclusion_mem_band (n : ℕ) (x : sphereEquator n) :
    equatorInclusion n x ∈ equatorialBand n := by
  simp [equatorInclusion, equatorialBand, sphereHeight, x.property.2]

/-! ## Normalized contraction of the equatorial band -/

/-- Before renormalization, multiply the height by `1-s` while leaving all
horizontal coordinates fixed. -/
def flattenRaw (n : ℕ) (s : unitInterval) (x : AmbientSphere n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  euclideanSnoc (euclideanInit x.1)
    ((1 - (s : ℝ)) * sphereHeight n x)

theorem flattenRaw_norm_sq (n : ℕ) (s : unitInterval) (x : AmbientSphere n) :
    ‖flattenRaw n s x‖ ^ 2 =
      1 - (sphereHeight n x) ^ 2 +
        ((1 - (s : ℝ)) * sphereHeight n x) ^ 2 := by
  rw [flattenRaw, euclideanSnoc_norm_sq]
  have hsphere : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hsplit := euclideanInit_norm_sq_add_last x.1
  rw [hsphere] at hsplit
  change ‖euclideanInit x.1‖ ^ 2 + sphereHeight n x ^ 2 = 1 ^ 2 at hsplit
  nlinarith

theorem flattenRaw_ne_zero (n : ℕ) (s : unitInterval) (x : AmbientSphere n)
    (hx : x ∈ equatorialBand n) : flattenRaw n s x ≠ 0 := by
  change |sphereHeight n x| < (1 / 2 : ℝ) at hx
  have ht := (abs_lt.mp hx).2
  have htneg := (abs_lt.mp hx).1
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hnorm := flattenRaw_norm_sq n s x
  intro hzero
  have hz : ‖flattenRaw n s x‖ ^ 2 = 0 := by rw [hzero, norm_zero]; norm_num
  rw [hz] at hnorm
  have ha : 0 ≤ ((1 - (s : ℝ)) * sphereHeight n x) ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (sphereHeight n x)]

/-- Normalize the flattened vector back onto the unit sphere. -/
def flattenSphere (n : ℕ) (s : unitInterval) (x : AmbientSphere n)
    (hx : x ∈ equatorialBand n) : AmbientSphere n :=
  ⟨NormedSpace.normalize (flattenRaw n s x), by
    simpa [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (flattenRaw_ne_zero n s x hx)⟩

theorem flattenRaw_last (n : ℕ) (s : unitInterval) (x : AmbientSphere n) :
    flattenRaw n s x (Fin.last n) =
      (1 - (s : ℝ)) * sphereHeight n x := by
  simp [flattenRaw]

theorem flattenSphere_height (n : ℕ) (s : unitInterval) (x : AmbientSphere n)
    (hx : x ∈ equatorialBand n) :
    sphereHeight n (flattenSphere n s x hx) =
      ‖flattenRaw n s x‖⁻¹ * ((1 - (s : ℝ)) * sphereHeight n x) := by
  simp [sphereHeight, flattenSphere, NormedSpace.normalize, flattenRaw_last]

theorem flattenSphere_mem_band (n : ℕ) (s : unitInterval) (x : AmbientSphere n)
    (hx : x ∈ equatorialBand n) :
    flattenSphere n s x hx ∈ equatorialBand n := by
  change |sphereHeight n (flattenSphere n s x hx)| < (1 / 2 : ℝ)
  rw [flattenSphere_height]
  let t : ℝ := sphereHeight n x
  let a : ℝ := 1 - (s : ℝ)
  let R : ℝ := ‖flattenRaw n s x‖
  have hRpos : 0 < R := norm_pos_iff.mpr (flattenRaw_ne_zero n s x hx)
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [s.2.2]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [s.2.1]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have htAbs : |t| < (1 / 2 : ℝ) := by exact hx
  have ht2 : 4 * t ^ 2 < 1 := by
    rcases abs_lt.mp htAbs with ⟨htl, htu⟩
    nlinarith [sq_nonneg t]
  have hat_le : (a * t) ^ 2 ≤ t ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg t)]
  have hR2 : R ^ 2 = 1 - t ^ 2 + (a * t) ^ 2 := by
    exact flattenRaw_norm_sq n s x
  have hsq : 4 * (a * t) ^ 2 < R ^ 2 := by nlinarith
  have habs : |a * t| < (1 / 2 : ℝ) * R := by
    rw [← sq_lt_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hRpos.le)]
    rw [sq_abs]
    nlinarith [sq_nonneg R]
  change |R⁻¹ * (a * t)| < (1 / 2 : ℝ)
  rw [abs_mul, abs_inv, abs_of_pos hRpos]
  rw [inv_mul_eq_div]
  exact (div_lt_iff₀ hRpos).2 (by simpa [mul_comm] using habs)

/-- The normalized flattening as a self-map of the equatorial band. -/
def bandFlatten (n : ℕ) (s : unitInterval) :
    equatorialBand n → equatorialBand n :=
  fun x => ⟨flattenSphere n s x.1 x.2, flattenSphere_mem_band n s x.1 x.2⟩

theorem flattenRaw_zero (n : ℕ) (x : AmbientSphere n) :
    flattenRaw n (0 : unitInterval) x = x.1 := by
  simp [flattenRaw, sphereHeight]

theorem bandFlatten_zero (n : ℕ) (x : equatorialBand n) :
    bandFlatten n (0 : unitInterval) x = x := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (flattenRaw n (0 : unitInterval) x.1) = x.1.1
  rw [flattenRaw_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (by
    simpa [Metric.mem_sphere, dist_zero_right] using x.1.2)

theorem flattenSphere_one_height (n : ℕ) (x : AmbientSphere n)
    (hx : x ∈ equatorialBand n) :
    sphereHeight n (flattenSphere n (1 : unitInterval) x hx) = 0 := by
  rw [flattenSphere_height]
  norm_num

/-- The terminal point of the contraction, as a literal equator point. -/
def bandProjectionToEquator (n : ℕ) (x : equatorialBand n) : sphereEquator n :=
  ⟨(flattenSphere n (1 : unitInterval) x.1 x.2).1,
    (flattenSphere n (1 : unitInterval) x.1 x.2).2,
    flattenSphere_one_height n x.1 x.2⟩

theorem flattenRaw_equator (n : ℕ) (s : unitInterval) (x : sphereEquator n) :
    flattenRaw n s (equatorInclusion n x) = x.1 := by
  simp only [flattenRaw, sphereHeight, equatorInclusion, x.property.2,
    mul_zero]
  simpa [x.property.2] using euclideanSnoc_init_last x.1

theorem bandFlatten_fixes_equator (n : ℕ) (s : unitInterval)
    (x : sphereEquator n) :
    (bandFlatten n s
      ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩).1 =
        equatorInclusion n x := by
  apply Subtype.ext
  change NormedSpace.normalize
      (flattenRaw n s (equatorInclusion n x)) = x.1
  rw [flattenRaw_equator]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property.1)

theorem continuous_bandFlatten_uncurried (n : ℕ) :
    Continuous (fun p : unitInterval × equatorialBand n =>
      bandFlatten n p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  let raw := fun p : unitInterval × equatorialBand n =>
    flattenRaw n p.1 p.2.1
  have hinit : Continuous (fun p : unitInterval × equatorialBand n =>
      euclideanInit p.2.1.1) :=
    continuous_euclideanInit.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hheight : Continuous (fun p : unitInterval × equatorialBand n =>
      sphereHeight n p.2.1) :=
    (continuous_sphereHeight n).comp (continuous_subtype_val.comp continuous_snd)
  have hs : Continuous (fun p : unitInterval × equatorialBand n => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hraw : Continuous raw := by
    exact continuous_euclideanSnoc.comp
      (hinit.prodMk ((continuous_const.sub hs).mul hheight))
  change Continuous (fun p : unitInterval × equatorialBand n =>
    NormedSpace.normalize (raw p))
  unfold NormedSpace.normalize
  rw [continuous_iff_continuousAt]
  intro p
  exact (((continuous_norm.comp hraw).continuousAt.inv₀
      (norm_ne_zero_iff.mpr (flattenRaw_ne_zero n p.1 p.2.1 p.2.2))).smul
        hraw.continuousAt)

theorem continuous_bandFlatten_one (n : ℕ) :
    Continuous (bandFlatten n (1 : unitInterval)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  let raw := fun x : equatorialBand n => flattenRaw n (1 : unitInterval) x.1
  have hraw : Continuous raw := by
    have hinit : Continuous (fun x : equatorialBand n => euclideanInit x.1.1) :=
      continuous_euclideanInit.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    have hheight : Continuous (fun x : equatorialBand n => sphereHeight n x.1) :=
      (continuous_sphereHeight n).comp continuous_subtype_val
    exact continuous_euclideanSnoc.comp
      (hinit.prodMk ((continuous_const.sub continuous_const).mul hheight))
  change Continuous (fun x : equatorialBand n => NormedSpace.normalize (raw x))
  unfold NormedSpace.normalize
  rw [continuous_iff_continuousAt]
  intro x
  exact (((continuous_norm.comp hraw).continuousAt.inv₀
      (norm_ne_zero_iff.mpr
        (flattenRaw_ne_zero n (1 : unitInterval) x.1 x.2))).smul hraw.continuousAt)

/-- The terminal projection, regarded as a continuous self-map of the band. -/
def bandProjectionMap (n : ℕ) : C(equatorialBand n, equatorialBand n) :=
  ⟨bandFlatten n (1 : unitInterval), continuous_bandFlatten_one n⟩

/-- The normalized height flattening is a strong deformation of the open
equatorial band onto its equator image. -/
def equatorialBandHomotopy (n : ℕ) : ContinuousMap.Homotopy
    (ContinuousMap.id (equatorialBand n)) (bandProjectionMap n) where
  toFun p := bandFlatten n p.1 p.2
  continuous_toFun := continuous_bandFlatten_uncurried n
  map_zero_left x := bandFlatten_zero n x
  map_one_left x := by
    exact rfl

/-- Continuous inclusion of the equator into its open band. -/
def equatorToBandMap (n : ℕ) : C(sphereEquator n, equatorialBand n) where
  toFun x := ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

theorem continuous_bandProjectionToEquator (n : ℕ) :
    Continuous (bandProjectionToEquator n) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (continuous_bandFlatten_one n))

/-- Continuous terminal projection from the band to the equator. -/
def bandToEquatorMap (n : ℕ) : C(equatorialBand n, sphereEquator n) :=
  ⟨bandProjectionToEquator n, continuous_bandProjectionToEquator n⟩

theorem equatorToBand_comp_bandToEquator (n : ℕ) :
    (equatorToBandMap n).comp (bandToEquatorMap n) = bandProjectionMap n := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem bandToEquator_comp_equatorToBand (n : ℕ) :
    (bandToEquatorMap n).comp (equatorToBandMap n) =
      ContinuousMap.id (sphereEquator n) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (flattenSphere n (1 : unitInterval)
    (equatorInclusion n x) (equatorInclusion_mem_band n x)).1 = x.1
  have hfix := bandFlatten_fixes_equator n (1 : unitInterval) x
  exact congrArg Subtype.val hfix

/-- The open equatorial band is homotopy equivalent to its literal equator.
The left inverse is supplied by the normalized strong deformation above; the
right inverse is an equality. -/
def equatorialBandHomotopyEquiv (n : ℕ) :
    equatorialBand n ≃ₕ sphereEquator n where
  toFun := bandToEquatorMap n
  invFun := equatorToBandMap n
  left_inv := by
    rw [equatorToBand_comp_bandToEquator]
    exact ⟨(equatorialBandHomotopy n).symm⟩
  right_inv := by
    rw [bandToEquator_comp_equatorToBand]

/-- The generating relation which glues the two equator copies by `h`. -/
inductive EquatorGlueRel (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Sum (AmbientSphere n) (AmbientSphere n) →
      Sum (AmbientSphere n) (AmbientSphere n) → Prop
  | glue (x : sphereEquator n) :
      EquatorGlueRel n h (Sum.inl (equatorInclusion n x))
        (Sum.inr (equatorInclusion n (h x)))

/-- The generated-relation quotient gluing two spheres along the equator. -/
abbrev EquatorGluing (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :=
  Quotient (Relation.EqvGen.setoid (EquatorGlueRel n h))

noncomputable instance (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    TopologicalSpace (EquatorGluing n h) :=
  TopologicalSpace.coinduced
    (fun x : Sum (AmbientSphere n) (AmbientSphere n) ↦ Quotient.mk _ x)
    inferInstance

/-- The canonical quotient map. -/
def quotientMap (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    Sum (AmbientSphere n) (AmbientSphere n) → EquatorGluing n h :=
  fun x ↦ Quotient.mk _ x

theorem quotientMap_surjective (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Function.Surjective (quotientMap n h) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

theorem quotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (quotientMap n h) := by
  exact ⟨quotientMap_surjective n h, rfl⟩

/-- On the sum before quotienting, the left cover member consists of the
whole left sphere and an equatorial band in the right sphere. -/
def leftPreimage (n : ℕ) : Set (Sum (AmbientSphere n) (AmbientSphere n))
  | .inl _ => True
  | .inr y => y ∈ equatorialBand n

/-- The symmetric right cover member before quotienting. -/
def rightPreimage (n : ℕ) : Set (Sum (AmbientSphere n) (AmbientSphere n))
  | .inl x => x ∈ equatorialBand n
  | .inr _ => True

theorem leftPreimage_isOpen (n : ℕ) : IsOpen (leftPreimage n) := by
  rw [isOpen_sum_iff]
  constructor
  · change IsOpen (Set.univ : Set (AmbientSphere n))
    exact isOpen_univ
  · change IsOpen (equatorialBand n)
    exact equatorialBand_isOpen n

theorem rightPreimage_isOpen (n : ℕ) : IsOpen (rightPreimage n) := by
  rw [isOpen_sum_iff]
  constructor
  · change IsOpen (equatorialBand n)
    exact equatorialBand_isOpen n
  · change IsOpen (Set.univ : Set (AmbientSphere n))
    exact isOpen_univ

theorem leftPreimage_respects (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) {x y}
    (hxy : Relation.EqvGen (EquatorGlueRel n h) x y) :
    x ∈ leftPreimage n ↔ y ∈ leftPreimage n := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | glue z =>
          change True ↔ equatorInclusion n (h z) ∈ equatorialBand n
          exact (iff_true_intro (equatorInclusion_mem_band n (h z))).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem rightPreimage_respects (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) {x y}
    (hxy : Relation.EqvGen (EquatorGlueRel n h) x y) :
    x ∈ rightPreimage n ↔ y ∈ rightPreimage n := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | glue z =>
          change equatorInclusion n z ∈ equatorialBand n ↔ True
          exact iff_true_intro (equatorInclusion_mem_band n z)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- At every homotopy time, the normalized band contraction respects the
arbitrary equator gluing homeomorphism.  This is the exact compatibility
needed before descending a product homotopy through the quotient. -/
theorem bandFlatten_glue_compatible (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    (x : sphereEquator n) :
    quotientMap n h
        (Sum.inl (bandFlatten n s
          ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩).1) =
      quotientMap n h
        (Sum.inr (bandFlatten n s
          ⟨equatorInclusion n (h x), equatorInclusion_mem_band n (h x)⟩).1) := by
  calc
    quotientMap n h
        (Sum.inl (bandFlatten n s
          ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩).1) =
        quotientMap n h (Sum.inl (equatorInclusion n x)) := by
          rw [bandFlatten_fixes_equator]
    _ = quotientMap n h (Sum.inr (equatorInclusion n (h x))) := by
      exact Quotient.sound (Relation.EqvGen.rel _ _ (EquatorGlueRel.glue x))
    _ = quotientMap n h
        (Sum.inr (bandFlatten n s
          ⟨equatorInclusion n (h x), equatorInclusion_mem_band n (h x)⟩).1) := by
          rw [bandFlatten_fixes_equator]

/-- The left open member descended to the quotient. -/
def leftOpen (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    Set (EquatorGluing n h) :=
  quotientMap n h '' leftPreimage n

/-- The right open member descended to the quotient. -/
def rightOpen (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    Set (EquatorGluing n h) :=
  quotientMap n h '' rightPreimage n

theorem quotientMap_preimage_leftOpen (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    quotientMap n h ⁻¹' leftOpen n h = leftPreimage n := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    change Quotient.mk _ y = Quotient.mk _ x at heq
    exact (leftPreimage_respects n h (Quotient.exact heq)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem quotientMap_preimage_rightOpen (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    quotientMap n h ⁻¹' rightOpen n h = rightPreimage n := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    change Quotient.mk _ y = Quotient.mk _ x at heq
    exact (rightPreimage_respects n h (Quotient.exact heq)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem leftOpen_isOpen (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsOpen (leftOpen n h) := by
  rw [← (quotientMap_isQuotientMap n h).isOpen_preimage,
    quotientMap_preimage_leftOpen]
  exact leftPreimage_isOpen n

theorem rightOpen_isOpen (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsOpen (rightOpen n h) := by
  rw [← (quotientMap_isQuotientMap n h).isOpen_preimage,
    quotientMap_preimage_rightOpen]
  exact rightPreimage_isOpen n

/-- The descended two-member open cover, indexed by `Bool`. -/
def gluingOpenCover (n : ℕ) (h : sphereEquator n ≃ₜ sphereEquator n) :
    Bool → Set (EquatorGluing n h)
  | true => leftOpen n h
  | false => rightOpen n h

theorem gluingOpenCover_isOpen (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (b : Bool) :
    IsOpen (gluingOpenCover n h b) := by
  cases b
  · exact rightOpen_isOpen n h
  · exact leftOpen_isOpen n h

theorem leftOpen_union_rightOpen (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftOpen n h ∪ rightOpen n h = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x⟩
  cases x with
  | inl x =>
      show _ ∈ leftOpen n h ∨ _ ∈ rightOpen n h
      exact Or.inl ⟨Sum.inl x, trivial, rfl⟩
  | inr x =>
      show _ ∈ leftOpen n h ∨ _ ∈ rightOpen n h
      exact Or.inr ⟨Sum.inr x, trivial, rfl⟩

theorem gluingOpenCover_covers (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Set.univ ⊆ ⋃ b, gluingOpenCover n h b := by
  intro x _
  have hx : x ∈ leftOpen n h ∪ rightOpen n h := by
    rw [leftOpen_union_rightOpen]
    trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.2 ⟨true, hx⟩
  · exact Set.mem_iUnion.2 ⟨false, hx⟩

/-- Both equatorial bands in the disjoint union. -/
def bothBandPreimage (n : ℕ) :
    Set (Sum (AmbientSphere n) (AmbientSphere n))
  | .inl x => x ∈ equatorialBand n
  | .inr x => x ∈ equatorialBand n

theorem quotientMap_preimage_inter_open (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    quotientMap n h ⁻¹' (leftOpen n h ∩ rightOpen n h) =
      bothBandPreimage n := by
  rw [preimage_inter, quotientMap_preimage_leftOpen,
    quotientMap_preimage_rightOpen]
  ext x
  cases x with
  | inl x =>
      change (True ∧ x ∈ equatorialBand n) ↔ x ∈ equatorialBand n
      simp
  | inr x =>
      change (x ∈ equatorialBand n ∧ True) ↔ x ∈ equatorialBand n
      simp

/-! ## Restricted quotient maps for the open pieces -/

theorem bothBandPreimage_isOpen (n : ℕ) : IsOpen (bothBandPreimage n) := by
  rw [isOpen_sum_iff]
  exact ⟨equatorialBand_isOpen n, equatorialBand_isOpen n⟩

/-- Literal topological identification of the named left source with the
preimage subtype used by `restrictPreimage`. -/
def leftPieceSourceHomeomorph (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftPreimage n ≃ₜ quotientMap n h ⁻¹' leftOpen n h :=
  Homeomorph.setCongr (quotientMap_preimage_leftOpen n h).symm

/-- Literal topological identification for the right source. -/
def rightPieceSourceHomeomorph (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    rightPreimage n ≃ₜ quotientMap n h ⁻¹' rightOpen n h :=
  Homeomorph.setCongr (quotientMap_preimage_rightOpen n h).symm

/-- Literal topological identification for the overlap source. -/
def intersectionPieceSourceHomeomorph (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    bothBandPreimage n ≃ₜ
      quotientMap n h ⁻¹' (leftOpen n h ∩ rightOpen n h) :=
  Homeomorph.setCongr (quotientMap_preimage_inter_open n h).symm

/-- The quotient map restricted to the left member of the open cover.  Its
domain is stated using the named preimage rather than an opaque set-theoretic
preimage subtype. -/
def leftPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (quotientMap n h ⁻¹' leftOpen n h) → leftOpen n h :=
  (leftOpen n h).restrictPreimage (quotientMap n h)

theorem leftPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (leftPieceQuotientMap n h) := by
  exact (quotientMap_isQuotientMap n h).restrictPreimage_isOpen
    (leftOpen_isOpen n h)

/-- The quotient map restricted to the right member of the open cover. -/
def rightPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (quotientMap n h ⁻¹' rightOpen n h) → rightOpen n h :=
  (rightOpen n h).restrictPreimage (quotientMap n h)

theorem rightPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (rightPieceQuotientMap n h) := by
  exact (quotientMap_isQuotientMap n h).restrictPreimage_isOpen
    (rightOpen_isOpen n h)

/-- The quotient map restricted to the overlap of the two open members. -/
def intersectionPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (quotientMap n h ⁻¹' (leftOpen n h ∩ rightOpen n h)) →
      ↥(leftOpen n h ∩ rightOpen n h) :=
  (leftOpen n h ∩ rightOpen n h).restrictPreimage (quotientMap n h)

theorem intersectionPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (intersectionPieceQuotientMap n h) := by
  have hopen : IsOpen (leftOpen n h ∩ rightOpen n h) :=
    (leftOpen_isOpen n h).inter (rightOpen_isOpen n h)
  exact (quotientMap_isQuotientMap n h).restrictPreimage_isOpen hopen

/-- Restricted quotient map with the named left source exposed. -/
def namedLeftPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftPreimage n → leftOpen n h :=
  leftPieceQuotientMap n h ∘ leftPieceSourceHomeomorph n h

theorem namedLeftPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (namedLeftPieceQuotientMap n h) :=
  (leftPieceQuotientMap_isQuotientMap n h).comp
    (leftPieceSourceHomeomorph n h).isQuotientMap

/-- Restricted quotient map with the named right source exposed. -/
def namedRightPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    rightPreimage n → rightOpen n h :=
  rightPieceQuotientMap n h ∘ rightPieceSourceHomeomorph n h

theorem namedRightPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (namedRightPieceQuotientMap n h) :=
  (rightPieceQuotientMap_isQuotientMap n h).comp
    (rightPieceSourceHomeomorph n h).isQuotientMap

/-- Restricted quotient map with the named overlap source exposed. -/
def namedIntersectionPieceQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    bothBandPreimage n → ↥(leftOpen n h ∩ rightOpen n h) :=
  intersectionPieceQuotientMap n h ∘ intersectionPieceSourceHomeomorph n h

theorem namedIntersectionPieceQuotientMap_isQuotientMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    IsQuotientMap (namedIntersectionPieceQuotientMap n h) :=
  (intersectionPieceQuotientMap_isQuotientMap n h).comp
    (intersectionPieceSourceHomeomorph n h).isQuotientMap

#print axioms equatorialBand_isOpen
#print axioms flattenRaw_ne_zero
#print axioms flattenSphere_mem_band
#print axioms bandFlatten_zero
#print axioms flattenSphere_one_height
#print axioms bandFlatten_fixes_equator
#print axioms continuous_bandFlatten_uncurried
#print axioms equatorialBandHomotopy
#print axioms equatorialBandHomotopyEquiv
#print axioms leftPreimage_respects
#print axioms rightPreimage_respects
#print axioms bandFlatten_glue_compatible
#print axioms quotientMap_preimage_leftOpen
#print axioms leftOpen_isOpen
#print axioms rightOpen_isOpen
#print axioms gluingOpenCover_isOpen
#print axioms leftOpen_union_rightOpen
#print axioms gluingOpenCover_covers
#print axioms quotientMap_preimage_inter_open
#print axioms leftPieceQuotientMap_isQuotientMap
#print axioms rightPieceQuotientMap_isQuotientMap
#print axioms intersectionPieceQuotientMap_isQuotientMap
#print axioms namedLeftPieceQuotientMap_isQuotientMap
#print axioms namedRightPieceQuotientMap_isQuotientMap
#print axioms namedIntersectionPieceQuotientMap_isQuotientMap

end ConstructionTargets.SphereEquatorGluingOpenCover
