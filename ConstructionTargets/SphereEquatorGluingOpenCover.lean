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

theorem continuous_equatorInclusion (n : ℕ) :
    Continuous (equatorInclusion n) :=
  continuous_subtype_val.subtype_mk _

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

/-! ## Explicit sum decompositions of the piece sources -/

/-- The logical equivalence `Equiv.subtypeSum` is a homeomorphism for the
standard sum and subtype topologies. -/
def subtypeSumHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (p : X ⊕ Y → Prop)
    (hleft : IsOpen {x | p (Sum.inl x)})
    (hright : IsOpen {y | p (Sum.inr y)}) :
    {z // p z} ≃ₜ {x // p (Sum.inl x)} ⊕ {y // p (Sum.inr y)} where
  toEquiv := Equiv.subtypeSum
  continuous_toFun := by
    rw [continuous_def]
    intro u hu
    have hl : IsOpen (Sum.inl ⁻¹' u) := hu.preimage continuous_inl
    have hr : IsOpen (Sum.inr ⁻¹' u) := hu.preimage continuous_inr
    have hl' : IsOpen (Subtype.val '' (Sum.inl ⁻¹' u)) :=
      hleft.isOpenMap_subtype_val _ hl
    have hr' : IsOpen (Subtype.val '' (Sum.inr ⁻¹' u)) :=
      hright.isOpenMap_subtype_val _ hr
    have hs : IsOpen
        (Sum.inl '' (Subtype.val '' (Sum.inl ⁻¹' u)) ∪
          Sum.inr '' (Subtype.val '' (Sum.inr ⁻¹' u))) :=
      (isOpenMap_inl _ hl').union (isOpenMap_inr _ hr')
    change IsOpen (Equiv.subtypeSum ⁻¹' u)
    rw [show Equiv.subtypeSum ⁻¹' u =
        Subtype.val ⁻¹'
          (Sum.inl '' (Subtype.val '' (Sum.inl ⁻¹' u)) ∪
            Sum.inr '' (Subtype.val '' (Sum.inr ⁻¹' u))) by
      ext z
      rcases z with ⟨x | y, hz⟩
      · simp only [Equiv.subtypeSum, Equiv.coe_fn_mk, Set.mem_preimage,
          Set.mem_union, Set.mem_image]
        aesop
      · simp only [Equiv.subtypeSum, Equiv.coe_fn_mk, Set.mem_preimage,
          Set.mem_union, Set.mem_image]
        aesop]
    exact hs.preimage continuous_subtype_val
  continuous_invFun := by
    rw [continuous_sum_dom]
    constructor <;> apply Continuous.subtype_mk
    · exact continuous_inl.comp continuous_subtype_val
    · exact continuous_inr.comp continuous_subtype_val

/-- The left source is literally one whole sphere plus the opposite
equatorial band. -/
def leftPreimageSumHomeomorph (n : ℕ) :
    leftPreimage n ≃ₜ AmbientSphere n ⊕ equatorialBand n :=
  (subtypeSumHomeomorph (leftPreimage n) isOpen_univ
      (equatorialBand_isOpen n)).trans <|
    Homeomorph.sumCongr
      ((Homeomorph.setCongr (by ext; exact iff_true_intro trivial)).trans
        (Homeomorph.Set.univ _))
      (Homeomorph.setCongr (by ext; rfl))

/-- The right source is its band followed by one whole sphere. -/
def rightPreimageSumHomeomorph (n : ℕ) :
    rightPreimage n ≃ₜ equatorialBand n ⊕ AmbientSphere n :=
  (subtypeSumHomeomorph (rightPreimage n) (equatorialBand_isOpen n)
      isOpen_univ).trans <|
    Homeomorph.sumCongr
      (Homeomorph.setCongr (by ext; rfl))
      ((Homeomorph.setCongr (by ext; exact iff_true_intro trivial)).trans
        (Homeomorph.Set.univ _))

/-- The overlap source is the sum of its two literal equatorial bands. -/
def bothBandPreimageSumHomeomorph (n : ℕ) :
    bothBandPreimage n ≃ₜ equatorialBand n ⊕ equatorialBand n :=
  (subtypeSumHomeomorph (bothBandPreimage n) (equatorialBand_isOpen n)
      (equatorialBand_isOpen n)).trans <|
    Homeomorph.sumCongr
      (Homeomorph.setCongr (by ext; rfl))
      (Homeomorph.setCongr (by ext; rfl))

/-! ## Branchwise source homotopies -/

/-- A whole-sphere branch is fixed throughout the deformation. -/
def fixedSphereBranch (n : ℕ) :
    unitInterval × AmbientSphere n → AmbientSphere n := Prod.snd

theorem continuous_fixedSphereBranch (n : ℕ) :
    Continuous (fixedSphereBranch n) := continuous_snd

/-- The band branch uses the already compiled normalized flattening. -/
def flattenedBandBranch (n : ℕ) :
    unitInterval × equatorialBand n → equatorialBand n :=
  fun p => bandFlatten n p.1 p.2

theorem continuous_flattenedBandBranch (n : ℕ) :
    Continuous (flattenedBandBranch n) :=
  continuous_bandFlatten_uncurried n

/-- Branchwise deformation of the split left source. -/
def leftSplitBranchHomotopy (n : ℕ) :
    (unitInterval × AmbientSphere n) ⊕
      (unitInterval × equatorialBand n) →
        AmbientSphere n ⊕ equatorialBand n :=
  Sum.elim (Sum.inl ∘ fixedSphereBranch n)
    (Sum.inr ∘ flattenedBandBranch n)

theorem continuous_leftSplitBranchHomotopy (n : ℕ) :
    Continuous (leftSplitBranchHomotopy n) := by
  apply Continuous.sumElim
  · exact continuous_inl.comp (continuous_fixedSphereBranch n)
  · exact continuous_inr.comp (continuous_flattenedBandBranch n)

/-- Branchwise deformation of the split right source. -/
def rightSplitBranchHomotopy (n : ℕ) :
    (unitInterval × equatorialBand n) ⊕
      (unitInterval × AmbientSphere n) →
        equatorialBand n ⊕ AmbientSphere n :=
  Sum.elim (Sum.inl ∘ flattenedBandBranch n)
    (Sum.inr ∘ fixedSphereBranch n)

theorem continuous_rightSplitBranchHomotopy (n : ℕ) :
    Continuous (rightSplitBranchHomotopy n) := by
  apply Continuous.sumElim
  · exact continuous_inl.comp (continuous_flattenedBandBranch n)
  · exact continuous_inr.comp (continuous_fixedSphereBranch n)

/-- Both branches of the split overlap are flattened. -/
def intersectionSplitBranchHomotopy (n : ℕ) :
    (unitInterval × equatorialBand n) ⊕
      (unitInterval × equatorialBand n) →
        equatorialBand n ⊕ equatorialBand n :=
  Sum.elim (Sum.inl ∘ flattenedBandBranch n)
    (Sum.inr ∘ flattenedBandBranch n)

theorem continuous_intersectionSplitBranchHomotopy (n : ℕ) :
    Continuous (intersectionSplitBranchHomotopy n) := by
  apply Continuous.sumElim
  · exact continuous_inl.comp (continuous_flattenedBandBranch n)
  · exact continuous_inr.comp (continuous_flattenedBandBranch n)

/-- Jointly continuous source homotopy on the named left preimage. -/
def leftPieceSourceHomotopy (n : ℕ) :
    unitInterval × leftPreimage n → leftPreimage n :=
  (leftPreimageSumHomeomorph n).symm ∘
    leftSplitBranchHomotopy n ∘
      Homeomorph.prodSumDistrib ∘
        Prod.map id (leftPreimageSumHomeomorph n)

theorem continuous_leftPieceSourceHomotopy (n : ℕ) :
    Continuous (leftPieceSourceHomotopy n) := by
  exact (leftPreimageSumHomeomorph n).symm.continuous.comp <|
    (continuous_leftSplitBranchHomotopy n).comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap (leftPreimageSumHomeomorph n).continuous

/-- Jointly continuous source homotopy on the named right preimage. -/
def rightPieceSourceHomotopy (n : ℕ) :
    unitInterval × rightPreimage n → rightPreimage n :=
  (rightPreimageSumHomeomorph n).symm ∘
    rightSplitBranchHomotopy n ∘
      Homeomorph.prodSumDistrib ∘
        Prod.map id (rightPreimageSumHomeomorph n)

theorem continuous_rightPieceSourceHomotopy (n : ℕ) :
    Continuous (rightPieceSourceHomotopy n) := by
  exact (rightPreimageSumHomeomorph n).symm.continuous.comp <|
    (continuous_rightSplitBranchHomotopy n).comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap (rightPreimageSumHomeomorph n).continuous

/-- Jointly continuous source homotopy on the named overlap preimage. -/
def intersectionPieceSourceHomotopy (n : ℕ) :
    unitInterval × bothBandPreimage n → bothBandPreimage n :=
  (bothBandPreimageSumHomeomorph n).symm ∘
    intersectionSplitBranchHomotopy n ∘
      Homeomorph.prodSumDistrib ∘
        Prod.map id (bothBandPreimageSumHomeomorph n)

theorem continuous_intersectionPieceSourceHomotopy (n : ℕ) :
    Continuous (intersectionPieceSourceHomotopy n) := by
  exact (bothBandPreimageSumHomeomorph n).symm.continuous.comp <|
    (continuous_intersectionSplitBranchHomotopy n).comp <|
      Homeomorph.prodSumDistrib.continuous.comp <|
        continuous_id.prodMap (bothBandPreimageSumHomeomorph n).continuous

@[simp] theorem leftPieceSourceHomotopy_inl (n : ℕ) (s : unitInterval)
    (x : AmbientSphere n) :
    (leftPieceSourceHomotopy n (s, ⟨Sum.inl x, trivial⟩)).1 = Sum.inl x := rfl

@[simp] theorem leftPieceSourceHomotopy_inr (n : ℕ) (s : unitInterval)
    (x : equatorialBand n) :
    (leftPieceSourceHomotopy n (s, ⟨Sum.inr x.1, x.2⟩)).1 =
      Sum.inr (bandFlatten n s x).1 := rfl

@[simp] theorem rightPieceSourceHomotopy_inl (n : ℕ) (s : unitInterval)
    (x : equatorialBand n) :
    (rightPieceSourceHomotopy n (s, ⟨Sum.inl x.1, x.2⟩)).1 =
      Sum.inl (bandFlatten n s x).1 := rfl

@[simp] theorem rightPieceSourceHomotopy_inr (n : ℕ) (s : unitInterval)
    (x : AmbientSphere n) :
    (rightPieceSourceHomotopy n (s, ⟨Sum.inr x, trivial⟩)).1 = Sum.inr x := rfl

@[simp] theorem intersectionPieceSourceHomotopy_inl (n : ℕ)
    (s : unitInterval) (x : equatorialBand n) :
    (intersectionPieceSourceHomotopy n (s, ⟨Sum.inl x.1, x.2⟩)).1 =
      Sum.inl (bandFlatten n s x).1 := rfl

@[simp] theorem intersectionPieceSourceHomotopy_inr (n : ℕ)
    (s : unitInterval) (x : equatorialBand n) :
    (intersectionPieceSourceHomotopy n (s, ⟨Sum.inr x.1, x.2⟩)).1 =
      Sum.inr (bandFlatten n s x).1 := rfl

/-! ## Source endpoint and fixation formulas -/

/-- The left-piece source deformation starts at the identity, independently
of the proof carried by the source subtype. -/
@[simp] theorem leftPieceSourceHomotopy_zero (n : ℕ)
    (x : leftPreimage n) :
    leftPieceSourceHomotopy n ((0 : unitInterval), x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x => rfl
  | inr x =>
      apply Subtype.ext
      simpa only [leftPieceSourceHomotopy_inr] using
        congrArg (fun y : equatorialBand n => Sum.inr y.1)
          (bandFlatten_zero n ⟨x, hx⟩)

/-- The right-piece source deformation starts at the identity, independently
of the proof carried by the source subtype. -/
@[simp] theorem rightPieceSourceHomotopy_zero (n : ℕ)
    (x : rightPreimage n) :
    rightPieceSourceHomotopy n ((0 : unitInterval), x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x =>
      apply Subtype.ext
      simpa only [rightPieceSourceHomotopy_inl] using
        congrArg (fun y : equatorialBand n => Sum.inl y.1)
          (bandFlatten_zero n ⟨x, hx⟩)
  | inr x => rfl

/-- The overlap source deformation starts at the identity, independently of
the proof carried by the source subtype. -/
@[simp] theorem intersectionPieceSourceHomotopy_zero (n : ℕ)
    (x : bothBandPreimage n) :
    intersectionPieceSourceHomotopy n ((0 : unitInterval), x) = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x =>
      apply Subtype.ext
      simpa only [intersectionPieceSourceHomotopy_inl] using
        congrArg (fun y : equatorialBand n => Sum.inl y.1)
          (bandFlatten_zero n ⟨x, hx⟩)
  | inr x =>
      apply Subtype.ext
      simpa only [intersectionPieceSourceHomotopy_inr] using
        congrArg (fun y : equatorialBand n => Sum.inr y.1)
          (bandFlatten_zero n ⟨x, hx⟩)

/-- The whole-sphere branch of the left source is fixed at every time. -/
theorem leftPieceSourceHomotopy_fixes_inl (n : ℕ) (s : unitInterval)
    (x : AmbientSphere n) (hx : Sum.inl x ∈ leftPreimage n) :
    leftPieceSourceHomotopy n (s, ⟨Sum.inl x, hx⟩) =
      ⟨Sum.inl x, hx⟩ := by
  apply Subtype.ext
  exact leftPieceSourceHomotopy_inl n s x

/-- The whole-sphere branch of the right source is fixed at every time. -/
theorem rightPieceSourceHomotopy_fixes_inr (n : ℕ) (s : unitInterval)
    (x : AmbientSphere n) (hx : Sum.inr x ∈ rightPreimage n) :
    rightPieceSourceHomotopy n (s, ⟨Sum.inr x, hx⟩) =
      ⟨Sum.inr x, hx⟩ := by
  apply Subtype.ext
  exact rightPieceSourceHomotopy_inr n s x

/-- At time one the band branch of the left source lies on the equator. -/
theorem leftPieceSourceHomotopy_inr_one (n : ℕ) (x : equatorialBand n)
    (hx : Sum.inr x.1 ∈ leftPreimage n) :
    (leftPieceSourceHomotopy n
      ((1 : unitInterval), ⟨Sum.inr x.1, hx⟩)).1 =
        Sum.inr (equatorInclusion n (bandProjectionToEquator n x)) := by
  rw [leftPieceSourceHomotopy_inr]
  rfl

/-- At time one the band branch of the right source lies on the equator. -/
theorem rightPieceSourceHomotopy_inl_one (n : ℕ) (x : equatorialBand n)
    (hx : Sum.inl x.1 ∈ rightPreimage n) :
    (rightPieceSourceHomotopy n
      ((1 : unitInterval), ⟨Sum.inl x.1, hx⟩)).1 =
        Sum.inl (equatorInclusion n (bandProjectionToEquator n x)) := by
  rw [rightPieceSourceHomotopy_inl]
  rfl

/-- At time one the left band branch of the overlap lies on the equator. -/
theorem intersectionPieceSourceHomotopy_inl_one (n : ℕ)
    (x : equatorialBand n) (hx : Sum.inl x.1 ∈ bothBandPreimage n) :
    (intersectionPieceSourceHomotopy n
      ((1 : unitInterval), ⟨Sum.inl x.1, hx⟩)).1 =
        Sum.inl (equatorInclusion n (bandProjectionToEquator n x)) := by
  rw [intersectionPieceSourceHomotopy_inl]
  rfl

/-- At time one the right band branch of the overlap lies on the equator. -/
theorem intersectionPieceSourceHomotopy_inr_one (n : ℕ)
    (x : equatorialBand n) (hx : Sum.inr x.1 ∈ bothBandPreimage n) :
    (intersectionPieceSourceHomotopy n
      ((1 : unitInterval), ⟨Sum.inr x.1, hx⟩)).1 =
        Sum.inr (equatorInclusion n (bandProjectionToEquator n x)) := by
  rw [intersectionPieceSourceHomotopy_inr]
  rfl

/-- The equator in the right band branch of the left source is fixed at every
time, with no dependence on the chosen membership proof. -/
theorem leftPieceSourceHomotopy_fixes_inr_equator (n : ℕ)
    (s : unitInterval) (x : sphereEquator n)
    (hx : Sum.inr (equatorInclusion n x) ∈ leftPreimage n) :
    leftPieceSourceHomotopy n
      (s, ⟨Sum.inr (equatorInclusion n x), hx⟩) =
        ⟨Sum.inr (equatorInclusion n x), hx⟩ := by
  apply Subtype.ext
  simpa only [leftPieceSourceHomotopy_inr] using
    congrArg Sum.inr (bandFlatten_fixes_equator n s x)

/-- The equator in the left band branch of the right source is fixed at every
time, with no dependence on the chosen membership proof. -/
theorem rightPieceSourceHomotopy_fixes_inl_equator (n : ℕ)
    (s : unitInterval) (x : sphereEquator n)
    (hx : Sum.inl (equatorInclusion n x) ∈ rightPreimage n) :
    rightPieceSourceHomotopy n
      (s, ⟨Sum.inl (equatorInclusion n x), hx⟩) =
        ⟨Sum.inl (equatorInclusion n x), hx⟩ := by
  apply Subtype.ext
  simpa only [rightPieceSourceHomotopy_inl] using
    congrArg Sum.inl (bandFlatten_fixes_equator n s x)

/-- The left equator branch of the overlap source is fixed at every time. -/
theorem intersectionPieceSourceHomotopy_fixes_inl_equator (n : ℕ)
    (s : unitInterval) (x : sphereEquator n)
    (hx : Sum.inl (equatorInclusion n x) ∈ bothBandPreimage n) :
    intersectionPieceSourceHomotopy n
      (s, ⟨Sum.inl (equatorInclusion n x), hx⟩) =
        ⟨Sum.inl (equatorInclusion n x), hx⟩ := by
  apply Subtype.ext
  simpa only [intersectionPieceSourceHomotopy_inl] using
    congrArg Sum.inl (bandFlatten_fixes_equator n s x)

/-- The right equator branch of the overlap source is fixed at every time. -/
theorem intersectionPieceSourceHomotopy_fixes_inr_equator (n : ℕ)
    (s : unitInterval) (x : sphereEquator n)
    (hx : Sum.inr (equatorInclusion n x) ∈ bothBandPreimage n) :
    intersectionPieceSourceHomotopy n
      (s, ⟨Sum.inr (equatorInclusion n x), hx⟩) =
        ⟨Sum.inr (equatorInclusion n x), hx⟩ := by
  apply Subtype.ext
  simpa only [intersectionPieceSourceHomotopy_inr] using
    congrArg Sum.inr (bandFlatten_fixes_equator n s x)

theorem leftPieceSourceHomotopy_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ leftPreimage n) (hb : b ∈ leftPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    quotientMap n h (leftPieceSourceHomotopy n (s, ⟨a, ha⟩)).1 =
      quotientMap n h (leftPieceSourceHomotopy n (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x =>
          have hx := bandFlatten_glue_compatible n h s x
          rw [bandFlatten_fixes_equator] at hx
          simpa using hx
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hmid : b ∈ leftPreimage n :=
        (leftPreimage_respects n h hab).mp ha
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

theorem leftPieceSourceHomotopy_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : leftPreimage n}
    (hab : namedLeftPieceQuotientMap n h a =
      namedLeftPieceQuotientMap n h b) :
    namedLeftPieceQuotientMap n h (leftPieceSourceHomotopy n (s, a)) =
      namedLeftPieceQuotientMap n h (leftPieceSourceHomotopy n (s, b)) := by
  apply Subtype.ext
  apply leftPieceSourceHomotopy_eq_of_eqv n h s a.2 b.2
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  exact Quotient.exact hab'

theorem rightPieceSourceHomotopy_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ rightPreimage n) (hb : b ∈ rightPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    quotientMap n h (rightPieceSourceHomotopy n (s, ⟨a, ha⟩)).1 =
      quotientMap n h (rightPieceSourceHomotopy n (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x =>
          calc
            _ = quotientMap n h
                (Sum.inr (bandFlatten n s
                  ⟨equatorInclusion n (h x),
                    equatorInclusion_mem_band n (h x)⟩).1) :=
              bandFlatten_glue_compatible n h s x
            _ = quotientMap n h
                (Sum.inr (equatorInclusion n (h x))) := by
              rw [bandFlatten_fixes_equator]
            _ = _ := by
              simpa only [Subsingleton.elim hb trivial] using
                congrArg (quotientMap n h)
                  (rightPieceSourceHomotopy_inr n s
                    (equatorInclusion n (h x))).symm
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hmid : b ∈ rightPreimage n :=
        (rightPreimage_respects n h hab).mp ha
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

theorem rightPieceSourceHomotopy_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : rightPreimage n}
    (hab : namedRightPieceQuotientMap n h a =
      namedRightPieceQuotientMap n h b) :
    namedRightPieceQuotientMap n h (rightPieceSourceHomotopy n (s, a)) =
      namedRightPieceQuotientMap n h (rightPieceSourceHomotopy n (s, b)) := by
  apply Subtype.ext
  apply rightPieceSourceHomotopy_eq_of_eqv n h s a.2 b.2
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  exact Quotient.exact hab'

theorem intersectionPieceSourceHomotopy_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ bothBandPreimage n) (hb : b ∈ bothBandPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    quotientMap n h (intersectionPieceSourceHomotopy n (s, ⟨a, ha⟩)).1 =
      quotientMap n h (intersectionPieceSourceHomotopy n (s, ⟨b, hb⟩)).1 := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x => exact bandFlatten_glue_compatible n h s x
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have haLeft : a ∈ leftPreimage n := by
        cases a with
        | inl => trivial
        | inr => exact ha
      have haRight : a ∈ rightPreimage n := by
        cases a with
        | inl => exact ha
        | inr => trivial
      have hmidLeft : b ∈ leftPreimage n :=
        (leftPreimage_respects n h hab).mp haLeft
      have hmidRight : b ∈ rightPreimage n :=
        (rightPreimage_respects n h hab).mp haRight
      have hmid : b ∈ bothBandPreimage n := by
        cases b with
        | inl => exact hmidRight
        | inr => exact hmidLeft
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

theorem intersectionPieceSourceHomotopy_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (s : unitInterval)
    {a b : bothBandPreimage n}
    (hab : namedIntersectionPieceQuotientMap n h a =
      namedIntersectionPieceQuotientMap n h b) :
    namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n (s, a)) =
      namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n (s, b)) := by
  apply Subtype.ext
  apply intersectionPieceSourceHomotopy_eq_of_eqv n h s a.2 b.2
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  exact Quotient.exact hab'

/-! ## Descent to the open quotient pieces -/

noncomputable def leftPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    unitInterval × leftOpen n h → leftOpen n h := fun p =>
  namedLeftPieceQuotientMap n h
    (leftPieceSourceHomotopy n
      (p.1, Function.surjInv
        (namedLeftPieceQuotientMap_isQuotientMap n h).surjective p.2))

theorem leftPieceHomotopyMap_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (p : unitInterval × leftPreimage n) :
    leftPieceHomotopyMap n h (p.1, namedLeftPieceQuotientMap n h p.2) =
      namedLeftPieceQuotientMap n h (leftPieceSourceHomotopy n p) := by
  apply leftPieceSourceHomotopy_fiber_coherent n h p.1
  exact Function.surjInv_eq
    (namedLeftPieceQuotientMap_isQuotientMap n h).surjective
    (namedLeftPieceQuotientMap n h p.2)

theorem continuous_leftPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (leftPieceHomotopyMap n h) := by
  apply (namedLeftPieceQuotientMap_isQuotientMap n h).continuous_lift_prod_right
  have hc : Continuous (fun p : unitInterval × leftPreimage n =>
      namedLeftPieceQuotientMap n h (leftPieceSourceHomotopy n p)) :=
    (namedLeftPieceQuotientMap_isQuotientMap n h).continuous.comp
      (continuous_leftPieceSourceHomotopy n)
  convert hc using 1
  funext p
  exact leftPieceHomotopyMap_pullback n h p

noncomputable def rightPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    unitInterval × rightOpen n h → rightOpen n h := fun p =>
  namedRightPieceQuotientMap n h
    (rightPieceSourceHomotopy n
      (p.1, Function.surjInv
        (namedRightPieceQuotientMap_isQuotientMap n h).surjective p.2))

theorem rightPieceHomotopyMap_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (p : unitInterval × rightPreimage n) :
    rightPieceHomotopyMap n h (p.1, namedRightPieceQuotientMap n h p.2) =
      namedRightPieceQuotientMap n h (rightPieceSourceHomotopy n p) := by
  apply rightPieceSourceHomotopy_fiber_coherent n h p.1
  exact Function.surjInv_eq
    (namedRightPieceQuotientMap_isQuotientMap n h).surjective
    (namedRightPieceQuotientMap n h p.2)

theorem continuous_rightPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (rightPieceHomotopyMap n h) := by
  apply (namedRightPieceQuotientMap_isQuotientMap n h).continuous_lift_prod_right
  have hc : Continuous (fun p : unitInterval × rightPreimage n =>
      namedRightPieceQuotientMap n h (rightPieceSourceHomotopy n p)) :=
    (namedRightPieceQuotientMap_isQuotientMap n h).continuous.comp
      (continuous_rightPieceSourceHomotopy n)
  convert hc using 1
  funext p
  exact rightPieceHomotopyMap_pullback n h p

noncomputable def intersectionPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    unitInterval × ↥(leftOpen n h ∩ rightOpen n h) →
      ↥(leftOpen n h ∩ rightOpen n h) := fun p =>
  namedIntersectionPieceQuotientMap n h
    (intersectionPieceSourceHomotopy n
      (p.1, Function.surjInv
        (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective p.2))

theorem intersectionPieceHomotopyMap_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (p : unitInterval × bothBandPreimage n) :
    intersectionPieceHomotopyMap n h
        (p.1, namedIntersectionPieceQuotientMap n h p.2) =
      namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n p) := by
  apply intersectionPieceSourceHomotopy_fiber_coherent n h p.1
  exact Function.surjInv_eq
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective
    (namedIntersectionPieceQuotientMap n h p.2)

theorem continuous_intersectionPieceHomotopyMap (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (intersectionPieceHomotopyMap n h) := by
  apply (namedIntersectionPieceQuotientMap_isQuotientMap n h).continuous_lift_prod_right
  have hc : Continuous (fun p : unitInterval × bothBandPreimage n =>
      namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n p)) :=
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).continuous.comp
      (continuous_intersectionPieceSourceHomotopy n)
  convert hc using 1
  funext p
  exact intersectionPieceHomotopyMap_pullback n h p

/-! ## Quotient endpoints and retained-subspace maps -/

/-- The descended left-piece homotopy starts at the identity. -/
@[simp] theorem leftPieceHomotopyMap_zero (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : leftOpen n h) :
    leftPieceHomotopyMap n h ((0 : unitInterval), x) = x := by
  obtain ⟨y, rfl⟩ :=
    (namedLeftPieceQuotientMap_isQuotientMap n h).surjective x
  calc
    _ = namedLeftPieceQuotientMap n h
        (leftPieceSourceHomotopy n ((0 : unitInterval), y)) :=
      leftPieceHomotopyMap_pullback n h ((0 : unitInterval), y)
    _ = _ := congrArg (namedLeftPieceQuotientMap n h)
      (leftPieceSourceHomotopy_zero n y)

/-- The descended right-piece homotopy starts at the identity. -/
@[simp] theorem rightPieceHomotopyMap_zero (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : rightOpen n h) :
    rightPieceHomotopyMap n h ((0 : unitInterval), x) = x := by
  obtain ⟨y, rfl⟩ :=
    (namedRightPieceQuotientMap_isQuotientMap n h).surjective x
  calc
    _ = namedRightPieceQuotientMap n h
        (rightPieceSourceHomotopy n ((0 : unitInterval), y)) :=
      rightPieceHomotopyMap_pullback n h ((0 : unitInterval), y)
    _ = _ := congrArg (namedRightPieceQuotientMap n h)
      (rightPieceSourceHomotopy_zero n y)

/-- The descended intersection homotopy starts at the identity. -/
@[simp] theorem intersectionPieceHomotopyMap_zero (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (x : ↥(leftOpen n h ∩ rightOpen n h)) :
    intersectionPieceHomotopyMap n h ((0 : unitInterval), x) = x := by
  obtain ⟨y, rfl⟩ :=
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective x
  calc
    _ = namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n ((0 : unitInterval), y)) :=
      intersectionPieceHomotopyMap_pullback n h ((0 : unitInterval), y)
    _ = _ := congrArg (namedIntersectionPieceQuotientMap n h)
      (intersectionPieceSourceHomotopy_zero n y)

/-- Inclusion of the retained whole left sphere into the left quotient
piece. -/
def leftSphereInclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    C(AmbientSphere n, leftOpen n h) :=
  ⟨fun x => namedLeftPieceQuotientMap n h ⟨Sum.inl x, trivial⟩,
    (namedLeftPieceQuotientMap_isQuotientMap n h).continuous.comp
      ((continuous_inl.comp continuous_id).subtype_mk (fun _ => trivial))⟩

/-- Inclusion of the retained whole right sphere into the right quotient
piece. -/
def rightSphereInclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    C(AmbientSphere n, rightOpen n h) :=
  ⟨fun x => namedRightPieceQuotientMap n h ⟨Sum.inr x, trivial⟩,
    (namedRightPieceQuotientMap_isQuotientMap n h).continuous.comp
      ((continuous_inr.comp continuous_id).subtype_mk (fun _ => trivial))⟩

/-- Inclusion of the left equator representative into the quotient overlap. -/
def equatorIntersectionInclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    C(sphereEquator n, ↥(leftOpen n h ∩ rightOpen n h)) :=
  ⟨fun x => namedIntersectionPieceQuotientMap n h
      ⟨Sum.inl (equatorInclusion n x), equatorInclusion_mem_band n x⟩,
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).continuous.comp
      ((continuous_inl.comp (continuous_equatorInclusion n)).subtype_mk _)⟩

/-- Retraction of the split left-piece source to its retained left sphere. -/
def leftSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    AmbientSphere n ⊕ equatorialBand n → AmbientSphere n :=
  Sum.elim id
    (equatorInclusion n ∘ h.symm ∘ bandProjectionToEquator n)

theorem continuous_leftSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (leftSplitRetraction n h) := by
  apply Continuous.sumElim
  · exact continuous_id
  · exact (continuous_equatorInclusion n).comp <|
      h.symm.continuous.comp (continuous_bandProjectionToEquator n)

/-- Retraction on the named left source, before descent through the quotient. -/
def leftSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftPreimage n → AmbientSphere n :=
  leftSplitRetraction n h ∘ leftPreimageSumHomeomorph n

theorem continuous_leftSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (leftSourceRetraction n h) :=
  (continuous_leftSplitRetraction n h).comp
    (leftPreimageSumHomeomorph n).continuous

@[simp] theorem leftSourceRetraction_inl (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : AmbientSphere n)
    (hx : Sum.inl x ∈ leftPreimage n) :
    leftSourceRetraction n h ⟨Sum.inl x, hx⟩ = x := rfl

@[simp] theorem leftSourceRetraction_inr (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : equatorialBand n)
    (hx : Sum.inr x.1 ∈ leftPreimage n) :
    leftSourceRetraction n h ⟨Sum.inr x.1, hx⟩ =
      equatorInclusion n (h.symm (bandProjectionToEquator n x)) := rfl

theorem leftSourceRetraction_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ leftPreimage n) (hb : b ∈ leftPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    leftSourceRetraction n h ⟨a, ha⟩ =
      leftSourceRetraction n h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x =>
          rw [leftSourceRetraction_inl]
          let xb : equatorialBand n :=
            ⟨equatorInclusion n (h x), equatorInclusion_mem_band n (h x)⟩
          have hproj : bandProjectionToEquator n xb = h x := by
            apply Subtype.ext
            simpa only [bandProjectionToEquator, xb, bandFlatten,
              equatorInclusion] using congrArg Subtype.val
                (bandFlatten_fixes_equator n (1 : unitInterval) (h x))
          have hr := leftSourceRetraction_inr n h xb hb
          rw [hr, hproj, Homeomorph.symm_apply_apply]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hmid : b ∈ leftPreimage n :=
        (leftPreimage_respects n h hab).mp ha
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

/-- The left source retraction is constant on fibers of the restricted
quotient map. -/
theorem leftSourceRetraction_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) {a b : leftPreimage n}
    (hab : namedLeftPieceQuotientMap n h a =
      namedLeftPieceQuotientMap n h b) :
    leftSourceRetraction n h a = leftSourceRetraction n h b := by
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  apply leftSourceRetraction_eq_of_eqv n h a.2 b.2
  exact Quotient.exact hab'

/-- Retraction of the left quotient piece onto its retained sphere. -/
noncomputable def leftPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftOpen n h → AmbientSphere n := fun x =>
  leftSourceRetraction n h <|
    Function.surjInv
      (namedLeftPieceQuotientMap_isQuotientMap n h).surjective x

theorem leftPieceRetraction_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : leftPreimage n) :
    leftPieceRetraction n h (namedLeftPieceQuotientMap n h x) =
      leftSourceRetraction n h x := by
  apply leftSourceRetraction_fiber_coherent n h
  exact Function.surjInv_eq
    (namedLeftPieceQuotientMap_isQuotientMap n h).surjective
    (namedLeftPieceQuotientMap n h x)

theorem continuous_leftPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (leftPieceRetraction n h) := by
  rw [(namedLeftPieceQuotientMap_isQuotientMap n h).continuous_iff]
  convert continuous_leftSourceRetraction n h using 1
  funext x
  exact leftPieceRetraction_pullback n h x

theorem leftPieceRetraction_comp_inclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (⟨leftPieceRetraction n h, continuous_leftPieceRetraction n h⟩ :
      C(leftOpen n h, AmbientSphere n)).comp (leftSphereInclusion n h) =
        ContinuousMap.id (AmbientSphere n) := by
  apply ContinuousMap.ext
  intro x
  exact leftPieceRetraction_pullback n h ⟨Sum.inl x, trivial⟩

/-- At time one, the descended left-piece homotopy is the retained-sphere
inclusion after the quotient retraction. -/
theorem leftPieceHomotopyMap_one (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : leftOpen n h) :
    leftPieceHomotopyMap n h ((1 : unitInterval), x) =
      leftSphereInclusion n h (leftPieceRetraction n h x) := by
  obtain ⟨y, rfl⟩ :=
    (namedLeftPieceQuotientMap_isQuotientMap n h).surjective x
  rw [leftPieceRetraction_pullback]
  calc
   leftPieceHomotopyMap n h
       ((1 : unitInterval), namedLeftPieceQuotientMap n h y) =
      namedLeftPieceQuotientMap n h
        (leftPieceSourceHomotopy n ((1 : unitInterval), y)) :=
   leftPieceHomotopyMap_pullback n h ((1 : unitInterval), y)
   _ = leftSphereInclusion n h (leftSourceRetraction n h y) := by
    rcases y with ⟨y, hy⟩
    cases y with
    | inl y =>
        rw [leftSourceRetraction_inl]
        exact congrArg (namedLeftPieceQuotientMap n h)
          (leftPieceSourceHomotopy_fixes_inl n (1 : unitInterval) y hy)
    | inr y =>
        let yb : equatorialBand n := ⟨y, hy⟩
        let z : sphereEquator n := h.symm (bandProjectionToEquator n yb)
        have hs : leftPieceSourceHomotopy n
            ((1 : unitInterval), ⟨Sum.inr y, hy⟩) =
            ⟨Sum.inr (equatorInclusion n (bandProjectionToEquator n yb)),
              equatorInclusion_mem_band n (bandProjectionToEquator n yb)⟩ := by
          apply Subtype.ext
          exact leftPieceSourceHomotopy_inr_one n yb hy
        have hr : leftSourceRetraction n h ⟨Sum.inr y, hy⟩ =
            equatorInclusion n (h.symm (bandProjectionToEquator n yb)) := by
          simpa only [yb] using leftSourceRetraction_inr n h yb hy
        rw [hr]
        rw [congrArg (namedLeftPieceQuotientMap n h) hs]
        apply Subtype.ext
        change Quotient.mk _
            (Sum.inr (equatorInclusion n (bandProjectionToEquator n yb))) =
          Quotient.mk _ (Sum.inl (equatorInclusion n z))
        have hglue : quotientMap n h (Sum.inl (equatorInclusion n z)) =
            quotientMap n h (Sum.inr (equatorInclusion n (h z))) := by
          exact Quotient.sound
            (Relation.EqvGen.rel _ _ (EquatorGlueRel.glue (n := n) (h := h) z))
        simpa only [z, Homeomorph.apply_symm_apply] using hglue.symm

/-- The descended deformation of the left quotient piece. -/
def leftPieceHomotopy (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (leftOpen n h))
      ((leftSphereInclusion n h).comp
        ⟨leftPieceRetraction n h, continuous_leftPieceRetraction n h⟩) where
  toFun := leftPieceHomotopyMap n h
  continuous_toFun := continuous_leftPieceHomotopyMap n h
  map_zero_left := leftPieceHomotopyMap_zero n h
  map_one_left := leftPieceHomotopyMap_one n h

/-- The left quotient piece is homotopy equivalent to its retained whole
sphere. -/
def leftPieceHomotopyEquiv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    leftOpen n h ≃ₕ AmbientSphere n where
  toFun := ⟨leftPieceRetraction n h, continuous_leftPieceRetraction n h⟩
  invFun := leftSphereInclusion n h
  left_inv := ⟨(leftPieceHomotopy n h).symm⟩
  right_inv := by rw [leftPieceRetraction_comp_inclusion]

/-! ## Right quotient-piece equivalence -/

def rightSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    equatorialBand n ⊕ AmbientSphere n → AmbientSphere n :=
  Sum.elim (equatorInclusion n ∘ h ∘ bandProjectionToEquator n) id

theorem continuous_rightSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (rightSplitRetraction n h) := by
  apply Continuous.sumElim
  · exact (continuous_equatorInclusion n).comp <|
      h.continuous.comp (continuous_bandProjectionToEquator n)
  · exact continuous_id

def rightSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    rightPreimage n → AmbientSphere n :=
  rightSplitRetraction n h ∘ rightPreimageSumHomeomorph n

theorem continuous_rightSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (rightSourceRetraction n h) :=
  (continuous_rightSplitRetraction n h).comp
    (rightPreimageSumHomeomorph n).continuous

@[simp] theorem rightSourceRetraction_inl (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : equatorialBand n)
    (hx : Sum.inl x.1 ∈ rightPreimage n) :
    rightSourceRetraction n h ⟨Sum.inl x.1, hx⟩ =
      equatorInclusion n (h (bandProjectionToEquator n x)) := rfl

@[simp] theorem rightSourceRetraction_inr (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : AmbientSphere n)
    (hx : Sum.inr x ∈ rightPreimage n) :
    rightSourceRetraction n h ⟨Sum.inr x, hx⟩ = x := rfl

theorem rightSourceRetraction_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ rightPreimage n) (hb : b ∈ rightPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    rightSourceRetraction n h ⟨a, ha⟩ =
      rightSourceRetraction n h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x =>
          let xb : equatorialBand n :=
            ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩
          have hproj : bandProjectionToEquator n xb = x := by
            apply Subtype.ext
            simpa only [bandProjectionToEquator, xb, bandFlatten,
              equatorInclusion] using congrArg Subtype.val
                (bandFlatten_fixes_equator n (1 : unitInterval) x)
          have hl := rightSourceRetraction_inl n h xb ha
          rw [hl, hproj, rightSourceRetraction_inr]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hmid : b ∈ rightPreimage n :=
        (rightPreimage_respects n h hab).mp ha
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

theorem rightSourceRetraction_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) {a b : rightPreimage n}
    (hab : namedRightPieceQuotientMap n h a =
      namedRightPieceQuotientMap n h b) :
    rightSourceRetraction n h a = rightSourceRetraction n h b := by
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  apply rightSourceRetraction_eq_of_eqv n h a.2 b.2
  exact Quotient.exact hab'

noncomputable def rightPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    rightOpen n h → AmbientSphere n := fun x =>
  rightSourceRetraction n h <|
    Function.surjInv
      (namedRightPieceQuotientMap_isQuotientMap n h).surjective x

theorem rightPieceRetraction_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : rightPreimage n) :
    rightPieceRetraction n h (namedRightPieceQuotientMap n h x) =
      rightSourceRetraction n h x := by
  apply rightSourceRetraction_fiber_coherent n h
  exact Function.surjInv_eq
    (namedRightPieceQuotientMap_isQuotientMap n h).surjective
    (namedRightPieceQuotientMap n h x)

theorem continuous_rightPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (rightPieceRetraction n h) := by
  rw [(namedRightPieceQuotientMap_isQuotientMap n h).continuous_iff]
  convert continuous_rightSourceRetraction n h using 1
  funext x
  exact rightPieceRetraction_pullback n h x

theorem rightPieceRetraction_comp_inclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (⟨rightPieceRetraction n h, continuous_rightPieceRetraction n h⟩ :
      C(rightOpen n h, AmbientSphere n)).comp (rightSphereInclusion n h) =
        ContinuousMap.id (AmbientSphere n) := by
  apply ContinuousMap.ext
  intro x
  exact rightPieceRetraction_pullback n h ⟨Sum.inr x, trivial⟩

theorem rightPieceHomotopyMap_one (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : rightOpen n h) :
    rightPieceHomotopyMap n h ((1 : unitInterval), x) =
      rightSphereInclusion n h (rightPieceRetraction n h x) := by
  obtain ⟨y, rfl⟩ :=
    (namedRightPieceQuotientMap_isQuotientMap n h).surjective x
  rw [rightPieceRetraction_pullback]
  calc
   rightPieceHomotopyMap n h
       ((1 : unitInterval), namedRightPieceQuotientMap n h y) =
      namedRightPieceQuotientMap n h
        (rightPieceSourceHomotopy n ((1 : unitInterval), y)) :=
    rightPieceHomotopyMap_pullback n h ((1 : unitInterval), y)
   _ = rightSphereInclusion n h (rightSourceRetraction n h y) := by
    rcases y with ⟨y, hy⟩
    cases y with
    | inl y =>
        let yb : equatorialBand n := ⟨y, hy⟩
        let z : sphereEquator n := bandProjectionToEquator n yb
        have hs : rightPieceSourceHomotopy n
            ((1 : unitInterval), ⟨Sum.inl y, hy⟩) =
            ⟨Sum.inl (equatorInclusion n z),
              equatorInclusion_mem_band n z⟩ := by
          apply Subtype.ext
          exact rightPieceSourceHomotopy_inl_one n yb hy
        have hr : rightSourceRetraction n h ⟨Sum.inl y, hy⟩ =
            equatorInclusion n (h z) := by
          simpa only [yb, z] using rightSourceRetraction_inl n h yb hy
        rw [hr, congrArg (namedRightPieceQuotientMap n h) hs]
        apply Subtype.ext
        change Quotient.mk _ (Sum.inl (equatorInclusion n z)) =
          Quotient.mk _ (Sum.inr (equatorInclusion n (h z)))
        exact Quotient.sound
          (Relation.EqvGen.rel _ _ (EquatorGlueRel.glue (n := n) (h := h) z))
    | inr y =>
        rw [rightSourceRetraction_inr]
        exact congrArg (namedRightPieceQuotientMap n h)
          (rightPieceSourceHomotopy_fixes_inr n (1 : unitInterval) y hy)

def rightPieceHomotopy (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (rightOpen n h))
      ((rightSphereInclusion n h).comp
        ⟨rightPieceRetraction n h, continuous_rightPieceRetraction n h⟩) where
  toFun := rightPieceHomotopyMap n h
  continuous_toFun := continuous_rightPieceHomotopyMap n h
  map_zero_left := rightPieceHomotopyMap_zero n h
  map_one_left := rightPieceHomotopyMap_one n h

def rightPieceHomotopyEquiv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    rightOpen n h ≃ₕ AmbientSphere n where
  toFun := ⟨rightPieceRetraction n h, continuous_rightPieceRetraction n h⟩
  invFun := rightSphereInclusion n h
  left_inv := ⟨(rightPieceHomotopy n h).symm⟩
  right_inv := by rw [rightPieceRetraction_comp_inclusion]

/-! ## Intersection quotient-piece equivalence -/

def intersectionSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    equatorialBand n ⊕ equatorialBand n → sphereEquator n :=
  Sum.elim (bandProjectionToEquator n)
    (h.symm ∘ bandProjectionToEquator n)

theorem continuous_intersectionSplitRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (intersectionSplitRetraction n h) := by
  apply Continuous.sumElim
  · exact continuous_bandProjectionToEquator n
  · exact h.symm.continuous.comp (continuous_bandProjectionToEquator n)

def intersectionSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    bothBandPreimage n → sphereEquator n :=
  intersectionSplitRetraction n h ∘ bothBandPreimageSumHomeomorph n

theorem continuous_intersectionSourceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (intersectionSourceRetraction n h) :=
  (continuous_intersectionSplitRetraction n h).comp
    (bothBandPreimageSumHomeomorph n).continuous

@[simp] theorem intersectionSourceRetraction_inl (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : equatorialBand n)
    (hx : Sum.inl x.1 ∈ bothBandPreimage n) :
    intersectionSourceRetraction n h ⟨Sum.inl x.1, hx⟩ =
      bandProjectionToEquator n x := rfl

@[simp] theorem intersectionSourceRetraction_inr (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) (x : equatorialBand n)
    (hx : Sum.inr x.1 ∈ bothBandPreimage n) :
    intersectionSourceRetraction n h ⟨Sum.inr x.1, hx⟩ =
      h.symm (bandProjectionToEquator n x) := rfl

theorem intersectionSourceRetraction_eq_of_eqv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    {a b : Sum (AmbientSphere n) (AmbientSphere n)}
    (ha : a ∈ bothBandPreimage n) (hb : b ∈ bothBandPreimage n)
    (hab : Relation.EqvGen (EquatorGlueRel n h) a b) :
    intersectionSourceRetraction n h ⟨a, ha⟩ =
      intersectionSourceRetraction n h ⟨b, hb⟩ := by
  induction hab with
  | rel a b hab =>
      cases hab with
      | glue x =>
          let xl : equatorialBand n :=
            ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩
          let xr : equatorialBand n :=
            ⟨equatorInclusion n (h x), equatorInclusion_mem_band n (h x)⟩
          have hpl : bandProjectionToEquator n xl = x := by
            apply Subtype.ext
            simpa only [bandProjectionToEquator, xl, bandFlatten,
              equatorInclusion] using congrArg Subtype.val
                (bandFlatten_fixes_equator n (1 : unitInterval) x)
          have hpr : bandProjectionToEquator n xr = h x := by
            apply Subtype.ext
            simpa only [bandProjectionToEquator, xr, bandFlatten,
              equatorInclusion] using congrArg Subtype.val
                (bandFlatten_fixes_equator n (1 : unitInterval) (h x))
          have hl := intersectionSourceRetraction_inl n h xl ha
          have hr := intersectionSourceRetraction_inr n h xr hb
          rw [hl, hr, hpl, hpr, Homeomorph.symm_apply_apply]
  | refl => rfl
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have haLeft : a ∈ leftPreimage n := by
        cases a with
        | inl => trivial
        | inr => exact ha
      have haRight : a ∈ rightPreimage n := by
        cases a with
        | inl => exact ha
        | inr => trivial
      have hmidLeft : b ∈ leftPreimage n :=
        (leftPreimage_respects n h hab).mp haLeft
      have hmidRight : b ∈ rightPreimage n :=
        (rightPreimage_respects n h hab).mp haRight
      have hmid : b ∈ bothBandPreimage n := by
        cases b with
        | inl => exact hmidRight
        | inr => exact hmidLeft
      exact (ih₁ ha hmid).trans (ih₂ hmid hb)

theorem intersectionSourceRetraction_fiber_coherent (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    {a b : bothBandPreimage n}
    (hab : namedIntersectionPieceQuotientMap n h a =
      namedIntersectionPieceQuotientMap n h b) :
    intersectionSourceRetraction n h a =
      intersectionSourceRetraction n h b := by
  have hab' := congrArg Subtype.val hab
  change Quotient.mk _ a.1 = Quotient.mk _ b.1 at hab'
  apply intersectionSourceRetraction_eq_of_eqv n h a.2 b.2
  exact Quotient.exact hab'

noncomputable def intersectionPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    ↥(leftOpen n h ∩ rightOpen n h) → sphereEquator n := fun x =>
  intersectionSourceRetraction n h <|
    Function.surjInv
      (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective x

theorem intersectionPieceRetraction_pullback (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (x : bothBandPreimage n) :
    intersectionPieceRetraction n h
        (namedIntersectionPieceQuotientMap n h x) =
      intersectionSourceRetraction n h x := by
  apply intersectionSourceRetraction_fiber_coherent n h
  exact Function.surjInv_eq
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective
    (namedIntersectionPieceQuotientMap n h x)

theorem continuous_intersectionPieceRetraction (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    Continuous (intersectionPieceRetraction n h) := by
  rw [(namedIntersectionPieceQuotientMap_isQuotientMap n h).continuous_iff]
  convert continuous_intersectionSourceRetraction n h using 1
  funext x
  exact intersectionPieceRetraction_pullback n h x

theorem intersectionPieceRetraction_comp_inclusion (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    (⟨intersectionPieceRetraction n h,
        continuous_intersectionPieceRetraction n h⟩ :
      C(↥(leftOpen n h ∩ rightOpen n h), sphereEquator n)).comp
        (equatorIntersectionInclusion n h) =
      ContinuousMap.id (sphereEquator n) := by
  apply ContinuousMap.ext
  intro x
  change intersectionPieceRetraction n h
      (namedIntersectionPieceQuotientMap n h
        ⟨Sum.inl (equatorInclusion n x), equatorInclusion_mem_band n x⟩) = x
  rw [intersectionPieceRetraction_pullback]
  let xb : equatorialBand n :=
    ⟨equatorInclusion n x, equatorInclusion_mem_band n x⟩
  have hr := intersectionSourceRetraction_inl n h xb
    (equatorInclusion_mem_band n x)
  rw [hr]
  apply Subtype.ext
  simpa only [bandProjectionToEquator, xb, bandFlatten,
    equatorInclusion] using congrArg Subtype.val
      (bandFlatten_fixes_equator n (1 : unitInterval) x)

theorem intersectionPieceHomotopyMap_one (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n)
    (x : ↥(leftOpen n h ∩ rightOpen n h)) :
    intersectionPieceHomotopyMap n h ((1 : unitInterval), x) =
      equatorIntersectionInclusion n h
        (intersectionPieceRetraction n h x) := by
  obtain ⟨y, rfl⟩ :=
    (namedIntersectionPieceQuotientMap_isQuotientMap n h).surjective x
  rw [intersectionPieceRetraction_pullback]
  calc
   intersectionPieceHomotopyMap n h
       ((1 : unitInterval), namedIntersectionPieceQuotientMap n h y) =
      namedIntersectionPieceQuotientMap n h
        (intersectionPieceSourceHomotopy n ((1 : unitInterval), y)) :=
    intersectionPieceHomotopyMap_pullback n h ((1 : unitInterval), y)
   _ = equatorIntersectionInclusion n h
       (intersectionSourceRetraction n h y) := by
    rcases y with ⟨y, hy⟩
    cases y with
    | inl y =>
        let yb : equatorialBand n := ⟨y, hy⟩
        have hs : intersectionPieceSourceHomotopy n
            ((1 : unitInterval), ⟨Sum.inl y, hy⟩) =
            ⟨Sum.inl (equatorInclusion n (bandProjectionToEquator n yb)),
              equatorInclusion_mem_band n (bandProjectionToEquator n yb)⟩ := by
          apply Subtype.ext
          exact intersectionPieceSourceHomotopy_inl_one n yb hy
        have hr : intersectionSourceRetraction n h ⟨Sum.inl y, hy⟩ =
            bandProjectionToEquator n yb := by
          simpa only [yb] using intersectionSourceRetraction_inl n h yb hy
        rw [hr, congrArg (namedIntersectionPieceQuotientMap n h) hs]
        apply Subtype.ext
        rfl
    | inr y =>
        let yb : equatorialBand n := ⟨y, hy⟩
        let z : sphereEquator n := h.symm (bandProjectionToEquator n yb)
        have hs : intersectionPieceSourceHomotopy n
            ((1 : unitInterval), ⟨Sum.inr y, hy⟩) =
            ⟨Sum.inr (equatorInclusion n (bandProjectionToEquator n yb)),
              equatorInclusion_mem_band n (bandProjectionToEquator n yb)⟩ := by
          apply Subtype.ext
          exact intersectionPieceSourceHomotopy_inr_one n yb hy
        have hr : intersectionSourceRetraction n h ⟨Sum.inr y, hy⟩ = z := by
          simpa only [yb, z] using intersectionSourceRetraction_inr n h yb hy
        rw [hr, congrArg (namedIntersectionPieceQuotientMap n h) hs]
        apply Subtype.ext
        change Quotient.mk _
            (Sum.inr (equatorInclusion n (bandProjectionToEquator n yb))) =
          Quotient.mk _ (Sum.inl (equatorInclusion n z))
        have hglue : quotientMap n h (Sum.inl (equatorInclusion n z)) =
            quotientMap n h (Sum.inr (equatorInclusion n (h z))) := by
          exact Quotient.sound
            (Relation.EqvGen.rel _ _
              (EquatorGlueRel.glue (n := n) (h := h) z))
        simpa only [z, Homeomorph.apply_symm_apply] using hglue.symm

def intersectionPieceHomotopy (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    ContinuousMap.Homotopy
      (ContinuousMap.id ↥(leftOpen n h ∩ rightOpen n h))
      ((equatorIntersectionInclusion n h).comp
        ⟨intersectionPieceRetraction n h,
          continuous_intersectionPieceRetraction n h⟩) where
  toFun := intersectionPieceHomotopyMap n h
  continuous_toFun := continuous_intersectionPieceHomotopyMap n h
  map_zero_left := intersectionPieceHomotopyMap_zero n h
  map_one_left := intersectionPieceHomotopyMap_one n h

def intersectionPieceHomotopyEquiv (n : ℕ)
    (h : sphereEquator n ≃ₜ sphereEquator n) :
    ↥(leftOpen n h ∩ rightOpen n h) ≃ₕ sphereEquator n where
  toFun := ⟨intersectionPieceRetraction n h,
    continuous_intersectionPieceRetraction n h⟩
  invFun := equatorIntersectionInclusion n h
  left_inv := ⟨(intersectionPieceHomotopy n h).symm⟩
  right_inv := by rw [intersectionPieceRetraction_comp_inclusion]

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
#print axioms subtypeSumHomeomorph
#print axioms leftPreimageSumHomeomorph
#print axioms rightPreimageSumHomeomorph
#print axioms bothBandPreimageSumHomeomorph
#print axioms continuous_fixedSphereBranch
#print axioms continuous_flattenedBandBranch
#print axioms continuous_leftSplitBranchHomotopy
#print axioms continuous_rightSplitBranchHomotopy
#print axioms continuous_intersectionSplitBranchHomotopy
#print axioms continuous_leftPieceSourceHomotopy
#print axioms continuous_rightPieceSourceHomotopy
#print axioms continuous_intersectionPieceSourceHomotopy
#print axioms leftPieceSourceHomotopy_zero
#print axioms rightPieceSourceHomotopy_zero
#print axioms intersectionPieceSourceHomotopy_zero
#print axioms leftPieceSourceHomotopy_fixes_inl
#print axioms rightPieceSourceHomotopy_fixes_inr
#print axioms leftPieceSourceHomotopy_inr_one
#print axioms rightPieceSourceHomotopy_inl_one
#print axioms intersectionPieceSourceHomotopy_inl_one
#print axioms intersectionPieceSourceHomotopy_inr_one
#print axioms leftPieceSourceHomotopy_fixes_inr_equator
#print axioms rightPieceSourceHomotopy_fixes_inl_equator
#print axioms intersectionPieceSourceHomotopy_fixes_inl_equator
#print axioms intersectionPieceSourceHomotopy_fixes_inr_equator
#print axioms leftPieceSourceHomotopy_eq_of_eqv
#print axioms leftPieceSourceHomotopy_fiber_coherent
#print axioms rightPieceSourceHomotopy_eq_of_eqv
#print axioms rightPieceSourceHomotopy_fiber_coherent
#print axioms intersectionPieceSourceHomotopy_eq_of_eqv
#print axioms intersectionPieceSourceHomotopy_fiber_coherent
#print axioms leftPieceHomotopyMap_pullback
#print axioms continuous_leftPieceHomotopyMap
#print axioms rightPieceHomotopyMap_pullback
#print axioms continuous_rightPieceHomotopyMap
#print axioms intersectionPieceHomotopyMap_pullback
#print axioms continuous_intersectionPieceHomotopyMap
#print axioms leftPieceHomotopyMap_zero
#print axioms rightPieceHomotopyMap_zero
#print axioms intersectionPieceHomotopyMap_zero
#print axioms leftSphereInclusion
#print axioms rightSphereInclusion
#print axioms equatorIntersectionInclusion
#print axioms continuous_leftSourceRetraction
#print axioms leftSourceRetraction_eq_of_eqv
#print axioms leftSourceRetraction_fiber_coherent
#print axioms continuous_leftPieceRetraction
#print axioms leftPieceRetraction_comp_inclusion
#print axioms leftPieceHomotopyMap_one
#print axioms leftPieceHomotopy
#print axioms leftPieceHomotopyEquiv
#print axioms continuous_rightSourceRetraction
#print axioms rightSourceRetraction_eq_of_eqv
#print axioms rightSourceRetraction_fiber_coherent
#print axioms continuous_rightPieceRetraction
#print axioms rightPieceRetraction_comp_inclusion
#print axioms rightPieceHomotopyMap_one
#print axioms rightPieceHomotopy
#print axioms rightPieceHomotopyEquiv
#print axioms continuous_intersectionSourceRetraction
#print axioms intersectionSourceRetraction_eq_of_eqv
#print axioms intersectionSourceRetraction_fiber_coherent
#print axioms continuous_intersectionPieceRetraction
#print axioms intersectionPieceRetraction_comp_inclusion
#print axioms intersectionPieceHomotopyMap_one
#print axioms intersectionPieceHomotopy
#print axioms intersectionPieceHomotopyEquiv

end ConstructionTargets.SphereEquatorGluingOpenCover
