import Mathlib
import ConstructionTargets.CoveringMonodromyCosets

open Set

def apm_t02a01_boundaryMonodromy (n : ℕ) (a b : ZMod n) : Equiv.Perm (ZMod n) :=
  Equiv.addRight a * Equiv.addRight b * (Equiv.addRight a)⁻¹ * (Equiv.addRight b)⁻¹

noncomputable def apm_t02a01_boundaryComponentCount (n : ℕ) (a b : ZMod n) : ℕ :=
  Nat.card {x : ZMod n // apm_t02a01_boundaryMonodromy n a b x = x}

theorem apm_t02a01_previous_encoding :
    ∀ (n : ℕ), 0 < n → ∀ a b : ZMod n,
      apm_t02a01_boundaryMonodromy n a b = 1 ∧
      apm_t02a01_boundaryComponentCount n a b = n := by
  intro n hn a b
  have hmon : apm_t02a01_boundaryMonodromy n a b = 1 := by
    ext x
    simp [apm_t02a01_boundaryMonodromy, Equiv.Perm.mul_apply]
    abel
  constructor
  · exact hmon
  · simp [apm_t02a01_boundaryComponentCount, hmon, Nat.card_zmod]

abbrev apm_t02a01_squareAnnulus :=
  {x : ℝ × ℝ // x.1 ∈ Set.Icc 0 1 ∧ x.2 ∈ Set.Icc 0 1 ∧
    (1 / 4 : ℝ) ≤ ‖x - (1 / 2, 1 / 2)‖}

inductive apm_t02a01_edgeRel :
    apm_t02a01_squareAnnulus → apm_t02a01_squareAnnulus → Prop
  | horizontal (y : ℝ) (hy : y ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((0, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((1, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(0, y), ⟨by norm_num, hy, h₀⟩⟩
        ⟨(1, y), ⟨by norm_num, hy, h₁⟩⟩
  | vertical (x : ℝ) (hx : x ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((x, 0) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((x, 1) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(x, 0), ⟨hx, by norm_num, h₀⟩⟩
        ⟨(x, 1), ⟨hx, by norm_num, h₁⟩⟩

def apm_t02a01_puncturedTorus :=
  Quotient (Relation.EqvGen.setoid apm_t02a01_edgeRel)

noncomputable instance : TopologicalSpace apm_t02a01_puncturedTorus :=
  TopologicalSpace.coinduced
    (fun x : apm_t02a01_squareAnnulus ↦
      (Quotient.mk _ x : apm_t02a01_puncturedTorus)) inferInstance

def apm_t02a01_boundary : Set apm_t02a01_puncturedTorus :=
  (fun x : apm_t02a01_squareAnnulus ↦
    (Quotient.mk _ x : apm_t02a01_puncturedTorus)) ''
      {x | ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)}

abbrev apm_t02a01_boundarySpace :=
  apm_t02a01_boundary

def apm_t02a01_restrictedCover {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) :
    p ⁻¹' apm_t02a01_boundary → apm_t02a01_boundarySpace :=
  fun x => ⟨p x.1, x.2⟩

def apm_t02a01_boundary_homeomorph_circle_aux_interior
    (x : apm_t02a01_squareAnnulus) : Prop :=
  x.1.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ x.1.2 ∈ Set.Ioo (0 : ℝ) 1

theorem apm_t02a01_boundary_homeomorph_circle_aux_rel_not_interior
    {x y : apm_t02a01_squareAnnulus} (h : apm_t02a01_edgeRel x y) :
    ¬ apm_t02a01_boundary_homeomorph_circle_aux_interior x ∧
      ¬ apm_t02a01_boundary_homeomorph_circle_aux_interior y := by
  cases h with
  | horizontal y hy h₀ h₁ =>
      constructor
      · intro h; exact (lt_irrefl (0 : ℝ)) h.1.1
      · intro h; exact (lt_irrefl (1 : ℝ)) h.1.2
  | vertical x hx h₀ h₁ =>
      constructor
      · intro h; exact (lt_irrefl (0 : ℝ)) h.2.1
      · intro h; exact (lt_irrefl (1 : ℝ)) h.2.2

theorem apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen
    {x y : apm_t02a01_squareAnnulus}
    (h : Relation.EqvGen apm_t02a01_edgeRel x y) :
    (apm_t02a01_boundary_homeomorph_circle_aux_interior x → x = y) ∧
      (apm_t02a01_boundary_homeomorph_circle_aux_interior y → x = y) := by
  induction h with
  | rel x y h =>
      obtain ⟨hx, hy⟩ :=
        apm_t02a01_boundary_homeomorph_circle_aux_rel_not_interior h
      exact ⟨fun hi ↦ (hx hi).elim, fun hi ↦ (hy hi).elim⟩
  | refl x => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | symm x y h ih => exact ⟨fun hi ↦ (ih.2 hi).symm, fun hi ↦ (ih.1 hi).symm⟩
  | trans x y z hxy hyz ihxy ihyz =>
      constructor
      · intro hx
        have hxy' := ihxy.1 hx
        subst y
        exact ihyz.1 hx
      · intro hz
        have hyz' := ihyz.2 hz
        subst z
        exact ihxy.2 hz

/-- The inner sphere of the square annulus (for the max norm on `ℝ × ℝ`, the
boundary of the square `[1/4, 3/4]²`) is a topological circle, e.g. by radial
projection `x ↦ (x - c) / ‖x - c‖₂` composed with `Circle` coordinates. -/
noncomputable def apm_t02a01_boundary_homeomorph_circle_aux_sphere_aux_radial
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 where
  toFun x := ⟨‖e x.1‖⁻¹ • e x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs]
    have hx : e x.1 ≠ 0 := e.map_ne_zero_iff.mpr
      (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using x.2))
    simp [abs_of_nonneg (norm_nonneg _), hx]⟩
  invFun y := ⟨‖e.symm y.1‖⁻¹ • e.symm y.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs]
    have hy : e.symm y.1 ≠ 0 := e.symm.map_ne_zero_iff.mpr
      (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using y.2))
    simp [abs_of_nonneg (norm_nonneg _), hy]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : e x.1 ≠ 0 := e.map_ne_zero_iff.mpr
      (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using x.2))
    simp [norm_smul, abs_of_nonneg (norm_nonneg _), hx,
      mem_sphere_zero_iff_norm.mp x.2]
  right_inv y := by
    apply Subtype.ext
    have hy : e.symm y.1 ≠ 0 := e.symm.map_ne_zero_iff.mpr
      (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using y.2))
    simp [norm_smul, abs_of_nonneg (norm_nonneg _), hy,
      mem_sphere_zero_iff_norm.mp y.2]
  continuous_toFun := by
    exact Continuous.subtype_mk
      (((e.continuous.comp continuous_subtype_val).norm.inv₀ (fun x ↦
        norm_ne_zero_iff.mpr (e.map_ne_zero_iff.mpr
          (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using x.2))))).smul
        (e.continuous.comp continuous_subtype_val)) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      (((e.symm.continuous.comp continuous_subtype_val).norm.inv₀ (fun x ↦
        norm_ne_zero_iff.mpr (e.symm.map_ne_zero_iff.mpr
          (norm_ne_zero_iff.mp (by simpa [mem_sphere_zero_iff_norm] using x.2))))).smul
        (e.symm.continuous.comp continuous_subtype_val)) _

theorem apm_t02a01_boundary_homeomorph_circle_aux_sphere :
    Nonempty ({x : apm_t02a01_squareAnnulus |
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)} ≃ₜ Circle) := by
  let c : ℝ × ℝ := (1 / 2, 1 / 2)
  let h : {x : apm_t02a01_squareAnnulus | ‖x.1 - c‖ = (1 / 4 : ℝ)} ≃ₜ
      Metric.sphere (0 : ℝ × ℝ) 1 :=
    { toFun := fun x ↦ ⟨(4 : ℝ) • (x.1.1 - c), by
          rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs]
          rw [x.2]
          norm_num⟩
      invFun := fun y ↦ ⟨⟨c + (1 / 4 : ℝ) • y.1, by
          have h1 := norm_fst_le y.1
          have h2 := norm_snd_le y.1
          have hyn : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
          have hb1 : -(1 : ℝ) ≤ y.1.1 ∧ y.1.1 ≤ 1 := abs_le.mp (by
            rw [hyn] at h1
            simpa [Real.norm_eq_abs] using h1)
          have hb2 : -(1 : ℝ) ≤ y.1.2 ∧ y.1.2 ≤ 1 := abs_le.mp (by
            rw [hyn] at h2
            simpa [Real.norm_eq_abs] using h2)
          dsimp [c] at *
          constructor
          · constructor <;> linarith
          constructor
          · constructor <;> linarith
          · simpa [norm_smul, Real.norm_eq_abs, hyn]⟩, by
          have hyn : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
          change ‖(c + (1 / 4 : ℝ) • y.1) - c‖ = (1 / 4 : ℝ)
          simpa [norm_smul, Real.norm_eq_abs, hyn]⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; dsimp [c]; module
      right_inv := by intro y; apply Subtype.ext; dsimp [c]; module
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨h.trans (apm_t02a01_boundary_homeomorph_circle_aux_sphere_aux_radial
    Complex.equivRealProdCLM.symm)⟩

/-- The quotient map restricts to a homeomorphism from the inner sphere onto
the boundary subtype.  Injectivity: inner-sphere points are interior to
`(0,1)²`, so their classes are singletons
(`apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen`).  Openness: the
interior points form an open saturated set, on which the quotient map is an
open embedding. -/
theorem apm_t02a01_boundary_homeomorph_circle_aux_quotient_aux_interior
    (x : apm_t02a01_squareAnnulus)
    (hx : ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)) :
    apm_t02a01_boundary_homeomorph_circle_aux_interior x := by
  have h₁ : ‖x.1.1 - (1 / 2 : ℝ)‖ ≤ (1 / 4 : ℝ) := by
    have h := norm_fst_le (x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ))
    change ‖x.1.1 - (1 / 2 : ℝ)‖ ≤
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ at h
    rw [hx] at h
    exact h
  have h₂ : ‖x.1.2 - (1 / 2 : ℝ)‖ ≤ (1 / 4 : ℝ) := by
    have h := norm_snd_le (x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ))
    change ‖x.1.2 - (1 / 2 : ℝ)‖ ≤
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ at h
    rw [hx] at h
    exact h
  constructor <;> constructor
  · have := (neg_le_of_abs_le h₁)
    norm_num at this ⊢
    linarith
  · have := (le_abs_self (x.1.1 - (1 / 2 : ℝ))).trans h₁
    norm_num at this ⊢
    linarith
  · have := (neg_le_of_abs_le h₂)
    norm_num at this ⊢
    linarith
  · have := (le_abs_self (x.1.2 - (1 / 2 : ℝ))).trans h₂
    norm_num at this ⊢
    linarith

theorem apm_t02a01_boundary_homeomorph_circle_aux_quotient :
    Nonempty ({x : apm_t02a01_squareAnnulus |
      ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)} ≃ₜ
        apm_t02a01_boundarySpace) := by
  let q : apm_t02a01_squareAnnulus → apm_t02a01_puncturedTorus :=
    fun x ↦ Quotient.mk _ x
  let S : Set apm_t02a01_squareAnnulus :=
    {x | ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)}
  let f : S → apm_t02a01_boundarySpace := fun x ↦
    ⟨q x, ⟨x, x.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hq : q x = q y := congrArg Subtype.val hxy
    have hr : Relation.EqvGen apm_t02a01_edgeRel x y := Quotient.eq'.mp hq
    exact (apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen hr).1
      (apm_t02a01_boundary_homeomorph_circle_aux_quotient_aux_interior x x.2)
  have hf_surj : Function.Surjective f := by
    rintro ⟨z, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hf_cont : Continuous f := by
    exact Continuous.subtype_mk
      (continuous_coinduced_rng.comp continuous_subtype_val) _
  let e : S ≃ apm_t02a01_boundarySpace := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨e.toHomeomorphOfContinuousOpen ?_ ?_⟩
  · exact hf_cont
  · intro U hU
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    let I : Set apm_t02a01_squareAnnulus :=
      {x | apm_t02a01_boundary_homeomorph_circle_aux_interior x}
    have hI : IsOpen I := by
      exact ((isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)).inter
        (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)))
    let W : Set apm_t02a01_puncturedTorus := q '' (V ∩ I)
    have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
    have hpre : q ⁻¹' W = V ∩ I := by
      ext x
      constructor
      · rintro ⟨y, hy, heq⟩
        have hr : Relation.EqvGen apm_t02a01_edgeRel y x := Quotient.eq'.mp heq
        have hyx :=
          (apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen hr).1 hy.2
        subst x
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hW : IsOpen W := hq.isOpen_preimage.mp (hpre.symm ▸ hV.inter hI)
    have himage : e '' (Subtype.val ⁻¹' V) =
        Subtype.val ⁻¹' W := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        change q x ∈ W
        exact ⟨x, ⟨hx,
          apm_t02a01_boundary_homeomorph_circle_aux_quotient_aux_interior x x.2⟩,
          rfl⟩
      · intro hz
        rcases z with ⟨z, hzbd⟩
        change z ∈ W at hz
        rcases hz with ⟨x, hx, rfl⟩
        rcases hzbd with ⟨y, hy, heq⟩
        have hr : Relation.EqvGen apm_t02a01_edgeRel y x := Quotient.eq'.mp heq
        have hyx :=
          (apm_t02a01_boundary_homeomorph_circle_aux_eq_of_eqvGen hr).2 hx.2
        subst y
        exact ⟨⟨x, hy⟩, hx.1, rfl⟩
    rw [himage]
    exact hW.preimage continuous_subtype_val

/-- The inner metric circle survives the outer-edge quotient and gives the
boundary subtype. -/
theorem apm_t02a01_boundary_homeomorph_circle :
    Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle) := by
  obtain ⟨q⟩ := apm_t02a01_boundary_homeomorph_circle_aux_quotient
  obtain ⟨c⟩ := apm_t02a01_boundary_homeomorph_circle_aux_sphere
  exact ⟨q.symm.trans c⟩

/-- Transport path connectedness across the concrete boundary-circle
homeomorphism.  The homeomorphism is an explicit hypothesis so this leaf is
independent of its construction. -/
theorem apm_t02a01_boundary_pathConnected
    (h : Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle)) :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) := by
  let e := h.some
  haveI : PathConnectedSpace Circle :=
    isPathConnected_iff_pathConnectedSpace.mp (by
      change IsPathConnected (Metric.sphere (0 : ℂ) 1)
      apply isPathConnected_sphere
      · rw [Complex.rank_real_complex]
        norm_num
      · norm_num)
  exact ⟨e.symm.surjective.pathConnectedSpace e.symm.continuous⟩

/-- Transport local path connectedness across the concrete boundary-circle
homeomorphism. -/
theorem apm_t02a01_boundary_locPathConnected
    (h : Nonempty (apm_t02a01_boundarySpace ≃ₜ Circle)) :
    Nonempty (LocPathConnectedSpace apm_t02a01_boundarySpace) := by
  obtain ⟨e⟩ := h
  let circleEquiv : AddCircle (1 : ℝ) ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  letI : LocPathConnectedSpace (AddCircle (1 : ℝ)) :=
    isQuotientMap_quotient_mk'.locPathConnectedSpace
  letI : LocPathConnectedSpace Circle :=
    circleEquiv.isQuotientMap.locPathConnectedSpace
  exact ⟨e.symm.isQuotientMap.locPathConnectedSpace⟩

/-- The two geometric instances used below, assembled from the independently
provable circle leaves. -/
theorem apm_t02a01_boundary_geometry :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) ∧
      Nonempty (LocPathConnectedSpace apm_t02a01_boundarySpace) := by
  have h := apm_t02a01_boundary_homeomorph_circle
  exact ⟨apm_t02a01_boundary_pathConnected h,
    apm_t02a01_boundary_locPathConnected h⟩

/-- Restricting a covering map to the full inverse image of a subtype is again
a covering map. -/
theorem apm_t02a01_restrictedCover_isCovering
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (hcover : IsCoveringMap p) :
    IsCoveringMap (apm_t02a01_restrictedCover p) := by
  exact hcover.restrictPreimage apm_t02a01_boundary

theorem apm_t02a01_boundary_monodromy_is_deck_commutator_aux_deck_injective
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (x : Stilde) : Function.Injective (fun z ↦ deck z x) := by
  intro z w hzw
  obtain ⟨q, hq, hqu⟩ :=
    hdeck_transitive x (deck z x) (hdeck_over z x).symm
  exact (hqu z rfl).trans (hqu w hzw.symm).symm

theorem apm_t02a01_boundary_monodromy_is_deck_commutator_aux_endpoint_deck
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcov : IsCoveringMap (apm_t02a01_restrictedCover p))
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (e : p ⁻¹' apm_t02a01_boundary)
    (gamma : FundamentalGroup apm_t02a01_boundarySpace
      (apm_t02a01_restrictedCover p e)) :
    ∃! z : ZMod n, (hcov.monodromy gamma ⟨e, rfl⟩).1.1 = deck z e.1 := by
  let y : Stilde := (hcov.monodromy gamma ⟨e, rfl⟩).1.1
  have hpy : p e.1 = p y := by
    have hy := congrArg Subtype.val (hcov.monodromy gamma ⟨e, rfl⟩).2
    change p y = p e.1 at hy
    exact hy.symm
  obtain ⟨z, hz, hzu⟩ := hdeck_transitive e.1 y hpy
  apply ExistsUnique.intro z hz.symm
  · intro y hy
    apply apm_t02a01_boundary_monodromy_is_deck_commutator_aux_deck_injective
        p n deck hdeck_over hdeck_transitive e.1
    exact hy.symm.trans hz.symm

/-! ### Inner boundary loop (design claude-14, 2026-10-14)

`perimeter s` runs once around the inner square `‖p - (1/2,1/2)‖∞ = 1/4` for
`s ∈ [0,4]`, starting and ending at the corner `(1/4,1/4)`:
`x = 1/4 + c(s)/2 - c(s-2)/2`, `y = 1/4 + c(s-1)/2 - c(s-3)/2`, where `c = clamp to [0,1]`.
Each quarter is one side of the square. -/

noncomputable def apm_t02a01_clamp01 (s : ℝ) : ℝ := max 0 (min 1 s)

noncomputable def apm_t02a01_perimeter (s : ℝ) : ℝ × ℝ :=
  (1 / 4 + apm_t02a01_clamp01 s / 2 - apm_t02a01_clamp01 (s - 2) / 2,
    1 / 4 + apm_t02a01_clamp01 (s - 1) / 2 - apm_t02a01_clamp01 (s - 3) / 2)

theorem apm_t02a01_perimeter_mem (s : ℝ) :
    apm_t02a01_perimeter s ∈ {x : ℝ × ℝ | x.1 ∈ Set.Icc 0 1 ∧ x.2 ∈ Set.Icc 0 1 ∧
      ‖x - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)} := by
  rcases le_total s 0 with hs | hs
  · have hc (k : ℝ) (hk : 0 ≤ k) : apm_t02a01_clamp01 (s - k) = 0 := by
      unfold apm_t02a01_clamp01
      rw [max_eq_left]
      linarith [min_le_right 1 (s - k)]
    have hc0 : apm_t02a01_clamp01 s = 0 := by simpa using hc 0 (by norm_num)
    simp [apm_t02a01_perimeter, hc0, hc 1 (by norm_num),
      hc 2 (by norm_num), hc 3 (by norm_num)]
    norm_num [Prod.norm_def]
  rcases le_total s 1 with hs1 | hs1
  · have hc0 : apm_t02a01_clamp01 s = s := by
      unfold apm_t02a01_clamp01
      rw [min_eq_right hs1, max_eq_right hs]
    have hc (k : ℝ) (hk : 1 ≤ k) : apm_t02a01_clamp01 (s - k) = 0 := by
      unfold apm_t02a01_clamp01
      rw [max_eq_left]
      linarith [min_le_right 1 (s - k)]
    simp only [apm_t02a01_perimeter, hc0, hc 1 (by norm_num),
      hc 2 (by norm_num), hc 3 (by norm_num)]
    norm_num [Prod.norm_def, abs_le] <;> (repeat' constructor) <;> linarith
  rcases le_total s 2 with hs2 | hs2
  · have hc0 : apm_t02a01_clamp01 s = 1 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_left hs1, max_eq_right] <;> norm_num
    have hc1 : apm_t02a01_clamp01 (s - 1) = s - 1 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hc (k : ℝ) (hk : 2 ≤ k) : apm_t02a01_clamp01 (s - k) = 0 := by
      unfold apm_t02a01_clamp01
      rw [max_eq_left]
      linarith [min_le_right 1 (s - k)]
    simp only [apm_t02a01_perimeter, hc0, hc1, hc 2 (by norm_num),
      hc 3 (by norm_num)]
    norm_num [Prod.norm_def, abs_le] <;> (repeat' constructor) <;> linarith
  rcases le_total s 3 with hs3 | hs3
  · have hc0 : apm_t02a01_clamp01 s = 1 := by
      unfold apm_t02a01_clamp01; rw [min_eq_left (by linarith), max_eq_right] <;> norm_num
    have hc1 : apm_t02a01_clamp01 (s - 1) = 1 := by
      unfold apm_t02a01_clamp01; rw [min_eq_left (by linarith), max_eq_right] <;> norm_num
    have hc2 : apm_t02a01_clamp01 (s - 2) = s - 2 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hc3 : apm_t02a01_clamp01 (s - 3) = 0 := by
      unfold apm_t02a01_clamp01
      rw [max_eq_left]; linarith [min_le_right 1 (s - 3)]
    simp only [apm_t02a01_perimeter, hc0, hc1, hc2, hc3]
    norm_num [Prod.norm_def, abs_le] <;> (repeat' constructor) <;> linarith
  rcases le_total s 4 with hs4 | hs4
  · have hc (k : ℝ) (hk : k ≤ 2) : apm_t02a01_clamp01 (s - k) = 1 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_left (by linarith), max_eq_right] <;> norm_num
    have hc3 : apm_t02a01_clamp01 (s - 3) = s - 3 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hc0 : apm_t02a01_clamp01 s = 1 := by simpa using hc 0 (by norm_num)
    simp only [apm_t02a01_perimeter, hc0, hc 1 (by norm_num),
      hc 2 (by norm_num), hc3]
    norm_num [Prod.norm_def, abs_le] <;> (repeat' constructor) <;> linarith
  · have hc (k : ℝ) (hk : k ≤ 3) : apm_t02a01_clamp01 (s - k) = 1 := by
      unfold apm_t02a01_clamp01
      rw [min_eq_left (by linarith), max_eq_right] <;> norm_num
    have hc0 : apm_t02a01_clamp01 s = 1 := by simpa using hc 0 (by norm_num)
    simp [apm_t02a01_perimeter, hc0, hc 1 (by norm_num),
      hc 2 (by norm_num), hc 3 (by norm_num)]
    norm_num [Prod.norm_def]

noncomputable def apm_t02a01_innerPoint (s : ℝ) : apm_t02a01_boundarySpace :=
  ⟨Quotient.mk _ ⟨apm_t02a01_perimeter s, (apm_t02a01_perimeter_mem s).1,
      (apm_t02a01_perimeter_mem s).2.1, (apm_t02a01_perimeter_mem s).2.2.ge⟩,
    ⟨_, (apm_t02a01_perimeter_mem s).2.2, rfl⟩⟩

noncomputable def apm_t02a01_innerBase : apm_t02a01_boundarySpace :=
  apm_t02a01_innerPoint 0

theorem apm_t02a01_innerPoint_continuous : Continuous apm_t02a01_innerPoint := by
  apply Continuous.subtype_mk
  exact continuous_coinduced_rng.comp
    (Continuous.subtype_mk (by
      unfold apm_t02a01_perimeter apm_t02a01_clamp01
      fun_prop) _)

theorem apm_t02a01_innerPoint_four : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase := by
  have hperimeter : apm_t02a01_perimeter 4 = apm_t02a01_perimeter 0 := by
    norm_num [apm_t02a01_perimeter, apm_t02a01_clamp01]
  exact Subtype.ext (congrArg (Quotient.mk _)
    (Subtype.ext hperimeter))

/-- The inner boundary traversed once, based at the corner `(1/4,1/4)`. -/
noncomputable def apm_t02a01_innerLoop
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    Path apm_t02a01_innerBase apm_t02a01_innerBase where
  toFun t := apm_t02a01_innerPoint (4 * t)
  continuous_toFun := hc.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [apm_t02a01_innerBase]
  target' := by simpa using h4

/-- The boundary is a circle: its π₁ at the base corner is generated by the inner loop. -/
theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_of_equiv
    {G : Type*} [Group G] (g : G) (e : G ≃* Multiplicative ℤ)
    (hg : e g = Multiplicative.ofAdd (1 : ℤ) ∨
      e g = Multiplicative.ofAdd (-1 : ℤ)) :
    ∀ x : G, ∃ k : ℤ, x = g ^ k := by
  intro x
  let m : ℤ := (e x).toAdd
  rcases hg with hg | hg
  · refine ⟨m, e.injective ?_⟩
    rw [map_zpow, hg]
    rw [← Int.ofAdd_mul, one_mul]
    exact (Multiplicative.ofAdd.apply_symm_apply (e x)).symm
  · refine ⟨-m, e.injective ?_⟩
    rw [map_zpow, hg]
    rw [← Int.ofAdd_mul]
    have hm : (-1 : ℤ) * -m = m := by ring
    rw [hm]
    exact (Multiplicative.ofAdd.apply_symm_apply (e x)).symm

/-! ### Winding of the inner loop (design claude-14, 2026-10-14)

`angleToBoundary` lifts `θ ↦ innerPoint (2θ/π)` from `[0, 2π)` to `AddCircle (2π)`
(`AddCircle.liftIco`). It is a continuous bijection from a compact space onto the boundary,
which is T2 because the boundary is a circle. So it is a homeomorphism, and composing with
`AddCircle.homeomorphCircle'` sends the inner loop to `integerLoop 1`, whose class has winding
`1` (`CircleUniversalCover.liftBasedLoopEndpointInteger_integerLoop`). -/

theorem apm_t02a01_innerPoint_injOn : Set.InjOn apm_t02a01_innerPoint (Set.Ico 0 4) := by
  sorry

theorem apm_t02a01_innerPoint_surjOn :
    ∀ b : apm_t02a01_boundarySpace, ∃ s ∈ Set.Ico (0 : ℝ) 4, apm_t02a01_innerPoint s = b := by
  sorry

instance apm_t02a01_twoPiPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def apm_t02a01_angleToBoundary
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    C(AddCircle (2 * Real.pi), apm_t02a01_boundarySpace) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0 (fun θ => apm_t02a01_innerPoint (2 * θ / Real.pi)),
    AddCircle.liftIco_continuous (by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        show apm_t02a01_innerPoint (2 * 0 / Real.pi) =
          apm_t02a01_innerPoint (2 * (0 + 2 * Real.pi) / Real.pi)
        rw [show 2 * (0 + 2 * Real.pi) / Real.pi = 4 by field_simp; ring, h4]
        simp [apm_t02a01_innerBase])
      ((hc.comp ((continuous_const.mul continuous_id).div_const _)).continuousOn)⟩

theorem apm_t02a01_angleToBoundary_bijective
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase)
    (hinj : Set.InjOn apm_t02a01_innerPoint (Set.Ico 0 4))
    (hsurj : ∀ b : apm_t02a01_boundarySpace,
      ∃ s ∈ Set.Ico (0 : ℝ) 4, apm_t02a01_innerPoint s = b) :
    Function.Bijective (apm_t02a01_angleToBoundary hc h4) := by
  sorry

/-- The final computation: transport across the homeomorphism (T2 from
`apm_t02a01_boundary_homeomorph_circle`, `Continuous.homeoOfEquivCompactToT2`) and
`AddCircle.homeomorphCircle'`. Under it the inner loop is `integerLoop 1`, which
`circleFundamentalGroupMulEquivInt` sends to `ofAdd 1`. -/
theorem apm_t02a01_circleWinding_of_bijective
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase)
    (hbij : Function.Bijective (apm_t02a01_angleToBoundary hc h4)) :
    ∃ e : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase ≃*
        Multiplicative ℤ,
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (1 : ℤ) ∨
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (-1 : ℤ) := by
  sorry

noncomputable def apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_winding_aux_pi1Homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_winding_aux_circleWinding
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    ∃ e : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase ≃*
        Multiplicative ℤ,
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (1 : ℤ) ∨
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (-1 : ℤ) :=
  apm_t02a01_circleWinding_of_bijective hc h4
    (apm_t02a01_angleToBoundary_bijective hc h4 apm_t02a01_innerPoint_injOn
      apm_t02a01_innerPoint_surjOn)

theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_winding
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    ∃ e : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase ≃*
        Multiplicative ℤ,
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (1 : ℤ) ∨
      e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (apm_t02a01_innerLoop hc h4))) = Multiplicative.ofAdd (-1 : ℤ) := by
  exact
    apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_winding_aux_circleWinding
      hc h4

theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    ∀ γ : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase,
      ∃ k : ℤ, γ = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (apm_t02a01_innerLoop hc h4))) ^ k := by
  obtain ⟨e, he⟩ :=
    apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_winding hc h4
  exact apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic_aux_of_equiv _ e he

/-! ### Commutator via the radial homotopy (design claude-14, 2026-10-14)

`apm_t02a01_radial l s = c + (1 + l) • (perimeter s - c)` with `c = (1/2,1/2)`: for `l = 0` it
is the inner square and for `l = 1` the outer square of the unit square, starting at `(0,0)`.
The square loop in the torus is the radial family at `l = 1`; its four sides are the
edge loops `A` (bottom, `(t,0)`) and `B` (right, `(1,t)`), with top and left identified with
their reverses.  A free homotopy of loops gives conjugation by the radial segment `δ`. -/

/-- Generic: a homotopy of maps from the square whose two vertical sides agree turns the
bottom loop into the top loop conjugated by the common side. -/
theorem apm_t02a01_freeHomotopy_conj {X : Type*} [TopologicalSpace X] {x y : X}
    (γ0 : Path x x) (γ1 : Path y y) (δ : Path x y)
    (F : C(unitInterval × unitInterval, X))
    (h0 : ∀ t, F (0, t) = γ0 t) (h1 : ∀ t, F (1, t) = γ1 t)
    (hl : ∀ s, F (s, 0) = δ s) (hr : ∀ s, F (s, 1) = δ s) :
    γ0.Homotopic (δ.trans (γ1.trans δ.symm)) := by
  sorry

noncomputable def apm_t02a01_radial (l s : ℝ) : ℝ × ℝ :=
  ((1 / 2 : ℝ), (1 / 2 : ℝ)) + (1 + l) • (apm_t02a01_perimeter s - ((1 / 2 : ℝ), (1 / 2 : ℝ)))

theorem apm_t02a01_radial_mem {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (s : ℝ) :
    (apm_t02a01_radial l s).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (apm_t02a01_radial l s).2 ∈ Set.Icc (0 : ℝ) 1 ∧
      (1 / 4 : ℝ) ≤ ‖apm_t02a01_radial l s - ((1 / 2 : ℝ), (1 / 2 : ℝ))‖ := by
  obtain ⟨-, -, hn⟩ := apm_t02a01_perimeter_mem s
  set v := apm_t02a01_perimeter s - ((1 / 2 : ℝ), (1 / 2 : ℝ)) with hv
  have hsub : apm_t02a01_radial l s - ((1 / 2 : ℝ), (1 / 2 : ℝ)) = (1 + l) • v := by
    simp [apm_t02a01_radial, hv]
  have hnorm : ‖(1 + l) • v‖ = (1 + l) / 4 := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith), hn]; ring
  have h1 : |((1 + l) • v).1| ≤ (1 + l) / 4 := by
    rw [← hnorm]; exact (Real.norm_eq_abs _).symm ▸ norm_fst_le _
  have h2 : |((1 + l) • v).2| ≤ (1 + l) / 4 := by
    rw [← hnorm]; exact (Real.norm_eq_abs _).symm ▸ norm_snd_le _
  have e1 : (apm_t02a01_radial l s).1 = 1 / 2 + ((1 + l) • v).1 := by
    simp [apm_t02a01_radial, hv]
  have e2 : (apm_t02a01_radial l s).2 = 1 / 2 + ((1 + l) • v).2 := by
    simp [apm_t02a01_radial, hv]
  rw [abs_le] at h1 h2
  refine ⟨⟨by rw [e1]; linarith [h1.1], by rw [e1]; linarith [h1.2]⟩,
    ⟨by rw [e2]; linarith [h2.1], by rw [e2]; linarith [h2.2]⟩, ?_⟩
  rw [hsub, hnorm]; linarith

/-- The radial family in the punctured torus, `l` and the loop parameter in `[0,1]`. -/
noncomputable def apm_t02a01_radialPt (p : unitInterval × unitInterval) :
    apm_t02a01_puncturedTorus :=
  Quotient.mk _ ⟨apm_t02a01_radial p.1 (4 * p.2), apm_t02a01_radial_mem p.1.2.1 p.1.2.2 _⟩

theorem apm_t02a01_radialPt_continuous : Continuous apm_t02a01_radialPt := by
  apply continuous_coinduced_rng.comp
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval ↦
    apm_t02a01_radial p.1 (4 * p.2))
  fun_prop (disch := aesop) [apm_t02a01_radial, apm_t02a01_perimeter,
    apm_t02a01_clamp01]

/-- The corner `(0,0)` of the torus, where `A` and `B` are based. -/
noncomputable def apm_t02a01_corner : apm_t02a01_puncturedTorus :=
  Quotient.mk _ ⟨((0 : ℝ), (0 : ℝ)), by norm_num, by norm_num, by norm_num [Prod.norm_def]⟩

/-- The bottom edge loop `A t = (t, 0)` and right edge loop `B t = (1, t)`. -/
noncomputable def apm_t02a01_edgeA (t : ℝ) : apm_t02a01_puncturedTorus :=
  Quotient.mk _ ⟨(max 0 (min 1 t), (0 : ℝ)), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩,
    by norm_num, by
      rw [Prod.norm_def]; norm_num⟩

noncomputable def apm_t02a01_edgeB (t : ℝ) : apm_t02a01_puncturedTorus :=
  Quotient.mk _ ⟨((1 : ℝ), max 0 (min 1 t)), by norm_num,
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, by
      rw [Prod.norm_def]; norm_num⟩


theorem apm_t02a01_radialPt_zero_zero :
    apm_t02a01_radialPt (0, 0) = apm_t02a01_innerBase.1 := by
  simp only [apm_t02a01_radialPt, apm_t02a01_innerBase, apm_t02a01_innerPoint]
  congr 1; apply Subtype.ext; simp [apm_t02a01_radial]

theorem apm_t02a01_radialPt_one_zero :
    apm_t02a01_radialPt (1, 0) = apm_t02a01_corner := by
  simp only [apm_t02a01_radialPt, apm_t02a01_corner]
  congr 1; apply Subtype.ext
  norm_num [apm_t02a01_radial, apm_t02a01_perimeter, apm_t02a01_clamp01]

theorem apm_t02a01_radialPt_one_one :
    apm_t02a01_radialPt (1, 1) = apm_t02a01_corner := by
  simp only [apm_t02a01_radialPt, apm_t02a01_corner]
  congr 1; apply Subtype.ext
  norm_num [apm_t02a01_radial, apm_t02a01_perimeter, apm_t02a01_clamp01]

theorem apm_t02a01_corner_eq_one_zero :
    apm_t02a01_corner = Quotient.mk _ ⟨((1 : ℝ), (0 : ℝ)), by norm_num, by norm_num,
      by norm_num [Prod.norm_def]⟩ :=
  Quotient.sound (Relation.EqvGen.rel _ _ (apm_t02a01_edgeRel.horizontal 0 (by norm_num)
    (by norm_num [Prod.norm_def]) (by norm_num [Prod.norm_def])))

theorem apm_t02a01_corner_eq_one_one :
    apm_t02a01_corner = Quotient.mk _ ⟨((1 : ℝ), (1 : ℝ)), by norm_num, by norm_num,
      by norm_num [Prod.norm_def]⟩ := by
  have hv : apm_t02a01_corner = Quotient.mk _ ⟨((0 : ℝ), (1 : ℝ)), by norm_num, by norm_num,
      by norm_num [Prod.norm_def]⟩ :=
    Quotient.sound (Relation.EqvGen.rel _ _ (apm_t02a01_edgeRel.vertical 0 (by norm_num)
      (by norm_num [Prod.norm_def]) (by norm_num [Prod.norm_def])))
  rw [hv]
  exact Quotient.sound (Relation.EqvGen.rel _ _ (apm_t02a01_edgeRel.horizontal 1 (by norm_num)
    (by norm_num [Prod.norm_def]) (by norm_num [Prod.norm_def])))

/-- The radial segment from the inner base corner `(1/4,1/4)` to the corner `(0,0)`. -/
noncomputable def apm_t02a01_delta (hc : Continuous apm_t02a01_radialPt) :
    Path apm_t02a01_innerBase.1 apm_t02a01_corner where
  toFun s := apm_t02a01_radialPt (s, 0)
  continuous_toFun := hc.comp (continuous_id.prodMk continuous_const)
  source' := apm_t02a01_radialPt_zero_zero
  target' := apm_t02a01_radialPt_one_zero

/-- The outer square loop at the corner. -/
noncomputable def apm_t02a01_outerLoop (hc : Continuous apm_t02a01_radialPt) :
    Path apm_t02a01_corner apm_t02a01_corner where
  toFun t := apm_t02a01_radialPt (1, t)
  continuous_toFun := hc.comp (continuous_const.prodMk continuous_id)
  source' := apm_t02a01_radialPt_one_zero
  target' := apm_t02a01_radialPt_one_one

theorem apm_t02a01_edgeA_continuous : Continuous apm_t02a01_edgeA := by
  exact continuous_coinduced_rng.comp
    (Continuous.subtype_mk
      ((continuous_const.max (continuous_const.min continuous_id)).prodMk
        continuous_const) _)

theorem apm_t02a01_edgeB_continuous : Continuous apm_t02a01_edgeB := by
  exact continuous_coinduced_rng.comp
    (Continuous.subtype_mk
      (continuous_const.prodMk (continuous_const.max (continuous_const.min continuous_id))) _)

noncomputable def apm_t02a01_loopA (hA : Continuous apm_t02a01_edgeA) :
    Path apm_t02a01_corner apm_t02a01_corner where
  toFun t := apm_t02a01_edgeA t
  continuous_toFun := hA.comp continuous_subtype_val
  source' := by
    simp only [apm_t02a01_edgeA, apm_t02a01_corner, Set.Icc.coe_zero]
    congr 1; apply Subtype.ext; norm_num
  target' := by
    rw [apm_t02a01_corner_eq_one_zero]
    simp only [apm_t02a01_edgeA, Set.Icc.coe_one]
    congr 1; apply Subtype.ext; norm_num

noncomputable def apm_t02a01_loopB (hB : Continuous apm_t02a01_edgeB) :
    Path apm_t02a01_corner apm_t02a01_corner where
  toFun t := apm_t02a01_edgeB t
  continuous_toFun := hB.comp continuous_subtype_val
  source' := by
    rw [apm_t02a01_corner_eq_one_zero]
    simp only [apm_t02a01_edgeB, Set.Icc.coe_zero]
    congr 1; apply Subtype.ext; norm_num
  target' := by
    rw [apm_t02a01_corner_eq_one_one]
    simp only [apm_t02a01_edgeB, Set.Icc.coe_one]
    congr 1; apply Subtype.ext; norm_num

/-- The inner loop pushed into the torus is the radial family at `l = 0`, and the radial
family's two vertical sides are both `δ`: so the generic conjugation lemma applies. -/
theorem apm_t02a01_inner_conj_outer
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase)
    (hr : Continuous apm_t02a01_radialPt)
    (hconj : ∀ {X : Type} [TopologicalSpace X] {x y : X}
      (γ0 : Path x x) (γ1 : Path y y) (δ : Path x y)
      (F : C(unitInterval × unitInterval, X)),
      (∀ t, F (0, t) = γ0 t) → (∀ t, F (1, t) = γ1 t) →
      (∀ s, F (s, 0) = δ s) → (∀ s, F (s, 1) = δ s) →
      γ0.Homotopic (δ.trans (γ1.trans δ.symm))) :
    ((apm_t02a01_innerLoop hc h4).map (continuous_subtype_val :
        Continuous ((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus))).Homotopic
      ((apm_t02a01_delta hr).trans ((apm_t02a01_outerLoop hr).trans (apm_t02a01_delta hr).symm)) := by
  sorry

/-- The outer square, read side by side: bottom `A`, right `B`, top `A` reversed, left `B`
reversed (opposite sides are identified in the torus). -/
theorem apm_t02a01_outer_word
    (hr : Continuous apm_t02a01_radialPt)
    (hA : Continuous apm_t02a01_edgeA) (hB : Continuous apm_t02a01_edgeB) :
    (apm_t02a01_outerLoop hr).Homotopic
      ((apm_t02a01_loopA hA).trans ((apm_t02a01_loopB hB).trans
        ((apm_t02a01_loopA hA).symm.trans (apm_t02a01_loopB hB).symm))) := by
  sorry

/-- Algebra: conjugate `A` and `B` by `δ` to get the commutator in `π₁(T, innerBase)`. -/
theorem apm_t02a01_commutator_of_homotopies
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase)
    (hr : Continuous apm_t02a01_radialPt)
    (hA : Continuous apm_t02a01_edgeA) (hB : Continuous apm_t02a01_edgeB)
    (hin : ((apm_t02a01_innerLoop hc h4).map (continuous_subtype_val :
        Continuous ((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus))).Homotopic
      ((apm_t02a01_delta hr).trans ((apm_t02a01_outerLoop hr).trans (apm_t02a01_delta hr).symm)))
    (hout : (apm_t02a01_outerLoop hr).Homotopic
      ((apm_t02a01_loopA hA).trans ((apm_t02a01_loopB hB).trans
        ((apm_t02a01_loopA hA).symm.trans (apm_t02a01_loopB hB).symm)))) :
    ∃ a b : FundamentalGroup apm_t02a01_puncturedTorus apm_t02a01_innerBase.1,
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) apm_t02a01_innerBase
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (apm_t02a01_innerLoop hc h4))) =
        a * b * a⁻¹ * b⁻¹ := by
  sorry

/-- In the punctured torus the inner loop is a commutator: deform it radially onto the
outer square, whose four sides are the two edge loops traversed `a b a⁻¹ b⁻¹`
(conjugated by the diagonal segment from the corner `(0,0)` to `(1/4,1/4)`). -/
theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_commutator
    (hc : Continuous apm_t02a01_innerPoint)
    (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase) :
    ∃ a b : FundamentalGroup apm_t02a01_puncturedTorus apm_t02a01_innerBase.1,
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) apm_t02a01_innerBase
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (apm_t02a01_innerLoop hc h4))) =
        a * b * a⁻¹ * b⁻¹ := by
  exact apm_t02a01_commutator_of_homotopies hc h4 apm_t02a01_radialPt_continuous
    apm_t02a01_edgeA_continuous apm_t02a01_edgeB_continuous
    (apm_t02a01_inner_conj_outer hc h4 apm_t02a01_radialPt_continuous
      (fun γ0 γ1 δ F h0 h1 hl hr => apm_t02a01_freeHomotopy_conj γ0 γ1 δ F h0 h1 hl hr))
    (apm_t02a01_outer_word apm_t02a01_radialPt_continuous
      apm_t02a01_edgeA_continuous apm_t02a01_edgeB_continuous)

theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_base
    (hcyc : ∀ (hc : Continuous apm_t02a01_innerPoint)
      (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase)
      (γ : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase),
      ∃ k : ℤ, γ = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (apm_t02a01_innerLoop hc h4))) ^ k)
    (hcomm : ∀ (hc : Continuous apm_t02a01_innerPoint)
      (h4 : apm_t02a01_innerPoint 4 = apm_t02a01_innerBase),
      ∃ a b : FundamentalGroup apm_t02a01_puncturedTorus apm_t02a01_innerBase.1,
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) apm_t02a01_innerBase
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (apm_t02a01_innerLoop hc h4))) =
        a * b * a⁻¹ * b⁻¹) :
    ∃ (delta : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase)
      (a b : FundamentalGroup apm_t02a01_puncturedTorus apm_t02a01_innerBase.1),
      (∀ gamma : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase,
        ∃ k : ℤ, gamma = delta ^ k) ∧
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) apm_t02a01_innerBase delta =
        a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨a, b, h⟩ := hcomm apm_t02a01_innerPoint_continuous apm_t02a01_innerPoint_four
  exact ⟨_, a, b, hcyc apm_t02a01_innerPoint_continuous apm_t02a01_innerPoint_four, h⟩

theorem apm_t02a01_boundary_pathConnected_concrete :
    Nonempty (PathConnectedSpace apm_t02a01_boundarySpace) :=
  apm_t02a01_boundary_pathConnected apm_t02a01_boundary_homeomorph_circle

/-- Move the base-corner statement to any boundary point: conjugating along a path in the
boundary preserves "cyclic" and sends a commutator to a commutator. -/
theorem apm_t02a01_boundary_inclusion_word_aux_generator_aux_transport
    (hpc : Nonempty (PathConnectedSpace apm_t02a01_boundarySpace))
    (h0 : ∃ (delta : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase)
      (a b : FundamentalGroup apm_t02a01_puncturedTorus apm_t02a01_innerBase.1),
      (∀ gamma : FundamentalGroup apm_t02a01_boundarySpace apm_t02a01_innerBase,
        ∃ k : ℤ, gamma = delta ^ k) ∧
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) apm_t02a01_innerBase delta =
        a * b * a⁻¹ * b⁻¹)
    (x : apm_t02a01_boundarySpace) :
    ∃ (delta : FundamentalGroup apm_t02a01_boundarySpace x)
      (a b : FundamentalGroup apm_t02a01_puncturedTorus x.1),
      (∀ gamma : FundamentalGroup apm_t02a01_boundarySpace x,
        ∃ k : ℤ, gamma = delta ^ k) ∧
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) x delta =
        a * b * a⁻¹ * b⁻¹ := by
  letI : PathConnectedSpace apm_t02a01_boundarySpace := hpc.some
  obtain ⟨delta₀, a₀, b₀, hcyc, hcomm⟩ := h0
  let i : C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus) :=
    ⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
      continuous_subtype_val⟩
  let p : Path apm_t02a01_innerBase x :=
    PathConnectedSpace.somePath apm_t02a01_innerBase x
  let q : Path apm_t02a01_innerBase.1 x.1 := p.map continuous_subtype_val
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath q
  refine ⟨e delta₀, E a₀, E b₀, ?_, ?_⟩
  · intro gamma
    obtain ⟨gamma₀, rfl⟩ := e.surjective gamma
    obtain ⟨k, hk⟩ := hcyc gamma₀
    refine ⟨k, ?_⟩
    rw [hk, map_zpow]
  · have hnatur :
        FundamentalGroup.map i x (e delta₀) =
          E (FundamentalGroup.map i apm_t02a01_innerBase delta₀) := by
      exact CategoryTheory.Functor.map_conj
        (FundamentalGroupoid.map i)
        ((CategoryTheory.Groupoid.isoEquivHom _ _).symm
          (Path.Homotopic.Quotient.mk p)) delta₀
    rw [hnatur, hcomm, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem apm_t02a01_boundary_inclusion_word_aux_generator
    (x : apm_t02a01_boundarySpace) :
    ∃ (delta : FundamentalGroup apm_t02a01_boundarySpace x)
      (a b : FundamentalGroup apm_t02a01_puncturedTorus x.1),
      (∀ gamma : FundamentalGroup apm_t02a01_boundarySpace x,
        ∃ k : ℤ, gamma = delta ^ k) ∧
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) x delta =
        a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨d0, a0, b0, hc0, hd0⟩ :=
    apm_t02a01_boundary_inclusion_word_aux_generator_aux_base
      (apm_t02a01_boundary_inclusion_word_aux_generator_aux_cyclic)
      (apm_t02a01_boundary_inclusion_word_aux_generator_aux_commutator)
  exact apm_t02a01_boundary_inclusion_word_aux_generator_aux_transport
    apm_t02a01_boundary_pathConnected_concrete ⟨d0, a0, b0, hc0, hd0⟩ x


/-- LIBRARY (square-annulus polygon word): after inclusion into the punctured
torus, every based loop on the inner boundary is a power of a commutator.  The
integer is its winding number.  This is the purely geometric half of the
boundary-monodromy calculation. -/
theorem apm_t02a01_boundary_inclusion_word
    (x : apm_t02a01_boundarySpace)
    (γ : FundamentalGroup apm_t02a01_boundarySpace x) :
    ∃ (a b : FundamentalGroup apm_t02a01_puncturedTorus x.1) (k : ℤ),
      FundamentalGroup.map
          (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
            continuous_subtype_val⟩ :
            C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus)) x γ =
        (a * b * a⁻¹ * b⁻¹) ^ k := by
  obtain ⟨delta, a, b, hcyclic, hdelta⟩ :=
    apm_t02a01_boundary_inclusion_word_aux_generator x
  obtain ⟨k, rfl⟩ := hcyclic γ
  refine ⟨a, b, k, ?_⟩
  rw [map_zpow, hdelta]

/-- LIBRARY (covering/deck algebra): if the image of a boundary loop is a power
of a commutator in the base fundamental group, its lifted endpoint is `deck 0`
because the deck-label group is abelian.  The word equality is an explicit
input, so this leaf is independent of the square-annulus geometry. -/
theorem apm_t02a01_monodromy_of_boundary_word
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcover : IsCoveringMap p)
    (hcov : IsCoveringMap (apm_t02a01_restrictedCover p))
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (e : p ⁻¹' apm_t02a01_boundary)
    (γ : FundamentalGroup apm_t02a01_boundarySpace
      (apm_t02a01_restrictedCover p e))
    (a b : FundamentalGroup apm_t02a01_puncturedTorus (p e.1)) (k : ℤ)
    (hword : FundamentalGroup.map
        (⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
          continuous_subtype_val⟩ :
          C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus))
        (apm_t02a01_restrictedCover p e) γ = (a * b * a⁻¹ * b⁻¹) ^ k) :
    (hcov.monodromy γ ⟨e, rfl⟩).1.1 = deck 0 e.1 := by
  let inc : C(apm_t02a01_boundarySpace, apm_t02a01_puncturedTorus) :=
    ⟨((↑) : apm_t02a01_boundarySpace → apm_t02a01_puncturedTorus),
      continuous_subtype_val⟩
  have hequiv (q : FundamentalGroup apm_t02a01_puncturedTorus (p e.1))
      (z : ZMod n) (x : p ⁻¹' {p e.1}) :
      (hcover.monodromy (FundamentalGroup.toPath q)
          ⟨deck z x.1, (hdeck_over z x.1).trans x.2⟩).1 =
        deck z (hcover.monodromy (FundamentalGroup.toPath q) x).1 := by
    obtain ⟨δ⟩ := FundamentalGroup.toPath q
    change hcover.liftPath δ (deck z x.1) _ 1 =
      deck z (hcover.liftPath δ x.1 _ 1)
    let L : C(unitInterval, Stilde) :=
      (⟨deck z, (deck z).continuous⟩ : C(Stilde, Stilde)).comp
        (hcover.liftPath δ x.1 (by simpa using x.2.symm))
    have hL : L = hcover.liftPath δ (deck z x.1) (by
        simpa [hdeck_over] using x.2.symm) := by
      apply (hcover.eq_liftPath_iff' _).2
      constructor
      · funext t
        exact (hdeck_over z _).trans
          (congr_fun (hcover.liftPath_lifts δ x.1 (by simpa using x.2.symm)) t)
      · simp [L, hcover.liftPath_zero]
    rw [← hL]
    rfl
  have hnaturality :
      (hcover.monodromy (FundamentalGroup.toPath
          (FundamentalGroup.map inc (apm_t02a01_restrictedCover p e) γ))
        ⟨e.1, rfl⟩).1 = (hcov.monodromy γ ⟨e, rfl⟩).1.1 := by
    obtain ⟨δ⟩ := γ
    change hcover.liftPath (inc.comp δ) e.1 _ 1 =
      (hcov.liftPath δ e _ 1).1
    let L : C(unitInterval, Stilde) :=
      ⟨fun t ↦ (hcov.liftPath δ e δ.source t).1, by fun_prop⟩
    have hL : L = hcover.liftPath (inc.comp δ) e.1 (by
        exact congrArg Subtype.val δ.source) := by
      apply (hcover.eq_liftPath_iff' _).2
      constructor
      · funext t
        exact congrArg Subtype.val
          (congr_fun (hcov.liftPath_lifts δ e δ.source) t)
      · simp [L, hcov.liftPath_zero]
    rw [← hL]
    rfl
  have hend (q : FundamentalGroup apm_t02a01_puncturedTorus (p e.1)) :
      ∃! z : ZMod n,
        (hcover.monodromy (FundamentalGroup.toPath q) ⟨e.1, rfl⟩).1 = deck z e.1 := by
    obtain ⟨z, hz, hzu⟩ := hdeck_transitive e.1
      (hcover.monodromy (FundamentalGroup.toPath q) ⟨e.1, rfl⟩).1
      (hcover.monodromy (FundamentalGroup.toPath q) ⟨e.1, rfl⟩).2.symm
    exact ⟨z, hz.symm, fun w hw ↦ hzu w hw.symm⟩
  let ρ : FundamentalGroup apm_t02a01_puncturedTorus (p e.1) →*
      Equiv.Perm (p ⁻¹' {p e.1}) :=
    { toFun := fun q ↦ Equiv.ofBijective
          (hcover.monodromy (FundamentalGroup.toPath q))
          (hcover.monodromy_bijective _)
      map_one' := by
        apply Equiv.ext
        intro x
        exact congrFun hcover.monodromy_refl x
      map_mul' := by
        intro q r
        apply Equiv.ext
        intro x
        exact hcover.monodromy_trans_apply _ _ _ }
  have hrho_comm (q r : FundamentalGroup apm_t02a01_puncturedTorus (p e.1)) :
      ρ q * ρ r = ρ r * ρ q := by
    obtain ⟨u, hu, -⟩ := hend q
    obtain ⟨v, hv, -⟩ := hend r
    ext x
    obtain ⟨z, hz, -⟩ := hdeck_transitive e.1 x.1 x.2.symm
    change (hcover.monodromy (FundamentalGroup.toPath q)
      (hcover.monodromy (FundamentalGroup.toPath r) x)).1 = _
    have hq := hequiv q z ⟨e.1, rfl⟩
    have hr := hequiv r z ⟨e.1, rfl⟩
    have hqv := hequiv q v ⟨e.1, rfl⟩
    have hru := hequiv r u ⟨e.1, rfl⟩
    have hx : x = ⟨deck z e.1, hdeck_over z e.1⟩ := Subtype.ext hz.symm
    subst x
    change (hcover.monodromy (FundamentalGroup.toPath q)
      (hcover.monodromy (FundamentalGroup.toPath r)
        ⟨deck z e.1, hdeck_over z e.1⟩)).1 =
      (hcover.monodromy (FundamentalGroup.toPath r)
        (hcover.monodromy (FundamentalGroup.toPath q)
          ⟨deck z e.1, hdeck_over z e.1⟩)).1
    have hr' : hcover.monodromy (FundamentalGroup.toPath r)
        ⟨deck z e.1, hdeck_over z e.1⟩ =
        ⟨deck z (hcover.monodromy (FundamentalGroup.toPath r)
          ⟨e.1, rfl⟩).1,
          (hdeck_over z _).trans
            (hcover.monodromy (FundamentalGroup.toPath r) ⟨e.1, rfl⟩).2⟩ :=
      Subtype.ext hr
    have hq' : hcover.monodromy (FundamentalGroup.toPath q)
        ⟨deck z e.1, hdeck_over z e.1⟩ =
        ⟨deck z (hcover.monodromy (FundamentalGroup.toPath q)
          ⟨e.1, rfl⟩).1,
          (hdeck_over z _).trans
            (hcover.monodromy (FundamentalGroup.toPath q) ⟨e.1, rfl⟩).2⟩ :=
      Subtype.ext hq
    have hu' : hcover.monodromy (FundamentalGroup.toPath q) ⟨e.1, rfl⟩ =
        ⟨deck u e.1, hdeck_over u e.1⟩ := Subtype.ext hu
    have hv' : hcover.monodromy (FundamentalGroup.toPath r) ⟨e.1, rfl⟩ =
        ⟨deck v e.1, hdeck_over v e.1⟩ := Subtype.ext hv
    have hvz : deck z (deck v e.1) = deck (v + z) e.1 := by
      have := congrArg (fun f : Homeomorph Stilde Stilde ↦ f e.1) (hdeck_add v z)
      exact this.symm
    have huz : deck z (deck u e.1) = deck (u + z) e.1 := by
      have := congrArg (fun f : Homeomorph Stilde Stilde ↦ f e.1) (hdeck_add u z)
      exact this.symm
    have hvz' : (⟨deck z (deck v e.1),
        (hdeck_over z _).trans (hdeck_over v e.1)⟩ : p ⁻¹' {p e.1}) =
        ⟨deck (v + z) e.1, hdeck_over (v + z) e.1⟩ := Subtype.ext hvz
    have huz' : (⟨deck z (deck u e.1),
        (hdeck_over z _).trans (hdeck_over u e.1)⟩ : p ⁻¹' {p e.1}) =
        ⟨deck (u + z) e.1, hdeck_over (u + z) e.1⟩ := Subtype.ext huz
    rw [hr', hq', hv', hu', hvz', huz']
    rw [hequiv q (v + z) ⟨e.1, rfl⟩, hequiv r (u + z) ⟨e.1, rfl⟩,
      hu, hv]
    calc
      deck (v + z) (deck u e.1) = deck (u + (v + z)) e.1 := by
        exact congrArg (fun f : Homeomorph Stilde Stilde ↦ f e.1)
          (hdeck_add u (v + z)).symm
      _ = deck (v + (u + z)) e.1 := by congr 1; abel
      _ = deck (u + z) (deck v e.1) := by
        exact congrArg (fun f : Homeomorph Stilde Stilde ↦ f e.1)
          (hdeck_add v (u + z))
  have hcomm : ρ (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hrho_comm a b]
    group
  have hpow : ρ ((a * b * a⁻¹ * b⁻¹) ^ k) = 1 := by
    rw [map_zpow, hcomm]
    exact one_zpow k
  have hendzero :
      (hcover.monodromy (FundamentalGroup.toPath
        ((a * b * a⁻¹ * b⁻¹) ^ k)) ⟨e.1, rfl⟩).1 = e.1 := by
    have := congrFun (congrArg Equiv.toFun hpow) (⟨e.1, rfl⟩ : p ⁻¹' {p e.1})
    exact congrArg Subtype.val this
  rw [hword] at hnaturality
  rw [← hnaturality]
  exact hendzero.trans (by rw [hdeck_zero]; rfl)

/-- The polygon word and the covering/deck calculation assembled.  Repaired
2026-10-14 (lemma-6 counterexample): `deck` must be an action (`hdeck_zero`,
`hdeck_add`), else `deck 0` may move points and the statement is false for the
constant loop. -/
theorem apm_t02a01_boundary_monodromy_is_deck_commutator
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcover : IsCoveringMap p)
    (hcov : IsCoveringMap (apm_t02a01_restrictedCover p))
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (e : p ⁻¹' apm_t02a01_boundary)
    (γ : FundamentalGroup apm_t02a01_boundarySpace
      (apm_t02a01_restrictedCover p e)) :
    ∃ u v : ZMod n,
      (hcov.monodromy γ ⟨e, rfl⟩).1.1 = deck (u + v - u - v) e.1 := by
  obtain ⟨a, b, k, hword⟩ :=
    apm_t02a01_boundary_inclusion_word (apm_t02a01_restrictedCover p e) γ
  have hzero := apm_t02a01_monodromy_of_boundary_word p n hcover hcov deck
    hdeck_zero hdeck_add hdeck_over hdeck_transitive e γ a b k hword
  exact ⟨0, 0, by simpa using hzero⟩

/-- The commutator translation is the identity because the deck group is the
abelian group `ZMod n`.  This is independent of the boundary geometry. -/
theorem apm_t02a01_deck_commutator_apply
    {Stilde : Type*} [TopologicalSpace Stilde] (n : ℕ)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (u v : ZMod n) (x : Stilde) :
    deck (u + v - u - v) x = x := by
  have hcomm : u + v - u - v = 0 := by
    abel
  rw [hcomm, hdeck_zero]
  rfl

/-- LIBRARY (boundary commutator + abelian deck group): monodromy of every
loop in the restricted boundary cover is trivial. -/
theorem apm_t02a01_boundary_monodromy_trivial
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hcover : IsCoveringMap p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    ∃ hcov : IsCoveringMap (apm_t02a01_restrictedCover p),
      ∀ (e : p ⁻¹' apm_t02a01_boundary)
        (γ : FundamentalGroup apm_t02a01_boundarySpace
          (apm_t02a01_restrictedCover p e)),
        hcov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  let hcov := apm_t02a01_restrictedCover_isCovering p hcover
  refine ⟨hcov, ?_⟩
  intro e γ
  obtain ⟨u, v, huv⟩ :=
    apm_t02a01_boundary_monodromy_is_deck_commutator p n hcover hcov deck
      hdeck_zero hdeck_add hdeck_over hdeck_transitive e γ
  apply Subtype.ext
  apply Subtype.ext
  exact huv.trans (apm_t02a01_deck_commutator_apply n deck hdeck_zero u v e.1)

/-- A covering over a path-connected base has a point above the chosen
basepoint in every connected component of its total space. -/
theorem apm_t02a01_component_meets_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q) (e : E) :
    Function.Surjective
      (fun x : q ⁻¹' {q e} => (x.1 : ConnectedComponents E)) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨γ⟩ := PathConnectedSpace.joined (q x) (q e)
  let Γ := hq.liftPath γ x (by simp)
  have hΓ0 : Γ 0 = x := hq.liftPath_zero γ x (by simp)
  have hΓ1 : q (Γ 1) = q e := by
    exact (congr_fun (hq.liftPath_lifts γ x (by simp)) 1).trans γ.target
  refine ⟨⟨Γ 1, by simpa using hΓ1⟩, ?_⟩
  rw [ConnectedComponents.coe_eq_coe']
  apply pathComponent_subset_component x
  exact ⟨⟨Γ, hΓ0, rfl⟩⟩

/-- Trivial monodromy (at every point) separates two points of the chosen
fiber into different connected components.  Repaired 2026-10-14 (lemma-2
counterexample): monodromy trivial only at `e` is not enough — add a connected
two-sheet cover as a second summand. -/
theorem apm_t02a01_fiber_injective_on_components
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q) (e : E)
    (hmono : ∀ (x : E) (γ : FundamentalGroup B (q x)),
      hq.monodromy γ ⟨x, rfl⟩ = ⟨x, rfl⟩) :
    Function.Injective
      (fun x : q ⁻¹' {q e} => (x.1 : ConnectedComponents E)) := by
  intro x y hxy
  letI : LocPathConnectedSpace E := by
    refine ⟨fun z => ?_⟩
    rw [Filter.hasBasis_self]
    intro t ht
    obtain ⟨f, hzf, hf⟩ := hq.isLocalHomeomorph z
    letI : LocPathConnectedSpace f.target := f.open_target.locPathConnectedSpace
    letI : LocPathConnectedSpace f.source :=
      f.toHomeomorphSourceTarget.symm.isQuotientMap.locPathConnectedSpace
    have ht' : Subtype.val ⁻¹' t ∈ nhds (⟨z, hzf⟩ : f.source) :=
      continuous_subtype_val.continuousAt ht
    obtain ⟨v, ⟨hvn, hvpath⟩, hvt⟩ :=
      (path_connected_basis (⟨z, hzf⟩ : f.source)).mem_iff.mp ht'
    refine ⟨Subtype.val '' v, ?_, hvpath.image continuous_subtype_val, ?_⟩
    · exact f.open_source.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hvn
    · exact image_subset_iff.mpr hvt
  have hcomponents : connectedComponent x.1 = connectedComponent y.1 :=
    ConnectedComponents.coe_eq_coe.mp hxy
  obtain ⟨δ⟩ := (connectedComponent_eq_iff_joined x.1 y.1).mp hcomponents
  have hbase : q y.1 = q x.1 := by
    exact y.2.trans x.2.symm
  let γ : FundamentalGroup B (q x.1) :=
    ((Path.Homotopic.Quotient.mk δ).map ⟨q, hq.continuous⟩).cast rfl hbase.symm
  have hmon := hmono x.1 γ
  have hmap := hq.monodromy_map (Path.Homotopic.Quotient.mk δ)
  apply Subtype.ext
  have hendpoint :
      (hq.monodromy γ ⟨x.1, rfl⟩).1 = y.1 := by
    simpa [γ, IsCoveringMap.monodromy, Path.Homotopic.Quotient.cast] using
      congrArg Subtype.val hmap
  exact (congrArg Subtype.val hmon).symm.trans hendpoint

/-- LIBRARY (covering monodromy): a path-connected base with trivial
monodromy has one connected component per point of a fiber. -/
theorem apm_t02a01_components_equiv_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace B] [LocPathConnectedSpace B]
    (q : E → B) (hq : IsCoveringMap q)
    (e : E)
    (hmono : ∀ (x : E) (γ : FundamentalGroup B (q x)),
      hq.monodromy γ ⟨x, rfl⟩ = ⟨x, rfl⟩) :
    Nonempty (ConnectedComponents E ≃ q ⁻¹' {q e}) := by
  let f : q ⁻¹' {q e} → ConnectedComponents E := fun x => x.1
  have hf : Function.Bijective f :=
    ⟨apm_t02a01_fiber_injective_on_components q hq e hmono,
      apm_t02a01_component_meets_fiber q hq e⟩
  exact ⟨(Equiv.ofBijective f hf).symm⟩

/-- The supplied simply transitive `ZMod n` deck action identifies every
fiber with `ZMod n`. -/
theorem apm_t02a01_fiber_card
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y)
    (x : p ⁻¹' apm_t02a01_boundary) :
    Nat.card (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) = n := by
  let f : ZMod n → (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) := fun z =>
    ⟨⟨deck z x.1, by
      change p (deck z x.1) ∈ apm_t02a01_boundary
      rw [hdeck_over]
      exact x.2⟩, by
        apply Subtype.ext
        exact hdeck_over z x.1⟩
  have hf_injective : Function.Injective f := by
    intro z w hzw
    have hz : deck z x.1 = (f w).1.1 := by
      simpa [f] using congrArg (fun y => y.1.1) hzw
    have hw : deck w x.1 = (f w).1.1 := by
      rfl
    obtain ⟨u, hu, huniq⟩ := hdeck_transitive x.1 (f w).1.1 (by
      change p x.1 = p (deck w x.1)
      symm
      exact hdeck_over w x.1)
    exact (huniq z hz).trans (huniq w hw).symm
  have hf_surjective : Function.Surjective f := by
    intro y
    have hpy : p x.1 = p y.1.1 := by
      have h := congrArg Subtype.val y.2
      exact h.symm
    obtain ⟨z, hz, _⟩ := hdeck_transitive x.1 y.1.1 hpy
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  let e : ZMod n ≃ (apm_t02a01_restrictedCover p ⁻¹'
      {apm_t02a01_restrictedCover p x}) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  rw [← Nat.card_congr e]
  exact Nat.card_zmod n

theorem apm_t02a01
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hn : 0 < n)
    (hcover : IsCoveringMap p)
    (hp_surjective : Function.Surjective p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    Nat.card (ConnectedComponents (p ⁻¹' apm_t02a01_boundary)) = n := by
  letI := (apm_t02a01_boundary_geometry).1.some
  letI := (apm_t02a01_boundary_geometry).2.some
  let a := Classical.choice (inferInstance : Nonempty apm_t02a01_boundarySpace)
  obtain ⟨b, hb⟩ := hp_surjective a.1
  let e : p ⁻¹' apm_t02a01_boundary := ⟨b, by
    change p b ∈ apm_t02a01_boundary
    rw [hb]
    exact a.property⟩
  obtain ⟨hcov, hmono⟩ := apm_t02a01_boundary_monodromy_trivial p n hcover deck
    hdeck_zero hdeck_add hdeck_over hdeck_transitive
  obtain ⟨equiv⟩ := apm_t02a01_components_equiv_fiber
    (apm_t02a01_restrictedCover p) hcov e hmono
  rw [Nat.card_congr equiv]
  exact apm_t02a01_fiber_card p n deck hdeck_over hdeck_transitive e

#print axioms apm_t02a01
