import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.SimplyConnectedOpenCover
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.ComponentRealLiftAssembly

/-! # APM t01A01: nonsurjective self-maps of `RP²` -/

open scoped LinearAlgebra.Projectivization

abbrev apm_t01A01_RP2 := Projectivization ℝ (Fin 3 → ℝ)

abbrev apm_t01A01_RP1 := Projectivization ℝ (Fin 2 → ℝ)

noncomputable instance : TopologicalSpace apm_t01A01_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

noncomputable instance : TopologicalSpace apm_t01A01_RP1 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 2 → ℝ))))

lemma apm_t01A01_factor_through_complement
    (f : C(apm_t01A01_RP2, apm_t01A01_RP2))
    (hnot_surj : ¬Function.Surjective f) :
    ∃ q : apm_t01A01_RP2,
      ∃ g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}),
        ∀ x, (g x : apm_t01A01_RP2) = f x := by
  obtain ⟨q, hq⟩ : ∃ q : apm_t01A01_RP2, ∀ x, f x ≠ q := by
    simpa [Function.Surjective] using hnot_surj
  refine ⟨q, ⟨fun x ↦ ⟨f x, hq x⟩, ?_⟩, ?_⟩
  · exact f.continuous.subtype_mk _
  · intro x
    rfl

lemma apm_t01A01_nullhomotopic_of_factor
    (f : C(apm_t01A01_RP2, apm_t01A01_RP2))
    (q : apm_t01A01_RP2)
    (g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}))
    (hfg : ∀ x, (g x : apm_t01A01_RP2) = f x)
    (p : {y : apm_t01A01_RP2 // y ≠ q})
    (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t01A01_RP2 (p : apm_t01A01_RP2)) := by
  let inclusion : C({y : apm_t01A01_RP2 // y ≠ q}, apm_t01A01_RP2) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl inclusion) hg
  have hleft : inclusion.comp g = f := by
    ext x
    exact hfg x
  simpa [hleft, inclusion] using hcomp

/-- The point `[0 : 0 : 1]`. -/
noncomputable def apm_t01A01_q0 : apm_t01A01_RP2 :=
  Projectivization.mk ℝ ![0, 0, 1] (by intro h; have := congrFun h 2; simp at this)

/-- Seat: removing any point of `RP²` gives a space homeomorphic to removing
`[0 : 0 : 1]` (an invertible linear map of `ℝ³` sending a representative of `q`
to `e₃` induces a homeomorphism of `RP²`, `ProjectiveQuotientDescent`; restrict
it to the complements). -/
theorem apm_t01A01_puncture_transitive (q : apm_t01A01_RP2) :
    Nonempty ({y : apm_t01A01_RP2 // y ≠ q} ≃ₜ {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}) := by
  sorry

/-- Seat: the retraction `[x : y : z] ↦ [x : y]` is well defined and continuous
off `[0 : 0 : 1]` (quotient descent from `{v | (v 0, v 1) ≠ 0}`). -/
-- BEGIN SEAT AREA
lemma apm_t01A01_retraction_exists_aux_firstTwo_ne_zero
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (hq : Projectivization.mk ℝ v hv ≠ apm_t01A01_q0) :
    (![v 0, v 1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  have h2 : v 2 ≠ 0 := by
    intro hz
    apply hv
    funext i
    fin_cases i <;> simp [h0, h1, hz]
  apply hq
  apply (Projectivization.mk_eq_mk_iff ℝ v ![0, 0, 1] hv (by
    intro h
    have := congrFun h 2
    simp at this)).mpr
  refine ⟨Units.mk0 (v 2) h2, ?_⟩
  funext i
  fin_cases i <;> simp [h0, h1]

theorem apm_t01A01_retraction_exists :
    ∃ r : C({y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}, apm_t01A01_RP1),
      ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0) (hq : Projectivization.mk ℝ v hv ≠ apm_t01A01_q0)
        (h2 : (![v 0, v 1] : Fin 2 → ℝ) ≠ 0),
        r ⟨Projectivization.mk ℝ v hv, hq⟩ = Projectivization.mk ℝ ![v 0, v 1] h2 := by
  let proj (v : Fin 3 → ℝ) : Fin 2 → ℝ := ![v 0, v 1]
  let fallback : apm_t01A01_RP1 :=
    Projectivization.mk ℝ ![1, 0] (by intro h; have := congrFun h 0; simp at this)
  let lift : {v : Fin 3 → ℝ // v ≠ 0} → apm_t01A01_RP1 := fun v ↦
    if h : proj v.1 ≠ 0 then Projectivization.mk ℝ (proj v.1) h else fallback
  have horbit : ∀ (a b : {v : Fin 3 → ℝ // v ≠ 0}) (t : ℝ),
      a = t • (b : Fin 3 → ℝ) → lift a = lift b := by
    intro a b t hab
    have ht : t ≠ 0 := by
      intro ht
      apply a.2
      simpa [ht] using hab
    have hp : proj a.1 = t • proj b.1 := by
      rw [hab]
      funext i
      fin_cases i <;> simp [proj]
    by_cases hb : proj b.1 ≠ 0
    · have ha : proj a.1 ≠ 0 := by
        rw [hp]
        exact smul_ne_zero ht hb
      simp only [lift, dif_pos ha, dif_pos hb]
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ ha hb).mpr
      exact ⟨t, hp.symm⟩
    · have ha : ¬ proj a.1 ≠ 0 := by simpa [hp, hb]
      simp only [lift]
      rw [dif_neg ha, dif_neg hb]
  let rfun : apm_t01A01_RP2 → apm_t01A01_RP1 :=
    Projectivization.lift lift horbit
  let U : Set apm_t01A01_RP2 := {y | y ≠ apm_t01A01_q0}
  let qmap := ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2
  have hqbase : Topology.IsQuotientMap qmap :=
    ⟨ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 2, rfl⟩
  have hU : IsOpen U := by
    apply hqbase.isOpen_preimage.mp
    have hc : Continuous (fun x : {v : Fin 3 → ℝ // v ≠ 0} ↦ proj x.1) := by
      apply continuous_pi
      intro i
      fin_cases i
      · change Continuous (fun x : {v : Fin 3 → ℝ // v ≠ 0} ↦ x.1 0)
        exact (continuous_apply 0).comp continuous_subtype_val
      · change Continuous (fun x : {v : Fin 3 → ℝ // v ≠ 0} ↦ x.1 1)
        exact (continuous_apply 1).comp continuous_subtype_val
    have heq : qmap ⁻¹' U = {x | proj x.1 ≠ 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · exact apm_t01A01_retraction_exists_aux_firstTwo_ne_zero x.1 x.2
      · intro hp he
        apply hp
        have hm := (Projectivization.mk_eq_mk_iff ℝ x.1 ![0, 0, 1] x.2 (by
          intro h; have := congrFun h 2; simp at this)).mp he
        obtain ⟨a, ha⟩ := hm
        funext i
        fin_cases i
        · have := congrFun ha 0
          simpa [proj] using this.symm
        · have := congrFun ha 1
          simpa [proj] using this.symm
    rw [heq]
    exact (isOpen_compl_singleton.preimage hc)
  have hqquot : Topology.IsQuotientMap (U.restrictPreimage qmap) :=
    hqbase.restrictPreimage_isOpen hU
  have hcomp : Continuous ((fun y : U ↦ rfun y.1) ∘ U.restrictPreimage qmap) := by
    let raw : {x : {v : Fin 3 → ℝ // v ≠ 0} // qmap x ∈ U} →
        {w : Fin 2 → ℝ // w ≠ 0} := fun x ↦
      ⟨proj x.1.1, apm_t01A01_retraction_exists_aux_firstTwo_ne_zero
        x.1.1 x.1.2 x.2⟩
    have hraw : Continuous raw := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      fin_cases i
      · change Continuous (fun x : {x : {v : Fin 3 → ℝ // v ≠ 0} // qmap x ∈ U} ↦ x.1.1 0)
        exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)
      · change Continuous (fun x : {x : {v : Fin 3 → ℝ // v ≠ 0} // qmap x ∈ U} ↦ x.1.1 1)
        exact (continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)
    have heq : (fun y : U ↦ rfun y.1) ∘ U.restrictPreimage qmap =
        ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 1 ∘ raw := by
      funext x
      change Projectivization.lift lift horbit (Projectivization.mk ℝ x.1.1 x.1.2) = _
      rw [Projectivization.lift_mk]
      have hp := apm_t01A01_retraction_exists_aux_firstTwo_ne_zero
        x.1.1 x.1.2 x.2
      simp only [lift]
      rw [dif_pos hp]
      rfl
    rw [heq]
    exact (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 1).comp hraw
  have hrfun : Continuous (fun y : U ↦ rfun y.1) := by
    exact hqquot.continuous_iff.mpr hcomp
  refine ⟨⟨fun y ↦ rfun y.1, hrfun⟩, ?_⟩
  intro v hv hq h2
  change rfun (Projectivization.mk ℝ v hv) = _
  rw [show rfun (Projectivization.mk ℝ v hv) = lift ⟨v, hv⟩ by
    exact Projectivization.lift_mk lift horbit v hv]
  have hp : proj v ≠ 0 := h2
  simp only [lift]
  rw [dif_pos hp]
-- END SEAT AREA

/-- Seat: the inclusion `[x : y] ↦ [x : y : 0]` misses `[0 : 0 : 1]` and is continuous. -/
theorem apm_t01A01_inclusion_exists :
    ∃ i : C(apm_t01A01_RP1, {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}),
      ∀ (w : Fin 2 → ℝ) (hw : w ≠ 0) (h3 : (![w 0, w 1, 0] : Fin 3 → ℝ) ≠ 0),
        (i (Projectivization.mk ℝ w hw) : apm_t01A01_RP2) =
          Projectivization.mk ℝ ![w 0, w 1, 0] h3 := by
  sorry

/-- Seat: for maps with these formulas, `r ∘ i = id` and `i ∘ r ≃ id` via
`H t [x : y : z] = [x : y : (1 - t) z]` (never `[0 : 0 : 1]` since `(x, y) ≠ 0`;
continuity by quotient descent of `I × (ℝ³ ∖ z-axis)`, `I` locally compact). -/
theorem apm_t01A01_retraction_homotopy
    (r : C({y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}, apm_t01A01_RP1))
    (hr : ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0) (hq : Projectivization.mk ℝ v hv ≠ apm_t01A01_q0)
        (h2 : (![v 0, v 1] : Fin 2 → ℝ) ≠ 0),
        r ⟨Projectivization.mk ℝ v hv, hq⟩ = Projectivization.mk ℝ ![v 0, v 1] h2)
    (i : C(apm_t01A01_RP1, {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}))
    (hi : ∀ (w : Fin 2 → ℝ) (hw : w ≠ 0) (h3 : (![w 0, w 1, 0] : Fin 3 → ℝ) ≠ 0),
        (i (Projectivization.mk ℝ w hw) : apm_t01A01_RP2) =
          Projectivization.mk ℝ ![w 0, w 1, 0] h3) :
    ContinuousMap.Homotopic (i.comp r) (ContinuousMap.id _) ∧
      r.comp i = ContinuousMap.id _ := by
  sorry

/-- LIBRARY: the complement of a point in `RP²` has the homotopy type of its
projective-line core.  A proof may choose coordinates sending `q` to a
coordinate line and descend the radial deformation through the projective
quotient. -/
theorem apm_t01A01_punctured_homotopyEquiv_projectiveLine
    (q : apm_t01A01_RP2) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {y : apm_t01A01_RP2 // y ≠ q} apm_t01A01_RP1) := by
  obtain ⟨e⟩ := apm_t01A01_puncture_transitive q
  obtain ⟨r, hr⟩ := apm_t01A01_retraction_exists
  obtain ⟨i, hi⟩ := apm_t01A01_inclusion_exists
  obtain ⟨h1, h2⟩ := apm_t01A01_retraction_homotopy r hr i hi
  exact ⟨e.toHomotopyEquiv.trans
    { toFun := r, invFun := i, left_inv := h1,
      right_inv := by rw [h2] }⟩

/-- LIBRARY: every map from `RP²` to the projective line is null-homotopic.
This is the `Z/2 → Z` lifting step, separated from the geometry of the
punctured target. -/
theorem apm_t01A01_projectiveLine_map_nullhomotopic
    (h : C(apm_t01A01_RP2, apm_t01A01_RP1)) :
    ∃ p : apm_t01A01_RP1,
      ContinuousMap.Homotopic h
        (ContinuousMap.const apm_t01A01_RP2 p) := by
  sorry

/-- LIBRARY: transport a null-homotopy across a target homotopy equivalence.
The conclusion deliberately takes the null-homotopy as an explicit hypothesis,
so this lemma is independent of the two geometric leaves above. -/
theorem apm_t01A01_nullhomotopic_of_target_homotopyEquiv
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (e : ContinuousMap.HomotopyEquiv Y Z) (g : C(X, Y))
    (p : Z)
    (hg : ContinuousMap.Homotopic (e.toFun.comp g)
      (ContinuousMap.const X p)) :
    ∃ y : Y, ContinuousMap.Homotopic g (ContinuousMap.const X y) := by
  refine ⟨e.invFun p, ?_⟩
  have hleft := ContinuousMap.Homotopic.comp e.left_inv
    (ContinuousMap.Homotopic.refl g)
  have hconst := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl e.invFun) hg
  exact hleft.symm.trans hconst

/-- Assembly of the punctured-projective-plane retraction, the projective-line
lifting argument, and transport back through the retraction. -/
theorem apm_t01A01_punctured_factor_nullhomotopic
    (q : apm_t01A01_RP2)
    (g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q})) :
    ∃ p : {y : apm_t01A01_RP2 // y ≠ q},
      ContinuousMap.Homotopic g (ContinuousMap.const apm_t01A01_RP2 p) := by
  obtain ⟨e⟩ := apm_t01A01_punctured_homotopyEquiv_projectiveLine q
  obtain ⟨p, hp⟩ :=
    apm_t01A01_projectiveLine_map_nullhomotopic (e.toFun.comp g)
  exact apm_t01A01_nullhomotopic_of_target_homotopyEquiv e g p hp

open CategoryTheory

theorem apm_t01A01_piOne_trivial_of_nullhomotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (p : Y)
    (hf : ContinuousMap.Homotopic f (ContinuousMap.const X p)) :
    ∀ (x : X) (γ : FundamentalGroup X x),
      FundamentalGroup.map f x γ = 1 := by
  intro x γ
  let c : C(X, Y) := ContinuousMap.const X p
  have hc : FundamentalGroup.map c x γ = 1 := by
    induction γ using Path.Homotopic.Quotient.ind with
    | mk q =>
      change Path.Homotopic.Quotient.map (.mk q) c =
        Path.Homotopic.Quotient.refl p
      rw [← Path.Homotopic.Quotient.mk_map]
      have hq : q.map c.continuous = Path.refl p := by
        ext t
        rfl
      rw [hq]
      rfl
  obtain ⟨H⟩ := hf
  let η := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  have hn := η.naturality γ
  change FundamentalGroup.map f x γ ≫ η.app (FundamentalGroupoid.mk x) =
    η.app (FundamentalGroupoid.mk x) ≫ FundamentalGroup.map c x γ at hn
  dsimp [c] at hc hn
  rw [hc] at hn
  change FundamentalGroup.map f x γ ≫ η.app (FundamentalGroupoid.mk x) =
    η.app (FundamentalGroupoid.mk x) ≫ 𝟙 (FundamentalGroupoid.mk p) at hn
  have hn' : FundamentalGroup.map f x γ ≫ η.app (FundamentalGroupoid.mk x) =
      η.app (FundamentalGroupoid.mk x) :=
    hn.trans (Category.comp_id _)
  apply (cancel_mono (η.app (FundamentalGroupoid.mk x))).mp
  exact hn'.trans (Category.id_comp _).symm

theorem apm_t01a01 :
    ∀ f : C(apm_t01A01_RP2, apm_t01A01_RP2),
      ¬Function.Surjective f →
      (∀ (x : apm_t01A01_RP2) (γ : FundamentalGroup apm_t01A01_RP2 x),
        FundamentalGroup.map f x γ = 1) ∧
      ∃ p : apm_t01A01_RP2,
        ContinuousMap.Homotopic f (ContinuousMap.const _ p) := by
  intro f hnot_surj
  obtain ⟨q, g, hfg⟩ := apm_t01A01_factor_through_complement f hnot_surj
  obtain ⟨p, hg⟩ := apm_t01A01_punctured_factor_nullhomotopic q g
  have hf : ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t01A01_RP2 (p : apm_t01A01_RP2)) :=
    apm_t01A01_nullhomotopic_of_factor f q g hfg p hg
  exact ⟨apm_t01A01_piOne_trivial_of_nullhomotopic f (p : apm_t01A01_RP2) hf,
    ⟨p, hf⟩⟩

#print axioms apm_t01a01
