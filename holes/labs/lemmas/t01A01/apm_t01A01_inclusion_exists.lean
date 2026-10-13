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
theorem apm_t01A01_retraction_exists :
    ∃ r : C({y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}, apm_t01A01_RP1),
      ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0) (hq : Projectivization.mk ℝ v hv ≠ apm_t01A01_q0)
        (h2 : (![v 0, v 1] : Fin 2 → ℝ) ≠ 0),
        r ⟨Projectivization.mk ℝ v hv, hq⟩ = Projectivization.mk ℝ ![v 0, v 1] h2 := by
  sorry

/-- Seat: the inclusion `[x : y] ↦ [x : y : 0]` misses `[0 : 0 : 1]` and is continuous. -/
-- BEGIN SEAT AREA
def apm_t01A01_inclusion_exists_aux_embed (w : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![w 0, w 1, 0]

lemma apm_t01A01_inclusion_exists_aux_nonzero
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    apm_t01A01_inclusion_exists_aux_embed w ≠ 0 := by
  intro h
  apply hw
  funext j
  fin_cases j
  · exact congrFun h 0
  · exact congrFun h 1

lemma apm_t01A01_inclusion_exists_aux_ne_q0
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    Projectivization.mk ℝ (apm_t01A01_inclusion_exists_aux_embed w)
        (apm_t01A01_inclusion_exists_aux_nonzero w hw) ≠ apm_t01A01_q0 := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _
    (apm_t01A01_inclusion_exists_aux_nonzero w hw) _).mp h
  apply hw
  funext j
  fin_cases j
  · have := congrFun ha 0
    simpa [apm_t01A01_inclusion_exists_aux_embed] using this.symm
  · have := congrFun ha 1
    simpa [apm_t01A01_inclusion_exists_aux_embed] using this.symm

theorem apm_t01A01_inclusion_exists :
    ∃ i : C(apm_t01A01_RP1, {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}),
      ∀ (w : Fin 2 → ℝ) (hw : w ≠ 0) (h3 : (![w 0, w 1, 0] : Fin 3 → ℝ) ≠ 0),
        (i (Projectivization.mk ℝ w hw) : apm_t01A01_RP2) =
          Projectivization.mk ℝ ![w 0, w 1, 0] h3 := by
  let lift : {w : (Fin 2 → ℝ) // w ≠ 0} →
      {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0} := fun w =>
    ⟨Projectivization.mk ℝ (apm_t01A01_inclusion_exists_aux_embed w.1)
      (apm_t01A01_inclusion_exists_aux_nonzero w.1 w.2),
      apm_t01A01_inclusion_exists_aux_ne_q0 w.1 w.2⟩
  have hlift : Continuous lift := by
    apply Continuous.subtype_mk
    change Continuous
      (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 ∘
        fun w : {w : (Fin 2 → ℝ) // w ≠ 0} =>
          ⟨apm_t01A01_inclusion_exists_aux_embed w.1,
            apm_t01A01_inclusion_exists_aux_nonzero w.1 w.2⟩)
    apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 2).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    fin_cases j
    · simpa [apm_t01A01_inclusion_exists_aux_embed] using
        ((continuous_apply (0 : Fin 2)).comp
          (continuous_subtype_val : Continuous
            (fun w : {w : (Fin 2 → ℝ) // w ≠ 0} => w.1)))
    · simpa [apm_t01A01_inclusion_exists_aux_embed] using
        ((continuous_apply (1 : Fin 2)).comp
          (continuous_subtype_val : Continuous
            (fun w : {w : (Fin 2 → ℝ) // w ≠ 0} => w.1)))
    · exact continuous_const
  obtain ⟨i, hi⟩ :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveHomogeneousMapDescent
      ℝ lift hlift (by
        intro a b t hab
        apply Subtype.ext
        apply (Projectivization.mk_eq_mk_iff ℝ _ _
          (apm_t01A01_inclusion_exists_aux_nonzero a.1 a.2)
          (apm_t01A01_inclusion_exists_aux_nonzero b.1 b.2)).mpr
        by_cases ht : t = 0
        · subst t
          exfalso
          apply a.2
          simpa using hab
        · refine ⟨Units.mk0 t ht, ?_⟩
          rw [hab]
          funext j
          fin_cases j <;> simp [apm_t01A01_inclusion_exists_aux_embed])
  refine ⟨i, ?_⟩
  intro w hw h3
  have h := congrArg Subtype.val (hi ⟨w, hw⟩)
  simpa [ConstructionTargets.ProjectiveSpaceTopology.quotientMap,
    apm_t01A01_inclusion_exists_aux_embed] using h
-- END SEAT AREA

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
