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
theorem apm_t01A01_inclusion_exists :
    ∃ i : C(apm_t01A01_RP1, {y : apm_t01A01_RP2 // y ≠ apm_t01A01_q0}),
      ∀ (w : Fin 2 → ℝ) (hw : w ≠ 0) (h3 : (![w 0, w 1, 0] : Fin 3 → ℝ) ≠ 0),
        (i (Projectivization.mk ℝ w hw) : apm_t01A01_RP2) =
          Projectivization.mk ℝ ![w 0, w 1, 0] h3 := by
  sorry

/-- Seat: for maps with these formulas, `r ∘ i = id` and `i ∘ r ≃ id` via
`H t [x : y : z] = [x : y : (1 - t) z]` (never `[0 : 0 : 1]` since `(x, y) ≠ 0`;
continuity by quotient descent of `I × (ℝ³ ∖ z-axis)`, `I` locally compact). -/
-- BEGIN SEAT AREA
lemma apm_t01A01_retraction_homotopy_aux_xy
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (hq : Projectivization.mk ℝ v hv ≠ apm_t01A01_q0) :
    (![v 0, v 1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  apply hq
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ hv _).mpr
  have hv2 : v 2 ≠ 0 := by
    intro hz
    apply hv
    funext j
    fin_cases j
    · exact congrFun h 0
    · exact congrFun h 1
    · exact hz
  refine ⟨Units.mk0 (v 2) hv2, ?_⟩
  funext j
  fin_cases j
  · simpa using (congrFun h 0).symm
  · simpa using (congrFun h 1).symm
  · simp

def apm_t01A01_retraction_homotopy_aux_vec
    (s : Set.Icc (0 : ℝ) 1) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0, v 1, s.1 * v 2]

lemma apm_t01A01_retraction_homotopy_aux_vec_ne
    (s : Set.Icc (0 : ℝ) 1) (v : Fin 3 → ℝ)
    (h2 : (![v 0, v 1] : Fin 2 → ℝ) ≠ 0) :
    apm_t01A01_retraction_homotopy_aux_vec s v ≠ 0 := by
  intro h
  apply h2
  funext j
  fin_cases j
  · exact congrFun h 0
  · exact congrFun h 1

lemma apm_t01A01_retraction_homotopy_aux_ne_q0
    (s : Set.Icc (0 : ℝ) 1) (v : Fin 3 → ℝ)
    (h2 : (![v 0, v 1] : Fin 2 → ℝ) ≠ 0) :
    Projectivization.mk ℝ (apm_t01A01_retraction_homotopy_aux_vec s v)
      (apm_t01A01_retraction_homotopy_aux_vec_ne s v h2) ≠ apm_t01A01_q0 := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _
    (apm_t01A01_retraction_homotopy_aux_vec_ne s v h2) _).mp h
  apply h2
  funext j
  fin_cases j
  · have z := congrFun ha 0; simpa [apm_t01A01_retraction_homotopy_aux_vec] using z.symm
  · have z := congrFun ha 1; simpa [apm_t01A01_retraction_homotopy_aux_vec] using z.symm

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
  let U : Set apm_t01A01_RP2 := {y | y ≠ apm_t01A01_q0}
  let q0 : C({v : {v : Fin 3 → ℝ // v ≠ 0} //
      ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U}, U) :=
    ⟨U.restrictPreimage (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2),
      (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 2).restrictPreimage⟩
  have hq0 : IsOpenQuotientMap q0 := by
    refine ⟨?_, q0.continuous, ?_⟩
    · exact (ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 2).restrictPreimage U
    · exact (ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen ℝ 2).restrictPreimage U
  let qp : C(Set.Icc (0 : ℝ) 1 × {v : {v : Fin 3 → ℝ // v ≠ 0} //
      ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U},
      Set.Icc (0 : ℝ) 1 × U) :=
    ⟨Prod.map id q0, continuous_id.prodMap q0.continuous⟩
  have hqp : Topology.IsQuotientMap qp :=
    (IsOpenQuotientMap.id.prodMap hq0).isQuotientMap
  let lift : C(Set.Icc (0 : ℝ) 1 × {v : {v : Fin 3 → ℝ // v ≠ 0} //
      ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U}, U) := by
    let F := fun z : Set.Icc (0 : ℝ) 1 × {v : {v : Fin 3 → ℝ // v ≠ 0} //
        ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U} =>
      apm_t01A01_retraction_homotopy_aux_vec z.1 z.2.1.1
    have hxy : ∀ z : Set.Icc (0 : ℝ) 1 × {v : {v : Fin 3 → ℝ // v ≠ 0} //
        ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U},
        (![z.2.1.1 0, z.2.1.1 1] : Fin 2 → ℝ) ≠ 0 := by
      intro z
      exact apm_t01A01_retraction_homotopy_aux_xy z.2.1.1 z.2.1.2 z.2.2
    refine ⟨fun z => ⟨Projectivization.mk ℝ (F z)
      (apm_t01A01_retraction_homotopy_aux_vec_ne z.1 z.2.1.1 (hxy z)),
      apm_t01A01_retraction_homotopy_aux_ne_q0 z.1 z.2.1.1 (hxy z)⟩, ?_⟩
    apply Continuous.subtype_mk
    change Continuous (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 ∘
      fun z => ⟨F z, apm_t01A01_retraction_homotopy_aux_vec_ne z.1 z.2.1.1 (hxy z)⟩)
    apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 2).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    fin_cases j
    · exact ((continuous_apply 0).comp continuous_subtype_val).comp
        (continuous_subtype_val.comp continuous_snd)
    · exact ((continuous_apply 1).comp continuous_subtype_val).comp
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_fst).mul
        (((continuous_apply 2).comp continuous_subtype_val).comp
          (continuous_subtype_val.comp continuous_snd))
  have hfac : Function.FactorsThrough lift qp := by
    intro a b hab
    apply Subtype.ext
    change Projectivization.mk ℝ
      (apm_t01A01_retraction_homotopy_aux_vec a.1 a.2.1.1) _ =
      Projectivization.mk ℝ
      (apm_t01A01_retraction_homotopy_aux_vec b.1 b.2.1.1) _
    apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    have hs := congrArg Prod.fst hab
    change a.1 = b.1 at hs
    have hv := congrArg Prod.snd hab
    change q0 a.2 = q0 b.2 at hv
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _ a.2.1.2 b.2.1.2).mp
      (congrArg Subtype.val hv)
    refine ⟨c, ?_⟩
    rw [hs]
    funext j
    fin_cases j
    · simpa [apm_t01A01_retraction_homotopy_aux_vec] using congrFun hc 0
    · simpa [apm_t01A01_retraction_homotopy_aux_vec] using congrFun hc 1
    · have hc2 := congrFun hc 2
      change (c : ℝ) * b.2.1.1 2 = a.2.1.1 2 at hc2
      change (c : ℝ) * (b.1.1 * b.2.1.1 2) =
        b.1.1 * a.2.1.1 2
      rw [← hc2]
      ring
  let H : C(Set.Icc (0 : ℝ) 1 × U, U) := hqp.lift lift hfac
  constructor
  · refine ⟨ContinuousMap.Homotopy.mk H ?_ ?_⟩
    · intro x
      obtain ⟨v, hv⟩ := ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 2 x.1
      have hx : x = ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v,
          hv ▸ x.2⟩ := Subtype.ext hv.symm
      rw [hx]
      apply Subtype.ext
      let vv : {v : {v : Fin 3 → ℝ // v ≠ 0} //
          ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U} :=
        ⟨v, hv ▸ x.2⟩
      have hh := DFunLike.congr_fun (hqp.lift_comp lift hfac)
        ((0 : Set.Icc (0 : ℝ) 1), vv)
      change H (0, ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v, _⟩) =
        lift (0, vv) at hh
      have hh' := congrArg Subtype.val hh
      change (H.toFun (0, ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v, _⟩)).1 =
        (lift (0, vv)).1 at hh'
      apply hh'.trans
      dsimp only [lift]
      have hqv : Projectivization.mk ℝ v.1 v.2 ≠ apm_t01A01_q0 := vv.2
      change Projectivization.mk ℝ
          (apm_t01A01_retraction_homotopy_aux_vec 0 v.1) _ =
        (i (r ⟨Projectivization.mk ℝ v.1 v.2, _⟩)).1
      rw [hr v.1 v.2 hqv (apm_t01A01_retraction_homotopy_aux_xy v.1 v.2 hqv)]
      rw [hi (![v.1 0, v.1 1])
        (apm_t01A01_retraction_homotopy_aux_xy v.1 v.2 hqv) (by
          intro h
          apply apm_t01A01_retraction_homotopy_aux_xy v.1 v.2 hqv
          funext j
          fin_cases j
          · exact congrFun h 0
          · exact congrFun h 1)]
      apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
      exact ⟨1, by ext j; fin_cases j <;> simp [apm_t01A01_retraction_homotopy_aux_vec]⟩
    · intro x
      obtain ⟨v, hv⟩ := ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 2 x.1
      have hx : x = ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v,
          hv ▸ x.2⟩ := Subtype.ext hv.symm
      rw [hx]
      apply Subtype.ext
      let vv : {v : {v : Fin 3 → ℝ // v ≠ 0} //
          ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v ∈ U} :=
        ⟨v, hv ▸ x.2⟩
      have hh := DFunLike.congr_fun (hqp.lift_comp lift hfac)
        ((1 : Set.Icc (0 : ℝ) 1), vv)
      change H (1, ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v, _⟩) =
        lift (1, vv) at hh
      have hh' := congrArg Subtype.val hh
      change (H.toFun (1, ⟨ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2 v, _⟩)).1 =
        (lift (1, vv)).1 at hh'
      apply hh'.trans
      apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
      exact ⟨1, by ext j; fin_cases j <;> simp [vv, apm_t01A01_retraction_homotopy_aux_vec]⟩
  · ext x
    obtain ⟨w, hw⟩ := ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 1 x
    subst x
    change r (i (Projectivization.mk ℝ w.1 w.2)) = Projectivization.mk ℝ w.1 w.2
    have h3 : (![w.1 0, w.1 1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro h; apply w.2; funext j; fin_cases j
      · exact congrFun h 0
      · exact congrFun h 1
    have h2 : (![(w.1 0), (w.1 1)] : Fin 2 → ℝ) ≠ 0 := by
      intro h; apply w.2; funext j; fin_cases j
      · exact congrFun h 0
      · exact congrFun h 1
    have hnq : Projectivization.mk ℝ (![w.1 0, w.1 1, 0]) h3 ≠
        apm_t01A01_q0 := by
      simpa [apm_t01A01_retraction_homotopy_aux_vec] using
        (apm_t01A01_retraction_homotopy_aux_ne_q0 ⟨0, by norm_num⟩
          (![w.1 0, w.1 1, 0]) (by simpa using h2))
    have hii : i (Projectivization.mk ℝ w.1 w.2) =
        ⟨Projectivization.mk ℝ (![w.1 0, w.1 1, 0]) h3,
          hnq⟩ := by
      apply Subtype.ext
      exact hi w.1 w.2 h3
    rw [hii, hr (![w.1 0, w.1 1, 0]) h3 hnq (by simpa using h2)]
    apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    exact ⟨1, by ext j; fin_cases j <;> simp⟩
-- END SEAT AREA

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
lemma apm_t01A01_projectiveLine_map_nullhomotopic_aux_homeomorph :
    Nonempty (apm_t01A01_RP1 ≃ₜ Circle) := by
  sorry

/-- Seat: the antipodal quotient `S² → RP²`, `x ↦ [x]`, is a continuous
surjective quotient map identifying antipodes (`ProjectiveQuotientDescent`). -/
theorem apm_t01A01_sphere_quotient :
    ∃ π : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, apm_t01A01_RP2),
      Function.Surjective π ∧ Topology.IsQuotientMap π ∧ (∀ x, π (-x) = π x) ∧
        ∀ x y, π x = π y → y = x ∨ y = -x := by
  sorry

/-- Seat: every map `S² → S¹` lifts through `Circle.exp` (`S²` is simply
connected: `ConstructionTargets.SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole`;
`Circle.exp` is a covering map, `isCoveringMap_exp`-style; lift by
`ConstructionTargets.CoveringLiftRestriction` / `IsCoveringMap.exists_lift`). -/
theorem apm_t01A01_sphere_circle_lift (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, Circle)) :
    ∃ h : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℝ), ∀ x, Circle.exp (h x) = g x := by
  sorry

/-- Seat: a map `RP² → S¹` has a real logarithm.  Lift `f ∘ π` to `h`; then
`h (-x) - h x ∈ 2πℤ` is continuous on the connected sphere, hence a constant
`c`, and applying it twice gives `c = -c`, so `c = 0`; `h` descends through the
quotient map `π`. -/
theorem apm_t01A01_projectivePlane_circle_log
    (π : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, apm_t01A01_RP2)) (hπs : Function.Surjective π)
    (hπq : Topology.IsQuotientMap π) (hπa : ∀ x, π (-x) = π x)
    (hπf : ∀ x y, π x = π y → y = x ∨ y = -x)
    (hlift : ∀ g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, Circle), ∃ h : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, ℝ), ∀ x, Circle.exp (h x) = g x)
    (f : C(apm_t01A01_RP2, Circle)) :
    ∃ k : C(apm_t01A01_RP2, ℝ), ∀ y, Circle.exp (k y) = f y := by
  sorry

/-- Seat: a circle-valued map with a real logarithm is homotopic to the
constant `1` (`H t y = exp ((1 - t) k y)`). -/
theorem apm_t01A01_circle_nullhomotopic_of_log {X : Type*} [TopologicalSpace X]
    (f : C(X, Circle)) (k : C(X, ℝ)) (hk : ∀ y, Circle.exp (k y) = f y) :
    ContinuousMap.Homotopic f (ContinuousMap.const X (1 : Circle)) := by
  sorry

lemma apm_t01A01_projectiveLine_map_nullhomotopic_aux_circle
    (f : C(apm_t01A01_RP2, Circle)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t01A01_RP2 (1 : Circle)) := by
  obtain ⟨π, hπs, hπq, hπa, hπf⟩ := apm_t01A01_sphere_quotient
  obtain ⟨k, hk⟩ := apm_t01A01_projectivePlane_circle_log π hπs hπq hπa hπf
    apm_t01A01_sphere_circle_lift f
  exact apm_t01A01_circle_nullhomotopic_of_log f k hk

theorem apm_t01A01_projectiveLine_map_nullhomotopic
    (h : C(apm_t01A01_RP2, apm_t01A01_RP1)) :
    ∃ p : apm_t01A01_RP1,
      ContinuousMap.Homotopic h
        (ContinuousMap.const apm_t01A01_RP2 p) := by
  obtain ⟨e⟩ := apm_t01A01_projectiveLine_map_nullhomotopic_aux_homeomorph
  let ef : C(apm_t01A01_RP1, Circle) := ⟨e, e.continuous⟩
  let ei : C(Circle, apm_t01A01_RP1) := ⟨e.symm, e.symm.continuous⟩
  have hh := apm_t01A01_projectiveLine_map_nullhomotopic_aux_circle
    (ef.comp h)
  refine ⟨e.symm 1, ?_⟩
  have hc := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl ei) hh
  have heq : ei.comp (ef.comp h) = h := by
    ext x
    exact e.symm_apply_apply (h x)
  rw [heq] at hc
  simpa [ei] using hc

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
