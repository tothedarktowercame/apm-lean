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

/-- LIBRARY: the complement of a point in `RP²` has the homotopy type of its
projective-line core.  A proof may choose coordinates sending `q` to a
coordinate line and descend the radial deformation through the projective
quotient. -/
theorem apm_t01A01_punctured_homotopyEquiv_projectiveLine
    (q : apm_t01A01_RP2) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {y : apm_t01A01_RP2 // y ≠ q} apm_t01A01_RP1) := by
  sorry

/-- LIBRARY: every map from `RP²` to the projective line is null-homotopic.
This is the `Z/2 → Z` lifting step, separated from the geometry of the
punctured target. -/
-- BEGIN SEAT AREA
theorem apm_t01A01_projectiveLine_map_nullhomotopic
    (h : C(apm_t01A01_RP2, apm_t01A01_RP1)) :
    ∃ p : apm_t01A01_RP1,
      ContinuousMap.Homotopic h
        (ContinuousMap.const apm_t01A01_RP2 p) := by
  sorry
-- END SEAT AREA

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
