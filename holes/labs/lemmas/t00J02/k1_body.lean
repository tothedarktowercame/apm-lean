import Mathlib
import ConstructionTargets.RelativeSingularConnectingNaturality
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization

/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- The chart sign of a centred chart is unique. -/
theorem chartSign_unique
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    {s s' : ℤ} (hs : IsChartSign e α x hx hα0 s) (hs' : IsChartSign e α x hx hα0 s') :
    s = s' := by
  obtain ⟨b, hb1, hb2⟩ := hs
  obtain ⟨b', hb1', hb2'⟩ := hs'
  have h0target : (0 : E2) ∈ α.target := by rw [← hα0]; exact α.map_source hx
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 α.target (0 : E2) α.open_target h0target
  have hbb : b = b' := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target 0)) 2)
    rw [hb1, hb1']
  subst hbb
  have h := hb2.symm.trans hb2'
  obtain ⟨r, hrSign, hr⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e x
  rw [← hr, smul_smul, smul_smul] at h
  have := ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective 0 x h
  rcases hrSign with rfl | rfl
  · simpa using this
  · simpa using this

section K1final
open ConstructionTargets.DiskBoundaryHomology

/-- An injective continuous map from an open subset of the plane into the
surface is the inverse of a chart (invariance of domain). -/
theorem chartOfEmbedding {S : Type} [TopologicalSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (W : Set E2) (hW : IsOpen W) (hne : W.Nonempty) (g : W → S) (hg : Continuous g)
    (hinj : Function.Injective g) :
    ∃ lam : OpenPartialHomeomorph S E2, lam.target = W ∧
      ∀ w : W, g w ∈ lam.source ∧ lam (g w) = w := by
  have hgopen : IsOpenMap g := openSubset_isOpenMap hW hg hinj
  have hemb : Topology.IsOpenEmbedding g :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg hinj hgopen
  haveI : Nonempty W := hne.to_subtype
  let φ := hemb.toOpenPartialHomeomorph g
  let ψ := hW.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : W → E2)
  refine ⟨φ.symm.trans ψ, ?_, ?_⟩
  · ext v
    simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Subtype.range_coe_subtype,
      Set.mem_univ, and_true]
    rfl
  · intro w
    refine ⟨?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_univ, and_true]
      exact ⟨w, rfl⟩
    · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      have := hemb.toOpenPartialHomeomorph_left_inv g (x := w)
      simp only [φ] at this ⊢
      rw [this]
      rfl

lemma recentre_apply' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' z : S) : recentre α x' z = α z - α x' := by
  simp [recentre, OpenPartialHomeomorph.trans_apply, sub_eq_add_neg]

lemma addRight_neg_symm_apply (c p : E2) : (Homeomorph.addRight (-c)).symm p = p + c := by
  rw [Homeomorph.addRight_symm, neg_neg]; rfl

lemma recentre_symm_apply' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' : S) (p : E2) : (recentre α x').symm p = α.symm (p + α x') := by
  simp [recentre, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, addRight_neg_symm_apply]

lemma mem_recentre_target' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' : S) (p : E2) (h : p + α x' ∈ α.target) : p ∈ (recentre α x').target := by
  simp [recentre, addRight_neg_symm_apply]
  exact h

lemma complexToE2_sub (z w : ℂ) : complexToE2 z - complexToE2 w = complexToE2 (z - w) := by
  rw [complexToE2_eq_repr, complexToE2_eq_repr, complexToE2_eq_repr, map_sub]

lemma complexToE2_eq_zero (z : ℂ) : complexToE2 z = 0 ↔ z = 0 := by
  rw [complexToE2_eq_repr]; exact LinearIsometryEquiv.map_eq_zero_iff _

lemma flatC_sub_eq (t : Circle) (p0 p1 v : ℝ) :
    flatC t p0 (v + p1) - flatC t 0 v =
      (t : ℂ) * (Complex.exp ((p0 : ℂ) * Complex.I) - 1 - (p1 : ℂ)) := by
  simp only [flatC, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  push_cast; ring

/-- **K1.** An embedded disk lies on the side `κ · sα · dφ` of its boundary. -/
theorem disk_side_at_regular_boundary_point
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      ∀ (t : Circle) (α : OpenPartialHomeomorph S E2)
        (hx : D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) ∈ α.source)
        (hα0 : α (D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t)) = 0)
        (sα : ℤ) (hsα : IsChartSign e α _ hx hα0 sα)
        (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hball : Metric.ball (0 : E2) ρ ⊆ α.target)
        (φ : ℝ → ℝ) (dφ : ℤ)
        (hdφ : (dφ = 1 ∧ StrictMonoOn φ (Set.Ioo (-δ) δ)) ∨
          (dφ = -1 ∧ StrictAntiOn φ (Set.Ioo (-δ) δ)))
        (hγα : ∀ r ∈ Set.Ioo (-δ) δ,
          D (ConstructionTargets.DiskBoundaryHomology.circleToDisk (t * Circle.exp r)) ∈ α.source ∧
          α (D (ConstructionTargets.DiskBoundaryHomology.circleToDisk (t * Circle.exp r))) =
            horizontal (φ r))
        (hk : ∀ p ∈ Metric.ball (0 : E2) ρ,
          (α.symm p ∈ Set.range (D ∘ ConstructionTargets.DiskBoundaryHomology.circleToDisk) ↔
            p 1 = 0)),
        ∃ η > 0, ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk,
          dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η → ‖(a : ℂ)‖ < 1 →
            D a ∈ α.source ∧ ‖α (D a)‖ < ρ ∧ 0 < ((κ * sα * dφ : ℤ) : ℝ) * (α (D a)) 1 := by
  obtain ⟨δD, κD, hκD, hδt, hDδ, hsD⟩ := exists_diskChart e D hD hDemb
  refine ⟨κD, hκD, ?_⟩
  intro t α hx hα0 sα hsα ρ δ hρ hδ hball φ dφ hdφ hγα hk
  obtain ⟨σ, hσ, η, hη, hside⟩ :=
    disk_side_aux_one_side D hD hDemb.injective t α hx hα0 ρ hρ hk
  suffices hσeq : σ = κD * sα * dφ by
    refine ⟨η, hη, fun a ha han => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hside a ha han
    exact ⟨h1, h2, by rw [← hσeq]; exact h3⟩
  obtain ⟨ε, hε, hε2, F, hFinj, hF0, hFup, hF, hG, hH⟩ :=
    k1_reflected_extension D hD hDemb.injective t α hα0 δ hδ φ dφ hdφ hγα σ hσ η hη
      (fun a h1 h2 => ⟨(hside a h1 h2).1, (hside a h1 h2).2.2⟩)
  have hdφ1 : dφ = 1 ∨ dφ = -1 := by
    rcases hdφ with ⟨h, _⟩ | ⟨h, _⟩
    exacts [Or.inl h, Or.inr h]
  -- the sign of α at its centre is ±1
  have hsα1 : sα = 1 ∨ sα = -1 := by
    obtain ⟨s0, hs0, hs0'⟩ := exists_chartSign e α _ hx hα0
    rw [chartSign_unique e α _ hx hα0 hsα hs0']; exact hs0
  -- box, ball
  let U := k1Box ε
  have hUo : IsOpen U := k1Box_isOpen ε
  have h0U : (0 : E2) ∈ U := k1Box_zero ε hε
  have hcoord : ∀ (p : E2) (i : Fin 2), |p i| ≤ ‖p‖ := fun p i => by
    have := PiLp.norm_apply_le p i; simpa [Real.norm_eq_abs] using this
  let B := Metric.ball (0 : E2) ε
  have hBU : B ⊆ U := fun p hp => by
    have hp' : ‖p‖ < ε := by simpa [B] using hp
    exact ⟨lt_of_le_of_lt (hcoord p 0) hp', lt_of_le_of_lt (hcoord p 1) hp'⟩
  have h0B : (0 : E2) ∈ B := Metric.mem_ball_self hε
  have hFz : ∀ p ∈ U, F p = 0 ↔ p = 0 := fun p hp =>
    ⟨fun h => hFinj hp h0U (h.trans hF0.symm), fun h => h ▸ hF0⟩
  -- degree dφ σ at 0
  have hzU : ∀ p : U, F p = 0 ↔ (p : E2) = 0 := fun p => hFz p p.2
  have hzdU : ∀ p : U, diagonalMap dφ σ p = 0 ↔ (p : E2) = 0 :=
    fun p => diagonalMap_zero_iff dφ σ hdφ1 hσ p
  have hmodel : diskSideSignedModel U dφ σ = restrictedMap U (diagonalMap dφ σ) := by
    ext p i; fin_cases i <;> rfl
  have hdeg0U : IsLocalDegreeTwo U F hzU (dφ * σ) := by
    obtain ⟨c, hc1, hc2⟩ := diagonal_localDegree U hUo h0U dφ σ hdφ1 hσ hzdU
    refine ⟨c, hc1, ?_⟩
    have e1 := relMap_congr (neighborhoodDeletedPoint U (0 : E2)) _ _ hmodel hG
      (by intro p hp h; exact hp ((hzdU p).mp h))
    calc _ = HomologicalComplex.homologyMap
          (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
            (restrictedMap U F) hF) 2 c := rfl
      _ = _ := by rw [hH, e1]; exact hc2
  have hzB : ∀ p : B, F p = 0 ↔ (p : E2) = 0 := fun p => hFz p (hBU p.2)
  have hdegB := (localDegreeTwo_iff_of_subset U B hUo Metric.isOpen_ball h0B hBU F hzU hzB _).mp
    hdeg0U
  have hrec0 : recentred F 0 = F := by ext p i; simp [recentred, hF0]
  have hza : ∀ p : B, recentred F 0 p = 0 ↔ (p : E2) = 0 := by rw [hrec0]; exact hzB
  have hdegB0 : IsLocalDegreeTwo B (recentred F 0) hza (dφ * σ) := by
    revert hza; rw [hrec0]; intro hza; exact hdegB
  -- the point a on the inward normal and the small ball Vb
  let a : E2 := EuclideanSpace.single 1 (ε / 2)
  have ha0 : a 0 = 0 := by simp [a]
  have ha1 : a 1 = ε / 2 := by simp [a]
  have hanorm : ‖a‖ = ε / 2 := by
    simp [a, EuclideanSpace.norm_single, abs_of_pos hε]
  let Vb := Metric.ball (0 : E2) (ε / 4)
  have hVbB : ∀ u ∈ Vb, a + u ∈ B := fun u hu => by
    have hu' : ‖u‖ < ε / 4 := by simpa [Vb] using hu
    show a + u ∈ Metric.ball (0 : E2) ε
    rw [mem_ball_zero_iff]
    calc ‖a + u‖ ≤ ‖a‖ + ‖u‖ := norm_add_le _ _
      _ < ε := by rw [hanorm]; linarith
  have hVbpos : ∀ u ∈ Vb, 0 < (a + u) 1 := fun u hu => by
    have hu' : ‖u‖ < ε / 4 := by simpa [Vb] using hu
    have h1 := hcoord u 1
    have : (a + u) 1 = ε / 2 + u 1 := by rw [PiLp.add_apply, ha1]
    rw [this]; linarith [neg_abs_le (u 1)]
  have h0Vb : (0 : E2) ∈ Vb := Metric.mem_ball_self (by linarith)
  have haB : a ∈ B := by simpa using hVbB 0 h0Vb
  have haU : a ∈ U := hBU haB
  have ha1pos : 0 < a 1 := by rw [ha1]; linarith
  -- the inverse chart near a
  let W := Metric.ball a (ε / 4)
  have hWV : ∀ w ∈ W, w - a ∈ Vb := fun w hw => by
    simpa [Vb, W, dist_eq_norm] using hw
  have hWU : ∀ w ∈ W, w ∈ U := fun w hw => by
    have := hBU (hVbB _ (hWV w hw)); simpa using this
  have hWpos : ∀ w ∈ W, 0 < w 1 := fun w hw => by
    have := hVbpos _ (hWV w hw); simpa using this
  have hmW : ∀ w : W, flatC t (w.1 0) (w.1 1) ∈ Disk := fun w =>
    (hFup w.1 (hWU w.1 w.2) (hWpos w.1 w.2)).fst
  let g : W → S := fun w => D ⟨flatC t (w.1 0) (w.1 1), hmW w⟩
  have hg : Continuous g := by
    apply hD.comp
    apply Continuous.subtype_mk
    unfold flatC
    have h0 : Continuous fun w : W => ((w.1 0 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val)
    have h1 : Continuous fun w : W => ((w.1 1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_subtype_val)
    fun_prop
  have hbox0 : ∀ w ∈ U, |w 0| ≤ 1 := fun w hw => by
    have := hw.1; linarith
  have hginj : Function.Injective g := by
    intro w w' h
    have h1 := congrArg Subtype.val (hDemb.injective h)
    obtain ⟨hu, hv⟩ := flatC_injective t (hbox0 _ (hWU _ w.2)) (hbox0 _ (hWU _ w'.2)) h1
    apply Subtype.ext
    ext i; fin_cases i
    · exact hu
    · exact hv
  have haW : a ∈ W := Metric.mem_ball_self (by linarith)
  obtain ⟨lam, hlamt, hlam⟩ := chartOfEmbedding W Metric.isOpen_ball ⟨a, haW⟩ g hg hginj
  let y := g ⟨a, haW⟩
  have hy : y ∈ lam.source := (hlam _).1
  have hlamy : lam y = a := (hlam _).2
  have hlamsymm : ∀ w : W, lam.symm w = g w := fun w => by
    have h := lam.left_inv (hlam w).1
    rw [(hlam w).2] at h; exact h
  -- facts about y
  obtain ⟨hma, hFa, hnorma, hdista⟩ := hFup a haU ha1pos
  have hyD : y = D ⟨flatC t (a 0) (a 1), hma⟩ := rfl
  have hyα : y ∈ α.source := by rw [hyD]; exact (hside _ hdista hnorma).1
  have hyρ : α y ∈ Metric.ball (0 : E2) ρ := by
    rw [mem_ball_zero_iff, hyD]; exact (hside _ hdista hnorma).2.1
  have hyδ : y ∈ δD.source := by rw [hyD]; exact (hDδ _ hnorma).1
  -- the three centred charts at y
  let lc := recentre lam y
  let β := recentre α y
  let γ := recentre δD y
  have hlc_src := mem_recentre_source lam y hy
  have hβ_src := mem_recentre_source α y hyα
  have hγ_src := mem_recentre_source δD y hyδ
  obtain ⟨sl, hsl1, hsl⟩ := exists_chartSign e lc y hlc_src (recentre_self lam y)
  have hsβ : IsChartSign e β y hβ_src (recentre_self α y) sα :=
    isChartSign_recentre e α _ hx hα0 ρ hball y hyα hyρ sα hsα
  have hsγ : IsChartSign e γ y hγ_src (recentre_self δD y) κD :=
    isChartSign_recentre_of_at e δD y hyδ κD (hsD y hyδ)
  -- Vb lies in lc.target, and lc.symm is g shifted by a
  have hVbW : ∀ p ∈ Vb, a + p ∈ W := fun p hp => by
    show a + p ∈ Metric.ball a (ε / 4)
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa [Vb] using hp
  have hVbt : Vb ⊆ lc.target := fun p hp => by
    apply mem_recentre_target'
    rw [hlamy, hlamt, add_comm]; exact hVbW p hp
  have hlcsymm : ∀ p (hp : p ∈ Vb), lc.symm p = g ⟨a + p, hVbW p hp⟩ := fun p hp => by
    rw [recentre_symm_apply', hlamy, add_comm]
    exact hlamsymm ⟨a + p, hVbW p hp⟩
  have hgval : ∀ p (hp : p ∈ Vb),
      g ⟨a + p, hVbW p hp⟩ = D ⟨flatC t ((a + p) 0) ((a + p) 1), hmW ⟨a + p, hVbW p hp⟩⟩ :=
    fun p hp => rfl
  -- first transition: lc → γ is the flattening map
  have hflat : ∀ p ∈ Vb, flatRecentred t p = γ (lc.symm p) := fun p hp => by
    have hint : ‖flatC t ((a + p) 0) ((a + p) 1)‖ < 1 :=
      (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1
    rw [hlcsymm p hp, recentre_apply', hgval p hp, (hDδ _ hint).2, hyD, (hDδ _ hnorma).2]
    change complexToE2 _ = complexToE2 (flatC t ((a + p) 0) ((a + p) 1)) -
      complexToE2 (flatC t (a 0) (a 1))
    rw [complexToE2_sub, PiLp.add_apply, PiLp.add_apply, ha0, ha1, zero_add, flatC_sub_eq]
  have hVb_strip : ∀ p ∈ Vb, |p 0| < 1 := fun p hp => by
    have : ‖p‖ < ε / 4 := by simpa [Vb] using hp
    linarith [hcoord p 0]
  have hz1 : ∀ p : Vb, flatRecentred t p = 0 ↔ (p : E2) = 0 := fun p => by
    constructor
    · intro h
      change complexToE2 _ = 0 at h
      rw [complexToE2_eq_zero, ← flatC_sub_eq t (p.1 0) (p.1 1) 1, sub_eq_zero] at h
      obtain ⟨h0, h1⟩ := flatC_injective t (hVb_strip p p.2).le (by simp) h
      ext i; fin_cases i
      · simpa using h0
      · simp; linarith
    · intro h
      change complexToE2 _ = 0
      rw [h]; simp [complexToE2]
  have hdegM := flatRecentred_localDegree t Vb Metric.isOpen_ball h0Vb
    (fun p hp => lt_trans (hVb_strip p hp) (by linarith [Real.pi_gt_three])) hz1
  have hdegT1 := chart_transition_degree e lc γ y hlc_src (recentre_self lam y) hγ_src
    (recentre_self δD y) Vb Metric.isOpen_ball h0Vb hVbt
    (fun p hp => by
      rw [hlcsymm p hp]
      apply mem_recentre_source
      exact (hDδ _ (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1).1)
    (flatRecentred t) hflat hz1 sl κD hsl hsγ hκD
  have hslκ : sl * κD = 1 :=
    localDegreeTwo_unique Vb Metric.isOpen_ball h0Vb _ hz1 hdegT1 hdegM
  -- second transition: lc → β is the recentred extension
  have hrecF : ∀ p ∈ Vb, recentred F a p = β (lc.symm p) := fun p hp => by
    rw [hlcsymm p hp, recentre_apply', hgval p hp, hyD]
    obtain ⟨hm', hF', _, _⟩ := hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))
    change F (a + p) - F a = _
    rw [hF', hFa]
  have hz2 : ∀ p : Vb, recentred F a p = 0 ↔ (p : E2) = 0 := fun p => by
    change F (a + p) - F a = 0 ↔ _
    rw [sub_eq_zero]
    constructor
    · intro h
      have := hFinj (hBU (hVbB _ p.2)) haU h
      simpa using this
    · intro h; rw [h, add_zero]
  have hdegT2 := chart_transition_degree e lc β y hlc_src (recentre_self lam y) hβ_src
    (recentre_self α y) Vb Metric.isOpen_ball h0Vb hVbt
    (fun p hp => by
      rw [hlcsymm p hp]
      apply mem_recentre_source
      exact (hside _ (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.2
        (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1).1)
    (recentred F a) hrecF hz2 sl sα hsl hsβ hsα1
  -- K1-A: the degree is the same at 0 and at a
  have hA := localDegreeTwo_recentred_eq B Metric.isOpen_ball (convex_ball _ _).isPreconnected
    F (hFinj.mono hBU) 0 a h0B haB B Vb Metric.isOpen_ball Metric.isOpen_ball h0B h0Vb
    (fun u hu => by simpa using hu) hVbB hza hz2 (dφ * σ) (sl * sα) hdegB0 hdegT2
  rcases hσ with rfl | rfl <;> rcases hκD with rfl | rfl <;> rcases hdφ1 with rfl | rfl <;>
    rcases hsα1 with rfl | rfl <;> rcases hsl1 with rfl | rfl <;> omega

#print axioms disk_side_at_regular_boundary_point
end K1final
end t00J02_ModelProduct
