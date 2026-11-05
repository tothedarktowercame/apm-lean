import Mathlib
import ConstructionTargets.RelativeSingularConnectingNaturality
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
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

abbrev Fch := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
  (AddCommGrpCat.of ℤ)

lemma chainHomology_eq_of_homotopic {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    {a b : C(P, Q)} (h : ContinuousMap.Homotopic a b) (n : ℕ) :
    HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom a)) n =
      HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom b)) n := by
  have := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    AddCommGrpCat (AddCommGrpCat.of ℤ) h n
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using this

lemma chainHomology_isIso_of_section {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (q : C(P, Q)) (s : C(Q, P)) (hqs : q.comp s = ContinuousMap.id Q)
    (hsq : ContinuousMap.Homotopic (s.comp q) (ContinuousMap.id P)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom q)) n) := by
  refine ⟨⟨HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom s)) n, ?_, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom q ≫ TopCat.ofHom s = TopCat.ofHom (s.comp q) := rfl
    rw [this, chainHomology_eq_of_homotopic hsq n]
    rw [show TopCat.ofHom (ContinuousMap.id P) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom s ≫ TopCat.ofHom q = TopCat.ofHom (q.comp s) := rfl
    rw [this, hqs, show TopCat.ofHom (ContinuousMap.id Q) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

/-- Relative homotopy invariance for maps of pairs. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) {f₀ f₁ : C(X, Y)}
    (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B)
    (h₀ : Set.MapsTo f₀ A B) (h₁ : Set.MapsTo f₁ A B) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSingularMap A B f₀ h₀) n =
      HomologicalComplex.homologyMap (relativeSingularMap A B f₁ h₁) n := by
  let A' : Set (X × unitInterval) := A ×ˢ univ
  let p : C(X × unitInterval, X) := ContinuousMap.fst
  have hp : Set.MapsTo p A' A := fun q hq => hq.1
  let ι : unitInterval → C(X, X × unitInterval) := fun t =>
    ⟨fun x => (x, t), continuous_id.prodMk continuous_const⟩
  have hι : ∀ t, Set.MapsTo (ι t) A A' := fun t x hx => ⟨hx, trivial⟩
  let Hc : C(X × unitInterval, Y) :=
    ⟨fun q => H (q.2, q.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hHc : Set.MapsTo Hc A' B := fun q hq => hH q.2 q.1 hq.1
  -- p is an isomorphism on relative homology
  have hpiso : ∀ m, IsIso (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) m) := by
    intro m
    -- the deformation retraction of the cylinder onto its bottom
    have hdef : ∀ {Z : Set X},
        ContinuousMap.Homotopic
          ((⟨fun z : (Z ×ˢ (univ : Set unitInterval) : Set _) =>
              (⟨((z : X × unitInterval).1, 0), ⟨z.2.1, trivial⟩⟩ :
                (Z ×ˢ (univ : Set unitInterval) : Set _)),
            by fun_prop⟩ : C(_, _)))
          (ContinuousMap.id _) := by
      intro Z
      refine ⟨{ toFun := fun r => ⟨((r.2 : X × unitInterval).1,
                  ⟨(r.1 : ℝ) * ((r.2 : X × unitInterval).2 : ℝ),
                    unitInterval.mul_mem r.1.2 (r.2 : X × unitInterval).2.2⟩),
                  ⟨r.2.2.1, trivial⟩⟩
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp
                map_one_left := by intro z; ext <;> simp }⟩
    have hdefX : ContinuousMap.Homotopic ((ι 0).comp p) (ContinuousMap.id _) := by
      refine ⟨{ toFun := fun r => ((r.2).1,
                  ⟨(r.1 : ℝ) * ((r.2).2 : ℝ), unitInterval.mul_mem r.1.2 (r.2).2.2⟩)
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp [ι, p]
                map_one_left := by intro z; ext <;> simp }⟩
    apply relativeSingularMap_homologyMap_isIso
    · exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) m
    · exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX m
    · intro j _
      exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) j
    · intro j _
      exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX j
  have hsec : ∀ t, HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n =
      inv (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) n) := by
    intro t
    haveI := hpiso n
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp A A' A (ι t) p (hι t) hp (by
        intro x hx; exact hx)]
    have : p.comp (ι t) = ContinuousMap.id X := by ext; rfl
    have hcongr : ∀ (F G : C(X, X)) (hFG : F = G) hF hG,
        relativeSingularMap A A F hF = relativeSingularMap A A G hG := by
      intro F G hFG _ _; subst hFG; rfl
    rw [hcongr _ _ this _ (fun x hx => hx), relativeSingularMap_id,
      HomologicalComplex.homologyMap_id]
  have hfac : ∀ t (f : C(X, Y)) (hf : Set.MapsTo f A B), Hc.comp (ι t) = f →
      HomologicalComplex.homologyMap (relativeSingularMap A B f hf) n =
        HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n ≫
          HomologicalComplex.homologyMap (relativeSingularMap A' B Hc hHc) n := by
    intro t f hf hfe
    subst hfe
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularMap_comp]
  rw [hfac 0 f₀ h₀ (by ext x; simp [Hc, ι]), hfac 1 f₁ h₁ (by ext x; simp [Hc, ι]),
    hsec 0, hsec 1]

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelCoherence

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.RelativeSingularHomologyHomotopy

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Relative H₂ map, with the map of pairs displayed explicitly. -/
abbrev transportMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) 2

lemma transportMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (hgf : MapsTo (g.comp f) A C) (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) hgf a :=
  ConcreteCategory.congr_hom (relativeSingularHomologyMap_comp A B C f g hf hg hgf 2) a

/-- The model local generator of `E2` at `p`. -/
abbrev G (p : E2) : (RelativeSingularChains (deletedPoint p)).homology 2 :=
  ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) p

def translate (v : E2) : C(E2, E2) := ⟨fun x => x + v, by fun_prop⟩

lemma translate_mapsTo (p v : E2) : MapsTo (translate v) (deletedPoint p) (deletedPoint (p + v)) := by
  intro x hx h
  apply hx
  change x + v = p + v at h
  exact add_right_cancel h

lemma ambientChartMap_apply (p : E2) (u : ConstructionTargets.HigherChartLocalGenerator.D 0) :
    (ConstructionTargets.HigherChartLocalGenerator.ambientChartMap (k := 0) p u : E2) =
      ConstructionTargets.HigherChartLocalGenerator.chartRadius (k := 0) p • (u : E2) + p := by
  change (chartAt (ConstructionTargets.HigherChartLocalGenerator.E 0) p).symm
      (ConstructionTargets.HigherChartLocalGenerator.chartRadius (k := 0) p • (u : E2) +
        chartAt (ConstructionTargets.HigherChartLocalGenerator.E 0) p p) = _
  simp

/-- Translation carries the model local generator at `p` to the one at `p + v`. -/
theorem translate_G (p v : E2) :
    transportMap (deletedPoint p) (deletedPoint (p + v)) (translate v) (translate_mapsTo p v) (G p) =
      G (p + v) := by
  open ConstructionTargets.HigherChartLocalGenerator in
  have h1 := transportMap_comp (P 0) (deletedPoint p) (deletedPoint (p + v))
    (ambientChartMap (k := 0) p) (translate v) (ambientChartMap_mapsTo (k := 0) p)
    (translate_mapsTo p v) ((translate_mapsTo p v).comp (ambientChartMap_mapsTo (k := 0) p))
    (ConstructionTargets.HigherModelLocalHomology.generator 0)
  change transportMap _ _ _ _ (transportMap (P 0) (deletedPoint p) (ambientChartMap (k := 0) p)
      (ambientChartMap_mapsTo (k := 0) p) (ConstructionTargets.HigherModelLocalHomology.generator 0)) =
    transportMap (P 0) (deletedPoint (p + v)) (ambientChartMap (k := 0) (p + v))
      (ambientChartMap_mapsTo (k := 0) (p + v)) (ConstructionTargets.HigherModelLocalHomology.generator 0)
  rw [h1]
  let r0 := chartRadius (k := 0) p
  let r1 := chartRadius (k := 0) (p + v)
  have hr0 : 0 < r0 := chartRadius_pos (k := 0) p
  have hr1 : 0 < r1 := chartRadius_pos (k := 0) (p + v)
  let H : ContinuousMap.Homotopy ((translate v).comp (ambientChartMap (k := 0) p))
      (ambientChartMap (k := 0) (p + v)) :=
    { toFun := fun q => ((1 - (q.1 : ℝ)) * r0 + (q.1 : ℝ) * r1) • ((q.2 : D 0) : E2) + (p + v)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro u
        change (((1 - 0) * r0 + 0 * r1) • ((u : D 0) : E2) + (p + v)) =
          (ambientChartMap (k := 0) p u : E2) + v
        rw [ambientChartMap_apply]
        simp only [sub_zero, one_mul, zero_mul, add_zero]
        abel
      map_one_left := by
        intro u
        change (((1 - 1) * r0 + 1 * r1) • ((u : D 0) : E2) + (p + v)) =
          (ambientChartMap (k := 0) (p + v) u : E2)
        rw [ambientChartMap_apply]
        simp only [sub_self, zero_mul, one_mul, zero_add]
        rfl }
  have hH : ∀ t : unitInterval, ∀ u ∈ P 0, H (t, u) ∈ deletedPoint (p + v) := by
    intro t u hu h
    have hu0 : ((u : D 0) : E2) ≠ 0 := hu
    have hc : 0 < (1 - (t : ℝ)) * r0 + (t : ℝ) * r1 := by
      have := t.2.1; have := t.2.2
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [← h0]; simpa using hr0
      · nlinarith
    change ((1 - (t : ℝ)) * r0 + (t : ℝ) * r1) • ((u : D 0) : E2) + (p + v) = p + v at h
    have h' : ((1 - (t : ℝ)) * r0 + (t : ℝ) * r1) • ((u : D 0) : E2) = 0 := by
      simpa using h
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hc.ne'
    · exact hu0 h''
  exact congrArg (fun m => m (ConstructionTargets.HigherModelLocalHomology.generator 0))
    (relativeSingularHomologyMap_eq_of_homotopy (P 0) (deletedPoint (p + v)) H hH _ _ 2)

lemma compl_mapsTo_deletedPoint {X : Type} [TopologicalSpace X] (K : Set X) (q : X) (hq : q ∈ K) :
    MapsTo (ContinuousMap.id X) Kᶜ (deletedPoint q) := by
  intro x hx h
  exact hx (by change x = q at h; rw [h]; exact hq)

lemma compl_mapsTo_compl {X : Type} [TopologicalSpace X] (K L : Set X) (h : L ⊆ K) :
    MapsTo (ContinuousMap.id X) Kᶜ Lᶜ := fun _ hx hl => hx (h hl)

/-- Restricting a closed-ball class to `p + v` is the translate of its restriction to `p`,
for `v` at most half the radius. -/
theorem res_translate (p v : E2) (R : ℝ) (hv : 2 * ‖v‖ ≤ R)
    (ω : (RelativeSingularChains (Metric.closedBall p R)ᶜ).homology 2) :
    transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (by
          rw [Metric.mem_closedBall, dist_eq_norm]; simp; linarith [norm_nonneg v])) ω =
      transportMap (deletedPoint p) (deletedPoint (p + v)) (translate v) (translate_mapsTo p v)
        (transportMap (Metric.closedBall p R)ᶜ (deletedPoint p) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by linarith [norm_nonneg v]))) ω) := by
  have hR2 : Metric.closedBall p (R - ‖v‖) ⊆ Metric.closedBall p R :=
    Metric.closedBall_subset_closedBall (by linarith [norm_nonneg v])
  have hq2 : p + v ∈ Metric.closedBall p (R - ‖v‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; simp; linarith
  have htr : MapsTo (translate v) (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ := by
    intro x hx hx2
    apply hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx2 ⊢
    change ‖x + v - p‖ ≤ R - ‖v‖ at hx2
    have : ‖x - p‖ ≤ ‖x + v - p‖ + ‖v‖ := by
      calc ‖x - p‖ = ‖(x + v - p) - v‖ := by congr 1; abel
        _ ≤ ‖x + v - p‖ + ‖v‖ := norm_sub_le _ _
    linarith
  -- translation is homotopic to the identity as a map of these pairs
  let H : ContinuousMap.Homotopy (ContinuousMap.id E2) (translate v) :=
    { toFun := fun q => q.2 + (q.1 : ℝ) • v
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [translate] }
  have hH : ∀ t : unitInterval, ∀ x ∈ (Metric.closedBall p R)ᶜ,
      H (t, x) ∈ (Metric.closedBall p (R - ‖v‖))ᶜ := by
    intro t x hx hx2
    apply hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx2 ⊢
    change ‖x + (t : ℝ) • v - p‖ ≤ R - ‖v‖ at hx2
    have ht : ‖(t : ℝ) • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
      exact mul_le_of_le_one_left (norm_nonneg v) t.2.2
    have : ‖x - p‖ ≤ ‖x + (t : ℝ) • v - p‖ + ‖(t : ℝ) • v‖ := by
      calc ‖x - p‖ = ‖(x + (t : ℝ) • v - p) - (t : ℝ) • v‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hhom := congrArg (fun m => m ω)
    (relativeSingularHomologyMap_eq_of_homotopy (Metric.closedBall p R)ᶜ
      (Metric.closedBall p (R - ‖v‖))ᶜ H hH (compl_mapsTo_compl _ _ hR2) htr 2)
  have hp1 : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self (by linarith [norm_nonneg v])
  have hq1 : p + v ∈ Metric.closedBall p R := hR2 hq2
  have htrq : MapsTo (translate v) (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) :=
    (translate_mapsTo p v).comp (compl_mapsTo_deletedPoint _ _ hp1)
  calc transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ hq1) ω
      = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (ContinuousMap.id E2) (compl_mapsTo_compl _ _ hR2) ω) :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (ContinuousMap.id E2)
          (compl_mapsTo_compl _ _ hR2) (compl_mapsTo_deletedPoint _ _ hq2)
          (compl_mapsTo_deletedPoint _ _ hq1) ω).symm
    _ = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (translate v) htr ω) := congrArg _ hhom
    _ = transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (translate v) htrq ω :=
        transportMap_comp _ _ _ (translate v) (ContinuousMap.id E2) htr
          (compl_mapsTo_deletedPoint _ _ hq2) htrq ω
    _ = _ :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (translate v)
          (compl_mapsTo_deletedPoint _ _ hp1) (translate_mapsTo p v) htrq ω).symm

end t00J02_ModelCoherence
