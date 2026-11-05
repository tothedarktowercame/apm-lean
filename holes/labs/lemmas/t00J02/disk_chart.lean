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
    (ωc : (RelativeSingularChains (Metric.closedBall p R)ᶜ).homology 2) :
    transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (by
          rw [Metric.mem_closedBall, dist_eq_norm]; simp; linarith [norm_nonneg v])) ωc =
      transportMap (deletedPoint p) (deletedPoint (p + v)) (translate v) (translate_mapsTo p v)
        (transportMap (Metric.closedBall p R)ᶜ (deletedPoint p) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by linarith [norm_nonneg v]))) ωc) := by
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
  have hhom := congrArg (fun m => m ωc)
    (relativeSingularHomologyMap_eq_of_homotopy (Metric.closedBall p R)ᶜ
      (Metric.closedBall p (R - ‖v‖))ᶜ H hH (compl_mapsTo_compl _ _ hR2) htr 2)
  have hp1 : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self (by linarith [norm_nonneg v])
  have hq1 : p + v ∈ Metric.closedBall p R := hR2 hq2
  have htrq : MapsTo (translate v) (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) :=
    (translate_mapsTo p v).comp (compl_mapsTo_deletedPoint _ _ hp1)
  calc transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ hq1) ωc
      = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (ContinuousMap.id E2) (compl_mapsTo_compl _ _ hR2) ωc) :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (ContinuousMap.id E2)
          (compl_mapsTo_compl _ _ hR2) (compl_mapsTo_deletedPoint _ _ hq2)
          (compl_mapsTo_deletedPoint _ _ hq1) ωc).symm
    _ = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (translate v) htr ωc) := congrArg _ hhom
    _ = transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (translate v) htrq ωc :=
        transportMap_comp _ _ _ (translate v) (ContinuousMap.id E2) htr
          (compl_mapsTo_deletedPoint _ _ hq2) htrq ωc
    _ = _ :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (translate v)
          (compl_mapsTo_deletedPoint _ _ hp1) (translate_mapsTo p v) htrq ωc).symm

end t00J02_ModelCoherence
-- Copied from Blueprint.lean (prelude through D2b, D1).
abbrev apm_t00j02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00j02_I2 := 𝓘(ℝ, apm_t00j02_E2)
abbrev apm_t00j02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00j02_hasGenusTwo (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t00j02_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00j02_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00j02_H k S)

def apm_t00j02_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t00j02_wrapsHandle {S : Type} [TopologicalSpace S]
    (c : C(Circle, S)) : Prop :=
  apm_t00j02_homologyMap 1 c ≠ 0

def apm_t00j02_transverse {S : Type} [TopologicalSpace S]
    [ChartedSpace apm_t00j02_E2 S]
    (f : S → S) (c : Circle → S) : Prop :=
  ∀ x z, f x = c z →
    LinearMap.range (mfderiv apm_t00j02_I2 apm_t00j02_I2 f x).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 1) apm_t00j02_I2 c z).toLinearMap = ⊤

abbrev apm_t00j02_componentsBoundDisks {S : Type} [TopologicalSpace S]
    (A : Set S) : Prop :=
  ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks A

def apm_t00j02_hasDegree {S : Type} [TopologicalSpace S]
    (f : C(S, S)) (degree : ℤ) : Prop :=
  ∃ e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ,
    ∀ x : apm_t00j02_H 2 S,
      e.hom (apm_t00j02_homologyMap 2 f x) = degree * e.hom x

abbrev t00J02_fiberRelativeHomology
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :=
  (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
    ({z : S | f z = y}ᶜ)).homology 2

noncomputable def t00J02_fiberRestriction
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S)
    (x : {x : S // f x = y}) :
    t00J02_fiberRelativeHomology f y ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))).homology 2 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({z : S | f z = y}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))
      (ContinuousMap.id S) (by
        intro z hz hzx
        have hzxe : z = (x : S) := by simpa using hzx
        subst z
        exact hz x.property)) 2

noncomputable def t00J02_fiberPushforward
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :
    t00J02_fiberRelativeHomology f y ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology 2 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({z : S | f z = y}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      f (by intro z hz; exact hz)) 2

noncomputable def t00J02_fiberCoordinates
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :
    t00J02_fiberRelativeHomology f y →
      ((x : {x : S // f x = y}) →
        (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))).homology 2) :=
  fun a x ↦ t00J02_fiberRestriction f y x a

/-- The chart-free local degree of `f` at an isolated point of the literal
fiber.  The class `a` is the coordinate basis vector in relative homology of
the whole finite fiber: it restricts to the localization of the global
fundamental class at `x` and to zero at every other fiber point.  Its
pushforward is `n` times the localized fundamental class at `y`. -/
def t00J02_IsLocalDegree
    {S : Type} [TopologicalSpace S] (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) (x : {x : S // f x = y}) (n : ℤ) : Prop :=
  ∃ a : t00J02_fiberRelativeHomology f y,
    t00J02_fiberRestriction f y x a =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap (x : S) 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e) ∧
    (∀ x' : {x : S // f x = y}, x' ≠ x →
      t00J02_fiberRestriction f y x' a = 0) ∧
    t00J02_fiberPushforward f y a = n •
      ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)

namespace t00J02_D1

abbrev H {X : Type} [TopologicalSpace X] (A : Set X) :=
  (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 2

noncomputable def restrict {X : Type} [TopologicalSpace X]
    {A B : Set X} (h : B ⊆ A) : H A ⟶ H B :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
      (ContinuousMap.id X) (fun _ hz hb ↦ hz (h hb))) 2

lemma restrict_comp {X : Type} [TopologicalSpace X]
    {A B C : Set X} (hBA : B ⊆ A) (hCB : C ⊆ B) (z : H A) :
    restrict hCB (restrict hBA z) = restrict (hCB.trans hBA) z := by
  have h := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
    Aᶜ Bᶜ Cᶜ (ContinuousMap.id X) (ContinuousMap.id X)
    (fun _ hz hb ↦ hz (hBA hb)) (fun _ hz hc ↦ hz (hCB hc))
    (fun _ hz hc ↦ hz (hBA (hCB hc))) 2
  exact congrArg (fun m ↦ m z) h

/-- Binary closed-support splitting: the restrictions from relative H₂ supported
on A ∪ B to H₂ supported on A and on B are jointly bijective when A and B are
closed and disjoint. This is the two-set relative Mayer--Vietoris theorem for
the open cover Aᶜ ∪ Bᶜ = X: its outer relative groups Hₙ(X,X) vanish, leaving
an isomorphism H₂(X,Aᶜ ∩ Bᶜ) → H₂(X,Aᶜ) × H₂(X,Bᶜ).
The existing closed-support joint-injectivity and gluing lemmas in
`CollaredConnectedSumHomology.BallCollar` prove the two halves. No manifold,
compactness, or finite-set decomposition is assumed.
Disjointness is necessary: for A=B={p} in R² the map is diagonal Z→Z², not
surjective. Closedness supplies the excisive open cover; no statement for
arbitrary non-excisive pairs is asserted. Empty supports cause no exception,
since Hₙ(X,X)=0. -/
lemma binary {X : Type} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    Function.Bijective (fun z : H (A ∪ B) ↦
      (restrict (show A ⊆ A ∪ B from subset_union_left) z,
       restrict (show B ⊆ A ∪ B from subset_union_right) z)) := by
  have hempty : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp hAB
  have hz (n : ℕ) : Subsingleton
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∩ B)ᶜ).homology n) := by
    apply AddCommGrpCat.subsingleton_of_isZero
    simpa only [hempty, compl_empty] using
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero X n
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint
      X A B hA hB 2 (hz 3) (u - v)
    · change restrict (show A ⊆ A ∪ B from subset_union_left) (u - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst huv)
    · change restrict (show B ⊆ A ∪ B from subset_union_right) (u - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd huv)
  · rintro ⟨u, v⟩
    obtain ⟨z, hzu, hzv⟩ :=
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue
        X A B hA hB 2 u v (@Subsingleton.elim _ (hz 2) _ _)
    exact ⟨z, Prod.ext hzu hzv⟩

noncomputable def coordinates {X : Type} [TopologicalSpace X] (A : Set X) :
    H A → ((x : A) → H ({x.1} : Set X)) :=
  fun z x ↦ restrict (singleton_subset_iff.mpr x.2) z

lemma finite_coordinates {X : Type} [TopologicalSpace X] [T2Space X]
    (A : Set X) (hA : A.Finite) : Function.Bijective (coordinates A) := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty =>
    have hz : CategoryTheory.Limits.IsZero (H (∅ : Set X)) := by
      simpa only [H, compl_empty] using
        ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero X 2
    letI : Subsingleton (H (∅ : Set X)) := AddCommGrpCat.subsingleton_of_isZero hz
    constructor
    · intro u v _
      exact Subsingleton.elim u v
    · intro g
      refine ⟨0, ?_⟩
      funext x
      exact False.elim x.2
  | @insert a A ha hA ih =>
    have hb := binary isClosed_singleton hA.isClosed
      (show Disjoint ({a} : Set X) A from disjoint_singleton_left.mpr ha)
    change Function.Bijective (fun z : H (insert a A) ↦
      (restrict (show {a} ⊆ insert a A from singleton_subset_iff.mpr (mem_insert a A)) z,
       restrict (subset_insert a A) z)) at hb
    constructor
    · intro u v huv
      apply hb.1
      apply Prod.ext
      · exact congrFun huv ⟨a, mem_insert a A⟩
      · apply ih.1
        funext x
        have he := congrFun huv (⟨x.1, mem_insert_of_mem a x.2⟩ : ↥(insert a A))
        simpa only [coordinates, restrict_comp] using he
    · intro g
      obtain ⟨v, hv⟩ := ih.2 (fun x : A ↦ g ⟨x.1, mem_insert_of_mem a x.2⟩)
      obtain ⟨u, hu⟩ := hb.2 (g ⟨a, mem_insert a A⟩, v)
      refine ⟨u, ?_⟩
      funext x
      rcases x with ⟨x, hx⟩
      rcases hx with rfl | hx
      · exact congrArg Prod.fst hu
      · have he := congrFun hv ⟨x, hx⟩
        have huB := congrArg Prod.snd hu
        dsimp only at huB
        dsimp only [coordinates] at he ⊢
        rw [← huB, restrict_comp] at he
        exact he

end t00J02_D1

/-- **D1 (finite-support excision, estimated 250--500 lines; LIBRARY).**  In
words: relative top homology supported on a finite fibre is recovered
bijectively by restricting to the point-local homology group at every fibre
point.

Why true: choose pairwise disjoint chart disks around the finite Hausdorff
fibre.  `LocalHomologyNeighborhoodExcision.neighborhoodInclusion_Hn_isIso`
identifies each disk-local group with its ambient point-local group;
`SingularExcision.relativeExcisionMap` removes the complement of the disks.
Finite Mayer--Vietoris, or the relative-chain direct sum for a finite disjoint
union, identifies the remaining relative group with the product of disk-local
groups.  For an empty fibre both sides are zero/singleton.  Finiteness and
Hausdorffness are essential for the disjoint disk choice. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D1
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (f : C(S, S)) (y : S) [Fintype {x : S // f x = y}] :
    Function.Bijective (t00J02_fiberCoordinates f y) := by
  have hf : ({x : S | f x = y} : Set S).Finite := by
    simpa using (Set.finite_range (fun x : {x : S // f x = y} ↦ (x : S)))
  exact t00J02_D1.finite_coordinates {x : S | f x = y} hf

/- **D2 (localization coefficient is a unit, LIBRARY).**  In words: at every
point `y` of a compact connected surface with `H₂ ≅ ℤ`, the localization of the
global generator is `±1` times the canonical chart generator of the point-local
group.  The existing `localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator`
gives some integer `r`; this leaf says `r` is a unit.  Why true: the
fundamental class of a closed connected orientable surface localizes to a
generator at every point (Hatcher Thm 3.26).  Connectedness is
needed: on two disjoint tori the localization of a class `(1,0)` vanishes at
points of the second torus (there `H₂ ≅ ℤ²`, so the hypothesis also fails).
(claude-14: replaces codex-15's D2a/D2b, which both reduced to
this coefficient.) -/
/-- **D2.1 (absolute localization coefficient transport, estimated 300--600
lines; LIBRARY).**  In words: on a path-connected surface, the absolute value
of the coefficient expressing a fixed global top class in the canonical
chart-local generator is independent of the point.

Why true: transport local homology classes along a path covered by finitely
many overlapping manifold charts.  On an overlap, the two chart generators
differ by the transition unit `±1`; naturality of `localizationMap` transports
the global class itself, so coefficients agree up to sign.  Chain the finite
overlap cover along a path.  Raw coefficients need not be equal because
`chartAt` may reverse orientation.  Path connectedness is essential: for two
disjoint tori the class `(1,0)` has coefficient one on the first component and
zero on the second. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y z : S) :
    |(ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient y| =
      |(ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient z| := by
  let D :=
    ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  let degree :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
      0 S e
  have hcoefficient (x : S) : D.localCoefficient x = degree x := by
    exact
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec
        0 e x (D.localCoefficient x) (D.localization_eq x)
  have hlocal : IsLocallyConstant (fun x : S ↦ (degree x).natAbs) := by
    exact
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant
        0 S e
  have hnat : (degree y).natAbs = (degree z).natAbs :=
    IsLocallyConstant.apply_eq_of_preconnectedSpace hlocal y z
  rw [hcoefficient y, hcoefficient z, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast hnat

/-- Compact-support reconstruction detects common divisors of all local
coefficients.  If an integer divides the localization coefficient of the
chosen global generator at every point, it divides the generator's global
coordinate `1`.  This is true by representing the global class by a finite
cycle, covering its compact support by finitely many chart domains, and using
excision to reconstruct the class from the corresponding local classes.
Estimated proof size: 220--400 lines. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point_aux_commonDivisor
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (d : ℤ)
    (hdiv : ∀ x : S, d ∣
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient x) : d ∣ 1 := by
  let D :=
    ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  obtain ⟨x, hx⟩ :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit
      0 S e
  have hcoefficient :
      D.localCoefficient x =
        ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
          0 S e x :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec
      0 e x (D.localCoefficient x) (D.localization_eq x)
  have hunit : IsUnit (D.localCoefficient x) := by
    rw [Int.isUnit_iff_natAbs_eq, hcoefficient]
    exact hx
  exact (hdiv x).trans (isUnit_iff_dvd_one.mp hunit)

/-- **D2.2 (one-point primitivity, estimated 350--700 lines; LIBRARY).**  In
words: the chosen generator of global `H₂ ≅ ℤ` localizes primitively at
at least one point of a compact connected boundaryless surface.

Why true: represent the inverse image of `1 : ℤ` under `e` by a finite
singular cycle.  If every point-local coefficient were divisible by a common
integer greater than one (or all were zero), finite chart excision and the
compact-support reconstruction of the global top class would make the global
cycle divisible by that integer in `H₂(S)`, contradicting that it maps to
`1`.  Equivalently this is the one-point normalization step in the manifold
fundamental-class theorem.  Compactness is essential for the finite
reconstruction, and the disconnected two-torus example shows why the result
must be paired with component transport rather than asserted componentwise
for an arbitrary global class. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) :
    ∃ z : S,
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
          S e).localCoefficient z = 1 ∨
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
          S e).localCoefficient z = -1 := by
  let D := ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  let z : S := Classical.choice (inferInstance : Nonempty S)
  have hdiv : ∀ x : S, D.localCoefficient z ∣ D.localCoefficient x := by
    intro x
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e x z
    rcases abs_eq_abs.mp habs with h | h
    · exact h ▸ dvd_refl _
    · rw [h]
      exact dvd_neg.mpr (dvd_refl _)
  have hone : D.localCoefficient z ∣ 1 :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point_aux_commonDivisor
      e (D.localCoefficient z) hdiv
  have hunit : IsUnit (D.localCoefficient z) := isUnit_iff_dvd_one.mpr hone
  exact ⟨z, Int.isUnit_eq_one_or hunit⟩

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∃ r : ℤ, (r = 1 ∨ r = -1) ∧
      r • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := by
  let D := ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  obtain ⟨z, hz | hz⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point e
  · refine ⟨D.localCoefficient y, ?_, D.localization_eq y⟩
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e y z
    rw [hz, abs_one] at habs
    change |D.localCoefficient y| = 1 at habs
    by_cases hnonneg : 0 ≤ D.localCoefficient y
    · left
      simpa [abs_of_nonneg hnonneg] using habs
    · right
      rw [abs_of_nonpos (le_of_not_ge hnonneg)] at habs
      omega
  · refine ⟨D.localCoefficient y, ?_, D.localization_eq y⟩
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e y z
    rw [hz, abs_neg, abs_one] at habs
    change |D.localCoefficient y| = 1 at habs
    by_cases hnonneg : 0 ≤ D.localCoefficient y
    · left
      simpa [abs_of_nonneg hnonneg] using habs
    · right
      rw [abs_of_nonpos (le_of_not_ge hnonneg)] at habs
      omega

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2a
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∀ b, ∃ n : ℤ, b = n •
      ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) := by
  intro b
  obtain ⟨r, hr, hloc⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e y
  obtain ⟨m, hm⟩ := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates (k := 0) y b
  refine ⟨m * r, ?_⟩
  rw [← hloc, smul_smul, ← hm]
  congr 1
  rcases hr with rfl | rfl <;> ring

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2b
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∀ n : ℤ, n • ConstructionTargets.ManifoldFundamentalClass.localizationMap
      y 2 (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
        (TopCat.of S) 2 e) = 0 → n = 0 := by
  intro n hn
  obtain ⟨r, hr, hloc⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e y
  rw [← hloc, smul_smul] at hn
  have h0 : (n * r) • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y =
      (0 : ℤ) • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y := by
    rw [hn, zero_smul]
  have hnr := ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
    0 y h0
  rcases hr with rfl | rfl <;> simpa using hnr


-- Copied from disc_model.lean.
namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def horizontal (u : ℝ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then u else 0)

lemma continuous_horizontal : Continuous horizontal := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [horizontal] using (continuous_id : Continuous (fun u : ℝ => u))
  · exact continuous_const

lemma horizontal_zero : horizontal 0 = 0 := by
  ext i
  simp [horizontal]

def horizontalSlice (U : Set E2) : Set ℝ := {u | horizontal u ∈ U}

def productMap (g : C(E2, ℝ)) : C(E2, E2) where
  toFun p := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if i = 0 then g p else p 1)
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa using g.continuous
    · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

def splitProductMap (g : C(E2, ℝ)) : C(E2, E2) :=
  productMap ⟨fun p => g (horizontal (p 0)),
    g.continuous.comp (by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi; intro i; fin_cases i
      · simpa [horizontal] using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
      · exact continuous_const)⟩

def sliceMap (U : Set E2) (g : C(E2, ℝ)) : C(horizontalSlice U, ℝ) where
  toFun u := g (horizontal u)
  continuous_toFun := g.continuous.comp <| by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa [horizontal] using
        (continuous_subtype_val : Continuous (fun u : horizontalSlice U => (u : ℝ)))
    · exact continuous_const

def restrictedMap (U : Set E2) (F : C(E2, E2)) : C(U, E2) :=
  F.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The degree of a map from an open neighborhood of the origin, expressed
exactly as in `t00J02_IsLocalDegree`: a neighborhood class restricts to the
standard ambient local generator and its pushforward is `n` times the target
generator. -/
def IsLocalDegreeTwo (U : Set E2) (F : C(E2, E2))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains (neighborhoodDeletedPoint U (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion U)
          (neighborhoodInclusion_mapsTo U 0)) 2 a =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (restrictedMap U F) (by
            intro p hp hFp
            exact hp ((hzero p).mp hFp))) 2 a =
      n • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2)


/-- Chart sign at `x` for a chart `α` centred at `x` (`α x = 0`): the class `b`
in `H₂(α.target, α.target ∖ 0)` that restricts to the standard local generator
of `E2` at `0` is carried by `α.symm` to `s` times the localized global
generator at `x`. -/
def chartInverseMap {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) : C(α.target, S) :=
  ⟨fun p => α.symm p, α.continuousOn_symm.restrict⟩

lemma chartInverseMap_mapsTo {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x : S) (_hx : x ∈ α.source) (hα0 : α x = 0) :
    Set.MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target (0 : E2))
      (deletedPoint x) := by
  intro p hp hpx
  apply hp
  have h1 : α (α.symm p) = (p : E2) := α.right_inv p.2
  change α.symm p = x at hpx
  rw [hpx, hα0] at h1
  exact h1.symm

def IsChartSign {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target 0)) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0)) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)

/-- `α` shifted so that `x'` goes to `0`. -/
def recentre {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2) (x' : S) :
    OpenPartialHomeomorph S E2 :=
  α.trans (Homeomorph.addRight (-(α x'))).toOpenPartialHomeomorph

lemma mem_recentre_source {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x' : S) (hx' : x' ∈ α.source) :
    x' ∈ (recentre α x').source := by
  simpa [recentre] using hx'

lemma recentre_self {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x' : S) :
    recentre α x' x' = 0 := by
  simp [recentre, OpenPartialHomeomorph.trans_apply]

lemma chartInverseMap_mapsTo_at {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x : S) (_hx : x ∈ α.source) :
    Set.MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target (α x))
      (deletedPoint x) := by
  intro p hp hpx
  apply hp
  have h1 : α (α.symm p) = (p : E2) := α.right_inv p.2
  change α.symm p = x at hpx
  rw [hpx] at h1
  exact h1.symm

/-- Chart sign of `α` at an arbitrary point `x` of its source (not necessarily
centred): the class of `H₂(α.target, α.target ∖ α x)` restricting to the model
local generator at `α x` is carried by `α.symm` to `s` times the localized global
generator at `x`. -/
def IsChartSignAt {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target (α x))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (α x))
          (deletedPoint (α x)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target (α x))) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (α x) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (α x))
          (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo_at α x hx)) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)


#print axioms mem_recentre_source
#print axioms recentre_self

section L1ball
open t00J02_ModelCoherence
open ConstructionTargets.CollaredConnectedSumHomology.BallCollar

local notation "restrictIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
local notation "homeoIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
local notation "ballModel" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model

/-- In an open `U ⊆ E2` containing a closed ball, restriction from the ball to an
interior point is an isomorphism on relative `H₂`. -/
lemma subtype_ball_res_isIso (U : Set E2) (hU : IsOpen U) (c : E2) (ρ : ℝ)
    (hK : Metric.closedBall c ρ ⊆ U) (p : E2) (hp : p ∈ Metric.ball c ρ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap {u : U | u.1 ∉ Metric.closedBall c ρ} {u : U | u.1 ∉ ({p} : Set E2)}
        (ContinuousMap.id U)
        (fun _ hx hb => hx (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hp) hb))) 2) :=
  (restrictIff U hU (Metric.closedBall c ρ) {p} Metric.isClosed_closedBall isClosed_singleton hK
    (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hp)) 2 two_pos).mp
    (ballModel 0 c p ρ (Metric.mem_ball.mp hp))

/-- Restriction from `α.symm '' (closed ball)` to a point of it is an isomorphism on `H₂(S, ·)`. -/
lemma chart_ball_res_isIso {S : Type} [TopologicalSpace S] [T2Space S]
    (α : OpenPartialHomeomorph S E2) (c : E2) (ρ : ℝ)
    (hK : Metric.closedBall c ρ ⊆ α.target) (x : S) (hx : x ∈ α.source)
    (hxK : α x ∈ Metric.ball c ρ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (α.symm '' Metric.closedBall c ρ)ᶜ (deletedPoint x)
        (ContinuousMap.id S)
        (fun y hy hyx => hy (by
          have h : y = x := hyx
          rw [h]
          exact ⟨α x, Metric.ball_subset_closedBall hxK, α.left_inv hx⟩))) 2) := by
  have hcpt : IsCompact (α.symm '' Metric.closedBall c ρ) :=
    (isCompact_closedBall c ρ).image_of_continuousOn (α.continuousOn_symm.mono hK)
  have hAU : α.symm '' Metric.closedBall c ρ ⊆ α.source := by
    rintro _ ⟨w, hw, rfl⟩; exact α.map_target (hK hw)
  have hxA : x ∈ α.symm '' Metric.closedBall c ρ :=
    ⟨α x, Metric.ball_subset_closedBall hxK, α.left_inv hx⟩
  refine (restrictIff α.source α.open_source (α.symm '' Metric.closedBall c ρ) {x}
    hcpt.isClosed isClosed_singleton hAU (Set.singleton_subset_iff.mpr hxA) 2 two_pos).mpr ?_
  refine (homeoIff α.toHomeomorphSourceTarget _ _
    {w : α.target | w.1 ∉ Metric.closedBall c ρ} {w : α.target | w.1 ∉ ({α x} : Set E2)}
    ?_ ?_ _ (fun _ hw hb => hw (Set.singleton_subset_iff.mpr
      (Metric.ball_subset_closedBall hxK) hb)) 2).mpr ?_
  · intro u
    simp only [Set.mem_setOf_eq, not_iff_not]
    change (u : S) ∈ α.symm '' Metric.closedBall c ρ ↔ α u ∈ Metric.closedBall c ρ
    constructor
    · rintro ⟨w, hw, hwu⟩
      rw [← hwu, α.right_inv (hK hw)]; exact hw
    · intro h
      exact ⟨α u, h, α.left_inv u.2⟩
  · intro u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_iff_not]
    change (u : S) = x ↔ α u = α x
    constructor
    · intro h; rw [h]
    · intro h; exact α.injOn u.2 hx h
  · exact subtype_ball_res_isIso α.target α.open_target c ρ hK (α x) hxK

/-- Model coherence: a closed-ball class restricting to the model generator at its centre
restricts to the model generator at every point within half the radius. -/
lemma model_coherent (p q : E2) (R : ℝ) (h : 2 * ‖q - p‖ ≤ R)
    (w : (RelativeSingularChains (Metric.closedBall p R)ᶜ).homology 2)
    (hp : transportMap (Metric.closedBall p R)ᶜ (deletedPoint p) (ContinuousMap.id E2)
      (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by linarith [norm_nonneg (q - p)]))) w = G p) :
    transportMap (Metric.closedBall p R)ᶜ (deletedPoint q) (ContinuousMap.id E2)
      (compl_mapsTo_deletedPoint _ _ (by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith [norm_nonneg (q - p)])) w = G q := by
  obtain ⟨v, rfl⟩ : ∃ v, q = p + v := ⟨q - p, by abel⟩
  have hv : 2 * ‖v‖ ≤ R := by simpa using h
  rw [res_translate p v R hv w, hp, translate_G]

lemma tcomp_auto {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) (hg.comp hf) a :=
  transportMap_comp A B C f g hf hg (hg.comp hf) a

local notation "factorLoc" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor

/-- One step of chart-sign constancy: from `x` to a point `x'` whose chart coordinate is
within half the radius of a closed ball around `α x` contained in the chart target. -/
lemma isChartSignAt_step {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x x' : S) (hx : x ∈ α.source) (hx' : x' ∈ α.source)
    (ρ : ℝ) (hρ : 0 < ρ) (hK : Metric.closedBall (α x) ρ ⊆ α.target)
    (hv : 2 * ‖α x' - α x‖ ≤ ρ) (s : ℤ) (h : IsChartSignAt e α x hx s) :
    IsChartSignAt e α x' hx' s := by
  obtain ⟨b, hb1, hb2⟩ := h
  have hxK : α x ∈ Metric.ball (α x) ρ := Metric.mem_ball_self hρ
  have hx'K : α x' ∈ Metric.ball (α x) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖α x' - α x‖ < ρ := by
      rcases eq_or_lt_of_le (norm_nonneg (α x' - α x)) with h0 | h0
      · rw [← h0]; exact hρ
      · linarith
    exact this
  let K := Metric.closedBall (α x) ρ
  let KT : Set α.target := {u | u.1 ∉ K}
  have hKT : ∀ q ∈ Metric.ball (α x) ρ, MapsTo (ContinuousMap.id α.target) KT
      (neighborhoodDeletedPoint α.target q) :=
    fun q hq _ hu hb => hu (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hq) hb)
  let resT := fun (q : E2) (hq : q ∈ Metric.ball (α x) ρ) =>
    transportMap KT (neighborhoodDeletedPoint α.target q) (ContinuousMap.id α.target) (hKT q hq)
  have hiso : IsIso (resT (α x) hxK) :=
    subtype_ball_res_isIso α.target α.open_target (α x) ρ hK (α x) hxK
  let wT := (asIso (resT (α x) hxK)).inv b
  have hwT : resT (α x) hxK wT = b := ConcreteCategory.congr_hom (asIso (resT (α x) hxK)).inv_hom_id b
  -- the class in `E2`
  have hinclK : MapsTo (neighborhoodInclusion α.target) KT Kᶜ := fun _ hu => hu
  let w := transportMap KT Kᶜ (neighborhoodInclusion α.target) hinclK wT
  have hres : ∀ q (hq : q ∈ Metric.ball (α x) ρ),
      transportMap (neighborhoodDeletedPoint α.target q) (deletedPoint q)
        (neighborhoodInclusion α.target) (neighborhoodInclusion_mapsTo α.target q) (resT q hq wT) =
      transportMap Kᶜ (deletedPoint q) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.ball_subset_closedBall hq)) w := by
    intro q hq
    rw [tcomp_auto, tcomp_auto]
    rfl
  refine ⟨resT (α x') hx'K wT, ?_, ?_⟩
  · have h0 : transportMap Kᶜ (deletedPoint (α x)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.ball_subset_closedBall hxK)) w = G (α x) := by
      rw [← hres (α x) hxK, hwT]; exact hb1
    have := model_coherent (α x) (α x') ρ hv w h0
    rw [← hres (α x') hx'K] at this
    exact this
  · -- the class in `S`
    let A := α.symm '' K
    have hAm : MapsTo (chartInverseMap α) KT Aᶜ := by
      intro u hu hA
      obtain ⟨k, hk, hku⟩ := hA
      apply hu
      have : k = u.1 := α.symm.injOn (by simpa using hK hk) (by simpa using u.2) hku
      rw [← this]; exact hk
    let W := transportMap KT Aᶜ (chartInverseMap α) hAm wT
    have hxA : ∀ y : S, y ∈ α.source → α y ∈ Metric.ball (α x) ρ → y ∈ A :=
      fun y hy hyb => ⟨α y, Metric.ball_subset_closedBall hyb, α.left_inv hy⟩
    have hresS : ∀ (y : S) (hy : y ∈ α.source) (hyb : α y ∈ Metric.ball (α x) ρ),
        transportMap (neighborhoodDeletedPoint α.target (α y)) (deletedPoint y) (chartInverseMap α)
          (chartInverseMap_mapsTo_at α y hy) (resT (α y) hyb wT) =
        transportMap Aᶜ (deletedPoint y) (ContinuousMap.id S)
          (compl_mapsTo_deletedPoint _ _ (hxA y hy hyb)) W := by
      intro y hy hyb
      rw [tcomp_auto, tcomp_auto]
      rfl
    let g := ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e
    let PK := HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ) 2 g
    have hloc : ∀ (y : S) (hyA : y ∈ A),
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2 g =
        transportMap Aᶜ (deletedPoint y) (ContinuousMap.id S)
          (compl_mapsTo_deletedPoint _ _ hyA) PK := by
      intro y hyA
      rw [factorLoc A y hyA 2]
      rfl
    have hWx : transportMap Aᶜ (deletedPoint x) (ContinuousMap.id S)
        (compl_mapsTo_deletedPoint _ _ (hxA x hx hxK)) (W - s • PK) = 0 := by
      rw [map_sub, map_zsmul, ← hresS x hx hxK, ← hloc x (hxA x hx hxK), hwT, hb2, sub_self]
    have hinj : W - s • PK = 0 := by
      haveI := chart_ball_res_isIso α (α x) ρ hK x hx hxK
      have hi := (ConcreteCategory.injective_of_mono_of_preservesPullback
        (HomologicalComplex.homologyMap
          (relativeSingularMap Aᶜ (deletedPoint x) (ContinuousMap.id S)
            (compl_mapsTo_deletedPoint _ _ (hxA x hx hxK))) 2))
      exact hi (by rw [hWx, map_zero])
    have hW : W = s • PK := sub_eq_zero.mp hinj
    rw [hresS x' hx' hx'K, hW, map_zsmul, ← hloc x' (hxA x' hx' hx'K)]

lemma isChartSignAt_congr {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2)
    (y y' : S) (h : y = y') (hy : y ∈ α.source) (hy' : y' ∈ α.source) (s : ℤ)
    (hs : IsChartSignAt e α y hy s) : IsChartSignAt e α y' hy' s := by
  subst h; exact hs

/-- **L1b.** A chart's sign is the same at all points of a ball in its target. -/
theorem isChartSignAt_constant_on_ball {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (c : E2) (R : ℝ) (hR : Metric.ball c R ⊆ α.target)
    (x x' : S) (hx : x ∈ α.source) (hx' : x' ∈ α.source)
    (hxR : α x ∈ Metric.ball c R) (hx'R : α x' ∈ Metric.ball c R)
    (s : ℤ) (h : IsChartSignAt e α x hx s) : IsChartSignAt e α x' hx' s := by
  let B := Metric.ball c R
  have hsrc : ∀ q : B, α.symm q ∈ α.source := fun q => α.map_target (hR q.2)
  let P : B → Prop := fun q => IsChartSignAt e α (α.symm q) (hsrc q) s
  -- radius of a closed ball around `q` inside `B`
  have hrad : ∀ q : B, 0 < (R - dist (q : E2) c) / 2 := fun q => by
    have := Metric.mem_ball.mp q.2; linarith
  have hsub : ∀ (q : E2) (r : ℝ), dist q c + r < R → Metric.closedBall q r ⊆ α.target := by
    intro q r hr y hy
    apply hR
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hy
    linarith [dist_triangle y q c]
  have hstep : ∀ (q q' : B), dist (q' : E2) q < (R - dist (q : E2) c) / 8 → P q → P q' := by
    intro q q' hd hq
    have hq0 : α (α.symm (q : E2)) = q := α.right_inv (hR q.2)
    have hq1 : α (α.symm (q' : E2)) = q' := α.right_inv (hR q'.2)
    have hρ := hrad q
    refine isChartSignAt_step e α (α.symm q) (α.symm q') (hsrc q) (hsrc q')
      ((R - dist (q : E2) c) / 2) hρ ?_ ?_ s hq
    · rw [hq0]; apply hsub; linarith
    · rw [hq0, hq1, ← dist_eq_norm]; linarith
  have hlc : IsLocallyConstant P := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro q
    have hρ := hrad q
    rw [Metric.eventually_nhds_iff]
    refine ⟨(R - dist (q : E2) c) / 16, by linarith, ?_⟩
    intro q' hd
    have hd' : dist (q' : E2) q < (R - dist (q : E2) c) / 16 := hd
    apply propext
    constructor
    · intro hq'
      apply hstep q' q _ hq'
      have h1 := dist_triangle (q' : E2) q c
      have h2 : dist (q : E2) q' = dist (q' : E2) q := dist_comm _ _
      rw [h2]
      have h3 := hrad q
      linarith
    · intro hq
      exact hstep q q' (by linarith) hq
  haveI : PreconnectedSpace B :=
    Subtype.preconnectedSpace (convex_ball c R).isPreconnected
  have hP := hlc.apply_eq_of_preconnectedSpace ⟨α x, hxR⟩ ⟨α x', hx'R⟩
  have h0 : P ⟨α x, hxR⟩ :=
    isChartSignAt_congr e α x _ (α.left_inv hx).symm hx _ s h
  have h1 : P ⟨α x', hx'R⟩ := hP ▸ h0
  exact isChartSignAt_congr e α _ x' (α.left_inv hx') _ hx' s h1

/-- The chart-sign predicate at a target point `q`, generic in `q`. -/
def ChartSignPt {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2) (x : S)
    (q : E2) (m : MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target q) (deletedPoint x))
    (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target q)).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target q)
          (deletedPoint q) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target q)) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) q ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target q)
          (deletedPoint x) (chartInverseMap α) m) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)

lemma chartSignPt_congr {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2) (x : S)
    (q₁ q₂ : E2) (h : q₁ = q₂) (m₁ m₂) (s : ℤ) :
    ChartSignPt e α x q₁ m₁ s → ChartSignPt e α x q₂ m₂ s := by
  subst h; exact id

lemma isChartSign_iff_at {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2)
    (x : S) (hx : x ∈ α.source) (hα0 : α x = 0) (s : ℤ) :
    IsChartSign e α x hx hα0 s ↔ IsChartSignAt e α x hx s :=
  ⟨chartSignPt_congr e α x 0 (α x) hα0.symm _ _ s,
   chartSignPt_congr e α x (α x) 0 hα0 _ _ s⟩

lemma translate_G' (p v q : E2) (h : p + v = q)
    (m : MapsTo (t00J02_ModelCoherence.translate v) (deletedPoint p) (deletedPoint q)) :
    transportMap (deletedPoint p) (deletedPoint q) (t00J02_ModelCoherence.translate v) m (G p) = G q := by
  subst h; exact translate_G p v

/-- **L1a.** Re-centring a chart at `x'` keeps its sign at `x'`. -/
theorem isChartSign_recentre_of_at {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x' : S) (hx' : x' ∈ α.source) (s : ℤ)
    (h : IsChartSignAt e α x' hx' s) :
    IsChartSign e (recentre α x') x' (mem_recentre_source α x' hx') (recentre_self α x') s := by
  obtain ⟨b, hb1, hb2⟩ := h
  let a := α x'
  have htgt : ∀ w ∈ α.target, w + -a ∈ (recentre α x').target := by
    intro w hw
    simp only [recentre, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Set.univ_inter, Set.mem_preimage]
    rw [Homeomorph.addRight_symm]
    simpa [a] using hw
  let sh : C(α.target, (recentre α x').target) :=
    ⟨fun w => ⟨w.1 + -a, htgt w.1 w.2⟩, (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  have hsh : MapsTo sh (neighborhoodDeletedPoint α.target a)
      (neighborhoodDeletedPoint (recentre α x').target 0) := by
    intro w hw h0
    apply hw
    change w.1 + -a = 0 at h0
    change w.1 = a
    exact (add_neg_eq_zero.mp h0)
  refine ⟨transportMap _ _ sh hsh b, ?_, ?_⟩
  · have hsq : (neighborhoodInclusion (recentre α x').target).comp sh =
        (t00J02_ModelCoherence.translate (-a)).comp (neighborhoodInclusion α.target) := by
      ext w; rfl
    have hm : MapsTo (t00J02_ModelCoherence.translate (-a)) (deletedPoint a) (deletedPoint 0) := by
      intro y hy h0; apply hy; change y + -a = 0 at h0; exact add_neg_eq_zero.mp h0
    calc _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint (0 : E2))
          ((neighborhoodInclusion (recentre α x').target).comp sh)
          ((neighborhoodInclusion_mapsTo _ 0).comp hsh) b := tcomp_auto _ _ _ _ _ _ _ b
      _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint (0 : E2))
          ((t00J02_ModelCoherence.translate (-a)).comp (neighborhoodInclusion α.target))
          (hm.comp (neighborhoodInclusion_mapsTo _ a)) b := by simp only [hsq]
      _ = transportMap (deletedPoint a) (deletedPoint (0 : E2)) (t00J02_ModelCoherence.translate (-a)) hm
          (transportMap _ _ (neighborhoodInclusion α.target)
            (neighborhoodInclusion_mapsTo _ a) b) := (tcomp_auto _ _ _ _ _ _ _ b).symm
      _ = _ := by
          have hb1' : transportMap _ _ (neighborhoodInclusion α.target)
            (neighborhoodInclusion_mapsTo _ a) b = G a := hb1
          rw [hb1']
          exact translate_G' a (-a) 0 (add_neg_cancel a) hm
  · have hsq : (chartInverseMap (recentre α x')).comp sh = chartInverseMap α := by
      ext w
      change α.symm ((Homeomorph.addRight (-α x')).symm (w.1 + -α x')) = α.symm w.1
      rw [Homeomorph.addRight_symm]
      simp
    calc _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint x')
          ((chartInverseMap (recentre α x')).comp sh)
          ((chartInverseMap_mapsTo _ x' (mem_recentre_source α x' hx') (recentre_self α x')).comp hsh) b :=
            tcomp_auto _ _ _ _ _ _ _ b
      _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint x')
          (chartInverseMap α) (chartInverseMap_mapsTo_at α x' hx') b := by simp only [hsq]
      _ = _ := hb2

/-- **L1.** Re-centring a centred chart at any point of a ball in its target keeps its sign. -/
theorem isChartSign_recentre {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (R : ℝ) (hR : Metric.ball (0 : E2) R ⊆ α.target)
    (x' : S) (hx' : x' ∈ α.source) (hx'R : α x' ∈ Metric.ball (0 : E2) R)
    (s : ℤ) (hs : IsChartSign e α x hx hα0 s) :
    IsChartSign e (recentre α x') x' (mem_recentre_source α x' hx') (recentre_self α x') s := by
  have hxR : α x ∈ Metric.ball (0 : E2) R := by
    rw [hα0]
    exact Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx'R))
  exact isChartSign_recentre_of_at e α x' hx' s
    (isChartSignAt_constant_on_ball e α 0 R hR x x' hx hx' hxR hx'R s
      ((isChartSign_iff_at e α x hx hα0 s).mp hs))

/-- The standard real-coordinate identification of the complex plane with the
two-dimensional Euclidean model. -/
def complexToE2 (z : ℂ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]

@[simp] lemma complexToE2_apply (z : ℂ) (i : Fin 2) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (complexToE2 z) i = ![z.re, z.im] i := by
  simp [complexToE2]

lemma complexToE2_injective : Function.Injective complexToE2 := by
  intro z w h
  apply Complex.ext
  · have := congrArg (fun q => (EuclideanSpace.equiv (Fin 2) ℝ) q 0) h
    simpa using this
  · have := congrArg (fun q => (EuclideanSpace.equiv (Fin 2) ℝ) q 1) h
    simpa using this

lemma continuous_complexToE2 : Continuous complexToE2 := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using Complex.continuous_re
  · simpa using Complex.continuous_im

/-- The interior of an embedded closed disk is open in a boundaryless
surface.  This is the exact invariance-of-domain input needed to construct
`exists_diskChart`; it is independent of all homology and orientation data. -/
theorem diskInterior_isOpenEmbedding
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    Topology.IsOpenEmbedding (fun a : {a : ConstructionTargets.DiskBoundaryHomology.Disk //
      ‖(a : ℂ)‖ < 1} => D a.1) := by
  sorry

/-- An embedded closed disk supplies its interior chart, and the orientation
coefficient of that chart is constant on the connected unit ball. -/
theorem exists_diskChart
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    ∃ (δ : OpenPartialHomeomorph S E2) (κD : ℤ), (κD = 1 ∨ κD = -1) ∧
      δ.target = Metric.ball (0 : E2) 1 ∧
      (∀ a : ConstructionTargets.DiskBoundaryHomology.Disk, ‖(a : ℂ)‖ < 1 →
        D a ∈ δ.source ∧ δ (D a) = complexToE2 a) ∧
      ∀ (y : S) (hy : y ∈ δ.source), IsChartSignAt e δ y hy κD := by
  sorry

end L1ball

#print axioms t00J02_ModelProduct.isChartSign_recentre
#print axioms t00J02_ModelProduct.isChartSignAt_constant_on_ball

end t00J02_ModelProduct
