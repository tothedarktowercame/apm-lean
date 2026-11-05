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

/-- The analogous one-dimensional local degree on the horizontal slice. -/
def IsLocalDegreeOne (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))).homology 1,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
          (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1 a =
      ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap
          (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ)) (sliceMap U g) (by
            intro u hu hgu
            have hprod : productMap g
                (⟨horizontal u, u.property⟩ : U) = 0 := by
              ext i
              fin_cases i
              · simpa [productMap] using hgu
              · simp [productMap, horizontal]
            have horigin := (hzero ⟨horizontal u, u.property⟩).mp hprod
            exact hu (by
              have horigin' := congrArg (fun p : E2 => p 0) horigin
              simpa [horizontal] using horigin'))) 1 a =
      n • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0

/-- A continuous real function with an isolated zero has one of the four possible
sign patterns on a sufficiently small punctured interval.  This is the
one-dimensional IVT input for reducing a local-degree calculation to the four
standard models `u`, `-u`, `u^2`, and `-u^2`. -/
theorem isolatedZero_sign_trichotomy
    (W : Set ℝ) (hW : IsOpen W) (h0W : (0 : ℝ) ∈ W)
    (h : C(ℝ, ℝ)) (hzero : ∀ u ∈ W, h u = 0 ↔ u = 0) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) δ ⊆ W ∧
      (((∀ u ∈ Set.Ioo (-δ) 0, h u < 0) ∧
          (∀ u ∈ Set.Ioo 0 δ, 0 < h u)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, 0 < h u) ∧
          (∀ u ∈ Set.Ioo 0 δ, h u < 0)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, 0 < h u) ∧
          (∀ u ∈ Set.Ioo 0 δ, 0 < h u)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, h u < 0) ∧
          (∀ u ∈ Set.Ioo 0 δ, h u < 0))) := by
  rcases Metric.isOpen_iff.mp hW 0 h0W with ⟨δ, hδ, hball⟩
  have hsub : Set.Ioo (-δ) δ ⊆ W := by
    intro u hu
    apply hball
    simpa [Real.dist_eq, abs_lt] using hu
  have hne (u : ℝ) (hu : u ∈ Set.Ioo (-δ) δ) (hu0 : u ≠ 0) : h u ≠ 0 := by
    intro hz
    exact hu0 ((hzero u (hsub hu)).mp hz)
  have hsame (a b : ℝ) (ha : a ∈ Set.Ioo (-δ) δ)
      (hb : b ∈ Set.Ioo (-δ) δ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
      (hab : 0 < a ↔ 0 < b) :
      (0 < h a ↔ 0 < h b) := by
    have forward (a b : ℝ) (ha : a ∈ Set.Ioo (-δ) δ)
        (hb : b ∈ Set.Ioo (-δ) δ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
        (hab : 0 < a ↔ 0 < b) (hpa : 0 < h a) : 0 < h b := by
      by_contra hn
      have hnb : h b < 0 := lt_of_le_of_ne (le_of_not_gt hn) (hne b hb hb0)
      have hzmem : (0 : ℝ) ∈ Set.uIcc (h a) (h b) := by
        simp [Set.mem_uIcc, hpa.le, hnb.le]
      rcases (intermediate_value_uIcc h.continuous.continuousOn hzmem) with
        ⟨z, hzab, hz⟩
      have hzI : z ∈ Set.Ioo (-δ) δ := by
        rcases Set.mem_uIcc.mp hzab with hzab | hzab
        · exact ⟨lt_of_lt_of_le ha.1 hzab.1, lt_of_le_of_lt hzab.2 hb.2⟩
        · exact ⟨lt_of_lt_of_le hb.1 hzab.1, lt_of_le_of_lt hzab.2 ha.2⟩
      have hz0 : z ≠ 0 := by
        rcases lt_or_gt_of_ne ha0 with hneg | hpos
        · have hbnot : ¬ 0 < b := fun hbpos =>
            (not_lt_of_ge hneg.le) (hab.mpr hbpos)
          have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbnot) hb0
          rcases Set.mem_uIcc.mp hzab with hzab | hzab
          · exact ne_of_lt (lt_of_le_of_lt hzab.2 hbneg)
          · exact ne_of_lt (lt_of_le_of_lt hzab.2 hneg)
        · have hbpos : 0 < b := hab.mp hpos
          rcases Set.mem_uIcc.mp hzab with hzab | hzab
          · exact ne_of_gt (lt_of_lt_of_le hpos hzab.1)
          · exact ne_of_gt (lt_of_lt_of_le hbpos hzab.1)
      exact hne z hzI hz0 hz
    exact ⟨forward a b ha hb ha0 hb0 hab,
      forward b a hb ha hb0 ha0 hab.symm⟩
  let p : ℝ := δ / 2
  let q : ℝ := -δ / 2
  have hp : p ∈ Set.Ioo 0 δ := by dsimp [p]; constructor <;> linarith
  have hq : q ∈ Set.Ioo (-δ) 0 := by dsimp [q]; constructor <;> linarith
  have hpI : p ∈ Set.Ioo (-δ) δ := ⟨by dsimp [p]; linarith, hp.2⟩
  have hqI : q ∈ Set.Ioo (-δ) δ := ⟨hq.1, by dsimp [q]; linarith⟩
  have right_pos_or_neg : 0 < h p ∨ h p < 0 := lt_or_gt_of_ne (hne p hpI (ne_of_gt hp.1)).symm
  have left_pos_or_neg : 0 < h q ∨ h q < 0 := lt_or_gt_of_ne (hne q hqI (ne_of_lt hq.2)).symm
  refine ⟨δ, hδ, hsub, ?_⟩
  rcases left_pos_or_neg with hl | hl <;> rcases right_pos_or_neg with hr | hr
  · exact Or.inr (Or.inr (Or.inl ⟨fun u hu => (hsame u q
      ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mpr hl,
      fun u hu => (hsame u p ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mpr hr⟩))
  · exact Or.inr (Or.inl ⟨fun u hu => (hsame u q
      ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mpr hl,
      fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hr.le) ((hsame u p
        ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mp hh))
        (hne u ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ (ne_of_gt hu.1))⟩)
  · exact Or.inl ⟨fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hl.le)
      ((hsame u q ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mp hh))
      (hne u ⟨hu.1, lt_trans hu.2 hδ⟩ (ne_of_lt hu.2)),
      fun u hu => (hsame u p ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mpr hr⟩
  · exact Or.inr (Or.inr (Or.inr ⟨fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hl.le)
      ((hsame u q ⟨hu.1, lt_trans hu.2 hδ⟩ hqI
        (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mp hh))
        (hne u ⟨hu.1, lt_trans hu.2 hδ⟩ (ne_of_lt hu.2)),
      fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hr.le) ((hsame u p
        ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mp hh))
        (hne u ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ (ne_of_gt hu.1))⟩))

def identityScalar : C(E2, ℝ) where
  toFun p := p 0
  continuous_toFun := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0

def positiveFoldScalar : C(E2, ℝ) where
  toFun p := (p 0) ^ 2
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2

def negativeFoldScalar : C(E2, ℝ) where
  toFun p := -((p 0) ^ 2)
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2).neg

lemma identity_productMap_zero_iff (U : Set E2) (p : U) :
    productMap identityScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h; ext i; fin_cases i
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 0) h
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, identityScalar]

lemma positiveFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap positiveFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : (p.1 0) ^ 2 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 0) h
    have h1 : p.1 1 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i; fin_cases i <;> simp [eq_zero_of_pow_eq_zero h0, h1]
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, positiveFoldScalar]

lemma negativeFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap negativeFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : -((p.1 0) ^ 2) = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 0) h
    have h1 : p.1 1 = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i; fin_cases i <;> simp [eq_zero_of_pow_eq_zero (neg_eq_zero.mp h0), h1]
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, negativeFoldScalar]

/-- The horizontal identity has one-dimensional local degree one. -/
theorem identity_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U identityScalar (identity_productMap_zero_iff U) 1 := by
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [one_smul]
  have hs : sliceMap U identityScalar = neighborhoodInclusion (horizontalSlice U) := by
    ext u; rfl
  have hcongr : ∀ (F G : C(horizontalSlice U, ℝ)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) F hF =
      relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) G hG := by
    intro F G hFG _ _; subst hFG; rfl
  rw [hcongr _ _ hs _ (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)]
  exact ConcreteCategory.congr_hom (asIso ι).inv_hom_id _

/-- A map from the horizontal slice which avoids zero induces the zero map on
one-dimensional local homology, since it factors through the self-pair. -/
lemma sliceHomologyMap_eq_zero_of_avoids (U : Set E2)
    (G : C(horizontalSlice U, ℝ)) (hG : ∀ u, G u ≠ 0)
    (hGm : Set.MapsTo G (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) G hGm) 1 = 0 := by
  have hfac := relativeSingularMap_comp
    (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
    (Set.univ : Set (horizontalSlice U)) (deletedPoint (0 : ℝ))
    (ContinuousMap.id _) G (fun _ _ => trivial) (fun u _ => hG u) hGm
  show HomologicalComplex.homologyMap
    (relativeSingularMap _ _ (G.comp (ContinuousMap.id _)) hGm) 1 = 0
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  rw [(selfRelativeSingularHomology_isZero (horizontalSlice U) 1).eq_zero_of_tgt
    (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (Set.univ : Set (horizontalSlice U)) (ContinuousMap.id _) (fun _ _ => trivial)) 1),
    Limits.zero_comp]

lemma fold_slice_localDegree_zero
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (σ : ℝ) (hσ : σ ≠ 0) (g : C(E2, ℝ)) (hg : ∀ p, g p = σ * (p 0) ^ 2)
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeOne U g hzero 0 := by
  let G1 : C(horizontalSlice U, ℝ) :=
    ⟨fun u => σ * ((u : ℝ) ^ 2 + 1), by fun_prop⟩
  let H : ContinuousMap.Homotopy (sliceMap U g) G1 :=
    { toContinuousMap :=
        ⟨fun r => σ * ((r.2 : ℝ) ^ 2 + (r.1 : ℝ)), by fun_prop⟩
      map_zero_left := by intro u; simp [sliceMap, hg, horizontal]
      map_one_left := by intro u; rfl }
  have hG1 : ∀ u, G1 u ≠ 0 := by
    intro u hu
    simp [G1] at hu
    rcases hu with hu | hu
    · exact hσ hu
    · nlinarith [sq_nonneg (u : ℝ)]
  have hHm : ∀ t : unitInterval, ∀ u ∈
      neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ),
      H (t, u) ∈ deletedPoint (0 : ℝ) := by
    intro t u hu hHu
    apply hu
    simp [H] at hHu
    rcases mul_eq_zero.mp hHu with hs | hs
    · exact absurd hs hσ
    · nlinarith [sq_nonneg (u : ℝ), t.2.1]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ))
    H hHm
    (by
      intro u hu hgu
      have hprod : productMap g (⟨horizontal u, u.property⟩ : U) = 0 := by
        ext i; fin_cases i
        · simpa [sliceMap, horizontal, productMap] using hgu
        · simp [productMap, horizontal]
      exact hu (by
        have := congrArg (fun p : E2 => p 0)
          ((hzero ⟨horizontal u, u.property⟩).mp hprod)
        simpa [horizontal] using this))
    (fun u _ => hG1 u) 1
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [zero_smul]
  erw [hmap, sliceHomologyMap_eq_zero_of_avoids U G1 hG1]
  rfl

theorem positiveFold_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U positiveFoldScalar (positiveFold_productMap_zero_iff U) 0 :=
  fold_slice_localDegree_zero U hU h0 1 one_ne_zero positiveFoldScalar
    (fun p => by simp [positiveFoldScalar]) _

theorem negativeFold_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U negativeFoldScalar (negativeFold_productMap_zero_iff U) 0 :=
  fold_slice_localDegree_zero U hU h0 (-1) (by norm_num) negativeFoldScalar
    (fun p => by simp [negativeFoldScalar]) _

lemma splitProductMap_zero_iff
    (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) (p : U) :
    splitProductMap g p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro hp
    have hv : (p : E2) 1 = 0 := by
      have := congrArg (fun q : E2 => q 1) hp
      simpa [splitProductMap, productMap] using this
    have hg : g (horizontal ((p : E2) 0)) = 0 := by
      have := congrArg (fun q : E2 => q 0) hp
      simpa [splitProductMap, productMap] using this
    have hp_horizontal : (p : E2) = horizontal ((p : E2) 0) := by
      ext i
      fin_cases i
      · simp [horizontal]
      · simpa [horizontal] using hv
    apply (hzero p).mp
    have hgp : g (p : E2) = 0 := by rw [hp_horizontal]; exact hg
    ext i
    fin_cases i
    · simpa [productMap] using hgp
    · simpa [productMap] using hv
  · intro hp
    have hpzero : productMap g p = 0 := (hzero p).mpr hp
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) hpzero
      simpa [splitProductMap, productMap, hp, horizontal] using h0
    · simpa [splitProductMap, productMap, hp]

/-- **Relative pair-homotopy step (estimated 80--140 lines).**
The homotopy `g_s(u,v)=g(u,s*v)` keeps the second coordinate equal to `v`,
so every intermediate product map has the same sole zero.  Relative prism
homotopy invariance therefore identifies the two local H2 maps. -/
theorem productMap_degree_iff_splitProductMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (productMap g) hzero n ↔
      IsLocalDegreeTwo U (splitProductMap g)
        (splitProductMap_zero_iff U g hzero) n := by
  let F₀ := restrictedMap U (splitProductMap g)
  let F₁ := restrictedMap U (productMap g)
  let H : ContinuousMap.Homotopy F₀ F₁ := {
    toFun := fun p =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
        if i = 0 then
          g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
            if j = 0 then (p.2 : E2) 0 else (p.1 : ℝ) * (p.2 : E2) 1))
        else (p.2 : E2) 1)
    continuous_toFun := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi
      intro i
      fin_cases i
      · apply g.continuous.comp
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
        apply continuous_pi
        intro j
        fin_cases j
        · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
            (continuous_subtype_val.comp continuous_snd)
        · exact (continuous_subtype_val.comp continuous_fst).mul
            ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
              (continuous_subtype_val.comp continuous_snd))
      · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
          (continuous_subtype_val.comp continuous_snd)
    map_zero_left := by
      intro p
      ext i
      fin_cases i <;> simp [F₀, restrictedMap, splitProductMap, productMap, horizontal]
    map_one_left := by
      intro p
      have hin :
          (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
            if j = 0 then (p : E2) 0 else (p : E2) 1) = (p : E2) := by
        ext j
        fin_cases j <;> simp
      ext i
      fin_cases i
      · simpa [F₁, restrictedMap, productMap, hin]
      · simp [F₁, restrictedMap, productMap] }
  have hH : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint U (0 : E2),
      H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    have hv : (p : E2) 1 = 0 := by
      have hh := congrArg (fun q : E2 => q 1) hHp
      simpa [H] using hh
    have hg : g (horizontal ((p : E2) 0)) = 0 := by
      have hh := congrArg (fun q : E2 => q 0) hHp
      change g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
        if j = 0 then (p : E2) 0 else (t : ℝ) * (p : E2) 1)) = 0 at hh
      rw [hv] at hh
      simpa [horizontal] using hh
    have hs : splitProductMap g p = 0 := by
      ext i
      fin_cases i
      · simpa [splitProductMap, productMap] using hg
      · simpa [splitProductMap, productMap] using hv
    exact hp ((splitProductMap_zero_iff U g hzero p).mp hs)
  have hmaps :=
    ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
        (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H hH
        (by
          intro p hp hFp
          exact hp ((splitProductMap_zero_iff U g hzero p).mp hFp))
        (by intro p hp hFp; exact hp ((hzero p).mp hFp)) 2
  constructor
  · rintro ⟨a, ha, hFa⟩
    refine ⟨a, ha, ?_⟩
    rw [hmaps]
    exact hFa
  · rintro ⟨a, ha, hFa⟩
    refine ⟨a, ha, ?_⟩
    rw [← hmaps]
    exact hFa

-- Two-dimensional model degrees (merged from model_degrees.lean).

def reflectionScalar : C(E2, ℝ) where
  toFun p := -(p 0)
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).neg

lemma reflection_productMap_zero_iff (U : Set E2) (p : U) :
    productMap reflectionScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) h
      simpa [productMap, reflectionScalar] using neg_eq_zero.mp h0
    · simpa [productMap, reflectionScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, reflectionScalar]



/-- The identity map carries the ambient local generator to itself.  The
neighborhood generator is obtained by inverting the neighborhood-inclusion
isomorphism.  Estimated size: 35--60 lines. -/
theorem identity_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap identityScalar)
      (identity_productMap_zero_iff U) 1 := by
  have hres : restrictedMap U (productMap identityScalar) = neighborhoodInclusion U := by
    ext p i
    fin_cases i <;> rfl
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)), hι _, ?_⟩
  rw [one_smul]
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _; subst hFG; rfl
  rw [hcongr _ _ hres _ (neighborhoodInclusion_mapsTo U 0)]
  exact hι _

def firstCoordinateReflection : C(E2, E2) where
  toFun := ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
  continuous_toFun :=
    (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).continuous

lemma firstCoordinateReflection_mapsTo_deletedPoint :
    MapsTo firstCoordinateReflection (deletedPoint (0 : E2)) (deletedPoint (0 : E2)) := by
  intro p hp hRp
  apply hp
  exact (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).injective
    (hRp.trans
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).map_zero.symm)

/-- The first-coordinate reflection acts as minus the identity on integral
first homology of the Euclidean unit circle, computed in additive groups.
The natural integral coefficient comparison transports the module computation. -/
lemma firstCoordinateReflection_circle_H1 :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (0 : Fin 2))) = -𝟙 _ := by
  let e := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of (T02A06.euclideanUnitSphere 2)) 1
  apply (cancel_epi e.hom).mp
  have h := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
    (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
      (0 : Fin 2))) 1
  rw [ConstructionTargets.CoefficientFirstReflection.circle_negative ℤ] at h
  simpa only [Functor.map_neg, Functor.map_id, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.id_comp, Category.comp_id] using h.symm

/-- Radial normalization intertwines reflection of the punctured plane with
reflection of its unit circle, since a linear isometry preserves norms. -/
lemma firstCoordinateReflection_radial_naturality :
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2).comp
      (⟨fun x : deletedPoint (0 : E2) =>
        ⟨firstCoordinateReflection x, firstCoordinateReflection_mapsTo_deletedPoint x.property⟩,
        firstCoordinateReflection.continuous.comp continuous_subtype_val |>.subtype_mk _⟩) =
    (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)).comp
      (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2) x.val) =
    ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
      (NormedSpace.normalize x.val)
  simp only [NormedSpace.normalize, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.map_smul]

/-- The first-coordinate reflection negates the standard ambient local
two-dimensional generator.  Radial naturality identifies the relative local
map with the reflection of the unit circle, where
`CoefficientFirstReflection.all_reflections_negative` computes the sign.
Estimated size: 70--110 lines. -/
lemma firstCoordinateReflection_ambientLocalGenerator :
    HomologicalComplex.homologyMap
        (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
          firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
        (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2)) =
      -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2) := by
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)
  let A := deletedPoint (0 : E2)
  let q := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2
  let j := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereInclusion E2
  let d := singularPairConnecting A 1
  haveI : Mono d := by
    apply (singularPairHomology_exact_relative A 1).mono_g
    exact (contractibleHigherHomology_isZero E2 2 (by decide)).eq_of_src _ _
  haveI : IsIso (H.map (TopCat.ofHom q)) := by
    exact ConstructionTargets.RelativeSingularHomologyHomotopy.chainHomology_isIso_of_section
      q j (by
        apply ContinuousMap.ext
        intro x
        exact ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize_unitSphereInclusion E2 x)
      ⟨ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.puncturedRadialHomotopy E2⟩ 1
  have hd : Function.Injective d := (AddCommGrpCat.mono_iff_injective d).mp inferInstance
  have hq : Function.Injective (H.map (TopCat.ofHom q)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  apply hd
  apply hq
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  let r := subspaceMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint
  have hn : d ≫ H.map r = ρ ≫ d :=
    ConstructionTargets.RelativeSingularConnectingNaturality.singularPairConnecting_naturality
      A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint 1
  have hr : r ≫ TopCat.ofHom q = TopCat.ofHom q ≫
      TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)) := by
    exact congrArg TopCat.ofHom firstCoordinateReflection_radial_naturality
  have hs : H.map r ≫ H.map (TopCat.ofHom q) = -(H.map (TopCat.ofHom q)) := by
    rw [← H.map_comp, hr]
    erw [H.map_comp]
    change H.map (TopCat.ofHom q) ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map _ = _
    rw [firstCoordinateReflection_circle_H1, Preadditive.comp_neg, Category.comp_id]
  have he : ρ ≫ d ≫ H.map (TopCat.ofHom q) = -(d ≫ H.map (TopCat.ofHom q)) := by
    rw [← Category.assoc, ← hn]
    erw [Category.assoc, hs, Preadditive.comp_neg]
    rfl
  have hv := ConcreteCategory.congr_hom he
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2))
  change (H.map (TopCat.ofHom q)) (d (ρ _)) =
    -((H.map (TopCat.ofHom q)) (d _)) at hv
  change (H.map (TopCat.ofHom q)).hom (d.hom (ρ.hom _)) =
    (H.map (TopCat.ofHom q)).hom (d.hom (-_))
  rw [map_neg]
  erw [map_neg]
  exact hv

/-- Reflection in the first coordinate acts by `-1` on two-dimensional local
homology.  This follows by transporting `all_reflections_negative` through
the radial local-homology isomorphism.  Estimated size: 70--110 lines. -/
theorem reflection_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap reflectionScalar)
      (reflection_productMap_zero_iff U) (-1) := by
  have hres : restrictedMap U (productMap reflectionScalar) =
      firstCoordinateReflection.comp (neighborhoodInclusion U) := by
    ext p i
    fin_cases i <;> simp [restrictedMap, productMap, reflectionScalar,
      firstCoordinateReflection, neighborhoodInclusion,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) 2
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
      firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 U (0 : E2) hU h0
  let z := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
    (k := 0) (0 : E2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv z, hι _, ?_⟩
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _
    subst hFG
    rfl
  have hcompMaps : MapsTo (firstCoordinateReflection.comp (neighborhoodInclusion U))
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) :=
    firstCoordinateReflection_mapsTo_deletedPoint.comp
      (neighborhoodInclusion_mapsTo U 0)
  rw [hcongr _ _ hres _ hcompMaps]
  have hcomp := relativeSingularHomologyMap_comp
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
    (deletedPoint (0 : E2)) (neighborhoodInclusion U) firstCoordinateReflection
    (neighborhoodInclusion_mapsTo U 0) firstCoordinateReflection_mapsTo_deletedPoint
    hcompMaps 2
  rw [← hcomp]
  change ρ (ι ((asIso ι).inv z)) = (-1 : ℤ) • z
  rw [hι, firstCoordinateReflection_ambientLocalGenerator]
  simp
  rfl


/-- A map of the neighbourhood that misses the origin entirely is zero on local homology:
it factors through the self-pair of `U`. -/
lemma homologyMap_eq_zero_of_avoids (U : Set E2) (G : C(U, E2)) (hG : ∀ p, G p ≠ 0)
    (hGm : Set.MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hGm) 2 = 0 := by
  have hfac := relativeSingularMap_comp (neighborhoodDeletedPoint U (0 : E2)) (Set.univ : Set U)
    (deletedPoint (0 : E2)) (ContinuousMap.id U) G (fun _ _ => trivial) (fun p _ => hG p) hGm
  show HomologicalComplex.homologyMap (relativeSingularMap _ _ (G.comp (ContinuousMap.id U)) hGm) 2 = 0
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  rw [(selfRelativeSingularHomology_isZero U 2).eq_zero_of_tgt
    (HomologicalComplex.homologyMap (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
      (Set.univ : Set U) (ContinuousMap.id U) (fun _ _ => trivial)) 2), Limits.zero_comp]

/-- The fold `(σ·u², v)` (σ = ±1) has local degree 0: it deforms through maps of pairs to
`(σ·(u²+1), v)`, whose image misses the origin. -/
lemma fold_localDegree_zero (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (σ : ℝ) (hσ : σ ≠ 0) (g : C(E2, ℝ)) (hg : ∀ p, g p = σ * (p 0) ^ 2)
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (productMap g) hzero 0 := by
  let cpt : C(unitInterval × U, ℝ × ℝ) :=
    ⟨fun r => (σ * (((r.2 : E2) 0) ^ 2 + (r.1 : ℝ)), (r.2 : E2) 1), by fun_prop⟩
  let Hf : C(unitInterval × U, E2) :=
    ⟨fun r => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => if i = 0 then (cpt r).1 else (cpt r).2),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by
        apply continuous_pi; intro i; fin_cases i
        · simpa using (continuous_fst.comp cpt.continuous)
        · simpa using (continuous_snd.comp cpt.continuous))⟩
  let G1 : C(U, E2) := ⟨fun p => Hf (1, p), Hf.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : ContinuousMap.Homotopy (restrictedMap U (productMap g)) G1 :=
    { toContinuousMap := Hf
      map_zero_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, productMap, hg]
      map_one_left := by intro p; rfl }
  have hG1 : ∀ p, G1 p ≠ 0 := by
    intro p h
    have := congrArg (fun q : E2 => q 0) h
    simp [G1, Hf, cpt] at this
    rcases this with h1 | h1
    · exact hσ h1
    · nlinarith [sq_nonneg ((p : E2) 0)]
  have hHm : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint U (0 : E2), H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    apply hp
    have h0' := congrArg (fun q : E2 => q 0) hHp
    have h1' := congrArg (fun q : E2 => q 1) hHp
    simp [H, Hf, cpt] at h0' h1'
    have h0'' : σ * (((p : E2) 0) ^ 2 + (t : ℝ)) = 0 := by
      exact h0'
    have hu : (p : E2) 0 = 0 := by
      rcases mul_eq_zero.mp h0'' with h | h
      · exact absurd h hσ
      · nlinarith [sq_nonneg ((p : E2) 0), t.2.1]
    ext i; fin_cases i
    · simpa using hu
    · simpa using h1'
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H hHm
    (by intro p hp hFp; exact hp ((hzero p).mp hFp)) (fun p _ => hG1 p) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [zero_smul]
  erw [hmap, homologyMap_eq_zero_of_avoids U G1 hG1]
  rfl

/-- The positive fold has zero local degree.  Its image lies in the closed
right half-plane; the relative `H₂` of that half-plane at the origin vanishes
because the half-plane and its puncture are contractible.  Estimated size:
90--150 lines. -/
theorem positiveFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap positiveFoldScalar)
      (positiveFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 1 one_ne_zero positiveFoldScalar
    (fun p => by simp [positiveFoldScalar]) _

/-- The negative fold has zero local degree by the identical half-plane
factorization through the closed left half-plane.  Estimated size: 25--45
lines once the positive half-plane calculation is available. -/
theorem negativeFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap negativeFoldScalar)
      (negativeFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 (-1) (by norm_num) negativeFoldScalar
    (fun p => by simp [negativeFoldScalar]) _


-- Shrinking, uniqueness and deformation to a model (two-dimensional).

lemma relMap_congr {P : Type} [TopologicalSpace P] (A : Set P) (F G : C(P, E2)) (hFG : F = G) hF hG :
    relativeSingularMap A (deletedPoint (0 : E2)) F hF =
      relativeSingularMap A (deletedPoint (0 : E2)) G hG := by
  subst hFG; rfl

/-- The local degree on a neighbourhood does not depend on the neighbourhood. -/
theorem localDegreeTwo_iff_of_subset (U V : Set E2) (hU : IsOpen U) (hV : IsOpen V)
    (h0V : (0 : E2) ∈ V) (hVU : V ⊆ U) (F : C(E2, E2))
    (hzU : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (hzV : ∀ p : V, F p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeTwo U F hzU n ↔ IsLocalDegreeTwo V F hzV n := by
  have h0U : (0 : E2) ∈ U := hVU h0V
  let j : C(V, U) := ⟨fun p => ⟨p, hVU p.2⟩, by fun_prop⟩
  have hj : Set.MapsTo j (neighborhoodDeletedPoint V (0 : E2)) (neighborhoodDeletedPoint U (0 : E2)) :=
    fun p hp => hp
  let J := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint V (0 : E2)) (neighborhoodDeletedPoint U (0 : E2)) j hj) 2
  have hcomp : ∀ (G : C(U, E2)) (hG : Set.MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)))
      (G' : C(V, E2)) (hG' : Set.MapsTo G' (neighborhoodDeletedPoint V (0 : E2)) (deletedPoint (0 : E2))),
      G.comp j = G' → ∀ b,
      HomologicalComplex.homologyMap (relativeSingularMap _ _ G hG) 2 (J b) =
        HomologicalComplex.homologyMap (relativeSingularMap _ _ G' hG') 2 b := by
    intro G hG G' hG' hGG b
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp _ _ _ j G hj hG (hGG ▸ hG'), relMap_congr _ _ _ hGG]
  have hιVU := hcomp (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)
    (neighborhoodInclusion V) (neighborhoodInclusion_mapsTo V 0) rfl
  have hFVU := hcomp (restrictedMap U F) (by intro p hp hFp; exact hp ((hzU p).mp hFp))
    (restrictedMap V F) (by intro p hp hFp; exact hp ((hzV p).mp hFp)) rfl
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0U
  let ιU := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  constructor
  · rintro ⟨a, ha, hFa⟩
    letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 V (0 : E2) hV h0V
    let ιV := HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint V (0 : E2)) (deletedPoint (0 : E2))
        (neighborhoodInclusion V) (neighborhoodInclusion_mapsTo V 0)) (0+2)
    refine ⟨(asIso ιV).inv (ιU a), ?_, ?_⟩
    · rw [ha]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
    · -- J (ιV⁻¹ (ιU a)) = a, since ιU ∘ J = ιV and ιU is injective
      have hJ : J ((asIso ιV).inv (ιU a)) = a := by
        apply (ConcreteCategory.injective_of_mono_of_preservesPullback ιU)
        have := hιVU ((asIso ιV).inv (ιU a))
        change ιU (J _) = ιV _ at this
        rw [this]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
      rw [← hFVU, hJ, hFa]
  · rintro ⟨b, hb, hFb⟩
    exact ⟨J b, by rw [hιVU, hb], by rw [hFVU, hFb]⟩

/-- Local degrees are unique. -/
theorem localDegreeTwo_unique (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (F : C(E2, E2))
    (hz : ∀ p : U, F p = 0 ↔ (p : E2) = 0) {n m : ℤ}
    (hn : IsLocalDegreeTwo U F hz n) (hm : IsLocalDegreeTwo U F hz m) : n = m := by
  obtain ⟨a, ha, hFa⟩ := hn
  obtain ⟨b, hb, hFb⟩ := hm
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  have hab : a = b := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
          (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2))
    exact ha.trans hb.symm
  subst hab
  exact ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective 0
    (0 : E2) (hFa.symm.trans hFb)

/-- Deformation to a model: if near 0 the slice of `g` has the same strict sign as the slice
of a model `m` (a function of the first coordinate only, vanishing only at 0), the split map
and the model product map have the same local degree. -/
theorem splitProductMap_degree_iff_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm : ∀ p : E2, m p = m (horizontal (p 0)))
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u)))
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g) (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeTwo U (productMap m) hzm n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  set ρ := min ε r with hρ
  have hρpos : 0 < ρ := lt_min hε hr
  let Q : Set E2 := Metric.ball 0 ρ
  have hQU : Q ⊆ U := fun p hp => hball (Metric.ball_subset_ball (min_le_right _ _) hp)
  have hQ0 : (0 : E2) ∈ Q := Metric.mem_ball_self hρpos
  have hcoord : ∀ p : E2, p ∈ Q → |p 0| < ε := by
    intro p hp
    have h1 : |p 0| ≤ ‖p‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
    have h2 : ‖p‖ < ρ := by simpa [Q] using hp
    linarith [min_le_left ε r]
  have hp_eq : ∀ p : E2, p 1 = 0 → p = horizontal (p 0) := by
    intro p h1; ext i; fin_cases i
    · simp [horizontal]
    · simpa [horizontal] using h1
  have hzS : ∀ p : Q, splitProductMap g p = 0 ↔ (p : E2) = 0 := fun p =>
    splitProductMap_zero_iff U g hzero ⟨p, hQU p.2⟩
  have hzM : ∀ p : Q, productMap m p = 0 ↔ (p : E2) = 0 := fun p => hzm ⟨p, hQU p.2⟩
  rw [localDegreeTwo_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzS,
    localDegreeTwo_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzM]
  -- the straight-line homotopy on Q
  let cpt : C(unitInterval × Q, ℝ × ℝ) :=
    ⟨fun r => ((1 - (r.1 : ℝ)) * g (horizontal ((r.2 : E2) 0)) + (r.1 : ℝ) * m (r.2 : E2),
      (r.2 : E2) 1), by
        refine Continuous.prodMk ?_ ?_
        · have hgc : Continuous fun r : unitInterval × Q => g (horizontal ((r.2 : E2) 0)) := by
            apply g.continuous.comp
            apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
            apply continuous_pi; intro i; fin_cases i
            · simpa [horizontal] using (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
                (continuous_subtype_val.comp continuous_snd)
            · exact continuous_const
          have hmc : Continuous fun r : unitInterval × Q => m (r.2 : E2) :=
            m.continuous.comp (continuous_subtype_val.comp continuous_snd)
          exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hgc).add
            ((continuous_subtype_val.comp continuous_fst).mul hmc)
        · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
            (continuous_subtype_val.comp continuous_snd)⟩
  let Hf : C(unitInterval × Q, E2) :=
    ⟨fun r => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => if i = 0 then (cpt r).1 else (cpt r).2),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by
        apply continuous_pi; intro i; fin_cases i
        · simpa using (continuous_fst.comp cpt.continuous)
        · simpa using (continuous_snd.comp cpt.continuous))⟩
  let H : ContinuousMap.Homotopy (restrictedMap Q (splitProductMap g)) (restrictedMap Q (productMap m)) :=
    { toContinuousMap := Hf
      map_zero_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, splitProductMap, productMap]
      map_one_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, productMap] }
  have hHm : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint Q (0 : E2),
      H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    apply hp
    change Hf (t, p) = 0 at hHp
    have e0 : (1 - (t : ℝ)) * g (horizontal ((p : E2) 0)) + (t : ℝ) * m (p : E2) = 0 := by
      simpa [Hf, cpt] using congrArg (fun q : E2 => q 0) hHp
    have e1 : (p : E2) 1 = 0 := by
      simpa [Hf, cpt] using congrArg (fun q : E2 => q 1) hHp
    have hpe := hp_eq (p : E2) e1
    by_contra hp0
    have hu0 : (p : E2) 0 ≠ 0 := by
      intro hu; apply hp0; rw [hpe, hu, horizontal_zero]
    have hlt := hcoord p p.2
    have hs := hsign _ hlt hu0
    have hmne : m (horizontal ((p : E2) 0)) ≠ 0 := fun h => hu0 ((hm0 _).mp h)
    rw [hm (p : E2)] at e0
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hgne : g (horizontal ((p : E2) 0)) ≠ 0 := by
      intro h
      have hmemU : horizontal ((p : E2) 0) ∈ U := hQU (by rw [← hpe]; exact p.2)
      have hz := (hzero ⟨horizontal ((p : E2) 0), hmemU⟩).mp (by
        ext i; fin_cases i
        · simpa [productMap] using h
        · simp [productMap, horizontal])
      exact hu0 (by simpa [horizontal] using congrArg (fun q : E2 => q 0) hz)
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hgneg : g (horizontal ((p : E2) 0)) < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h => absurd (hs.mp h) (not_lt.mpr hneg.le)) hgne
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h (neg_pos.mpr hneg),
          mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hgneg.le)]
    · have hgpos : 0 < g (horizontal ((p : E2) 0)) := hs.mpr hpos
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h hpos, mul_nonneg (sub_nonneg.mpr ht1) hgpos.le]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint Q (0 : E2)) (deletedPoint (0 : E2)) H hHm
    (by intro p hp hFp; exact hp ((hzS p).mp hFp))
    (by intro p hp hFp; exact hp ((hzM p).mp hFp)) 2
  constructor
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [← hmap]; exact hFa⟩
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [hmap]; exact hFa⟩



-- One-dimensional shrinking, uniqueness and deformation to a model.

theorem realLocalGenerator_zsmul_injective :
    Function.Injective (fun r : ℤ =>
      r • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) := by
  letI := ConstructionTargets.OneDimensionalChartLocalGenerator.realLineAtlas
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap ConstructionTargets.OneDiskIncreasingOrientation.P
      (deletedPoint (0 : ℝ))
      (ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap (0 : ℝ))
      (ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_mapsTo (0 : ℝ))) 1
  letI := ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_H1_isIso (0 : ℝ)
  intro r s hrs
  change r • f ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1Generator =
    s • f ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1Generator at hrs
  rw [← map_zsmul, ← map_zsmul] at hrs
  have h := ConcreteCategory.injective_of_mono_of_preservesPullback f hrs
  have hc := congrArg
    ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt.hom h
  erw [map_zsmul, map_zsmul,
    ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt_generator] at hc
  simpa using hc

lemma relMap_congr1 {P : Type} [TopologicalSpace P] (A : Set P) (F G : C(P, ℝ)) (hFG : F = G)
    hF hG :
    relativeSingularMap A (deletedPoint (0 : ℝ)) F hF =
      relativeSingularMap A (deletedPoint (0 : ℝ)) G hG := by
  subst hFG; rfl

lemma sliceMap_mapsTo (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    Set.MapsTo (sliceMap U g) (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) := by
  intro u hu hgu
  have hprod : productMap g (⟨horizontal u, u.property⟩ : U) = 0 := by
    ext i
    fin_cases i
    · simpa [productMap] using hgu
    · simp [productMap, horizontal]
  have horigin := (hzero ⟨horizontal u, u.property⟩).mp hprod
  exact hu (by
    have horigin' := congrArg (fun p : E2 => p 0) horigin
    simpa [horizontal] using horigin')

/-- The one-dimensional local degree does not depend on the neighbourhood. -/
theorem localDegreeOne_iff_of_subset (U V : Set E2) (hU : IsOpen U) (hV : IsOpen V)
    (h0V : (0 : E2) ∈ V) (hVU : V ⊆ U) (g : C(E2, ℝ))
    (hzU : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hzV : ∀ p : V, productMap g p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeOne U g hzU n ↔ IsLocalDegreeOne V g hzV n := by
  have h0U : (0 : E2) ∈ U := hVU h0V
  have hUo : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hVo : IsOpen (horizontalSlice V) := hV.preimage continuous_horizontal
  have hU0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0U
  have hV0 : (0 : ℝ) ∈ horizontalSlice V := by simpa [horizontalSlice, horizontal_zero] using h0V
  let j : C(horizontalSlice V, horizontalSlice U) := ⟨fun u => ⟨u, hVU u.2⟩, by fun_prop⟩
  have hj : Set.MapsTo j (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) := fun p hp => hp
  let J := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) j hj) 1
  have hcomp : ∀ (G : C(horizontalSlice U, ℝ))
      (hG : Set.MapsTo G (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ)))
      (G' : C(horizontalSlice V, ℝ))
      (hG' : Set.MapsTo G' (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ)) (deletedPoint (0 : ℝ))),
      G.comp j = G' → ∀ b,
      HomologicalComplex.homologyMap (relativeSingularMap _ _ G hG) 1 (J b) =
        HomologicalComplex.homologyMap (relativeSingularMap _ _ G' hG') 1 b := by
    intro G hG G' hG' hGG b
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp _ _ _ j G hj hG (hGG ▸ hG'), relMap_congr1 _ _ _ hGG]
  have hιVU := hcomp (neighborhoodInclusion (horizontalSlice U))
    (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)
    (neighborhoodInclusion (horizontalSlice V))
    (neighborhoodInclusion_mapsTo (horizontalSlice V) 0) rfl
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hUo hU0
  let ιU := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ))
      (neighborhoodInclusion (horizontalSlice U)) (neighborhoodInclusion_mapsTo _ 0)) 1
  constructor
  · rintro ⟨a, ha, hFa⟩
    letI := neighborhoodInclusion_H1_isIso (horizontalSlice V) (0 : ℝ) hVo hV0
    let ιV := HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
        (deletedPoint (0 : ℝ))
        (neighborhoodInclusion (horizontalSlice V)) (neighborhoodInclusion_mapsTo _ 0)) 1
    refine ⟨(asIso ιV).inv (ιU a), ?_, ?_⟩
    · rw [ha]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
    · have hJ : J ((asIso ιV).inv (ιU a)) = a := by
        apply (ConcreteCategory.injective_of_mono_of_preservesPullback ιU)
        have := hιVU ((asIso ιV).inv (ιU a))
        change ιU (J _) = ιV _ at this
        rw [this]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
      rw [← hcomp (sliceMap U g) (sliceMap_mapsTo U g hzU) (sliceMap V g)
        (sliceMap_mapsTo V g hzV) rfl, hJ, hFa]
  · rintro ⟨b, hb, hFb⟩
    exact ⟨J b, by rw [hιVU, hb], by
      rw [hcomp (sliceMap U g) (sliceMap_mapsTo U g hzU) (sliceMap V g)
        (sliceMap_mapsTo V g hzV) rfl, hFb]⟩

/-- One-dimensional local degrees are unique. -/
theorem localDegreeOne_unique (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g : C(E2, ℝ))
    (hz : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) {n m : ℤ}
    (hn : IsLocalDegreeOne U g hz n) (hm : IsLocalDegreeOne U g hz m) : n = m := by
  obtain ⟨a, ha, hFa⟩ := hn
  obtain ⟨b, hb, hFb⟩ := hm
  have hUo : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hU0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hUo hU0
  have hab : a = b := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ))
          (neighborhoodInclusion (horizontalSlice U)) (neighborhoodInclusion_mapsTo _ 0)) 1)
    exact ha.trans hb.symm
  subst hab
  exact realLocalGenerator_zsmul_injective (hFa.symm.trans hFb)

/-- One-dimensional deformation to a model with the same strict signs near 0. -/
theorem sliceMap_degree_iff_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u)))
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeOne U g hzero n ↔ IsLocalDegreeOne U m hzm n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  set ρ := min ε r with hρ
  have hρpos : 0 < ρ := lt_min hε hr
  let Q : Set E2 := Metric.ball 0 ρ
  have hQU : Q ⊆ U := fun p hp => hball (Metric.ball_subset_ball (min_le_right _ _) hp)
  have hQ0 : (0 : E2) ∈ Q := Metric.mem_ball_self hρpos
  have hcoord : ∀ u : ℝ, u ∈ horizontalSlice Q → |u| < ε := by
    intro u hu
    have h1 : |(horizontal u) 0| ≤ ‖horizontal u‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (horizontal u) 0
    have h2 : ‖horizontal u‖ < ρ := by simpa [Q, horizontalSlice] using hu
    have h3 : (horizontal u) 0 = u := by simp [horizontal]
    rw [h3] at h1
    linarith [min_le_left ε r]
  have hzQ : ∀ p : Q, productMap g p = 0 ↔ (p : E2) = 0 := fun p => hzero ⟨p, hQU p.2⟩
  have hzM : ∀ p : Q, productMap m p = 0 ↔ (p : E2) = 0 := fun p => hzm ⟨p, hQU p.2⟩
  rw [localDegreeOne_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzQ,
    localDegreeOne_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzM]
  let H : ContinuousMap.Homotopy (sliceMap Q g) (sliceMap Q m) :=
    { toContinuousMap :=
        ⟨fun r => (1 - (r.1 : ℝ)) * sliceMap Q g r.2 + (r.1 : ℝ) * sliceMap Q m r.2, by
          have h1 : Continuous fun r : unitInterval × horizontalSlice Q => sliceMap Q g r.2 :=
            (sliceMap Q g).continuous.comp continuous_snd
          have h2 : Continuous fun r : unitInterval × horizontalSlice Q => sliceMap Q m r.2 :=
            (sliceMap Q m).continuous.comp continuous_snd
          exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul h1).add
            ((continuous_subtype_val.comp continuous_fst).mul h2)⟩
      map_zero_left := by intro u; simp
      map_one_left := by intro u; simp }
  have hHm : ∀ t : unitInterval, ∀ u ∈ neighborhoodDeletedPoint (horizontalSlice Q) (0 : ℝ),
      H (t, u) ∈ deletedPoint (0 : ℝ) := by
    intro t u hu e0
    apply hu
    change (1 - (t : ℝ)) * g (horizontal (u : ℝ)) + (t : ℝ) * m (horizontal (u : ℝ)) = 0 at e0
    by_contra hu0
    have hs := hsign _ (hcoord u u.2) hu0
    have hmne : m (horizontal (u : ℝ)) ≠ 0 := fun h => hu0 ((hm0 _).mp h)
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hgne : g (horizontal (u : ℝ)) ≠ 0 := fun h =>
      sliceMap_mapsTo Q g hzQ hu (show sliceMap Q g u = 0 from h)
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hgneg : g (horizontal (u : ℝ)) < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h => absurd (hs.mp h) (not_lt.mpr hneg.le)) hgne
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h (neg_pos.mpr hneg),
          mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hgneg.le)]
    · have hgpos : 0 < g (horizontal (u : ℝ)) := hs.mpr hpos
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h hpos, mul_nonneg (sub_nonneg.mpr ht1) hgpos.le]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint (horizontalSlice Q) (0 : ℝ)) (deletedPoint (0 : ℝ)) H hHm
    (sliceMap_mapsTo Q g hzQ) (sliceMap_mapsTo Q m hzM) 1
  constructor
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [← hmap]; exact hFa⟩
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [hmap]; exact hFa⟩

open ConstructionTargets.ChartPairRelativeHomologyTransport
  ConstructionTargets.T02A06HemisphereExcision in
/-- Negation reverses the real local orientation. The model disk reflection
acts by minus the identity on every relative class; neighborhood excision and
the real-line coordinate homeomorphism transport that action to the ambient
real line, without comparing choices of generators. -/
theorem realNegation_realLocalGenerator :
    HomologicalComplex.homologyMap
      (relativeSingularMap (deletedPoint (0 : ℝ)) (deletedPoint (0 : ℝ))
        (⟨fun u : ℝ => -u, continuous_neg⟩ : C(ℝ, ℝ))
        (by intro u hu h; exact hu (neg_eq_zero.mp h))) 1
      (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) =
    -ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 := by
  let E := EuclideanSpace ℝ (Fin 1)
  let U : Set E := Metric.ball 0 1
  let P := puncturedOpenDiskSet 1
  let A := deletedPoint (0 : E)
  let B := deletedPoint (0 : ℝ)
  let e := ConstructionTargets.OneDimensionalChartLocalGenerator.realLineCoordinates.symm
  have he0 : e (0 : E) = 0 := rfl
  have hepair : ∀ x, x ∈ A ↔ e x ∈ B := by
    intro x
    change x ≠ 0 ↔ e x ≠ 0
    rw [← he0, e.injective.ne_iff]
  let c := pairContinuousMap e
  have hc : MapsTo c A B := pairContinuousMap_mapsTo e A B hepair
  let i := neighborhoodInclusion U
  have hi : MapsTo i P A := neighborhoodInclusion_mapsTo U 0
  let f := c.comp i
  have hf : MapsTo f P B := hc.comp hi
  let n : C(ℝ, ℝ) := ⟨fun u => -u, continuous_neg⟩
  have hn : MapsTo n B B := by
    intro u hu h
    exact hu (neg_eq_zero.mp h)
  let Hf := HomologicalComplex.homologyMap (relativeSingularMap P B f hf) 1
  haveI : IsIso Hf := by
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap P A i hi) 1) :=
      neighborhoodInclusion_H1_isIso U (0 : E) Metric.isOpen_ball
        (Metric.mem_ball_self (by norm_num))
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap A B c hc) 1) :=
      relativeSingularMap_homeomorphPair_isIso e A B hepair 1
    change IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap P B (c.comp i) hf) 1)
    rw [← relativeSingularHomologyMap_comp P A B i c hi hc hf 1]
    infer_instance
  have hs := ConstructionTargets.OneDiskLocalOrientation.relativeH1_square
    P B ConstructionTargets.OneDiskLocalOrientation.reflection n f
    ConstructionTargets.OneDiskLocalOrientation.reflection_mapsTo hn hf (by
      apply ContinuousMap.ext
      intro x
      rfl)
  rw [ConstructionTargets.OneDiskLocalOrientation.reflection_H1_eq_neg_id] at hs
  have hneg : HomologicalComplex.homologyMap (relativeSingularMap B B n hn) 1 = -𝟙 _ := by
    apply (cancel_epi Hf).mp
    simpa only [ConstructionTargets.OneDiskLocalOrientation.RH,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
      using hs.symm
  have h := ConcreteCategory.congr_hom hneg
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0)
  exact h

/-- The horizontal reflection has one-dimensional local degree −1. -/
theorem reflection_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U reflectionScalar (reflection_productMap_zero_iff U) (-1) := by
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  let ν : C(ℝ, ℝ) := ⟨fun u : ℝ => -u, continuous_neg⟩
  have hν : Set.MapsTo ν (deletedPoint (0 : ℝ)) (deletedPoint (0 : ℝ)) := by
    intro u hu h; exact hu (neg_eq_zero.mp h)
  have hs : sliceMap U reflectionScalar = ν.comp (neighborhoodInclusion (horizontalSlice U)) := by
    ext u; simp [sliceMap, reflectionScalar, horizontal, ν]; rfl
  rw [relMap_congr1 _ _ _ hs _ (hν.comp (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)),
    ← relativeSingularMap_comp _ _ _ _ _ (neighborhoodInclusion_mapsTo (horizontalSlice U) 0) hν,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  erw [ConcreteCategory.congr_hom (asIso ι).inv_hom_id _]
  rw [ConcreteCategory.id_apply, neg_one_zsmul]
  exact realNegation_realLocalGenerator

lemma localDegreeTwo_iff_eq (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (F : C(E2, E2))
    (hz : ∀ p : U, F p = 0 ↔ (p : E2) = 0) {c : ℤ} (hc : IsLocalDegreeTwo U F hz c) (n : ℤ) :
    IsLocalDegreeTwo U F hz n ↔ n = c :=
  ⟨fun hn => localDegreeTwo_unique U hU h0 F hz hn hc, fun h => h ▸ hc⟩

lemma localDegreeOne_iff_eq (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g : C(E2, ℝ))
    (hz : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) {c : ℤ} (hc : IsLocalDegreeOne U g hz c)
    (n : ℤ) :
    IsLocalDegreeOne U g hz n ↔ n = c :=
  ⟨fun hn => localDegreeOne_unique U hU h0 g hz hn hc, fun h => h ▸ hc⟩

/-- The diagonal linear map with independently signed coordinate factors. -/
def diagonalMap (d σ : ℤ) : C(E2, E2) :=
  ⟨fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![(d : ℝ) * p 0, (σ : ℝ) * p 1], by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop⟩

lemma diagonalMap_one_one : diagonalMap 1 1 = productMap identityScalar := by
  ext p i
  fin_cases i <;> simp [diagonalMap, productMap, identityScalar]

lemma diagonalMap_neg_one_one : diagonalMap (-1) 1 = productMap reflectionScalar := by
  ext p i
  fin_cases i <;> simp [diagonalMap, productMap, reflectionScalar]

lemma diagonalMap_zero_iff (d σ : ℤ)
    (hd : d = 1 ∨ d = -1) (hσ : σ = 1 ∨ σ = -1) (p : E2) :
    diagonalMap d σ p = 0 ↔ p = 0 := by
  rcases hd with rfl | rfl <;> rcases hσ with rfl | rfl
  all_goals
    constructor
    · intro h
      ext i
      fin_cases i
      · have hi := congrArg (fun q : E2 => q 0) h
        simpa [diagonalMap] using hi
      · have hi := congrArg (fun q : E2 => q 1) h
        simpa [diagonalMap] using hi
    · rintro rfl
      ext i
      fin_cases i <;> simp [diagonalMap]

/-- The diagonal-degree formula when the second coordinate has positive
sign.  These are exactly the identity and first-reflection computations. -/
theorem diagonal_localDegree_of_sigma_one
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (d : ℤ)
    (hd : d = 1 ∨ d = -1)
    (hz : ∀ p : U, diagonalMap d 1 p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (diagonalMap d 1) hz (d * 1) := by
  rcases hd with rfl | rfl
  · simpa only [diagonalMap_one_one, mul_one] using
      identity_productMap_localDegree U hU h0
  · simpa only [diagonalMap_neg_one_one, mul_one] using
      reflection_productMap_localDegree U hU h0

/-- One trichotomy case: compare both degrees with a model whose degrees agree. -/
lemma split_iff_slice_of_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm : ∀ p : E2, m p = m (horizontal (p 0)))
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0)
    (c : ℤ) (h2 : IsLocalDegreeTwo U (productMap m) hzm c) (h1 : IsLocalDegreeOne U m hzm c)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u))) (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g) (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeOne U g hzero n := by
  rw [splitProductMap_degree_iff_model U hU h0 g m hzero hm hm0 ε hε hsign hzm,
    sliceMap_degree_iff_model U hU h0 g m hzero hm0 ε hε hsign hzm,
    localDegreeTwo_iff_eq U hU h0 _ hzm h2, localDegreeOne_iff_eq U hU h0 _ hzm h1]


/-- **Suspension/product identity (estimated 180--300 lines; LIBRARY).**
For the split map `(u,v) ↦ (g(u,0),v)`, the relative H2 generator is the
oriented suspension/cross-product of the relative H1 generator with the
positive normal interval generator.  Consequently its local coefficient is
the same integer. -/
theorem splitProductMap_degree_iff_sliceMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g)
        (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeOne U g hzero n := by
  have hW : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hW0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0
  let h : C(ℝ, ℝ) := g.comp ⟨horizontal, continuous_horizontal⟩
  have hg0 : g 0 = 0 := by
    have := congrArg (fun q : E2 => q 0) ((hzero ⟨0, h0⟩).mpr rfl)
    simpa [productMap] using this
  have hzh : ∀ u ∈ horizontalSlice U, h u = 0 ↔ u = 0 := by
    intro u hu
    constructor
    · intro hu0
      by_contra hne
      exact sliceMap_mapsTo U g hzero (x := ⟨u, hu⟩) hne
        (show sliceMap U g ⟨u, hu⟩ ∈ ({0} : Set ℝ) from hu0)
    · rintro rfl; simpa [h, horizontal_zero] using hg0
  obtain ⟨δ, hδ, -, hcase⟩ := isolatedZero_sign_trichotomy _ hW hW0 h hzh
  have hside : ∀ u, |u| < δ → u ≠ 0 → (u ∈ Set.Ioo (-δ) 0 ∧ u < 0) ∨ (u ∈ Set.Ioo 0 δ ∧ 0 < u) := by
    intro u hu hu0
    rcases lt_or_gt_of_ne hu0 with hn | hp
    · exact Or.inl ⟨⟨(abs_lt.mp hu).1, hn⟩, hn⟩
    · exact Or.inr ⟨⟨hp, (abs_lt.mp hu).2⟩, hp⟩
  have hhu : ∀ u, h u = g (horizontal u) := fun _ => rfl
  rcases hcase with ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine split_iff_slice_of_model U hU h0 g identityScalar hzero
      (fun p => by simp [identityScalar, horizontal])
      (fun u => by simp [identityScalar, horizontal])
      (identity_productMap_zero_iff U) 1
      (identity_productMap_localDegree U hU h0) (identity_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : identityScalar (horizontal u) = u := by simp [identityScalar, horizontal]
    rw [hv, ← hhu]
    rcases hside u hu hu0 with ⟨hI, hs⟩ | ⟨hI, hs⟩
    · exact iff_of_false (not_lt.mpr (hl u hI).le) (not_lt.mpr hs.le)
    · exact iff_of_true (hr u hI) hs
  · refine split_iff_slice_of_model U hU h0 g reflectionScalar hzero
      (fun p => by simp [reflectionScalar, horizontal])
      (fun u => by simp [reflectionScalar, horizontal])
      (reflection_productMap_zero_iff U) (-1)
      (reflection_productMap_localDegree U hU h0) (reflection_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : reflectionScalar (horizontal u) = -u := by simp [reflectionScalar, horizontal]
    rw [hv, ← hhu]
    rcases hside u hu hu0 with ⟨hI, hs⟩ | ⟨hI, hs⟩
    · exact iff_of_true (hl u hI) (by linarith)
    · exact iff_of_false (not_lt.mpr (hr u hI).le) (by linarith)
  · refine split_iff_slice_of_model U hU h0 g positiveFoldScalar hzero
      (fun p => by simp [positiveFoldScalar, horizontal])
      (fun u => by simp [positiveFoldScalar, horizontal])
      (positiveFold_productMap_zero_iff U) 0
      (positiveFold_productMap_localDegree U hU h0) (positiveFold_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : positiveFoldScalar (horizontal u) = u ^ 2 := by simp [positiveFoldScalar, horizontal]
    rw [hv, ← hhu]
    have hsq : 0 < u ^ 2 := by positivity
    rcases hside u hu hu0 with ⟨hI, -⟩ | ⟨hI, -⟩
    · exact iff_of_true (hl u hI) hsq
    · exact iff_of_true (hr u hI) hsq
  · refine split_iff_slice_of_model U hU h0 g negativeFoldScalar hzero
      (fun p => by simp [negativeFoldScalar, horizontal])
      (fun u => by simp [negativeFoldScalar, horizontal])
      (negativeFold_productMap_zero_iff U) 0
      (negativeFold_productMap_localDegree U hU h0) (negativeFold_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : negativeFoldScalar (horizontal u) = -(u ^ 2) := by
      simp [negativeFoldScalar, horizontal]
    rw [hv, ← hhu]
    have hsq : ¬ 0 < -(u ^ 2) := not_lt.mpr (by nlinarith [sq_nonneg u])
    rcases hside u hu hu0 with ⟨hI, -⟩ | ⟨hI, -⟩
    · exact iff_of_false (not_lt.mpr (hl u hI).le) hsq
    · exact iff_of_false (not_lt.mpr (hr u hI).le) hsq

/-- **Model product local-degree lemma (M).**  In standard oriented
coordinates, adjoining the unchanged positive normal coordinate preserves
the local degree. -/
theorem productMap_degree_iff_sliceMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (productMap g) hzero n ↔
      IsLocalDegreeOne U g hzero n := by
  exact (productMap_degree_iff_splitProductMap_degree U hU h0 g hzero n).trans
    (splitProductMap_degree_iff_sliceMap_degree U hU h0 g hzero n)

end t00J02_ModelProduct
#print axioms t00J02_ModelProduct.productMap_degree_iff_sliceMap_degree
