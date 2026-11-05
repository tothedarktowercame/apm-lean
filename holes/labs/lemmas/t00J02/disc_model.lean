import Mathlib
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
  sorry

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
