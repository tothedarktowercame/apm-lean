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
