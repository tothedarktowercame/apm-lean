import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Topological homotopies and singular homology

The simplicial homotopy invariance theorem in Mathlib is connected here to
ordinary homotopies of continuous maps.
-/

noncomputable section

namespace ConstructionTargets.SingularHomologyHomotopy

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

/-- A cylinder homotopy in `TopCat` induces a simplicial homotopy between the
maps of singular simplicial sets. -/
noncomputable def topCatHomotopyToSSet
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) :
    SSet.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h := (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map h
  h₀ := by
    change _ = TopCat.toSSet.map f
    simp only [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₀]
  h₁ := by
    change _ = TopCat.toSSet.map g
    simp only [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, h₁]
  rel := by
    ext n x
    exact x.1.property.elim

/-- Topologically homotopic maps induce equal maps on integral singular
homology. -/
theorem singularHomology_map_eq_of_topCatHomotopy
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C] (R : C)
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map g := by
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := C) (R := R)
      (f := TopCat.toSSet.map f) (g := TopCat.toSSet.map g)
      (H := (topCatHomotopyToSSet h h₀ h₁).toSimplicialObjectHomotopy) n

/-- Convert a standard continuous-map homotopy to the categorical cylinder
convention used by `TopCat`. -/
def continuousMapHomotopyCylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.of X ⊗ TopCat.I ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
    H.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

@[simp] theorem continuousMapHomotopyCylinder_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₀ ≫ continuousMapHomotopyCylinder H = TopCat.ofHom f := by
  ext x
  change H (0, x) = f x
  simp

@[simp] theorem continuousMapHomotopyCylinder_one
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₁ ≫ continuousMapHomotopyCylinder H = TopCat.ofHom g := by
  ext x
  change H (1, x) = g x
  simp

/-- Homotopic continuous maps induce equal maps on singular homology, for
coefficients in any category supporting the singular homology construction. -/
theorem singularHomology_map_eq_of_homotopic
    (D : Type*) [Category D] [Preadditive D] [HasCoproducts D]
    [CategoryWithHomology D] (R : D)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopic f g) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor D n).obj R).map
        (TopCat.ofHom f) =
      ((AlgebraicTopology.singularHomologyFunctor D n).obj R).map
        (TopCat.ofHom g) := by
  rcases H with ⟨H⟩
  exact singularHomology_map_eq_of_topCatHomotopy D R
    (continuousMapHomotopyCylinder H)
    (continuousMapHomotopyCylinder_zero H)
    (continuousMapHomotopyCylinder_one H) n

/-- A constant map induces zero on positive-degree singular homology. -/
theorem singularHomology_map_const_eq_zero
    (D : Type*) [Category D] [Preadditive D] [HasCoproducts D]
    [CategoryWithHomology D] (R : D)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (y : Y) :
    ((AlgebraicTopology.singularHomologyFunctor D n).obj R).map
      (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  let p : C(X, Unit) := ContinuousMap.const X ()
  let q : C(Unit, Y) := ContinuousMap.const Unit y
  let F := (AlgebraicTopology.singularHomologyFunctor D n).obj R
  have hfactor : ContinuousMap.const X y = q.comp p := by
    ext
    rfl
  have hzero : IsZero (F.obj (TopCat.of Unit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      D n R (TopCat.of Unit) hn
  rw [hfactor]
  change F.map (TopCat.ofHom (q.comp p)) = 0
  rw [show TopCat.ofHom (q.comp p) = TopCat.ofHom p ≫ TopCat.ofHom q by rfl,
    F.map_comp]
  have hq : F.map (TopCat.ofHom q) = 0 := hzero.eq_of_src _ _
  rw [hq]
  simp

/-- A nullhomotopic continuous map induces zero on singular homology in every
positive degree. -/
theorem singularHomology_map_eq_zero_of_nullhomotopic
    (D : Type*) [Category D] [Preadditive D] [HasCoproducts D]
    [CategoryWithHomology D] (R : D)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (f : C(X, Y))
    (hf : ContinuousMap.Nullhomotopic f) :
    ((AlgebraicTopology.singularHomologyFunctor D n).obj R).map
      (TopCat.ofHom f) = 0 := by
  rcases hf with ⟨y, H⟩
  rw [singularHomology_map_eq_of_homotopic D R H n]
  exact singularHomology_map_const_eq_zero D R n hn y

#print axioms singularHomology_map_eq_of_topCatHomotopy
#print axioms continuousMapHomotopyCylinder
#print axioms singularHomology_map_eq_of_homotopic
#print axioms singularHomology_map_const_eq_zero
#print axioms singularHomology_map_eq_zero_of_nullhomotopic

end ConstructionTargets.SingularHomologyHomotopy
