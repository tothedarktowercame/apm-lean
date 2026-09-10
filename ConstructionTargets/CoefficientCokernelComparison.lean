import ConstructionTargets.CoefficientSmallComparison
import Mathlib.Algebra.Homology.HomologySequenceLemmas
noncomputable section
namespace ConstructionTargets.CoefficientCokernelComparison
open CategoryTheory CategoryTheory.Limits
variable (R : Type) [CommRing R]
noncomputable def cokernelShortComplex
    {K L : ChainComplex (ModuleCat.{0} R) ℕ} (f : K ⟶ L) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

theorem cokernelShortComplex_shortExact
    {K L : ChainComplex (ModuleCat.{0} R) ℕ} (f : K ⟶ L) [Mono f] :
    (cokernelShortComplex R f).ShortExact := by
  apply ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
  · change Mono f
    infer_instance
  · change Epi (cokernel.π f)
    infer_instance

/-- A commuting square of chain maps induces the corresponding morphism of
cokernel short exact sequences. -/
noncomputable def cokernelSquareMap
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') :
    cokernelShortComplex R f ⟶ cokernelShortComplex R f' :=
  ShortComplex.homMk a b (cokernel.map f f' a b h) h.symm (by
    dsimp [cokernelShortComplex]
    symm
    apply cokernel.π_desc)

/-- Consumer-level relative comparison: if the two absolute vertical maps in
a square of monic chain maps induce isomorphisms in a degree and the adjacent
degree, then so does the induced map on relative cokernels. -/
theorem cokernelSquare_homologyMap_isIso
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f'] (i : ℕ)
    (ha : IsIso (HomologicalComplex.homologyMap a i))
    (hb : IsIso (HomologicalComplex.homologyMap b i))
    (haPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap a j))
    (hbPrev : ∀ j, (ComplexShape.down ℕ).Rel i j →
      IsIso (HomologicalComplex.homologyMap b j)) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.map f f' a b h) i) := by
  let φ := cokernelSquareMap R f f' a b h
  have hφ := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
    (cokernelShortComplex_shortExact R f)
    (cokernelShortComplex_shortExact R f') i
  apply hφ
  · change Epi (HomologicalComplex.homologyMap a i)
    letI := ha
    infer_instance
  · change IsIso (HomologicalComplex.homologyMap b i)
    exact hb
  · intro j hj
    change IsIso (HomologicalComplex.homologyMap a j)
    exact haPrev j hj
  · intro j hj
    change Mono (HomologicalComplex.homologyMap b j)
    letI := hbPrev j hj
    infer_instance

/-- All chain modules and R are Type 0. This is a comparison of actual cokernels. -/
def comparisonIso
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f']
    (ha : ∀ n, IsIso (HomologicalComplex.homologyMap a n))
    (hb : ∀ n, IsIso (HomologicalComplex.homologyMap b n)) (n : ℕ) :
    (cokernel f).homology n ≅ (cokernel f').homology n := by
  letI := cokernelSquare_homologyMap_isIso R f f' a b h n (ha n) (hb n)
    (fun j _ => ha j) (fun j _ => hb j)
  exact asIso (HomologicalComplex.homologyMap (cokernel.map f f' a b h) n)

theorem comparisonIso_hom
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f']
    (ha : ∀ n, IsIso (HomologicalComplex.homologyMap a n))
    (hb : ∀ n, IsIso (HomologicalComplex.homologyMap b n)) (n : ℕ) :
    (comparisonIso R f f' a b h ha hb n).hom =
      HomologicalComplex.homologyMap (cokernel.map f f' a b h) n := rfl

theorem inverse_left
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f']
    (ha : ∀ n, IsIso (HomologicalComplex.homologyMap a n))
    (hb : ∀ n, IsIso (HomologicalComplex.homologyMap b n)) (n : ℕ) :
    (comparisonIso R f f' a b h ha hb n).inv ≫
      HomologicalComplex.homologyMap (cokernel.map f f' a b h) n = 𝟙 _ :=
  (comparisonIso R f f' a b h ha hb n).inv_hom_id

theorem inverse_right
    {K L K' L' : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ f') [Mono f] [Mono f']
    (ha : ∀ n, IsIso (HomologicalComplex.homologyMap a n))
    (hb : ∀ n, IsIso (HomologicalComplex.homologyMap b n)) (n : ℕ) :
    HomologicalComplex.homologyMap (cokernel.map f f' a b h) n ≫
      (comparisonIso R f f' a b h ha hb n).inv = 𝟙 _ :=
  (comparisonIso R f f' a b h ha hb n).hom_inv_id

def integral_identity_example (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (cokernel (𝟙 C)).homology n ≅ (cokernel (𝟙 C)).homology n :=
  comparisonIso ℤ (𝟙 C) (𝟙 C) (𝟙 C) (𝟙 C) rfl
    (fun j => by simp only [HomologicalComplex.homologyMap_id]; infer_instance)
    (fun j => by simp only [HomologicalComplex.homologyMap_id]; infer_instance) n

def rational_identity_example (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (cokernel (𝟙 C)).homology n ≅ (cokernel (𝟙 C)).homology n :=
  comparisonIso ℚ (𝟙 C) (𝟙 C) (𝟙 C) (𝟙 C) rfl
    (fun j => by simp only [HomologicalComplex.homologyMap_id]; infer_instance)
    (fun j => by simp only [HomologicalComplex.homologyMap_id]; infer_instance) n

#print axioms cokernelShortComplex_shortExact
#print axioms cokernelSquare_homologyMap_isIso
#print axioms comparisonIso_hom
#print axioms inverse_left
#print axioms inverse_right
end ConstructionTargets.CoefficientCokernelComparison
