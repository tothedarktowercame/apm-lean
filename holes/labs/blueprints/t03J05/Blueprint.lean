import Mathlib
import ConstructionTargets.Surfaces

open scoped ContDiff Manifold
open ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t03J05_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t03J05_E4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t03J05_I4 := modelWithCornersSelf ℝ apm_t03J05_E4
abbrev apm_t03J05_Torus := Circle × Circle
abbrev apm_t03J05_GenusTwoSurface := Surface true 2

def apm_t03J05_productTorusMap {F : Type} [TopologicalSpace F]
    (a b : C(Circle, F)) : C(apm_t03J05_Torus, F × F) :=
  ⟨fun st ↦ (a st.1, b st.2),
    (a.continuous.comp continuous_fst).prodMk
      (b.continuous.comp continuous_snd)⟩

def apm_t03J05_imageIntersection {M : Type} [TopologicalSpace M]
    (f g : C(apm_t03J05_Torus, M)) : Set M := Set.range f ∩ Set.range g

abbrev apm_t03J05_punctured (F : Type) (x : F) := {y : F // y ≠ x}

def apm_t03J05_unpunctureCurve {F : Type} [TopologicalSpace F]
    (x : F) (a : C(Circle, apm_t03J05_punctured F x)) : C(Circle, F) :=
  ⟨fun s ↦ (a s).1, continuous_subtype_val.comp a.continuous⟩

def apm_t03J05_IsSingleTransverseCrossing {F : Type} [TopologicalSpace F]
    (a b : C(Circle, F)) : Prop :=
  ∃ p : F, Set.range a ∩ Set.range b = {p} ∧
    ∃ U : Set F, IsOpen U ∧ p ∈ U ∧
      ∃ e : U ≃ₜ apm_t03J05_E2,
        (∀ y : U, y.1 ∈ Set.range a ↔ (e y) 1 = 0) ∧
        (∀ y : U, y.1 ∈ Set.range b ↔ (e y) 0 = 0)

structure apm_t03J05_CurveSystem
    (x : apm_t03J05_GenusTwoSurface)
    (a₁ b₁ a₂ b₂ : C(Circle,
      apm_t03J05_punctured apm_t03J05_GenusTwoSurface x)) : Prop where
  emb_a₁ : Topology.IsEmbedding a₁
  emb_b₁ : Topology.IsEmbedding b₁
  emb_a₂ : Topology.IsEmbedding a₂
  emb_b₂ : Topology.IsEmbedding b₂
  cross₁ : apm_t03J05_IsSingleTransverseCrossing
    (apm_t03J05_unpunctureCurve x a₁) (apm_t03J05_unpunctureCurve x b₁)
  cross₂ : apm_t03J05_IsSingleTransverseCrossing
    (apm_t03J05_unpunctureCurve x a₂) (apm_t03J05_unpunctureCurve x b₂)
  disjoint_a₁_a₂ : Disjoint (Set.range a₁) (Set.range a₂)
  disjoint_a₁_b₂ : Disjoint (Set.range a₁) (Set.range b₂)
  disjoint_b₁_a₂ : Disjoint (Set.range b₁) (Set.range a₂)
  disjoint_b₁_b₂ : Disjoint (Set.range b₁) (Set.range b₂)

lemma apm_t03J05_eulerCharacteristic_genusTwo :
    eulerCharacteristic true 2 = -2 := by
  norm_num [eulerCharacteristic]

lemma apm_t03J05_productTorusMap_isEmbedding
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b) :
    Topology.IsEmbedding (apm_t03J05_productTorusMap a b) := by
  exact ha.prodMap hb

lemma apm_t03J05_unpunctureCurve_isEmbedding
    {F : Type} [TopologicalSpace F] (x : F)
    (a : C(Circle, apm_t03J05_punctured F x))
    (ha : Topology.IsEmbedding a) :
    Topology.IsEmbedding (apm_t03J05_unpunctureCurve x a) := by
  exact Topology.IsEmbedding.subtypeVal.comp ha

lemma apm_t03J05_imageIntersection_product_self
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F)) :
    apm_t03J05_imageIntersection (apm_t03J05_productTorusMap a a)
        (apm_t03J05_productTorusMap b b) =
      (Set.range a ∩ Set.range b) ×ˢ (Set.range a ∩ Set.range b) := by
  ext p
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact ⟨⟨⟨s.1, congrArg Prod.fst hs⟩, ⟨t.1, congrArg Prod.fst ht⟩⟩,
      ⟨⟨s.2, congrArg Prod.snd hs⟩, ⟨t.2, congrArg Prod.snd ht⟩⟩⟩
  · rintro ⟨⟨⟨s₁, hs₁⟩, ⟨t₁, ht₁⟩⟩, ⟨⟨s₂, hs₂⟩, ⟨t₂, ht₂⟩⟩⟩
    exact ⟨⟨(s₁, s₂), Prod.ext hs₁ hs₂⟩,
      ⟨(t₁, t₂), Prod.ext ht₁ ht₂⟩⟩

lemma apm_t03J05_odd_product_intersection_of_crossing
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F))
    (h : apm_t03J05_IsSingleTransverseCrossing a b) :
    Nat.card {p // p ∈ apm_t03J05_imageIntersection
      (apm_t03J05_productTorusMap a a)
      (apm_t03J05_productTorusMap b b)} % 2 = 1 := by
  rcases h with ⟨p, hp, -⟩
  rw [apm_t03J05_imageIntersection_product_self, hp]
  simp

/-- **LIBRARY: polygon-surface curve geometry.** -/
theorem apm_t03J05_genusTwo_curve_system :
    ∃ (x : apm_t03J05_GenusTwoSurface)
      (a₁ b₁ a₂ b₂ : C(Circle,
        apm_t03J05_punctured apm_t03J05_GenusTwoSurface x)),
      apm_t03J05_CurveSystem x a₁ b₁ a₂ b₂ := by
  sorry

/-- **LIBRARY: localized mod-2 intersection and ambient invariance.** -/
theorem apm_t03J05_curve_system_ambient_separation
    (x : apm_t03J05_GenusTwoSurface)
    (a₁ b₁ a₂ b₂ : C(Circle,
      apm_t03J05_punctured apm_t03J05_GenusTwoSurface x))
    (hs : apm_t03J05_CurveSystem x a₁ b₁ a₂ b₂) :
    let g : Fin 3 → C(apm_t03J05_Torus,
        apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
          apm_t03J05_punctured apm_t03J05_GenusTwoSurface x) :=
      ![apm_t03J05_productTorusMap a₁ a₁,
        apm_t03J05_productTorusMap b₁ b₁,
        apm_t03J05_productTorusMap a₂ a₂]
    (∀ i, Topology.IsEmbedding (g i)) ∧
    ∀ (X : Type) [TopologicalSpace X] [T2Space X]
        [ChartedSpace apm_t03J05_E4 X]
        [IsManifold apm_t03J05_I4 (⊤ : ℕ∞) X]
        [BoundarylessManifold apm_t03J05_I4 X]
        (incl : C(apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
          apm_t03J05_punctured apm_t03J05_GenusTwoSurface x, X)),
      Topology.IsOpenEmbedding incl → ∀ i j : Fin 3, i ≠ j →
        ¬ ContinuousMap.Homotopic (incl.comp (g i)) (incl.comp (g j)) := by
  sorry

theorem apm_t03j05 :
    eulerCharacteristic true 2 = -2 ∧
    ∃ (x : apm_t03J05_GenusTwoSurface)
        (a₁ b₁ a₂ b₂ : C(Circle, apm_t03J05_punctured apm_t03J05_GenusTwoSurface x)),
      Topology.IsEmbedding a₁ ∧ Topology.IsEmbedding b₁ ∧
      Topology.IsEmbedding a₂ ∧ Topology.IsEmbedding b₂ ∧
      let A₁ := apm_t03J05_unpunctureCurve x a₁
      let B₁ := apm_t03J05_unpunctureCurve x b₁
      Topology.IsEmbedding (apm_t03J05_productTorusMap A₁ A₁) ∧
      Topology.IsEmbedding (apm_t03J05_productTorusMap B₁ B₁) ∧
      apm_t03J05_IsSingleTransverseCrossing A₁ B₁ ∧
      Nat.card {p // p ∈ apm_t03J05_imageIntersection
        (apm_t03J05_productTorusMap A₁ A₁)
        (apm_t03J05_productTorusMap B₁ B₁)} % 2 = 1 ∧
      let g : Fin 3 → C(apm_t03J05_Torus,
          apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
            apm_t03J05_punctured apm_t03J05_GenusTwoSurface x) :=
        ![apm_t03J05_productTorusMap a₁ a₁,
          apm_t03J05_productTorusMap b₁ b₁,
          apm_t03J05_productTorusMap a₂ a₂]
      (∀ i, Topology.IsEmbedding (g i)) ∧
      ∀ (X : Type) [TopologicalSpace X] [T2Space X]
          [ChartedSpace apm_t03J05_E4 X]
          [IsManifold apm_t03J05_I4 (⊤ : ℕ∞) X]
          [BoundarylessManifold apm_t03J05_I4 X]
          (incl : C(apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
            apm_t03J05_punctured apm_t03J05_GenusTwoSurface x, X)),
        Topology.IsOpenEmbedding incl → ∀ i j : Fin 3, i ≠ j →
          ¬ ContinuousMap.Homotopic (incl.comp (g i)) (incl.comp (g j)) := by
  refine ⟨apm_t03J05_eulerCharacteristic_genusTwo, ?_⟩
  rcases apm_t03J05_genusTwo_curve_system with ⟨x, a₁, b₁, a₂, b₂, hs⟩
  refine ⟨x, a₁, b₁, a₂, b₂, hs.emb_a₁, hs.emb_b₁, hs.emb_a₂, hs.emb_b₂, ?_⟩
  dsimp only
  refine ⟨apm_t03J05_productTorusMap_isEmbedding _ _
      (apm_t03J05_unpunctureCurve_isEmbedding x a₁ hs.emb_a₁)
      (apm_t03J05_unpunctureCurve_isEmbedding x a₁ hs.emb_a₁),
    apm_t03J05_productTorusMap_isEmbedding _ _
      (apm_t03J05_unpunctureCurve_isEmbedding x b₁ hs.emb_b₁)
      (apm_t03J05_unpunctureCurve_isEmbedding x b₁ hs.emb_b₁),
    hs.cross₁, apm_t03J05_odd_product_intersection_of_crossing _ _ hs.cross₁, ?_⟩
  exact apm_t03J05_curve_system_ambient_separation x a₁ b₁ a₂ b₂ hs

#print axioms apm_t03j05
