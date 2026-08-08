import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t03J05: product tori distinguished in every ambient four-manifold

## Statement repairs

Mathlib has no oriented-intersection API for embedded submanifolds.  The
nonzero integer intersection assertion in part (a) is minimally weakened to
nonzero mod-2 intersection, computed from the actual intersection of the two
embedded torus images.

## Encoding questions

The genus-two surface is the concrete polygon quotient `Surface true 2` from
`ConstructionTargets.Surfaces`. The puncture, product-torus maps, their actual
image intersection, every ambient smooth four-manifold and open inclusion,
and the asserted non-homotopies are genuine objects.
-/

open scoped ContDiff Manifold
open ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t03J05_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t03J05_E4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t03J05_I2 := modelWithCornersSelf ℝ apm_t03J05_E2
abbrev apm_t03J05_I4 := modelWithCornersSelf ℝ apm_t03J05_E4
abbrev apm_t03J05_Torus := Circle × Circle
abbrev apm_t03J05_GenusTwoSurface := Surface true 2

def apm_t03J05_productTorusMap {F : Type} [TopologicalSpace F]
    (a b : C(Circle, F)) : C(apm_t03J05_Torus, F × F) :=
  ⟨fun st ↦ (a st.1, b st.2),
    (a.continuous.comp continuous_fst).prodMk
      (b.continuous.comp continuous_snd)⟩

def apm_t03J05_imageIntersection {M : Type} [TopologicalSpace M]
    (f g : C(apm_t03J05_Torus, M)) : Set M :=
  Set.range f ∩ Set.range g

abbrev apm_t03J05_punctured (F : Type) (x : F) := {y : F // y ≠ x}

def apm_t03J05_unpunctureCurve {F : Type} [TopologicalSpace F]
    (x : F) (a : C(Circle, apm_t03J05_punctured F x)) : C(Circle, F) :=
  ⟨fun s ↦ (a s).1, continuous_subtype_val.comp a.continuous⟩

lemma apm_t03J05_eulerCharacteristic_genusTwo :
    eulerCharacteristic true 2 = -2 := by
  norm_num [eulerCharacteristic]

/-- Products of embedded circle parametrizations give embedded product tori. -/
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

/-- The actual intersection of two diagonal product tori is exactly the
Cartesian square of the corresponding curve-image intersection. -/
lemma apm_t03J05_imageIntersection_product_self
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F)) :
    apm_t03J05_imageIntersection
        (apm_t03J05_productTorusMap a a)
        (apm_t03J05_productTorusMap b b) =
      (Set.range a ∩ Set.range b) ×ˢ (Set.range a ∩ Set.range b) := by
  ext p
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact ⟨⟨⟨s.1, congrArg Prod.fst hs⟩, ⟨t.1, congrArg Prod.fst ht⟩⟩,
      ⟨⟨s.2, congrArg Prod.snd hs⟩, ⟨t.2, congrArg Prod.snd ht⟩⟩⟩
  · rintro ⟨⟨⟨s₁, hs₁⟩, ⟨t₁, ht₁⟩⟩,
      ⟨⟨s₂, hs₂⟩, ⟨t₂, ht₂⟩⟩⟩
    exact ⟨⟨(s₁, s₂), Prod.ext hs₁ hs₂⟩,
      ⟨(t₁, t₂), Prod.ext ht₁ ht₂⟩⟩

lemma apm_t03J05_card_imageIntersection_product_self
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F)) :
    Nat.card {p // p ∈ apm_t03J05_imageIntersection
        (apm_t03J05_productTorusMap a a)
        (apm_t03J05_productTorusMap b b)} =
      Nat.card {x // x ∈ Set.range a ∩ Set.range b} ^ 2 := by
  rw [apm_t03J05_imageIntersection_product_self]
  calc
    Nat.card {p // p ∈ (Set.range a ∩ Set.range b) ×ˢ
        (Set.range a ∩ Set.range b)} =
        Nat.card ({x // x ∈ Set.range a ∩ Set.range b} ×
          {x // x ∈ Set.range a ∩ Set.range b}) :=
      Nat.card_congr Equiv.subtypeProdEquivProd
    _ = Nat.card {x // x ∈ Set.range a ∩ Set.range b} ^ 2 := by
      rw [Nat.card_prod, pow_two]

lemma apm_t03J05_odd_imageIntersection_product_self
    {F : Type} [TopologicalSpace F] (a b : C(Circle, F))
    (hodd : Nat.card {x // x ∈ Set.range a ∩ Set.range b} % 2 = 1) :
    Nat.card {p // p ∈ apm_t03J05_imageIntersection
        (apm_t03J05_productTorusMap a a)
        (apm_t03J05_productTorusMap b b)} % 2 = 1 := by
  rw [apm_t03J05_card_imageIntersection_product_self, pow_two, Nat.mul_mod,
    hodd]

theorem apm_t03j05
    :
    eulerCharacteristic true 2 = -2 ∧
    ∃ (x : apm_t03J05_GenusTwoSurface)
        (a₁ b₁ a₂ b₂ :
          C(Circle, apm_t03J05_punctured apm_t03J05_GenusTwoSurface x)),
      Topology.IsEmbedding a₁ ∧ Topology.IsEmbedding b₁ ∧
      Topology.IsEmbedding a₂ ∧ Topology.IsEmbedding b₂ ∧
      let A₁ := apm_t03J05_unpunctureCurve x a₁
      let B₁ := apm_t03J05_unpunctureCurve x b₁
      Topology.IsEmbedding (apm_t03J05_productTorusMap A₁ A₁) ∧
      Topology.IsEmbedding (apm_t03J05_productTorusMap B₁ B₁) ∧
      Nat.card {p // p ∈ apm_t03J05_imageIntersection
        (apm_t03J05_productTorusMap A₁ A₁)
        (apm_t03J05_productTorusMap B₁ B₁)} % 2 = 1 ∧
      let g : Fin 3 →
          C(apm_t03J05_Torus,
            apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
              apm_t03J05_punctured apm_t03J05_GenusTwoSurface x) :=
        ![apm_t03J05_productTorusMap a₁ a₁,
          apm_t03J05_productTorusMap b₁ b₁,
          apm_t03J05_productTorusMap a₂ a₂]
      (∀ i, Topology.IsEmbedding (g i)) ∧
      ∀ (X : Type)
          [TopologicalSpace X]
          [ChartedSpace apm_t03J05_E4 X]
          [IsManifold apm_t03J05_I4 (⊤ : ℕ∞) X]
          [BoundarylessManifold apm_t03J05_I4 X]
          (incl : C(
            apm_t03J05_punctured apm_t03J05_GenusTwoSurface x ×
            apm_t03J05_punctured apm_t03J05_GenusTwoSurface x, X)),
        Topology.IsOpenEmbedding incl →
        ∀ i j : Fin 3, i ≠ j →
          ¬ ContinuousMap.Homotopic
            (incl.comp (g i)) (incl.comp (g j)) := by
  /-
  CLOSER HOP 3 boundary. Going beyond the previous generic embedding work,
  this hop eliminates the four-dimensional intersection-cardinality
  calculation. `apm_t03J05_imageIntersection_product_self` proves that the
  actual intersection of the diagonal product-torus images is exactly the
  Cartesian square of the two curve images' intersection.
  `apm_t03J05_card_imageIntersection_product_self` transports this equality
  through `Equiv.subtypeProdEquivProd` and `Nat.card_prod`, and
  `apm_t03J05_odd_imageIntersection_product_self` proves that an odd curve
  intersection automatically gives the frozen odd product-torus intersection.
  The Euler conjunct is also now assembled directly in the main theorem.

  Renewed searches consulted `LEMMA-INDEX.md`, all `ConstructionTargets/`,
  the promoted polygon-surface source, sibling `t03J03`, the RP² intersection
  artifact `t96J06`, Mathlib's set-product/subtype equivalences, quotient
  topology, circle embeddings, mod-two intersection, singular homology, and
  ambient homotopy APIs, plus git history. The set-product machinery was used
  above; no concrete embedded curve system on `Surface true 2` or invariant
  proving ambient nonhomotopy under every open embedding was found.

  The remaining geometric bridge is now narrower: construct the four punctured
  curves with odd two-dimensional image intersection, then supply the ambient
  homotopy invariant for the three resulting product tori. The frozen
  statement is unchanged.
  -/
  refine ⟨apm_t03J05_eulerCharacteristic_genusTwo, ?_⟩
  sorry
