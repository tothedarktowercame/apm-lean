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
  sorry
