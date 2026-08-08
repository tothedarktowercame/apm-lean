import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t98A02 — homology of a connected sum of four-manifolds

The connected sum is the actual quotient described in the source: remove the
open interiors of two embedded closed four-balls and identify corresponding
points of their boundary three-spheres.  Its homology groups are Mathlib's
integral singular homology modules.

## Statement repairs

The construction and the supplied top-homology fact require `X₁` and `X₂` to
be closed.  The source initially says only “connected oriented 4-manifolds,”
but its intended solution uses closedness.  We therefore include compactness,
along with the supplied integral top-homology hypotheses.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev T98A02E4 := EuclideanSpace ℝ (Fin 4)
abbrev T98A02I4 := 𝓘(ℝ, T98A02E4)
abbrev T98A02Disk := Metric.closedBall (0 : T98A02E4) 1
abbrev T98A02Sphere := Metric.sphere (0 : T98A02E4) 1

def t98A02SphereInDisk (x : T98A02Sphere) : T98A02Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

abbrev T98A02Punctured (X : Type) (φ : T98A02Disk → X) :=
  {x : X // x ∉ φ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}}

inductive T98A02GlueRel {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Sum (T98A02Punctured X₁ φ₁) (T98A02Punctured X₂ φ₂) →
      Sum (T98A02Punctured X₁ φ₁) (T98A02Punctured X₂ φ₂) → Prop
  | boundary (s : T98A02Sphere)
      (h₁ : φ₁ (t98A02SphereInDisk s) ∉
        φ₁ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1})
      (h₂ : φ₂ (t98A02SphereInDisk s) ∉
        φ₂ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}) :
      T98A02GlueRel φ₁ φ₂
        (Sum.inl ⟨φ₁ (t98A02SphereInDisk s), h₁⟩)
        (Sum.inr ⟨φ₂ (t98A02SphereInDisk s), h₂⟩)

def T98A02ConnectedSum {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :=
  Quotient (Relation.EqvGen.setoid (T98A02GlueRel φ₁ φ₂))

noncomputable instance {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    TopologicalSpace (T98A02ConnectedSum φ₁ φ₂) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

def t98A02QuotientMap {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Sum (T98A02Punctured X₁ φ₁) (T98A02Punctured X₂ φ₂) →
      T98A02ConnectedSum φ₁ φ₂ :=
  fun z ↦ Quotient.mk _ z

lemma t98A02_continuous_quotientMap
    {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Continuous (t98A02QuotientMap φ₁ φ₂) := by
  exact continuous_coinduced_rng

lemma t98A02_surjective_quotientMap
    {X₁ X₂ : Type} (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Function.Surjective (t98A02QuotientMap φ₁ φ₂) := by
  exact Quotient.mk_surjective

def t98A02_leftInclusion {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    T98A02Punctured X₁ φ₁ → T98A02ConnectedSum φ₁ φ₂ :=
  fun x ↦ t98A02QuotientMap φ₁ φ₂ (.inl x)

def t98A02_rightInclusion {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    T98A02Punctured X₂ φ₂ → T98A02ConnectedSum φ₁ φ₂ :=
  fun x ↦ t98A02QuotientMap φ₁ φ₂ (.inr x)

lemma t98A02_continuous_leftInclusion
    {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Continuous (t98A02_leftInclusion φ₁ φ₂) := by
  exact (t98A02_continuous_quotientMap φ₁ φ₂).comp continuous_inl

lemma t98A02_continuous_rightInclusion
    {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Continuous (t98A02_rightInclusion φ₁ φ₂) := by
  exact (t98A02_continuous_quotientMap φ₁ φ₂).comp continuous_inr

lemma t98A02_boundary_identified
    {X₁ X₂ : Type} (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (s : T98A02Sphere)
    (h₁ : φ₁ (t98A02SphereInDisk s) ∉
      φ₁ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1})
    (h₂ : φ₂ (t98A02SphereInDisk s) ∉
      φ₂ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}) :
    t98A02_leftInclusion φ₁ φ₂ ⟨φ₁ (t98A02SphereInDisk s), h₁⟩ =
      t98A02_rightInclusion φ₁ φ₂ ⟨φ₂ (t98A02SphereInDisk s), h₂⟩ := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (T98A02GlueRel.boundary s h₁ h₂))

lemma t98A02_gluedDesc_respects
    {X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z))
    (hfg : ∀ (s : T98A02Sphere)
      (h₁ : φ₁ (t98A02SphereInDisk s) ∉
        φ₁ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1})
      (h₂ : φ₂ (t98A02SphereInDisk s) ∉
        φ₂ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}),
      f ⟨φ₁ (t98A02SphereInDisk s), h₁⟩ =
        g ⟨φ₂ (t98A02SphereInDisk s), h₂⟩)
    {x y} (hxy : Relation.EqvGen (T98A02GlueRel φ₁ φ₂) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab with
      | boundary s h₁ h₂ => exact hfg s h₁ h₂
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def t98A02_gluedDesc
    {X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z))
    (hfg : ∀ (s : T98A02Sphere)
      (h₁ : φ₁ (t98A02SphereInDisk s) ∉
        φ₁ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1})
      (h₂ : φ₂ (t98A02SphereInDisk s) ∉
        φ₂ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}),
      f ⟨φ₁ (t98A02SphereInDisk s), h₁⟩ =
        g ⟨φ₂ (t98A02SphereInDisk s), h₂⟩) :
    C(T98A02ConnectedSum φ₁ φ₂, Z) := by
  let raw := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy ↦
      t98A02_gluedDesc_respects φ₁ φ₂ f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy ↦
      t98A02_gluedDesc_respects φ₁ φ₂ f g hfg hxy)⟩

@[simp] lemma t98A02_gluedDesc_leftInclusion
    {X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z))
    (hfg) (x : T98A02Punctured X₁ φ₁) :
    t98A02_gluedDesc φ₁ φ₂ f g hfg (t98A02_leftInclusion φ₁ φ₂ x) = f x := rfl

@[simp] lemma t98A02_gluedDesc_rightInclusion
    {X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z))
    (hfg) (x : T98A02Punctured X₂ φ₂) :
    t98A02_gluedDesc φ₁ φ₂ f g hfg (t98A02_rightInclusion φ₁ φ₂ x) = g x := rfl

lemma t98A02_gluedDesc_unique
    {X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z))
    (hfg) (u : C(T98A02ConnectedSum φ₁ φ₂, Z))
    (hul : ∀ x, u (t98A02_leftInclusion φ₁ φ₂ x) = f x)
    (hur : ∀ x, u (t98A02_rightInclusion φ₁ φ₂ x) = g x) :
    u = t98A02_gluedDesc φ₁ φ₂ f g hfg := by
  ext y
  obtain ⟨x, rfl⟩ := t98A02_surjective_quotientMap φ₁ φ₂ y
  cases x with
  | inl x => exact hul x
  | inr x => exact hur x

abbrev t98A02H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem apm_t98a02 :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 ⊤ X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 ⊤ X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  /-
  PARTIAL boundary (closer hop 2). Following the quotient-eliminator pattern
  indexed in `LEMMA-INDEX.md` from siblings `t01J03`, `t02A04`, and `t03J02`,
  this hop compiles the full point-set gluing interface.
  `t98A02QuotientMap` is continuous and surjective, the two punctured-piece
  inclusions are continuous, and `t98A02_boundary_identified` proves the
  generating boundary equality. `t98A02_gluedDesc_respects` performs EqvGen
  induction; `t98A02_gluedDesc`, its two computation lemmas, and
  `t98A02_gluedDesc_unique` give the continuous universal property of the
  connected-sum quotient.

  Searches of `ConstructionTargets/`, all connected-sum and gluing siblings,
  Mathlib's singular-homology, excision, exact-sequence, CW, manifold, and
  Mayer--Vietoris sources, and git history found no singular excision theorem,
  singular Mayer--Vietoris sequence, or cellular-to-singular comparison.
  Mathlib's named Mayer--Vietoris development is for sheaf cohomology and does
  not apply to `t98A02H`. Completing the frozen conclusions additionally needs
  homology invariance under deleting an embedded open four-ball in degrees
  `1..3`, the boundary-sphere connecting map/top-degree orientation argument,
  connectedness of this quotient for `H₀`, and dimension-vanishing above
  four. The compiled topological pushout eliminator does not by itself supply
  those homological bridges.
  -/
  sorry
