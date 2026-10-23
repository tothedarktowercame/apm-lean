import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CollaredConnectedSumHomology

/-!
# Blueprint for APM t98A02

The missing input is a connected-sum theorem for the concrete collared quotient
and Mathlib's integral singular-homology functor.  It is isolated below as one
library-scale theorem; the registered theorem is then a direct application.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev T98A02E4 := EuclideanSpace ℝ (Fin 4)
abbrev T98A02I4 := modelWithCornersSelf ℝ T98A02E4
abbrev T98A02Disk := Metric.closedBall (0 : T98A02E4) 1
abbrev T98A02Sphere := Metric.sphere (0 : T98A02E4) 1

def t98A02SphereInDisk (x : T98A02Sphere) : T98A02Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

abbrev T98A02CollarBall := Metric.closedBall (0 : T98A02E4) 2

def t98A02DiskInCollarBall (u : T98A02Disk) : T98A02CollarBall :=
  ⟨u, Metric.closedBall_subset_closedBall (by norm_num) u.property⟩

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

abbrev t98A02H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

namespace T98A02Adapter

open ConstructionTargets.CollaredConnectedSumHomology

/-- **LIBRARY (B12a).** The frozen quotient presentation agrees with the
generic collared connected-sum quotient. -/
theorem quotientHomeomorph {X₁ X₂ : Type}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (c₁ : BallCollar 4 X₁) (c₂ : BallCollar 4 X₂)
    (hc₁ : c₁.smallMap = φ₁) (hc₂ : c₂.smallMap = φ₂) :
    Nonempty (T98A02ConnectedSum φ₁ φ₂ ≃ₜ ConnectedSum c₁ c₂) := by
  subst φ₁
  subst φ₂
  let p₁ : T98A02Punctured X₁ c₁.smallMap → c₁.Punctured := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let p₂ : T98A02Punctured X₂ c₂.smallMap → c₂.Punctured := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let q₁ : c₁.Punctured → T98A02Punctured X₁ c₁.smallMap := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let q₂ : c₂.Punctured → T98A02Punctured X₂ c₂.smallMap := fun x ↦
    ⟨x.1, by simpa [dist_eq_norm] using x.2⟩
  let f : Sum (T98A02Punctured X₁ c₁.smallMap)
      (T98A02Punctured X₂ c₂.smallMap) → Sum c₁.Punctured c₂.Punctured
    | Sum.inl x => Sum.inl (p₁ x)
    | Sum.inr x => Sum.inr (p₂ x)
  let g : Sum c₁.Punctured c₂.Punctured →
      Sum (T98A02Punctured X₁ c₁.smallMap)
        (T98A02Punctured X₂ c₂.smallMap)
    | Sum.inl x => Sum.inl (q₁ x)
    | Sum.inr x => Sum.inr (q₂ x)
  have hfg (x) : g (f x) = x := by
    cases x <;> simp [f, g, p₁, p₂, q₁, q₂]
  have hgf (x) : f (g x) = x := by
    cases x <;> simp [f, g, p₁, p₂, q₁, q₂]
  have hfrel {x y} (h : T98A02GlueRel c₁.smallMap c₂.smallMap x y) :
      Relation.EqvGen (GlueRel c₁ c₂) (f x) (f y) := by
    cases h with
    | boundary s h₁ h₂ =>
      apply Relation.EqvGen.rel
      exact GlueRel.boundary s
  have hgrel {x y} (h : GlueRel c₁ c₂ x y) :
      Relation.EqvGen (T98A02GlueRel c₁.smallMap c₂.smallMap) (g x) (g y) := by
    cases h with
    | boundary s =>
      apply Relation.EqvGen.rel
      apply T98A02GlueRel.boundary s
  let F : T98A02ConnectedSum c₁.smallMap c₂.smallMap → ConnectedSum c₁ c₂ :=
    Quotient.map' f (fun _ _ h => by
      change Relation.EqvGen (GlueRel c₁ c₂) _ _
      induction h with
      | rel _ _ h => exact hfrel h
      | refl x => exact (Relation.EqvGen.refl (f x) :
          Relation.EqvGen (GlueRel c₁ c₂) (f x) (f x))
      | symm _ _ _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans (f x) (f y) (f z) ih₁ ih₂)
  let G : ConnectedSum c₁ c₂ → T98A02ConnectedSum c₁.smallMap c₂.smallMap :=
    Quotient.map' g (fun _ _ h => by
      change Relation.EqvGen (T98A02GlueRel c₁.smallMap c₂.smallMap) _ _
      induction h with
      | rel _ _ h => exact hgrel h
      | refl x => exact (Relation.EqvGen.refl (g x) :
          Relation.EqvGen (T98A02GlueRel c₁.smallMap c₂.smallMap) (g x) (g x))
      | symm _ _ _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans (g x) (g y) (g z) ih₁ ih₂)
  have hFG (x) : G (F x) = x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      have hh := congrArg
        (Quotient.mk (Relation.EqvGen.setoid (T98A02GlueRel c₁.smallMap c₂.smallMap))) (hfg x)
      simpa [F, G] using hh
  have hGF (x) : F (G x) = x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      have hh := congrArg (Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))) (hgf x)
      simpa [F, G] using hh
  have hfcont : Continuous f := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_inl.comp (continuous_subtype_val.subtype_mk _)
    · exact continuous_inr.comp (continuous_subtype_val.subtype_mk _)
  have hgcont : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_inl.comp (continuous_subtype_val.subtype_mk _)
    · exact continuous_inr.comp (continuous_subtype_val.subtype_mk _)
  refine ⟨{ toEquiv := ⟨F, G, hFG, hGF⟩, continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · rw [continuous_coinduced_dom]
    exact continuous_coinduced_rng.comp hfcont
  · rw [continuous_coinduced_dom]
    exact continuous_coinduced_rng.comp hgcont

/-- **LIBRARY (B12b).** Homology invariance transports the complete table
across the quotient homeomorphism. -/
theorem transportHomology {X₁ X₂ : Type}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂)
    (c₁ : BallCollar 4 X₁) (c₂ : BallCollar 4 X₂)
    (e : T98A02ConnectedSum φ₁ φ₂ ≃ₜ ConnectedSum c₁ c₂)
    (h : Nonempty (H 0 (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k, 0 < k → k < 4 → Nonempty (H k (ConnectedSum c₁ c₂) ≅
        ModuleCat.of ℤ ((H k X₁) × (H k X₂)))) ∧
      Nonempty (H 4 (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k, 4 < k → Limits.IsZero (H k (ConnectedSum c₁ c₂)))) :
    let Y := T98A02ConnectedSum φ₁ φ₂
    Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, 1 ≤ k → k ≤ 3 → Nonempty (t98A02H k Y ≅
      ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
    Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  dsimp
  rcases h with ⟨hzero, hmiddle, htop, habove⟩
  let F (k : ℕ) :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)
  have he (k : ℕ) : t98A02H k (T98A02ConnectedSum φ₁ φ₂) ≅
      H k (ConnectedSum c₁ c₂) :=
    (F k).mapIso (TopCat.isoOfHomeo e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hzero.map fun i ↦ he 0 ≪≫ i
  · intro k hk₁ hk₃
    exact (hmiddle k (by omega) (by omega)).map fun i ↦ he k ≪≫ i
  · exact htop.map fun i ↦ he 4 ≪≫ i
  · intro k hk
    exact Limits.IsZero.of_iso (habove k (by omega)) (he k)

end T98A02Adapter

/-- **LIBRARY boundary.** Integral singular homology of a collared connected
sum of closed connected four-manifolds.  A proof requires the production
open-cover Mayer--Vietoris sequence, comparison with `t98A02H`, punctured
manifold local homology, and the top connecting-map calculation. -/
theorem t98A02_collaredConnectedSum_homology :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      (∃ ψ₁ : T98A02CollarBall → X₁, Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t98A02DiskInCollarBall u) = φ₁ u) →
      (∃ ψ₂ : T98A02CollarBall → X₂, Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t98A02DiskInCollarBall u) = φ₂ u) →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₁)) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₂)) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  intro X₁ X₂ _ _ _ _ _ _ _ _ _ _ _ _ φ₁ φ₂ hφ₁ hφ₂
    hcollar₁ hcollar₂ htop₁ htop₂ habove₁ habove₂
  rcases hcollar₁ with ⟨ψ₁, hψ₁, hcompat₁⟩
  rcases hcollar₂ with ⟨ψ₂, hψ₂, hcompat₂⟩
  let c₁ : ConstructionTargets.CollaredConnectedSumHomology.BallCollar 4 X₁ :=
    { smallMap := φ₁, largeMap := ψ₁, smallEmbedding := hφ₁,
      largeEmbedding := hψ₁, compatible := funext hcompat₁ }
  let c₂ : ConstructionTargets.CollaredConnectedSumHomology.BallCollar 4 X₂ :=
    { smallMap := φ₂, largeMap := ψ₂, smallEmbedding := hφ₂,
      largeEmbedding := hψ₂, compatible := funext hcompat₂ }
  have hgeneric := ConstructionTargets.CollaredConnectedSumHomology.connectedSum_homology
    4 (by norm_num) X₁ X₂ c₁ c₂ htop₁ htop₂
    (fun k hk => habove₁ k (by omega)) (fun k hk => habove₂ k (by omega))
  let e := Classical.choice (T98A02Adapter.quotientHomeomorph φ₁ φ₂ c₁ c₂ rfl rfl)
  exact T98A02Adapter.transportHomology φ₁ φ₂ c₁ c₂ e hgeneric

theorem apm_t98a02 :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      (∃ ψ₁ : T98A02CollarBall → X₁, Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t98A02DiskInCollarBall u) = φ₁ u) →
      (∃ ψ₂ : T98A02CollarBall → X₂, Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t98A02DiskInCollarBall u) = φ₂ u) →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₁)) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₂)) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  exact t98A02_collaredConnectedSum_homology

#print axioms apm_t98a02
