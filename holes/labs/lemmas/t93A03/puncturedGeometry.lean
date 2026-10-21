import Mathlib
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.CollaredConnectedSumHomology

/-! # Blueprint for the repaired APM t93A03 statement. -/

open FundamentalGroupoid
open scoped ContinuousMap

noncomputable section

abbrev T93A03E3 := EuclideanSpace ℝ (Fin 3)
abbrev T93A03Disk := Metric.closedBall (0 : T93A03E3) 1
abbrev T93A03Sphere2 := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03Summand := Circle × T93A03Sphere2
abbrev T93A03Boundary := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03CollarBall := Metric.closedBall (0 : T93A03E3) 2

def t93A03BoundaryInDisk (x : T93A03Boundary) : T93A03Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

def t93A03DiskInCollarBall (u : T93A03Disk) : T93A03CollarBall :=
  ⟨u, Metric.closedBall_subset_closedBall (by norm_num) u.property⟩

abbrev T93A03Punctured (φ : T93A03Disk → T93A03Summand) :=
  {x : T93A03Summand //
    x ∉ φ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}}

inductive T93A03ConnectedSumRel
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) →
      Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) → Prop
  | boundary (s : T93A03Boundary)
      (h₁ : φ₁ (t93A03BoundaryInDisk s) ∉
        φ₁ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1})
      (h₂ : φ₂ (t93A03BoundaryInDisk s) ∉
        φ₂ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}) :
      T93A03ConnectedSumRel φ₁ φ₂
        (Sum.inl ⟨φ₁ (t93A03BoundaryInDisk s), h₁⟩)
        (Sum.inr ⟨φ₂ (t93A03BoundaryInDisk s), h₂⟩)

def T93A03ConnectedSum
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :=
  Quotient (Relation.EqvGen.setoid (T93A03ConnectedSumRel φ₁ φ₂))

noncomputable instance
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    TopologicalSpace (T93A03ConnectedSum φ₁ φ₂) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

namespace T93A03PiOne

open ConstructionTargets.CollaredConnectedSumHomology

/-- A concrete basepoint on the gluing two-sphere. -/
def sphereBasepoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by
    simp [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

/-- **LEAF (P1).** The frozen quotient presentation is the generic
collared connected sum built from the same small maps. -/
theorem quotientHomeomorph
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (c₁ c₂ : BallCollar 3 T93A03Summand)
    (hc₁ : c₁.smallMap = φ₁) (hc₂ : c₂.smallMap = φ₂) :
    Nonempty (T93A03ConnectedSum φ₁ φ₂ ≃ₜ ConnectedSum c₁ c₂) := by
  sorry

/-- **LEAF (P2).** The product `S¹ × S²`, viewed as a three-manifold
through an `E 1 × E 2 ≃ E 3` model change, has an open, path-connected
collared puncture. -/
-- BEGIN SEAT AREA
theorem puncturedGeometry (c : BallCollar 3 T93A03Summand) :
    IsOpen c.radialTwo ∧ PathConnectedSpace c.Punctured := by
  sorry
-- END SEAT AREA

/-- **LEAF (P3).** A collared puncture of `S¹ × S²` has the
rank-one free fundamental group, at the boundary basepoint. -/
theorem puncturedPiOne (c : BallCollar 3 T93A03Summand)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    Nonempty (FundamentalGroup c.Punctured (c.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1)) := by
  sorry

/-- **LIBRARY (P4).** Based van Kampen for the standard connected-sum cover.
This is the generic two-open free-product boundary missing from the existing
fundamental-groupoid pseudopushout API. -/
theorem standardCoverPiOneFreeProduct
    (c₁ c₂ : BallCollar 3 T93A03Summand)
    (hcover : HasStandardCover c₁ c₂)
    (e₁ : FundamentalGroup c₁.Punctured (c₁.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1))
    (e₂ : FundamentalGroup c₂.Punctured (c₂.boundaryMap sphereBasepoint) ≃*
      FreeGroup (Fin 1)) :
    ∃ x : ConnectedSum c₁ c₂,
      Nonempty (FundamentalGroup (ConnectedSum c₁ c₂) x ≃*
        Monoid.Coprod (FreeGroup (Fin 1)) (FreeGroup (Fin 1))) := by
  sorry

/-- **LEAF (P5).** The free product of two rank-one free groups is the
rank-two free group. -/
theorem twoRankOneFreeProduct :
    Nonempty (Monoid.Coprod (FreeGroup (Fin 1)) (FreeGroup (Fin 1)) ≃*
      FreeGroup (Fin 2)) := by
  sorry

/-- **LEAF (P6).** Transport a based fundamental-group computation across
a homeomorphism, allowing the basepoint to move to its inverse image. -/
theorem transportPiOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (y : Y) (G : Type*) [Group G]
    (h : Nonempty (FundamentalGroup Y y ≃* G)) :
    Nonempty (FundamentalGroup X (e.symm y) ≃* G) := by
  sorry

end T93A03PiOne

/-- **LIBRARY.** Van Kampen for the concrete collared connected sum, including
the punctured-summand comparisons and the two circle computations. -/
theorem t93A03_collaredConnectedSum_piOne
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ∃ x : T93A03ConnectedSum φ₁ φ₂,
      Nonempty (FundamentalGroup (T93A03ConnectedSum φ₁ φ₂) x ≃*
        FreeGroup (Fin 2)) := by
  open ConstructionTargets.CollaredConnectedSumHomology in
    rcases hcollar₁ with ⟨ψ₁, hψ₁, hcompat₁⟩
    rcases hcollar₂ with ⟨ψ₂, hψ₂, hcompat₂⟩
    let c₁ : BallCollar 3 T93A03Summand :=
      { smallMap := φ₁
        largeMap := ψ₁
        smallEmbedding := hφ₁
        largeEmbedding := hψ₁
        compatible := funext hcompat₁ }
    let c₂ : BallCollar 3 T93A03Summand :=
      { smallMap := φ₂
        largeMap := ψ₂
        smallEmbedding := hφ₂
        largeEmbedding := hψ₂
        compatible := funext hcompat₂ }
    obtain ⟨hopen₁, hpath₁⟩ := T93A03PiOne.puncturedGeometry c₁
    obtain ⟨hopen₂, hpath₂⟩ := T93A03PiOne.puncturedGeometry c₂
    letI := hpath₁
    letI := hpath₂
    let hcover := BallCollar.connectedSum_standardCover c₁ c₂ hopen₁ hopen₂
    obtain ⟨e₁⟩ := T93A03PiOne.puncturedPiOne c₁ hopen₁ hpath₁
    obtain ⟨e₂⟩ := T93A03PiOne.puncturedPiOne c₂ hopen₂ hpath₂
    obtain ⟨y, ⟨evk⟩⟩ :=
      T93A03PiOne.standardCoverPiOneFreeProduct c₁ c₂ hcover e₁ e₂
    obtain ⟨ealg⟩ := T93A03PiOne.twoRankOneFreeProduct
    obtain ⟨eq⟩ := T93A03PiOne.quotientHomeomorph φ₁ φ₂ c₁ c₂ rfl rfl
    refine ⟨eq.symm y, ?_⟩
    exact T93A03PiOne.transportPiOne eq y (FreeGroup (Fin 2)) ⟨evk.trans ealg⟩

/-- A fundamental-group equivalence with a nontrivial free group obstructs
simple connectivity. -/
theorem t93A03_not_simplyConnected_of_piOne_equiv
    {X : Type*} [TopologicalSpace X] (x : X)
    (e : FundamentalGroup X x ≃* FreeGroup (Fin 2)) :
    ¬ SimplyConnectedSpace X := by
  intro hsc
  letI : SimplyConnectedSpace X := hsc
  letI : Subsingleton (FundamentalGroup X x) :=
    inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))
  have h := congrArg e
    (Subsingleton.elim (e.symm (FreeGroup.of (0 : Fin 2))) (e.symm 1))
  exact FreeGroup.of_ne_one (0 : Fin 2) (by simpa using h)

theorem apm_t93a03
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂) := by
  obtain ⟨x, ⟨e⟩⟩ :=
    t93A03_collaredConnectedSum_piOne φ₁ φ₂ hφ₁ hφ₂ hcollar₁ hcollar₂
  exact t93A03_not_simplyConnected_of_piOne_equiv x e

#print axioms apm_t93a03
