import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # t93J03: the Klein-bottle group and its planar cyclic-cover subspaces

K is the disk quotient with boundary word aabb. The presentation is the
printed b⁻¹ab=a⁻¹ relation. Part (a) supplies the presentation isomorphism;
part (b) refers to its a-generator. The subspace topology, all three local/
connectedness conditions, and the induced inclusion homomorphism are retained.
Semilocal simple connectedness is defined directly by small loops contracting
in the WHOLE space, not by demanding simply connected neighborhoods.
-/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section

namespace T93J03

def a : FreeGroup Bool := FreeGroup.of false
def b : FreeGroup Bool := FreeGroup.of true

def relations : Set (FreeGroup Bool) := {b⁻¹ * a * b * a}
abbrev PresentedKleinGroup := PresentedGroup relations

def generatorA : PresentedKleinGroup := PresentedGroup.of false

def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : Path x x, (∀ t, γ t ∈ U) → Path.Homotopic γ (Path.refl x)

def inclusion (X : Set KleinBottle) : C(X, KleinBottle) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end T93J03
open T93J03

theorem apm_t93j03 :
    ∀ k : KleinBottle, ∃ e : FundamentalGroup KleinBottle k ≃* PresentedKleinGroup,
      ∀ (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X],
      SemilocallySimplyConnected X → ∀ (x : X) (hx : (x : KleinBottle) = k),
      (∀ g ∈ (FundamentalGroup.mapOfEq (inclusion X) hx).range,
        e g ∈ Subgroup.zpowers generatorA) →
      ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  sorry
