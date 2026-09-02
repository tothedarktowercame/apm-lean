import ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
import ConstructionTargets.TwoOpenFundamentalGroupoidSpan

/-!
# Connector systems compatible with a two-open span

For a path-connected two-open cover with simply connected overlap, this file
chooses connectors on the overlap and both pieces.  On points coming from the
overlap, the piece connectors are literally the images of the overlap
connectors.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenLegCompatibleConnectorSystems

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan

variable {X : Type} [TopologicalSpace X] {U V : Set X}

structure LegCompatibleConnectorSystems
    (w : (U ∩ V : Set X)) where
  overlap : ConnectorSystem (FundamentalGroupoid (U ∩ V : Set X))
  left : ConnectorSystem (FundamentalGroupoid U)
  right : ConnectorSystem (FundamentalGroupoid V)
  overlap_base : overlap.base = FundamentalGroupoid.mk w
  left_base : left.base =
    (overlapFundamentalGroupoidMap (X := X) (U := U) (V := V) true).obj overlap.base
  right_base : right.base =
    (overlapFundamentalGroupoidMap (X := X) (U := U) (V := V) false).obj overlap.base
  left_connector : ∀ Z,
    (overlapFundamentalGroupoidMap (X := X) (U := U) (V := V) true).mapIso
        (overlap.connector Z) =
      (eqToIso left_base.symm).trans
        (left.connector ((overlapFundamentalGroupoidMap
          (X := X) (U := U) (V := V) true).obj Z))
  right_connector : ∀ Z,
    (overlapFundamentalGroupoidMap (X := X) (U := U) (V := V) false).mapIso
        (overlap.connector Z) =
      (eqToIso right_base.symm).trans
        (right.connector ((overlapFundamentalGroupoidMap
          (X := X) (U := U) (V := V) false).obj Z))

def pathConnector {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (y₀ : Y) (Z : FundamentalGroupoid Y) : FundamentalGroupoid.mk y₀ ≅ Z :=
  asIso (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ Z.as))

def overlapConnectors [SimplyConnectedSpace (U ∩ V : Set X)]
    (w : (U ∩ V : Set X)) :
    ConnectorSystem (FundamentalGroupoid (U ∩ V : Set X)) where
  base := FundamentalGroupoid.mk w
  connector := pathConnector w

def leftConnectors [PathConnectedSpace U] [SimplyConnectedSpace (U ∩ V : Set X)]
    (w : (U ∩ V : Set X)) : ConnectorSystem (FundamentalGroupoid U) where
  base := FundamentalGroupoid.mk ⟨w.1, w.2.1⟩
  connector Z := by
    classical
    by_cases h : Z.as.1 ∈ V
    · let z : (U ∩ V : Set X) := ⟨Z.as.1, Z.as.2, h⟩
      exact (overlapFundamentalGroupoidMap
        (X := X) (U := U) (V := V) true).mapIso
          ((overlapConnectors w).connector (FundamentalGroupoid.mk z))
    · exact pathConnector ⟨w.1, w.2.1⟩ Z

def rightConnectors [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
    (w : (U ∩ V : Set X)) : ConnectorSystem (FundamentalGroupoid V) where
  base := FundamentalGroupoid.mk ⟨w.1, w.2.2⟩
  connector Z := by
    classical
    by_cases h : Z.as.1 ∈ U
    · let z : (U ∩ V : Set X) := ⟨Z.as.1, h, Z.as.2⟩
      exact (overlapFundamentalGroupoidMap
        (X := X) (U := U) (V := V) false).mapIso
          ((overlapConnectors w).connector (FundamentalGroupoid.mk z))
    · exact pathConnector ⟨w.1, w.2.2⟩ Z

theorem existsTwoOpenLegCompatibleConnectorSystems
    (X : Type) [TopologicalSpace X] (U V : Set X)
    (hU : PathConnectedSpace U) (hV : PathConnectedSpace V)
    (hUV : SimplyConnectedSpace (U ∩ V : Set X)) :
    ∃ w : (U ∩ V : Set X), Nonempty (LegCompatibleConnectorSystems w) := by
  letI := hU
  letI := hV
  letI := hUV
  let w : (U ∩ V : Set X) := Classical.choice inferInstance
  refine ⟨w, ⟨{
    overlap := overlapConnectors w
    left := leftConnectors w
    right := rightConnectors w
    overlap_base := rfl
    left_base := rfl
    right_base := rfl
    left_connector := ?_
    right_connector := ?_ }⟩⟩
  · intro Z
    cases Z with
    | mk z =>
      change _ = (eqToIso rfl).trans ((leftConnectors w).connector _)
      simp only [eqToIso_refl, Iso.refl_trans]
      exact (show (leftConnectors w).connector
          ((overlapFundamentalGroupoidMap
            (X := X) (U := U) (V := V) true).obj (FundamentalGroupoid.mk z)) =
          (overlapFundamentalGroupoidMap
            (X := X) (U := U) (V := V) true).mapIso
              ((overlapConnectors w).connector (FundamentalGroupoid.mk z)) by
        simp [leftConnectors, overlapFundamentalGroupoidMap, overlapToPiece, z.2.2]).symm
  · intro Z
    cases Z with
    | mk z =>
      change _ = (eqToIso rfl).trans ((rightConnectors w).connector _)
      simp only [eqToIso_refl, Iso.refl_trans]
      exact (show (rightConnectors w).connector
          ((overlapFundamentalGroupoidMap
            (X := X) (U := U) (V := V) false).obj (FundamentalGroupoid.mk z)) =
          (overlapFundamentalGroupoidMap
            (X := X) (U := U) (V := V) false).mapIso
              ((overlapConnectors w).connector (FundamentalGroupoid.mk z)) by
        simp [rightConnectors, overlapFundamentalGroupoidMap, overlapToPiece, z.2.1]).symm

#print axioms existsTwoOpenLegCompatibleConnectorSystems

end ConstructionTargets.TwoOpenLegCompatibleConnectorSystems
