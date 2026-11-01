import Mathlib
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.KleinBottlePiOne
import ConstructionTargets.StandardSurfaceFiniteCover
import ConstructionTargets.t93J03Closure

/-!
# APM t95A01: examples and obstruction for double covers

The three imperative parts of the printed problem are encoded as one
conjunction giving their answers.

For the first part, the explicit space is the presentation complex
`S¹ ∪_{z ↦ z³} D²`.  Its displayed fundamental group is `ZMod 3`; the
statement separately records path connectedness, failure of simple
connectedness, and the absence of every connected two-sheeted covering.

For the second part, the space is the repository's concrete `aabb` polygon
quotient model of the Klein bottle.  Non-orientability is stated intrinsically,
as vanishing of integral `H₂` of this closed surface (a closed connected orientable
surface has `H₂ = ℤ`), and the asserted self-map is a genuine covering map with
every fibre of cardinal two.  Compactness is included explicitly; “surface” is carried by the
standard disk-polygon quotient construction itself.

For the third part, “finite fundamental group” is expressed by `Finite` on
the actual based fundamental group.  The conclusion universally rules out a
two-sheeted covering self-map of every path-connected space.  No local
path-connectedness or semilocally-simply-connectedness is added: the
nonexistence direction only uses path lifting for the supplied covering map.
-/

open Set
open ConstructionTargets
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APM.T95A01

/-- The degree-three attaching loop used for the explicit `ℤ/3` presentation
complex. -/
def degreeThreeLoop : C(Circle, Circle) where
  toFun z := z ^ (3 : ℕ)
  continuous_toFun := continuous_pow 3

/-- The concrete presentation complex `S¹ ∪_{z ↦ z³} D²`. -/
abbrev ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.Cell degreeThreeLoop

/-- Its canonical basepoint, coming from `1 ∈ S¹`. -/
def threePresentationBasepoint : ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.cellIncl degreeThreeLoop 1

/-- The exact `aabb` polygon pairing whose quotient is the concrete Klein
bottle used below. -/
abbrev KleinPairing := ConstructionTargets.t93J03Closure.kleinPairingData

end APM.T95A01

open APM.T95A01

/-- APM t95A01.  The answers are respectively the degree-three presentation
complex, the Klein bottle, and nonexistence in the finite-fundamental-group
case. -/
theorem apm_t95a01 :
    (Nonempty ThreePresentationComplex ∧
      IsPathConnected (Set.univ : Set ThreePresentationComplex) ∧
      Nonempty
        (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
          Multiplicative (ZMod 3)) ∧
      ¬ SimplyConnectedSpace ThreePresentationComplex ∧
      ∀ (E : Type) [TopologicalSpace E] [ConnectedSpace E]
          (p : E → ThreePresentationComplex),
        ¬ (IsCoveringMap p ∧
          ∀ x : ThreePresentationComplex,
            Nat.card {e : E // p e = x} = 2)) ∧
    (CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of KleinBottle)) ∧
      IsCompact (Set.univ : Set KleinBottle) ∧
      ∃ p : KleinBottle → KleinBottle,
        IsCoveringMap p ∧
        ∀ x : KleinBottle, Nat.card {y : KleinBottle // p y = x} = 2) ∧
    (∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
      Finite (FundamentalGroup X x) →
      ∀ p : X → X,
        ¬ (IsCoveringMap p ∧
          ∀ z : X, Nat.card {y : X // p y = z} = 2)) := by
  sorry
