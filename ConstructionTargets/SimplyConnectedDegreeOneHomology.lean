import ConstructionTargets.DegreeOneHurewiczSurjective
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Degree-one singular homology of simply connected spaces

The degree-one Hurewicz map is surjective on every path-connected space.  For a
simply connected space its fundamental-group source is a subsingleton, so the
integral singular-homology target is a zero object in `AddCommGrpCat`.
-/

noncomputable section

namespace ConstructionTargets.SimplyConnectedDegreeOneHomology

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjective

/-- Integral degree-one singular homology of a simply connected space is zero.

The comparison is kept in the production `AddCommGrpCat` category: the
surjective Hurewicz map has codomain `Multiplicative (IntegralH1 Y)`, and the
last step merely transports subsingletonness back across the additive/
multiplicative type synonym. -/
theorem simplyConnected_singularH1_isZero
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] :
    IsZero (SingularHomology 1 (TopCat.of Y)) := by
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  letI : Subsingleton (FundamentalGroup Y y) := by
    change Subsingleton (Path.Homotopic.Quotient y y)
    infer_instance
  letI : Subsingleton (Multiplicative (IntegralH1 Y)) :=
    (fundamentalGroupH1Hom_surjective y).subsingleton
  letI : Subsingleton (IntegralH1 Y) :=
    ⟨fun a b => congrArg Multiplicative.toAdd
      (Subsingleton.elim (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

#print axioms simplyConnected_singularH1_isZero

end ConstructionTargets.SimplyConnectedDegreeOneHomology
