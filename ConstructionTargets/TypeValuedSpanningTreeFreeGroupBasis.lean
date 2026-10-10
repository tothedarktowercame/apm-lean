import ConstructionTargets.FiniteIndexFreeGroupSchreierRank

open CategoryTheory Quiver

noncomputable section

universe u

namespace IsFreeGroupoid.SpanningTree

/-- The Type-valued basis underlying Mathlib's spanning-tree proof that the
vertex group of a free groupoid is free. -/
noncomputable def endBasis {G : Type u} [Groupoid G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
        Set (Quiver.Total (IsFreeGroupoid.Generators G)))
      (End (show G from Quiver.root T)) :=
  FiniteIndexFreeGroupSchreierRank.spanningTreeBasis T

#check endBasis
#print axioms endBasis

end IsFreeGroupoid.SpanningTree
