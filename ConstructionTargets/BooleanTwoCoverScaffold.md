# Boolean two-cover scaffold

`BooleanTwoCoverScaffold.lean` makes the two ambient range subcomplexes the
primary objects and defines the small object as their supremum. Consequently
the intersection, union, and four Mayer--Vietoris arrows are definitionally
aligned. `coverSmallSSet_booleanCover` proves that this object is the generic
Boolean `coverSmallSSet`.

The compiled fixture constructs the existing chain-level pushout directly
from these definitions, with no `eqToIso` in any arrow. This does not yet
identify its union homology with production singular homology: that comparison
still occurs at the outer boundary through the generic cover-small homology
isomorphism. The scaffold changes where the equality is handled; it does not
assert Mayer--Vietoris exactness or a homology computation.

`reassembly_comp_ambient` proves the first boundary comparison literally at
chain level: stored-union reassembly followed by ambient inclusion is the
biproduct descent of the two ambient range inclusions.

The next boundary does not become definitional under this design. The short
complex starts at `leftRange U ⊓ rightRange V`, whereas the actual production
source is the singular complex of `U ∩ V`; their comparison still uses
`ambientSubspaceRange_inf`. Thus storing `P,Q` makes the union arrows literal
but cannot simultaneously make the intersection range definitionally equal
to the actual intersection subspace. No production exactness theorem is
asserted until that comparison is transported.

The attempted transport reached a precise dependent-type boundary.  Applying
`congrArg (fun P : S.Subcomplex ↦ (P : SSet))` to
`ambientSubspaceRange_inf U V` does construct the object equality needed by
`ssetChains.mapIso (eqToIso ...)`.  However, eliminating that equality to
prove either required square fails on the dependent `Subcomplex.obj` family.
The missing public interface is a naturality theorem of the following shape
(and its right-hand analogue):

```lean
intersectionRangeChainsIso(U,V).hom ≫
    ssetChains.map (ambientSubspaceRangeInclusion inter_subset_left) =
  ssetChains.map
    (subcomplexIntersectionToLeft (leftRange U) (rightRange V))
```

Lean's first residual was the dependent equation
`range (subspaceInclusion (U ∩ V)).app n =
ambientSubspaceRange U .obj n ⊓ ambientSubspaceRange V .obj n`.
Neither `ambientSubspaceRange_inf` nor the existing range-chain naturality
lemmas provide transport coherence for that equality.  Hiding it behind a
fresh assumed square would merely restate the missing comparison, so this
target stops here.

The union-side comparison now uses `smallSSetIsoCoverSmall`, a concrete
`Subcomplex.homOfLE` isomorphism in both directions. Its forward map commutes
definitionally with ambient inclusion by
`smallSSetIsoCoverSmall_hom_comp_ambient`. This supplies representation
coherence only, not production Mayer--Vietoris exactness.

The `true` and `false` member triangles now compile as
`leftToSmall_comp_smallSSetIsoCoverSmall` and
`rightToSmall_comp_smallSSetIsoCoverSmall`; both are definitional consequences
of the concrete `homOfLE` maps.
