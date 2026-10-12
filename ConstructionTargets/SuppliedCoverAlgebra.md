# Supplied-cover algebra blueprint

This foundation follows `~/notes/closer/routes/covering.md`, section A
(`Small supplied-cover algebra`) and node C7 (`Concrete orbit-quotient
route`).  Its consumers are `t99J01`, `t97A03`, `t93J03`, and `t00A02`.
It deliberately does not construct a cover from an arbitrary subgroup.

The Lean file will be `ConstructionTargets/SuppliedCoverAlgebra.lean`.
The construction imports `ConstructionTargets/CoveringMonodromyCosets.lean`,
Mathlib `Topology.Homotopy.Lifting`, `Topology.Covering.Quotient`,
`GroupTheory.Subgroup.Ker`, and `GroupTheory.Index`.  In particular it reuses
`coveringInducedFundamentalGroupMap_injective`, `MonoidHom.ofInjective`,
`Subgroup.index_map_equiv`, `Topology.IsEmbedding.of_comp`,
`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`, and
`IsQuotientCoveringMap.isCoveringMap`.

### B1. Fundamental group as the induced range

lean: `ConstructionTargets.SuppliedCoverAlgebra.coveringFundamentalGroupEquivRange`
:
```lean
noncomputable def coveringFundamentalGroupEquivRange
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) :
    FundamentalGroup E e ≃*
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range
```

uses: `ConstructionTargets.coveringInducedFundamentalGroupMap_injective`,
Mathlib `MonoidHom.ofInjective`

status: proved (current program commit)

Apply `MonoidHom.ofInjective` to the induced fundamental-group homomorphism
and its existing injectivity theorem.  The resulting codomain is definitionally
the range subgroup.  No connectedness hypothesis is needed: injectivity of
the induced map is pointwise for every covering and every chosen `e`.

### B2. Embedding detected after composition

lean: `ConstructionTargets.SuppliedCoverAlgebra.isEmbedding_of_comp_eq` :
```lean
theorem isEmbedding_of_comp_eq
    {A E B : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [TopologicalSpace B] (l : A → E) (p : E → B) (i : A → B)
    (hl : Continuous l) (hp : Continuous p)
    (hi : Topology.IsEmbedding i) (h : p ∘ l = i) :
    Topology.IsEmbedding l
```

uses: Mathlib `Topology.IsEmbedding.of_comp`

status: proved (current program commit)

Rewrite `hi` along `h` to obtain `IsEmbedding (p ∘ l)`.  Apply
`Topology.IsEmbedding.of_comp hp hl` to that fact.  Thus `hl`, `hp`, `hi`,
and `h` are all used.  This is the exact adapter needed after the Klein-bottle
lift composes to the subtype embedding.

### B3. Transport the covering subgroup into a free group

lean: `ConstructionTargets.SuppliedCoverAlgebra.coveringFundamentalGroupEquivFreeSubgroup`
and
`ConstructionTargets.SuppliedCoverAlgebra.coveringFreeSubgroup_index` :
```lean
noncomputable def coveringFundamentalGroupEquivFreeSubgroup
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) (r : ℕ)
    (base : FundamentalGroup B (p e) ≃* FreeGroup (Fin r)) :
    FundamentalGroup E e ≃*
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.map
        base.toMonoidHom

theorem coveringFreeSubgroup_index
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) (r : ℕ)
    (base : FundamentalGroup B (p e) ≃* FreeGroup (Fin r)) :
    ((ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.map
      base.toMonoidHom).index =
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.index
```

uses: B1, Mathlib `MonoidHom.ofInjective`, `Subgroup.index_map_equiv`

status: proved (current program commit)

Let `H` be the induced range.  Restrict `base.toMonoidHom` to `H`, with
codomain `H.map base.toMonoidHom`; it is injective because `base` is
injective and it is surjective onto the mapped subgroup by the definition of
`Subgroup.map`.  `MulEquiv.ofBijective` gives `H ≃* H.map
base.toMonoidHom`; compose it with B1.  The index theorem is exactly
`Subgroup.index_map_equiv base H`.  Hence the covering, point, rank, and base
equivalence hypotheses are each used, and no fiber finiteness is assumed.

### B4. Transport an orbit quotient covering along a homeomorphism

lean: `ConstructionTargets.SuppliedCoverAlgebra.isCoveringMap_homeomorph_comp_quotientMk`
:
```lean
theorem isCoveringMap_homeomorph_comp_quotientMk
    {G X B : Type*} [Group G] [TopologicalSpace X] [TopologicalSpace B]
    [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    (h : MulAction.orbitRel.Quotient G X ≃ₜ B) :
    IsCoveringMap (h ∘ Quotient.mk (MulAction.orbitRel G X))
```

uses: Mathlib
`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`,
`IsQuotientCoveringMap.isCoveringMap`, and composition of a covering with a
homeomorphism

status: proved (current program commit)

Use `free` to install `IsCancelSMul G X`: if `g • x = g' • x`, cancel by
the group action and apply `free` to `g'⁻¹ * g`.  The Mathlib quotient theorem
then makes `Quotient.mk (MulAction.orbitRel G X)` a quotient covering and
hence a covering.  Compose its evenly covered neighborhoods with the target
homeomorphism `h`; equivalently apply the pinned covering-composition theorem
for `h`.  Proper discontinuity, local compactness, and T2 are consumed by the
quotient theorem, continuous scalar multiplication by the orbit quotient
topology, freeness by `IsCancelSMul`, and `h` by the final transport.

No node depends on B4 except the concrete Klein-bottle and antipodal-RP2
routes.  B1 and B3 are the supplied-cover classification branch; B2 is the
lift-embedding branch.
