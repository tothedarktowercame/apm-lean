# Blueprint: deck-group quotient fundamental groups

## Provenance and fixed representation

This blueprint follows the route audits for `t00A02` (step
`apm_t00A02_bridge_antipodalCover_isCoveringMap`) and `t00J07` (step
`rp2_antipodal_cover_and_pi1`), and the `TOPOLOGY-ROUTES.md` routes for
`t92J05` (`simply-connected-cover-fiber-bijection`) and `t93J03`
(`deck-group-fundamental-group`). The same general theorem is also named by
the routes for `t99J01`.

The final theorem uses Mathlib's orbit quotient
`MulAction.orbitRel.Quotient G X`, based at `Quotient.mk _ x`, and
`FundamentalGroup` as the endomorphism group of Mathlib's fundamental
groupoid. It assumes `T2Space X` and `LocallyCompactSpace X`; these hypotheses
are required by Mathlib's properly-discontinuous quotient-covering theorem.

The construction builds on:

- `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` and its
  `IsCoveringMap` projection;
- `IsCoveringMap.monodromy`, `monodromy_refl`, `monodromy_trans_apply`, and
  `monodromy_map`;
- `SimplyConnectedSpace.paths_homotopic` and the induced
  `PathConnectedSpace` instance;
- `CategoryTheory.End.mul_def`, under which multiplication reverses
  categorical composition.

### B1. Orbit projection is a covering

lean: `quotientMk_isCoveringMap` :
`[Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
[ProperlyDiscontinuousSMul G X] [LocallyCompactSpace X] [T2Space X] ->
(∀ g x, g • x = x → g = 1) -> IsCoveringMap (Quotient.mk
(MulAction.orbitRel G X))`

uses: Mathlib `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`

status: proved `d8ae72972f6621f135d22e9053de496cedf2e908`

Freeness supplies `IsCancelSMul G X`. Mathlib then constructs evenly covered
neighborhoods from proper discontinuity, local compactness, and Hausdorffness.

### B2. Acting-group coordinates on a quotient-covering fiber

lean: `quotientCoveringOrbitFiberEquiv` :
`(h : IsQuotientCoveringMap f G) -> (e : E) -> G ≃ f ⁻¹' {f e}`

uses: Mathlib `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`,
`IsQuotientCoveringMap.isCancelSMul`

status: proved `52fd959c5549a4f6fc41cef6b9416b2ae2b3e119`

Send `g` to `g • e`. Cancellation proves injectivity. Every point in the
fiber is in the orbit of `e`, which proves surjectivity. The specialization
`orbitQuotientFiberEquiv` applies this to B1's orbit projection.

### B3. Raw endpoint monodromy

lean: `orbitEndpointMonodromyRaw` :
`FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x) → G`

uses: B1, B2, Mathlib `IsCoveringMap.monodromy`

status: proved `3f64958a92525bd9c45cf1efd531c539e61e1713`

Lift a loop from `x`, take its endpoint in the fiber, and apply the inverse of
B2's coordinate equivalence. `orbitEndpointMonodromyRaw_one` uses
`monodromy_refl` and proves that the constant loop has coordinate `1`.

### B4. Deck-equivariance of monodromy

lean: `orbitMonodromy_deck_equivariant` :
`(quotientMk_isCoveringMap free).monodromy γ
  (orbitQuotientFiberEquiv free x g) =
 g • (quotientMk_isCoveringMap free).monodromy γ ⟨x, rfl⟩`

uses: B1, B2, Mathlib uniqueness of path lifts

status: planned

Represent `γ` by a path. The translate by `g` of its lift from `x` is
continuous because of `ContinuousConstSMul`; the orbit projection of that
translate equals the original base path. Its initial point is `g • x`.
Uniqueness of path lifts therefore identifies it with the lift starting at
`g • x`; evaluating at `1` proves the displayed equality. Descend through
`Path.Homotopic.Quotient` using the definition of `monodromy`.

### B5. Raw endpoint coordinates reverse multiplication

lean: `orbitEndpointMonodromyRaw_mul` :
`orbitEndpointMonodromyRaw free x (a * b) =
 orbitEndpointMonodromyRaw free x b * orbitEndpointMonodromyRaw free x a`

uses: B3, B4, Mathlib `monodromy_trans_apply`,
`CategoryTheory.End.mul_def`

status: planned

Expand multiplication in the fundamental group using `End.mul_def`; it is
the path `b` followed by `a`. Apply `monodromy_trans_apply`. The first lift
ends at the translate indexed by the raw coordinate of `b`. Apply B4 to the
second lift from that translated point. B2's injectivity then identifies the
composite endpoint coordinate with the displayed reversed product.

### B6. Endpoint monodromy homomorphism

lean: `orbitEndpointMonodromy` :
`FundamentalGroup (MulAction.orbitRel.Quotient G X) (Quotient.mk _ x) →* G`

uses: B3, B5

status: planned

Define the value on `a` to be `(orbitEndpointMonodromyRaw free x a)⁻¹`.
B3's identity law proves `map_one`; B5 and `mul_inv_rev` prove `map_mul` in
the required order.

### B7. Surjectivity in a simply connected total space

lean: `orbitEndpointMonodromy_surjective` :
`Function.Surjective (orbitEndpointMonodromy free x)`

uses: B2, B6, `SimplyConnectedSpace`'s `PathConnectedSpace` instance,
Mathlib `IsCoveringMap.monodromy_map`

status: planned

For `g : G`, choose a path in `X` from `x` to `g⁻¹ • x`. Project it to
the orbit quotient; its endpoints become equal, so it defines a based loop.
`monodromy_map` says that lifting this projected loop from `x` returns the
chosen path, hence its raw endpoint coordinate is `g⁻¹`. B6 inverts that
coordinate and maps the loop to `g`.

### B8. Injectivity in a simply connected total space

lean: `orbitEndpointMonodromy_injective` :
`Function.Injective (orbitEndpointMonodromy free x)`

uses: B1, B2, B6, Mathlib `IsCoveringMap.injective_path_homotopic_map`,
`SimplyConnectedSpace.paths_homotopic`

status: planned

It suffices to prove the kernel is trivial. If B6 maps a loop to `1`, its raw
coordinate is `1`, so B2 identifies the endpoint of its lift with `x`. The
lift is therefore a loop in `X`. Simple connectedness makes it homotopic to
the constant loop. Projecting that homotopy shows the original base loop is
the identity; equivalently use `injective_path_homotopic_map` after comparing
the lift with the constant lifted loop.

### B9. Fundamental group equals the acting group

lean: `freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv` :
`Nonempty (FundamentalGroup (MulAction.orbitRel.Quotient G X)
  (Quotient.mk _ x) ≃* G)`

uses: B6, B7, B8

status: planned

Package B6 with B7 and B8 using `MulEquiv.ofBijective`. This uses every final
hypothesis: continuity/proper discontinuity/local compactness/Hausdorffness in
B1, freeness in B1 and B2, local path-connectedness through the covering and
lifting API, and simple connectedness in B7 and B8.

### B10. Consumer specializations

lean: finite-action and Klein-plane/RP² adapter declarations, with exact names
chosen in their consumer rows

uses: B9 and each consumer's already proved action, quotient identification,
and simple-connectivity declarations

status: planned

For finite free actions, obtain `ProperlyDiscontinuousSMul` from Mathlib's
finite-group instance and apply B9 after rewriting the consumer quotient into
`MulAction.orbitRel.Quotient`. For RP², use the antipodal action of
`Multiplicative (ZMod 2)` on the sphere. For the Klein-plane consumer, use its
free properly discontinuous plane action and its explicit quotient
homeomorphism, transporting basepoints and fundamental groups along that
homeomorphism. These are separate bounded adapters because their quotient
representations differ from B9's literal orbit quotient.
