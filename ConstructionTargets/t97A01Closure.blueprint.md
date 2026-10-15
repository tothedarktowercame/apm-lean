# t97A01 closure blueprint

## Triage verdict

The frozen statement is true and faithful.  Its first quotient has boundary
word `a a b b c c`; its second has boundary word
`a b a⁻¹ b⁻¹ c c`.  Both are closed nonorientable genus-three surfaces,
so each has `H₀ = ℤ`, `H₁ = ℤ² × ZMod 2`, and `Hₖ = 0` for `k ≥ 2`.
The second has the displayed one-relator fundamental group.

The disk is nonempty, both relations pair all six boundary arcs, and all six
vertices lie in one generated equivalence class.  The degree-two boundary
vectors are `(2,2,2)` and `(0,0,2)`.  Both maps `ℤ → ℤ³` are injective,
and both cokernels have Smith normal form `ℤ² × ZMod 2`.

`holes/labs/blueprints/t97A01/Blueprint.lean` repeats the frozen definitions
and theorem type.  Its final proof is complete modulo the two LIBRARY results
below; that assembly proof should be copied into `Main.lean` rather than
re-derived.

## B1 — polygon singular homology adapter (LIBRARY)

Declaration: `apm_t97a01_polygon_singular_homology`.

Simultaneously compute integral singular homology for the two literal
six-edge quotients.  Instantiate the banked
`ConstructionTargets.PolygonSurfaceHomology.polygonQuotient_homology` theorem
with pairing data for the words `aabbcc` and `aba⁻¹b⁻¹cc`, then identify the
foundation's quotient types with the frozen `EqvGen` quotients.

For both words, specialize the attaching map and its algebraic models:

- `aabbcc` gives the vector `(2,2,2)`;
- `aba⁻¹b⁻¹cc` gives `(0,0,2)`;
- the kernels are zero;
- the cokernels are linearly equivalent to `ℤ × ℤ × ZMod 2`.

The common geometry, Mayer–Vietoris exactness, and general kernel/cokernel
calculation are already banked in `PolygonSurfaceHomology`; this closure row
owes only the two finite pairing records, quotient comparison, and bounded
integer-linear reductions required by the frozen types.

Dependencies:

- `ConstructionTargets.PolygonSurfaceHomology.polygonQuotient_homology`
- the frozen definitions copied from the blueprint fixture.

Truth check: injectivity and Smith normal forms follow from elementary
unimodular coordinate changes.  This result supplies all six homology clauses
of the final theorem.

## B2 — torus-crosscap fundamental group (LIBRARY)

Declaration: `apm_t97a01_torusRP2_fundamentalGroup`.

Apply the banked polygon van Kampen construction to the literal
torus-crosscap pairing.  The outer piece retracts to the three-circle wedge;
tracking the positive overlap circle through the six arcs reads
`a b a⁻¹ b⁻¹ c c`.  Reduce the pushout by the contractible inner piece to
the normal-closure quotient, identify it with the stated `PresentedGroup`,
and transport the radial basepoint to the frozen centre basepoint.

Closest banked modules:

- `ConstructionTargets.PolygonSurfacePiOne`
- `ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms`
- `ConstructionTargets.FiniteCircleWedgeFundamentalGroup`
- `ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout`

Remaining substeps are the literal pairing adapter, path-level ordered-word
specialization, quotient presentation comparison, and basepoint transport.
Abelianizing the relation gives `2c = 0`, agreeing independently with B1.

## B3 — final assembly

Copy the already-proved final conjunction from
`holes/labs/blueprints/t97A01/Blueprint.lean`: destructure B1 and append B2.
Do not change any frozen definition or the registered theorem statement.

Dependency layers:

1. B1 and B2 are independent after their shared foundations are banked.
2. B3 depends on B1 and B2.

## Verification

Each implementation job must keep the target and `Main.lean` placeholder-free
except for the pre-existing registered placeholder until final assembly, use
only standard axioms, and run:

```text
lake env lean problems/t97A01/lean/Main.lean
python3 scripts/statement-registry.py check
```

The read-only source blueprint compiles with `sorryAx` only through B1 and B2.
