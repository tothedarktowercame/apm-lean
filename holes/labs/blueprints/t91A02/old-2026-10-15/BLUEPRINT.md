# Blueprint for t91A02

## Triage verdict

The registered statement is true and unchanged. The former single
`t91A02_eulerCharacteristic_finite_cover` library hole is now a sorry-free
assembly from four independent leaves. The split exposes a genuine missing
foundation: `Surface` is presently only a quotient type plus a separately
defined integer formula. No existing theorem connects that formula to
singular homology or proves Euler multiplicativity for finite covers.

The import of `ConstructionTargets.RationalLefschetz` supplies the semantic
predicate `HasEulerCharacteristic`; it imports only `Mathlib` and does not
import any `SphereCap*` or `LinearGraphMeasure` module.

## Independent leaves

### `t91A02_surface16_hasEulerCharacteristic` — LIBRARY

The rational singular-homology Euler characteristic of `Surface false 16` is
`-14`. This is independent of the cover and of all other leaves.

Expected route: construct the finite polygon CW complex for the quotient disk,
identify its cellular chain groups as dimensions `1, 16, 1`, and use the
cellular/singular comparison. At the Mathlib layer the relevant API starts at
`AlgebraicTopology.singularHomologyFunctor`; the value is packaged by
`ConstructionTargets.RationalLefschetz.HasEulerCharacteristic`, and traces of
identity maps reduce using `LinearMap.trace_id` and the finite-free dimension
API.

Estimate: 300–700 lines after a reusable polygon-CW model exists; substantially
larger if that model must be built here. This is not honestly a 30–150-line
seat with the current imports, so it remains marked LIBRARY.

Degenerate checks: the quotient disk is nonempty (the disk contains `0`), and
genus `16` is positive. The one-vertex, sixteen-edge, one-face count is
`1 - 16 + 1 = -14`; boundary vertices must all be identified, while no
interior point is identified with a boundary point.

### `t91A02_surface8_hasEulerCharacteristic` — LIBRARY

The same computation for `Surface false 8`, yielding `1 - 8 + 1 = -6`.
Independent of every other leaf. It should use exactly the same polygon-CW
and singular/cellular comparison lemmas as the sixteen-crosscap leaf, with
`LinearMap.trace_id` for the final alternating trace.

Estimate: 20–50 lines if the reusable generic polygon-surface homology theorem
lands first; otherwise 300–700 lines. The intended shared prerequisite is
`program-2026-10-13-polygon-surface-homology`.

Degenerate checks: again the quotient is nonempty and genus `8` is positive;
the edge relation has the nonorientable (same-direction) sign convention, but
Euler characteristic depends only on cell counts, not the boundary signs.

### `t91A02_cover_hasEulerCharacteristic_mul` — LIBRARY

Given the covering map, positive constant fibre cardinality, and the base
Euler computation explicitly as a hypothesis, prove that the total space has
Euler characteristic `sheets * (-6)`. It is independent of both surface
computation leaves, so a cover-transfer seat can work in parallel.

Expected route: use evenly covered neighborhoods from `IsCoveringMap`, form
the finite-sheet transfer on singular chains/homology, and prove the usual
finite-cover Euler formula. Relevant Mathlib entry points are `IsCoveringMap`,
`IsCoveringMap.isOpenMap`, `AlgebraicTopology.singularHomologyFunctor`,
`LinearMap.trace`, and finite-sum reindexing via `Fintype.sum_equiv`.
`ConstructionTargets.CoveringDegree` contains useful fibre-cardinality
infrastructure, but currently no Euler theorem.

Estimate: 500–1200 lines for the absent general finite-cover theorem, then
10–30 lines for this adapter. This is a genuine shared-library foundation and
is not hidden in an overloaded surface-specific proof.

Degenerate checks: `0 < sheets` excludes the empty zero-sheet case. Constant
fibre cardinality is assumed at every base point, so disconnected-base degree
variation is irrelevant. No connectedness assumption is needed when the
global degree is constant.

### `t91A02_hasEulerCharacteristic_unique`

Two `HasEulerCharacteristic X` witnesses have equal values. Independent of
the surface and cover leaves.

Expected proof: unfold `HasEulerCharacteristic` and `HasLefschetzNumber`, take
the maximum of the two vanishing bounds, extend both finite alternating sums
to that maximum using the `Subsingleton` hypotheses, and compare them. Useful
Mathlib lemmas are `Finset.sum_subset`, `Finset.sum_eq_zero`,
`LinearMap.trace_eq_zero_of_subsingleton`, and `Nat.lt_of_lt_of_le`.

Estimate: 40–90 lines. Empty/rank-zero homology groups cause no issue: their
trace contribution is zero. The conclusion compares two separately supplied
values, so the lemma does not restate a hypothesis.

## Assembly

`t91A02_eulerCharacteristic_finite_cover` contains no `sorry`. It supplies
the base computation to the cover-transfer leaf, compares the resulting total
Euler value with the independent source computation using uniqueness, and
finishes by normalization of `eulerCharacteristic` and rational/integer casts.
The registered theorem `apm_t91a02` is byte-identical and remains the final
integer contradiction.

Dependency layers:

- Layer 1, mutually independent: the four leaves above.
- Layer 2: `t91A02_eulerCharacteristic_finite_cover` (sorry-free assembly).
- Layer 3: `apm_t91a02` (already proved and unchanged).

The unavoidable doubt is scope: the two polygon homology leaves and the
finite-cover transfer leaf cannot currently be reduced to 30–150 lines because
Mathlib has neither the concrete polygon CW model nor a ready finite-cover
Euler theorem. Splitting them further in this file would merely introduce
ad-hoc definitions of those missing foundations rather than independently
provable seats.
