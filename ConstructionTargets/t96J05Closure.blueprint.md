# t96J05 closure blueprint

Source: `holes/labs/blueprints/t96J05/BLUEPRINT.md` and its compiled
`Blueprint.lean`. The registered statement and its definitions remain frozen.

## Triage

The statement is true and faithful. It permits the chosen radial level to
have dimension `k ≤ m`, including `k = m` when the radius is constant. The
positive-dimensional and nonempty hypotheses exclude the zero-radius
singleton degeneration.

## Definitions

Reuse verbatim the blueprint/Main definitions of the Euclidean model, literal
norm-level subtype, and embedded smooth radial-level predicate.

Define an internal strengthened package
`apm_t96j05_BoundedRadialLevel X r` which contains a witness `k`, proofs
`k ≤ m` and `k ≤ n`, a charted manifold structure on the literal radial
level, its smooth ambient inclusion, and `Nonempty (radialLevel X r)`.
Its forgetful lemma returns the conjunction in the registered conclusion.
This package is private closure infrastructure; it does not alter any frozen
definition or statement.

## Milestones

### C1 — constant radius

`apm_t96j05_constant_radius_level`: if every point of the embedded smooth
`m`-manifold has the same positive norm `r`, the radial level is all of `X`.
Transport the supplied manifold structure across the subtype equivalence and
choose `k = m`. Return the strengthened package: its `k ≤ n` field is exactly
the supplied `hmn : m ≤ n`, and its nonempty field is transported from
`Nonempty X`. The geometric proof is already present in `Blueprint.lean` and
should be moved without re-derivation; only the genuine bound fields are new.

### C2 — positive regular radius (LIBRARY)

`apm_t96j05_exists_regular_radius`: on a nonempty connected
positive-dimensional smooth manifold, a smooth squared-radius map not covered
by the positive constant-radius alternative has an attained positive value at
which its manifold derivative is surjective.

Route: prove squared radius nonconstant; its connected continuous image is a
nondegenerate interval in `[0,∞)`; choose a positive open interval in that
image; use finite-dimensional manifold Sard to select a regular value outside
the critical values; take its square root and transport regularity through
`r ^ 2 = c`. Reuse the arbitrary-model Sard development shared with t01A08
and t01J04, especially `SardGeneralModel.modelRange_geometry` and
`SardConvexDomain.criticalImageNull`; extend it only at the generality this
statement needs.

### C3 — regular fiber

`apm_t96j05_regular_radius_level`: a positive inhabited radial level with
surjective squared-radius derivative has the required embedded smooth
structure. Apply `ManifoldRegularFiberGlobalAtlas`, identify its model with
`EuclideanSpace ℝ (Fin (m - 1))` by finrank, transport across
`RadialSquaredFiber.norm_sq_eq_sq_iff`, and choose `k = m - 1`. Return the
strengthened package, using `hlevel` for its nonempty field and deriving
`m - 1 ≤ n` by `(Nat.sub_le m 1).trans hmn`. Thus both formerly unused
hypotheses occur in mathematical data delivered by this node. The geometric
proof is already present in `Blueprint.lean` and should be moved without
re-derivation; only the package fields are new.

### C4 — assembly

Copy the placeholder-free assembly of `apm_t96j05` from `Blueprint.lean`.
Split on a positive constant radius: C1 closes that branch; otherwise C2
provides a positive regular radius and C3 constructs its level. Pass `hmn`
to C1 or C3, then apply the package's forgetful lemma. Do not retain the
dummy `have _ := hmn` from the source blueprint.

## Hypothesis accounting

Every final hypothesis has a descendant. In particular, `hmn` proves the
`k ≤ n` field of the strengthened result in both branches (`k = m` for C1,
`k = m - 1` for C3). The C2 witness `hlevel` is the nonempty field of C3's
strengthened result. These fields are constructed before the forgetful lemma
projects the frozen public conclusion; neither is an unused binder or a
proof-only dummy binding.

## Dependency order

C1, C2, and C3 are independent. C4 depends on all three. Only C2 is a
library obligation; C1, C3, and C4 are already compiled modulo the C2
placeholder.

## Gates

The final `problems/t96J05/lean/Main.lean` must compile with no placeholders,
the statement registry must remain unchanged, and `#print axioms apm_t96j05`
may report only `propext`, `Classical.choice`, and `Quot.sound`.
