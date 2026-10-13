# Blueprint for a97J08

## Triage

**Verdict: true and faithful.** The Lean theorem encodes the source statement's rectifiable Jordan curve by continuity on `[0,1]`, equal endpoints, injectivity on `[0,1)`, and bounded variation. Its `curveInterior` is the union of bounded complementary components, and `zeroCount` uses the positive part of the meromorphic divisor, so multiplicity is retained.

The usual degenerate failures are excluded. A constant curve cannot satisfy the stated injectivity. If the encoded interior is empty, both zero counts are zero. The hypotheses that `g` is nonzero on the curve and that the convergence is locally uniform are exactly those needed for the eventual Rouché inequality. As a topology check, an annulus has a bounded complementary component and its central circle is visibly noncontractible, whereas the complement of a disk has no bounded component. The missing planar lemma also becomes vacuous for an empty domain.

The 2026-08-26 classification was accurate: the missing construction is a loop in an open planar domain which surrounds a bounded connected component of its complement. The current file already defines the radial map from the domain to `Circle` and proves that a circle admitting the required degree-one homotopy certificate is non-nullhomotopic. I searched the current Mathlib tree for Alexander duality, planar/Jordan separation, Schoenflies, surrounding loops, and bounded-complement-component results. No theorem presently supplies this construction. Thus the construction remains blocked at the library level, not at the later analytic argument.

## Definitions and proved infrastructure

`Blueprint.lean` retains the definitions and every proved lemma from `problems/a97J08/lean/Main.lean`. In particular, it already proves compactness and boundary estimates, locally uniform limit analyticity, disk-wise Rouché transfer, finite divisor decomposition and additivity, conversion of noncontractible circles to essential based loops, and the final zero-count assembly. The main theorem contains no `sorry`.

## Remaining lemma

### `apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component`

**Statement in words.** If `D` is open and the connected component of `Dᶜ` containing `z` is bounded, then there is a continuous circle in `D` which is not nullhomotopic.

**Why it is true.** This is the classical planar hole theorem. Let `K` be the bounded complementary component. A planar separation/Alexander-duality argument produces a loop in `D` with nonzero winding number about `z`. Composing that loop with the already defined radial map

`w ↦ (w - z) / ‖w - z‖`

gives a circle map of nonzero degree (a degree-one representative is enough after the usual normalization). Such a composite cannot be nullhomotopic. The proved lemma `apm_a97j08_not_nullhomotopic_of_circle_homotopyLeftInverse` is the final API bridge once the construction is expressed as a homotopy-left-inverse certificate. The earlier lemmas `apm_a97j08_nonempty_of_bounded_compl_component` and `apm_a97j08_compl_component_compact_connected` already package the elementary prerequisites.

**Estimated size.** About 200–500 lines if developed from a suitable planar separation or winding-number theorem; substantially larger if Alexander duality/Jordan separation must itself be built. This exceeds the preferred session size because Mathlib currently lacks the natural foundational split point. Splitting the statement into weaker ad hoc construction lemmas would merely hide that same missing theorem.

**Dependencies.** Definitions plus the already proved radial-map and homotopy/degree lemmas; no other unfinished lemma.

**Truth checks.** Hand-checked on an annulus, where a concentric circle witnesses the conclusion. Checked the disk and empty-domain edge cases, where the bounded-component premise does not arise. The general assertion is the standard equivalence between simple connectivity of a plane domain and connectedness of its complement in the Riemann sphere.

## Dependency layers

- Layer 1: `apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component`.
- Layer 2: none unfinished. All consequences, including the main theorem, are already compiled proofs.

There is only one remaining independent seat. Useful parallel work would require first adding a reusable planar Alexander-duality or separation API to Mathlib/ConstructionTargets, which is outside this theorem's present local decomposition.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a97J08/Blueprint.lean
```

The final command in the file prints:

```text
'apm_a97j08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole source of `sorryAx` is the remaining planar construction lemma above.
