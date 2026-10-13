# Blueprint for t98A02

## Triage

Verdict: **true and faithful**.

The source computes the integral homology of the connected sum of two closed,
connected, oriented four-manifolds.  The registered Lean statement spells out
the closedness used by the informal solution (`CompactSpace`, Hausdorff
manifolds), assumes the supplied top-homology fact, and assumes vanishing above
dimension four.  Its radius-two extensions are the formal replacement for the
source's assertion that the removed balls are top simplices: they provide the
exterior collars needed by the open-cover argument.  Thus the older audit's
counterexample concern about arbitrary wild embedded balls does not apply to
the current statement.

I tried the principal degeneracies.  The manifold and path-connectedness
hypotheses exclude empty spaces and disconnected zero-space pathologies.  The
radius-one ball embeds into each summand, so neither summand is empty.  Taking
both summands to be `S⁴` gives `S⁴ # S⁴`, and the claimed groups reduce
to `ℤ` in degrees zero and four and zero otherwise.  Taking two copies of
`S² × S²` gives rank four in degree two and the expected top and bottom
copies of `ℤ`.  The middle-degree product in `ModuleCat` is the finite direct
sum, as required.  The endpoint inequalities cover exactly `k = 1,2,3`,
`k = 4`, and `k ≥ 5`, without a gap.

No solve-loop counterexample or revision was present.  The current collared
audit and topology ledger instead report a foundational library obstruction.

## Remaining lemma

### `t98A02_collaredConnectedSum_homology` — LIBRARY

**Statement in words.** For the concrete quotient obtained by deleting the
interiors of two embedded four-balls that extend across exterior collars, the
integral singular homology is `ℤ` in degrees zero and four, the product of the
two summands' homologies in degrees one through three, and zero above degree
four.

**Why true.** Apply singular open-cover Mayer--Vietoris twice.  First compute a
punctured summand from a collar cover: puncturing preserves homology in degrees
at most three, kills top homology, and the boundary `S³` maps to zero in degree
three.  Next cover the connected-sum quotient by the two punctured summands
thickened through the collars; their intersection deformation-retracts to
`S³`.  Exactness then gives the direct-product formula in degrees one through
three and identifies the degree-four connecting map with an isomorphism onto
`H₃(S³) ≅ ℤ`.  Path-connectedness gives degree zero, and the supplied
dimension bounds plus exactness give vanishing above degree four.

The nearest sorry-free repository infrastructure is
`ConstructionTargets.ProductionOpenCoverMayerVietoris`, together with the
coefficient/singular comparison, disk-boundary homology, excision, and
manifold-local-homology modules.  The topology audit identifies four genuine
missing programs inside this one library theorem:

1. comparison of production integral homology with `t98A02H`;
2. local-to-global/top homology for a punctured closed four-manifold;
3. the explicit collared complement and connected-sum open-cover geometry;
4. the top connecting-map calculation and exact-sequence assembly.

These are tightly coupled through the production chain model and are not
independent 30--150-line seats.  The audit estimates the punctured-manifold and
open-cover pieces at hundreds to thousands of lines.  Following the batch rule
for a missing 300+ line library result, the blueprint states the result once
rather than disguising its conclusion as a predicate or manufacturing trivial
adapter lemmas.

**Expected size.** Approximately 2,000--5,000 lines in aggregate, likely as a
multi-file ConstructionTargets program; the final consumer adapter should be
under 100 lines once that program exists.

**Dependencies.** None within this blueprint.  Externally it depends on the
four library programs listed above.  The already proved quotient maps-out
universal property in `problems/t98A02/lean/Main.lean` is useful for validating
the glued topology but does not itself imply a homology pushout theorem.

**Truth check.** Besides the `S⁴` and `S² × S²` examples above, the hand
Mayer--Vietoris calculation has only one nonzero intersection group in positive
degree, `H₃(S³) = ℤ`.  The orientation/fundamental-class boundary makes its
map to the two punctured pieces zero, yielding one (not two) top classes.  The
collar hypotheses are precisely what rules out the wild-ball failure mode.

## Assembly

The registered theorem `apm_t98a02` is proved by direct application of the
library theorem and has no `sorry` of its own.  Its type is identical to the
type in `problems/t98A02/lean/Main.lean`.

## Dependency layers

* **Layer 1 (LIBRARY program):**
  `t98A02_collaredConnectedSum_homology`.
* **Layer 2 (already compiled):** `apm_t98a02` applies Layer 1 directly.

There is one admitted lemma.  There are no honest parallel lemma seats at the
present abstraction boundary; parallel work belongs inside the larger library
program after its chain-model interfaces are fixed.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t98A02/Blueprint.lean
```

The output of `#print axioms apm_t98a02` was:

```text
'apm_t98a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole `sorryAx` enters through
`t98A02_collaredConnectedSum_homology`; the main theorem contains no direct
`sorry`.
