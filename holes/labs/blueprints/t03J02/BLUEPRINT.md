# Blueprint for t03J02

## Triage

Verdict: **true and faithful**.

`Main.lean` encodes each simple closed curve by an embedding of `Circle` into
the standard torus, records null-homotopy, forms the generated-relation
quotient, and asks for exactly the classical answers
`π₁ = ℤ² * ℤ²`, `H₀ = ℤ`, `H₁ = ℤ⁴`, `H₂ = ℤ³`, and `H_k = 0` for `k ≥ 3`.

I tried the important edge cases.  `Circle` and the torus are nonempty, so the
basepoint and gluing locus cannot disappear.  An embedding rules out a
constant attaching map.  Null-homotopy makes both induced fundamental-group
and first-homology maps trivial.  Abelianizing `ℤ² * ℤ²` gives `ℤ⁴`, agreeing
with `H₁`; and the ranks give Euler characteristic `1 - 4 + 3 = 0`, agreeing
with `χ(T²) + χ(T²) - χ(S¹) = 0`.  No counterexample appears in the solve-loop
records or topology audit.

The topology ledger's reviewed STOP is genuine: maps-out universality of the
quotient does not itself produce collars.  For arbitrary topological embedded
circles, one first needs annular-neighborhood/Jordan--Schoenflies input before
the existing open-cover van Kampen and Mayer--Vietoris infrastructure applies.

## Available infrastructure

The blueprint imports these sorry-free modules (checked by source search):

* `ConstructionTargets.TwoOpenFreeProductMapping`, providing a two-open-set
  fundamental-group free-product theorem when the overlap is simply connected;
* `ConstructionTargets.ProductionOpenCoverMayerVietoris`, providing the
  production singular Mayer--Vietoris exact sequence;
* `ConstructionTargets.T00A01MayerVietorisAdapters`, providing useful
  homotopy-invariance and exactness adapters;
* `ConstructionTargets.SingularHomologyConcrete`, providing concrete singular
  homology access.

The first module does not directly handle this circle overlap.  The attaching
maps must first be shown trivial and the resulting group pushout reduced to a
free product.  Searches for `annulusNeighborhood`, `pushout_openCover`,
`TwoOpenFreeProduct`, and `MayerVietoris` found no sorry-free construction of
the required embedded-circle collar or quotient cover.

## Remaining lemmas

### `apm_t03J02_pushout_openCover` — LIBRARY

**Statement in words.** For two embedded attaching circles, the quotient has
an open cover whose pieces are homotopy equivalent to the two tori and whose
intersection is homotopy equivalent to the circle.

**Why true.** Use the annular-neighborhood theorem for a topological embedded
circle in a surface.  Give each torus a half-collar from the other side after
gluing.  The enlarged summands are open, cover the quotient, retract to their
original tori, and their overlap retracts to the common core circle.

**Expected size.** 500–1000 lines: the missing shared collar/Schoenflies
program dominates; the quotient-cover assembly is about 180–300 lines.

**Dependencies.** Definitions only.  This is the shared dependency of both
invariant calculations.

**Truth check.** In the model case where each circle is the boundary of a
small embedded disk in a torus, ordinary annular collars give exactly this
cover.  Compactness of `Circle` and embedding into the Hausdorff torus make
the range closed, ruling out the usual nonclosed-subspace pathology.

### `apm_t03J02_fundamentalGroup_of_openCover` — LIBRARY

**Statement in words.** Given the cover conclusion and null-homotopy of both
attaching maps, the fundamental group of the quotient is the frozen
four-generator/two-commutator presentation.

**Why true.** Seifert--van Kampen identifies the group as the pushout of the
two torus groups over the circle group.  Both legs are trivial by the supplied
null-homotopies, so this pushout is the free product.  Compute each torus group
as `ℤ²` and identify its free product with the displayed `PresentedGroup`.
The imported two-open fundamental-groupoid program supplies much of the
open-cover categorical machinery, but a circle-overlap pushout adapter and
the concrete torus calculation remain.

**Expected size.** 300–600 lines (one library program).

**Dependencies.** The conclusion of `apm_t03J02_pushout_openCover`, passed as
an explicit hypothesis so this seat can work independently.

**Truth check.** On generators, the overlap generator maps to the identity on
both sides; hence the amalgamation adds no cross relation.  The resulting
presentation has precisely `[a₁,b₁]` and `[a₂,b₂]`.

### `apm_t03J02_homology_of_openCover` — LIBRARY

**Statement in words.** Given the same cover conclusion and null attaching
maps, compute all integral singular homology groups in the frozen form.

**Why true.** Apply production Mayer--Vietoris.  The degree-one circle map into
the sum of torus homologies is zero by null-homotopy.  Exactness gives
`H₁ ≅ ℤ⁴` and a short exact sequence `0 → ℤ² → H₂ → ℤ → 0`; it splits because
`ℤ` is free, yielding `H₂ ≅ ℤ³`.  Connectedness gives `H₀ ≅ ℤ`, and the same
sequence gives vanishing above degree two.  The imported production sequence
exists; the substantial remaining work is the concrete torus/circle
coordinates and exact-sequence module algebra.

**Expected size.** 300–700 lines (one library program).

**Dependencies.** The conclusion of `apm_t03J02_pushout_openCover`, passed as
an explicit hypothesis.  It is independent of the fundamental-group lemma.

**Truth check.** The split sequence gives ranks `2 + 1 = 3` in degree two;
Euler characteristic and abelianization independently agree with the result.

## Dependency layers

* **Layer 1:** `apm_t03J02_pushout_openCover` (shared geometry program).
* **Layer 2, parallel:** `apm_t03J02_fundamentalGroup_of_openCover` and
  `apm_t03J02_homology_of_openCover`, each receiving Layer 1's conclusion as a
  hypothesis.
* **Layer 3:** the sorry-free `apm_t03j02` conjunction assembly.

One caveat for implementers: the compact cover certificate records homotopy
types, while compatibility of its equivalences with the canonical quotient
maps is not bundled into extra structure.  The two invariant programs still
have `j₁`, `j₂`, their null-homotopies, and the concrete quotient available,
so their statements are true, but a stronger future collar API may make their
proofs substantially shorter.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J02/Blueprint.lean
```

The final output of `#print axioms apm_t03j02` is:

```text
'apm_t03j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings identifying `sorry` are exactly the three top-level library
lemmas.  The main theorem contains no direct `sorry`.
