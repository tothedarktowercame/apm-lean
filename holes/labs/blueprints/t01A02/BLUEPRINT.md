# Blueprint for t01A02

## Triage

Verdict: **true and faithful**.  The registered Lean theorem uses the concrete
torus `Circle × Circle`, the coordinatewise squaring cover, integral singular
`H₂`, and exactly the non-surjectivity and factorization hypotheses in
`problem.md`.

I tried the relevant degeneracies.  A constant map is nonsurjective and its
`H₂` map is zero; if its value is `(1,1)`, it factors through the squaring
cover and has that value as a fixed point.  Coordinate maps such as
`(z,w) ↦ (z²,1)` are nonsurjective and have zero top-dimensional degree.
The cover itself is surjective, so it does not accidentally satisfy the
non-surjectivity hypothesis of part (c).  There is no empty-space or zero-space
degeneracy because `Circle × Circle` is fixed and inhabited.  These checks
agree with the informal degree/Lefschetz argument and with the batch note that
the statement was graded faithful.

The concrete cover/deck-action theorem is already proved in the sorry-free
`ConstructionTargets.TorusSquareDeckAction`.  The once-punctured torus `H₂`
calculation and the factor-through-zero adapter are already proved in the
sorry-free `ConstructionTargets.T01A02PuncturedTorusH2`; the blueprint imports
and uses them.  I also searched all sorry-free `ConstructionTargets` files for
`T01A02`, `Torus`, and `Lefschetz`.  `RationalLefschetz` defines only an
interface and supplies no fixed-point theorem.  No existing module supplies
the remaining integer-lift/planar-surjectivity result.

## Remaining lemmas

### `apm_t01A02_punctured_H2_isZero`

**Statement in words.** The integral second singular homology of the torus
with any one point removed is zero.

**Why true.** The banked theorem
`ConstructionTargets.T01A02PuncturedTorus.puncturedTorus_H2_isZero` proves this
for the fixed puncture `(-1,-1)`.  Coordinatewise multiplication by constants
in `Circle` is a homeomorphism carrying an arbitrary `q` to that point.
Restrict it with `Homeomorph.subtypeCongr`, apply the homology functor to the
resulting `TopCat` isomorphism, and transport `IsZero` across that isomorphism.
The relevant banked theorem and `H2map_eq_zero_of_factor` were checked by
compiling the import and the downstream adapter in `Blueprint.lean`.

**Expected size.** 30–60 lines.

**Dependencies.** Definitions and
`ConstructionTargets.T01A02PuncturedTorusH2` only.

**Truth check.** At the banked puncture this is exactly the compiled theorem.
Multiplication on each circle has an explicit inverse, so no special point
(including `(1,1)` and `(-1,-1)`) is exceptional.

### `apm_t01A02_fixedPoint_or_surjective_of_lift` (LIBRARY)

**Statement in words.** If a torus self-map factors through coordinatewise
squaring, then it either has a fixed point or is surjective.

**Why true.** Lift the map to a continuous `F : ℝ² → ℝ²`.  Its
periodicity determines an integer matrix `A`, and factorization through the
double-in-each-coordinate cover makes the relevant winding matrix even.  If
there is no fixed point, the parity calculation makes `I-A` invertible.  The
periodic error `F-(I-A)` is bounded on a fundamental square.  The standard
bounded-perturbation theorem in the plane then makes `F` surjective, and hence
the original torus map surjective.  Equivalently, this is the elementary lift
proof of the Lefschetz parity argument from the informal solution.

This is marked LIBRARY because its two missing foundations are precisely the
topology audit's `torus_map_integer_lift` (estimated 120–220 lines) and
`planar_bounded_perturbation_surjective` (150–300 lines).  Splitting the final
dichotomy into fake adapters would not make either foundation independently
provable in a lemma seat.  The statement does not assume non-surjectivity and
does not contain its conclusion as a predicate or hypothesis.

**Expected size.** Two foundation programs of 120–220 and 150–300 lines,
followed by an 80–140 line adapter, matching
`/home/joe/notes/closer/audits/t01A02.edn`.

**Dependencies.** Definitions only.  It is independent of the punctured
torus homology lemma.

**Truth check.** For the identity map the left disjunct holds everywhere and
the right disjunct also holds.  For a constant factorizing map, its constant
value is a fixed point.  For the squaring cover itself, surjectivity supplies
the right disjunct.  These exercise the singular, constant, and nontrivial
covering cases.  The hand proof is the integer-matrix parity argument above.

## Proved assembly

`apm_t01A02_H2map_eq_zero` chooses a missed point, factors `f` through its
complement, and applies the banked factor-through-zero theorem plus the first
lemma.  `apm_t01A02_covering_group` is proved entirely from the banked deck
action.  The final theorem resolves the fixed-point/surjective dichotomy using
the given non-surjectivity hypothesis.  The main theorem has no direct
`sorry`.

## Dependency layers

* **Layer 1 (parallel):** `apm_t01A02_punctured_H2_isZero` and the LIBRARY
  program for `apm_t01A02_fixedPoint_or_surjective_of_lift`.
* **Layer 2 (already compiled):** the `H₂` adapter and final conjunction,
  after the corresponding Layer 1 results are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A02/Blueprint.lean
```

The output of `#print axioms apm_t01a02` was:

```text
'apm_t01a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 declarations.
