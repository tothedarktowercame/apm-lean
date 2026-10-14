# Blueprint for t91A01

## Triage

Verdict: **true and faithful**.  `Main.lean` is the registered repaired
encoding.  It makes the informal “compact, oriented surface” precise as a
compact connected boundaryless smooth two-manifold, and it computes the local
index from the normalized chart field rather than accepting an arbitrary
integer label.

I tried the relevant degeneracies.  The type `F` cannot be empty because the
theorem supplies `p : F`.  The zero field cannot satisfy
`apm_t91a01_hasIndexThreeZero`, since that predicate requires the chart field
to be nonzero at every point of the linking circle.  Radius zero is excluded by
`0 < r`.  A constant nonzero field cannot satisfy `V p = 0`.  If `p` were the
only zero, the encoded linking map contributes local index `3`, while
Poincaré--Hopf and orientability make the Euler characteristic of the closed
surface even; hence the conclusion follows exactly as in the informal proof.

There is no cached solve-loop `Main.lean` for this problem, no matching
solve-loop record, and no exact `t91A01` row in the available topology
worklists or audits.  I also searched the sorry-free `ConstructionTargets`
modules by the terms `Poincare`, `Hopf`, `Euler`, `vector`, `index`, and
`surface`.  None supplies Poincaré--Hopf or local vector-field index theory.
The closest related repository effort is the closure program for `t01J05`,
whose recorded missing theorem is likewise a Poincaré--Hopf bridge (there for
a nowhere-zero one-form).  The surface classification and polygon-surface
homology modules do not identify the local winding of a tangent section or
prove the index-sum theorem, so importing them would not remove the genuine
missing foundation.

## Definitions

The definitions are copied unchanged from `Main.lean`: the complex cubic
field, the two-dimensional manifold model, the explicit orientation
certificate, the tangent field in a chart, the circle parametrization, the
continuous cubic circle map, and `apm_t91a01_hasIndexThreeZero`.  No predicate
is defined as the desired global conclusion: the index-three predicate only
contains local disk, nonvanishing, normalization, and homotopy data.

## Lemmas

### `apm_t91a01_vectorField_zero_iff` (proved)

**Statement.** The explicit field `z ↦ z³` vanishes exactly at `0`.

**Why true.** This is `pow_eq_zero` over `ℂ`; `simp` closes it after unfolding
the definition.

**Expected size.** Already proved in 2 lines.

**Dependencies.** Definitions only.

**Truth check.** At the degenerate input `z = 0`, both sides hold.  For
`z ≠ 0`, a power in the field `ℂ` is nonzero.

### `apm_t91a01_vectorField_on_unit_circle` (proved)

**Statement.** On `exp(iθ)`, the cubic field is `exp(i(3θ))`.

**Why true.** Rewrite the third power of an exponential with
`Complex.exp_nat_mul`, then normalize the scalar coercions and use `ring`.

**Expected size.** Already proved in 8 lines.

**Dependencies.** Definitions only.

**Truth check.** At `θ = 0`, both sides are `1`.  The identity is the standard
exponential law and is valid at all periodic endpoint representatives.

### `apm_t91a01_index_three_forces_other_zero` — LIBRARY

**Statement.** On a compact connected oriented boundaryless smooth surface, a
smooth tangent section with an isolated zero `p` whose actual normalized chart
link is homotopic to `z ↦ z³` has another zero.

**Why true.** Develop local index as the degree/winding number of the
normalized field on the boundary of a chart disk.  Homotopy invariance and the
cubic link give index `3` at `p`.  If there were no other zero, compactness and
the supplied isolation data reduce the Poincaré--Hopf sum to this single
index, so `χ(F) = 3`.  Poincaré--Hopf together with the classification (or
Poincaré duality) of compact connected oriented closed surfaces gives
`χ(F) = 2 - 2g`, an even integer, a contradiction.

This is marked LIBRARY rather than divided into fake short obligations:
Mathlib and the sorry-free repository modules currently have neither the
local degree/index package for tangent sections nor Poincaré--Hopf.  A real
implementation should be a shared program with the Poincaré--Hopf foundation
needed by `t01J05`; its surface specialization must additionally connect the
literal `apm_t91a01_hasIndexThreeZero` chart link to local index.  No existing
named shared-foundation program in the batch notes has this statement form.

**Expected size.** 1500–3000 lines as a foundation program, not one lemma-seat
session.  The local index API and global Poincaré--Hopf proof should be reusable
construction modules, but the blueprint records one honest library boundary.

**Dependencies.** Definitions only.  It deliberately does not assume the
conclusion, an index sum, an Euler-characteristic formula, or another lemma's
local hypothesis.

**Truth check.** If `p` were the only zero, the sum of indices would be the odd
integer `3`.  Every compact connected oriented closed surface has Euler
characteristic `2 - 2g`, which is even.  On the sphere the required remaining
index sum is `-1`; on the torus it is `-3`.  The empty, zero-field, radius-zero,
and nonisolated-zero edge cases are excluded by the actual hypotheses as
described in triage.  I am mathematically confident in the lemma; the doubt is
only the amount of missing formal infrastructure.

## Assembly

The main theorem uses the two proved elementary lemmas for the first two
conjuncts and applies the LIBRARY lemma to the third.  The main theorem has no
`sorry` of its own and its type is copied exactly from `Main.lean`.

## Dependency layers

* **Layer 1 (independent):** the two elementary lemmas (already proved) and
  `apm_t91a01_index_three_forces_other_zero` (LIBRARY).
* **Layer 2 (already proved):** conjunction assembly in `apm_t91a01`.

There are three named lemmas total, of which one is an unresolved LIBRARY
obligation.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t91A01/Blueprint.lean
```

The output of `#print axioms apm_t91a01` is:

```text
'apm_t91a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only declaration warning for `sorry` is the LIBRARY lemma.  The main
theorem therefore receives `sorryAx` only through that lemma.
