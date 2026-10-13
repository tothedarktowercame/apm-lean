# Blueprint for t01J05

## Triage and repair

Verdict: **false as written; faithful after adding `[T2Space X]`**.

The source says that `X` is a manifold.  In the standard convention used by
the source, manifolds are Hausdorff (and second countable).  The Lean
`IsManifold` class is deliberately local and does not include Hausdorffness.
The smallest repair is therefore the `[T2Space X]` instance added in
`RevisedMain.lean`; compactness then supplies the needed countability in the
usual manifold applications.  No mathematical hypothesis from `problem.md`
was removed, and no hypothesis carrying the Poincaré--Hopf argument was added.

The registry counterexample survives all the unrepaired hypotheses.  Take the
circle with one point doubled, equivalently two circles glued along the
complement of one point.  It is a compact non-Hausdorff boundaryless smooth
one-manifold; identity transition maps give it a nowhere-zero `dθ`.  The
Mayer--Vietoris computation gives rational `H₀ ≅ ℚ` and `H₁ ≅ ℚ²`, hence the
frozen Euler characteristic is `1 - 2 = -1`.  It is excluded by `[T2Space X]`.
A compiled `Refute.lean` was not included: constructing this non-Hausdorff
manifold together with Mathlib chart and smooth-section instances would be a
substantial topology development and would not improve the registry's direct
mathematical counterexample.

Other degeneracies were checked.  For `n = 0`, every cotangent vector is zero,
so a nowhere-zero one-form forces `X` empty; the existing categorical `H₀`
calculation then gives Euler characteristic zero.  Empty positive-dimensional
manifolds are also harmless.  The fiberwise orientation predicate has no
continuity condition, but this does not make the conclusion false: the theorem
in fact does not need orientability.

## Reused completed work

`Blueprint.lean` retains the solve loop's compiled zero-dimensional argument:

- `apm_t01J05_eulerCharacteristic_zero` unfolds the one-term alternating sum;
- `apm_t01J05_isEmpty_of_nowhereZero_zeroDim` proves geometric emptiness;
- `apm_t01J05_finrank_H0_eq_zero_of_isEmpty` computes `H₀` of the empty space;
- `apm_t01J05_zeroDim` combines these results.

These declarations are sorry-free and need no lemma seat.

## Remaining lemma

### `apm_t01J05_poincareHopf_oneForm` — LIBRARY

**Statement in words.** A positive-dimensional compact Hausdorff smooth
manifold without boundary that carries a nowhere-zero smooth one-form has zero
Euler characteristic, where Euler characteristic is exactly the alternating
sum of rational Mathlib singular-homology finranks used by the problem.

**Why true.** Build a smooth Riemannian metric by a partition of unity.  Its
musical isomorphism sends the covector field to a smooth nowhere-zero tangent
vector field.  Poincaré--Hopf says the Euler characteristic is the sum of the
local indices of its zeros; the zero set is empty.  Finally identify the Euler
number in Poincaré--Hopf with the displayed rational singular-homology
alternating sum.

**Why LIBRARY.** Mathlib has smooth sections, tangent bundles, and structures
for already-supplied Riemannian metrics, but the topology-loop and solve-loop
audits found no packaged Poincaré--Hopf theorem, no global metric-construction
theorem in the needed form, and no comparison theorem to this literal
singular-homology sum.  The closest sorry-free vocabulary file is
`ConstructionTargets/ManifoldFormTargets.lean`; it defines chartwise forms but
does not supply any of these three bridges.  Thus this is one honest program,
not several nominal 30-line lemmas whose proofs would each conceal the same
missing index theorem.

**Estimate.** 600--1500 lines, depending on whether the program develops
Poincaré--Hopf through local indices or Euler classes.  This exceeds an
ordinary lemma seat.

**Dependencies.** Definitions only.  The main theorem gives this lemma the
positive-dimensional branch directly; the zero-dimensional branch uses the
completed lemmas above.

**Truth checks.** For `S¹`, `dθ` is nowhere zero and `χ = 0`.  For a torus,
translation-invariant one-forms give the same check.  On an even sphere the
nonzero Euler characteristic correctly forbids such a form.  The boundary
case `n = 0` is deliberately excluded and separately proved.  The doubled
circle counterexample fails precisely the new Hausdorff hypothesis.

## Dependency layers

- Layer 1: `apm_t01J05_poincareHopf_oneForm` (LIBRARY program).
- Layer 2 (already compiled): `apm_t01j05`, combining the LIBRARY result with
  the existing zero-dimensional theorem.

Lemma count: **1 remaining top-level lemma**, marked LIBRARY.

## Compilation and axioms

Both files compiled with the required 12 GiB scope:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01J05/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01J05/Blueprint.lean
```

The final `#print axioms apm_t01j05` output was:

```text
'apm_t01j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole `sorryAx` enters through
`apm_t01J05_poincareHopf_oneForm`; the main theorem has no direct `sorry`.
