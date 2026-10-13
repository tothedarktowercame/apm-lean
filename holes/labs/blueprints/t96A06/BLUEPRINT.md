# t96A06 blueprint

## Triage

Verdict: **true and faithful**.  The Lean theorem states all three requests in
the problem: descent of the displayed quadratic formula, Lefschetz number
`-3`, and failure to be homotopic to the identity.

The obvious degeneracy is harmless.  If both complex squares represented by
the four real coordinates vanish, then both complex inputs vanish, so the
input vector was zero.  This is already formalized by
`t96A06Polynomial_nonzero`.  Homogeneity has even degree, so replacing a
representative by any nonzero real scalar does not change the resulting
projective point.  The existing sorry-free theorem
`t96A06Polynomial_descends` supplies the continuous descent.

## Definitions

`T96A06.IsPolynomialDescent f` is the pointwise commutative-square condition
saying that `f` is exactly the projective map induced by the printed
polynomial.  It contains no invariant or desired conclusion.

## Open lemma

### `T96A06_polynomialDescent_invariants` — LIBRARY

**Statement in words.** Every continuous self-map of the coinduced model of
`RP³` which agrees pointwise with the displayed quadratic descent has
Lefschetz number `-3` and is not homotopic to the identity.

**Why true.** Identify `ℝ⁴` with `ℂ²`.  The lift is
`(z,w) ↦ (z²,w²)`.  Its normalized map on `S³` has degree four (a regular
value has four preimages, all with positive local degree).  Compare the sphere
double cover with the coinduced projective model to show that the descended
map acts by multiplication by four on rational `H₃(RP³)`.  Rationally,
`RP³` has `H₀ ≅ ℚ`, `H₃ ≅ ℚ`, and all other homology zero, hence
the alternating trace is `1 - 4 = -3`.  Homotopy invariance of induced
homology maps would give the identity the same Lefschetz number, whereas its
number is `1 - 1 = 0`.

This is deliberately one LIBRARY lemma: the topology audit estimates the
missing RP³ rational-homology package at 500–1000 lines and the sphere degree
calculation at 700–1500 lines.  Splitting these into nominal 30–150-line
consumer lemmas would hide, rather than parallelize, the missing foundation.
The closest sorry-free modules are
`ConstructionTargets.SphereHomology`,
`ConstructionTargets.SphereAntipodalHomology`, and
`ConstructionTargets.CoefficientSphereAntipodal`.  The already attempted
sphere-to-coinduced-RP³ covering comparison is still missing; the topology
worklist records two reviewed STOPs because the only attempted package
postulated its essential fields.  No sorry-containing construction target is
imported here.

**Estimate.** 1400–2800 lines total, as a foundation/program rather than a
single lemma-seat session.

**Dependencies.** None among blueprint lemmas; it uses only the definitions
block.  Internally the future library program should proceed through: sphere
covering comparison; rational homology of RP³; degree four of normalized
complex squaring; transfer of degree to RP³; finite alternating trace and
homotopy invariance.

**Truth check.** For the regular projective value represented by `(1,0,1,0)`,
the equations `z²,w² ∈ ℝ·(1,1)` give four projective preimages after
quotienting the common sign, and the real Jacobian determinant away from the
coordinate axes is positive.  This agrees with degree `4`.  The homology
calculation gives `1-4=-3`, while the identity gives `0`.

## Already-proved assembly

`T96A06_polynomialMap_eq_consumerPolynomial` and
`T96A06_polynomialMap_descends` are sorry-free wrappers around the existing
construction target.  The main theorem merely chooses that descended map,
packages its nonzero witness, and invokes the LIBRARY lemma.

## Dependency layers

- Layer 0 (already proved): polynomial nonvanishing, orbit compatibility, and
  continuous projective descent.
- Layer 1 (program): `T96A06_polynomialDescent_invariants`.
- Layer 2 (sorry-free assembly): `apm_t96a06`.

## Axiom audit

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96A06/Blueprint.lean
holes/labs/blueprints/t96A06/Blueprint.lean:55:8: warning: declaration uses `sorry`
'apm_t96a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through
`T96A06_polynomialDescent_invariants`.
