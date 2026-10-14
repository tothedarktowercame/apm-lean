# t96A06 blueprint

## Triage

Verdict: **true and faithful**. The registered theorem is unchanged. The
quadratic has no nonzero common zero (`t96A06Polynomial_nonzero`), and the
already proved `t96A06Polynomial_descends` supplies its continuous descent.

The former 1400--2800-line invariant boundary is now split at the rational
singular-homology interface. All eight leaves below are top-level and
independent: none mentions another new lemma. The old
`T96A06_polynomialDescent_invariants` is a sorry-free assembly.

## Independent leaves

### `T96A06_rp3_rationalHomology_finite` (80--140 lines)

Every rational singular homology group of the coinduced model of `RP³` is
finite-dimensional. Develop the cellular/quotient comparison once, then use
`FiniteDimensional.of_equiv`. Relevant interfaces are the sphere homology
equivalences and off-degree vanishing in `ConstructionTargets.SphereHomology`.
The missing ingredient is comparison of the sphere antipodal quotient with
`ProjectiveSpaceTopology.Space`; it must be proved, not postulated.

### `T96A06_rp3_rationalHomology_vanishes_above_three` (80--140 lines)

Rational homology is subsingleton above degree three. Use the same
quotient/cellular comparison and
`sphereHomologyObj_offDegree_subsingleton`. This says only `3 < k`, exactly
the support certificate needed by `HasLefschetzNumber`, and preserves degree
three.

### `T96A06_polynomialDescent_trace_zero` (40--90 lines)

The induced endomorphism on rational `H₀` has trace one. Show the quotient is
nonempty and path connected (lift points to `S³`), identify `H₀` with `ℚ`,
and use functoriality of `AlgebraicTopology.singularHomologyFunctor`.
`coordinateLine` supplies a point, so there is no empty-space degeneracy.

### `T96A06_polynomialDescent_trace_one` (30--70 lines)

The degree-one trace is zero. Prove rational `H₁(RP³)` vanishes (integrally it
is `Z/2`, hence is killed over `ℚ`) and use trace on the zero module. Candidate
tools are the quotient long exact sequence,
`SphereAntipodalHomology.antipodal_homology`, and
`LinearMap.trace_eq_matrix_trace`; confirm local names with `#check`.

### `T96A06_polynomialDescent_trace_two` (30--70 lines)

The degree-two trace is zero. Use the cellular boundary map (multiplication by
two in the relevant projective-space degree) or the antipodal quotient
comparison, then trace on the zero module. Boundary sign conventions are
irrelevant once that boundary is an isomorphism over `ℚ`.

### `T96A06_polynomialDescent_trace_three` (100--150 lines)

The substantive degree leaf: the descent acts by multiplication by four on
rational `H₃`, hence has trace four. Normalize `(z,w) ↦ (z²,w²)` on `S³`;
a regular value away from the coordinate axes has four preimages after the
common antipodal identification, all with positive local sign. Transfer this
through the antipodal quotient. Relevant foundations are
`ConstructionTargets.SphereHomology`, `SphereAntipodalHomology`, and
`CoefficientSphereAntipodal`. If the regular-value degree theorem is absent,
keep that missing foundation visibly LIBRARY rather than postulating fields.

### `T96A06_identity_trace_three` (30--60 lines)

The identity has trace one on rational `H₃(RP³)`. Identify that group with
`ℚ`, rewrite the induced identity map by functoriality, and use
`LinearMap.trace_id` plus finrank one. This is separate from the polynomial
degree leaf, so it cannot inherit that leaf's sorry.

### `T96A06_homotopic_induced_eq` (10--25 lines)

Homotopic maps induce equal rational homology maps. Import
`ConstructionTargets.SingularHomologyHomotopy` if needed and specialize
`singularHomology_map_eq_of_homotopic (ModuleCat ℚ) (ModuleCat.of ℚ ℚ)`.
That theorem is already sorry-free; this leaf should close by `simpa`/`change`.

## Sorry-free assembly

`T96A06_polynomialDescent_invariants` uses bound `3`, expands the four-term
sum with `Finset.sum_range_succ`, rewrites the four traces, and obtains
`1 - 4 = -3` by `norm_num`. A hypothetical homotopy makes the degree-three
endomorphisms equal, so congruence of trace contradicts `4 = 1`.

`apm_t96a06` remains byte-identical and merely chooses the existing descent
and invokes this assembly.

## Degeneracy and truth audit

- Polynomial nonvanishing is discharged before these leaves.
- `RP³` is nonempty, so the `H₀` trace is one rather than zero.
- The support bound is strict (`3 < k`), preserving top homology.
- Odd-dimensional real projective space is orientable, so rational `H₃` is
  one-dimensional.
- Use a regular value with both complex coordinates nonzero; coordinate-axis
  values are unsuitable for the four-preimage local-degree count.
- No leaf restates `IsPolynomialDescent`, assumes its own conclusion, or
  mentions another new leaf.

## Axiom audit

The file compiles with eight warnings, one per independent leaf. The assembly
and main theorem contain no `sorry`; `#print axioms apm_t96a06` reports
`sorryAx` only through those leaves, with `propext`, `Classical.choice`, and
`Quot.sound`.
