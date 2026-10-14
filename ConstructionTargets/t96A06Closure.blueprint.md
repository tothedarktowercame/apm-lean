# t96A06 closure blueprint

The frozen consumer is `problems/t96A06/lean/Main.lean`.  Its space is the
literal algebraic projectivization `Space ℝ 3`, its map is the printed four
coordinate quadratic, and `HasLefschetzNumber` is the actual rational
singular-homology trace predicate.  No alternate RP³ model or abstract map may
replace these definitions.

The earlier row named a source blueprint under
`holes/labs/blueprints/t96A06/`, but that directory does not exist.  This
reviewable plan is therefore the first program milestone.  The descent proof
already compiles in `ProjectiveConsumerLiftDemonstrations`; the remaining work
is homology, degree, trace bookkeeping, and assembly.

## C1. Exact polynomial descent — proved

Reuse `t96A06Polynomial_nonzero`, `t96A06Polynomial_orbit`, and
`t96A06Polynomial_descends`.  The formula is complex squaring on each of two
complex coordinates, but the conclusion stays in the frozen real-vector
quotient.  Copy the already compiled comparison and descent proof from Main.

This is now compiled in `t96A06Closure.lean`: `polynomialDescent` fixes the
witness, `polynomialDescent_quotientMap` gives its exact representative
formula, and `exists_polynomialDescent_formula` matches the registered
existential clause.

## C2. Rational homology of RP³ — library

Construct data for the literal `Space ℝ 3`:

- every rational singular homology group is finite-dimensional;
- groups above degree 3 are subsingleton;
- H₀ and H₃ are linearly equivalent to ℚ;
- H₁ and H₂ are subsingleton.

Use the sphere double cover and rational covering transfer.  The antipodal
map on S³ has degree `+1`, so transfer identifies the invariant part with all
of H₃; in intermediate degrees sphere homology vanishes.  Package these
facts in a local structure whose fields directly discharge
`HasLefschetzNumber`, rather than substituting an integral calculation.

Shared dependency: reuse the coefficient/sphere and trace infrastructure also
needed by t99J05, but do not identify real and complex projective homology.

The first part now compiles in `t96A06Closure.lean`:
`nonzeroVectors3PathConnectedSpace` and `rp3PathConnectedSpace` establish
connectedness of the exact quotient model, and `rp3RationalH0Iso` computes
its degree-zero rational homology as `ℚ`.
The normalized projection from the concrete unit three-sphere is now tied to
the frozen quotient topology: `rp3RadialToSphere` is continuous, its composite
with `sphereProjection 3` is the original nonzero-vector quotient map, and
`rp3SphereProjection_isQuotientMap` proves the exact quotient authority needed
before constructing the two-sheeted covering transfer.  The companion theorem
`rp3SphereProjection_eq_iff` computes every fiber as exactly a point and its
antipode.
The local half of the covering construction is also compiled:
`rp3SphereProjection_isOpenMap` follows from the quotient authority and the
antipodal saturation formula, while positive hemispheres give injective open
restrictions around every sphere point.  Hence
`rp3SphereProjection_isLocalHomeomorph`.  The covering milestone is now
compiled as well: `rp3SphereProjection_isClosedMap` uses the same antipodal
saturation formula for closed sets, and
`t96A06_rp3_sphere_covering` applies the finite-fiber local-homeomorphism
criterion after bounding each fiber by its explicit antipodal pair.  Rational
transfer through this covering now has its exact sheet-count input:
`rp3SphereAntipodal_ne` separates the two points and
`t96A06_rp3_sphere_twoSheeted` packages finiteness and cardinality two as
`IsKSheetedCover (sphereProjection 3) 2`.  The induced rational homology
transfer and its consequences remain.

## C3. Degree four of the quadratic map — library

Restrict complex squaring `(u,v) ↦ (u²,v²)` radially to S³ and prove that
its degree is 4.  A bounded route is a regular-value computation: choose a
target with both complex coordinates nonzero, classify its four preimages,
and show the real Jacobian preserves orientation at each.  Then compare the
sphere lift with the descended RP³ map through the two double-cover
projections.  Record the resulting action on H₃(RP³;ℚ) as multiplication by
4.  The comparison must use the actual descended-map equation from C1.

## C4. Lefschetz and identity values — library

From C2 and C3, prove `HasLefschetzNumber f (-3)`: H₀ contributes 1, H₁ and
H₂ contribute 0, and H₃ contributes `-4`.  Separately prove
`HasLefschetzNumber (ContinuousMap.id RP3) 0`.  Use homotopy invariance of
singular-homology maps to show any map homotopic to the identity has
Lefschetz number 0; uniqueness follows by comparing the finite trace sums.
Consequently the descended map is not homotopic to the identity.

## C5. Main assembly

Choose the map supplied by C1, retain its exact formula for every nonzero
vector, attach C4's value and nonhomotopy proof, and return the registered
conjunction.  `polynomialMap_nonzero` supplies the existential proof term in
the first conjunct.  The sole placeholder changes from one to zero only here.

## Dependency order and gates

C1 is banked.  C2 and the sphere-degree part of C3 are independent; C3's
projective comparison uses C1.  C4 depends on C2 and C3.  C5 depends on C1
and C4.

Every milestone must compile without `sorry` or new axioms.  Final gates are
`lake env lean problems/t96A06/lean/Main.lean` and
`python3 scripts/statement-registry.py check`; the registered statement and
all definitions it mentions remain unchanged.
