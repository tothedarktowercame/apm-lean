# Proof Outline: t03J02

The genuine quotient presentation is now accompanied by a named continuous
surjection from the disjoint union and a proof that the two circle embeddings
agree pointwise after quotienting.

Closer hop 2 adds `apm_t03J02_gluedDesc`, its restriction equations, and
`apm_t03J02_gluedDesc_unique`, establishing the quotient's full function-level
continuous pushout universal property.

Closer hop 3 packages that property as the actual equivalence
`apm_t03J02_gluedDescEquiv` between continuous maps out of the quotient and
compatible pairs of maps from the two torus summands. The canonical continuous
coprojections are now named `apm_t03J02_gluedInl` and `apm_t03J02_gluedInr`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J02.md`

## Remaining boundary

- connect the compiled maps-out equivalence to an invariant theorem;
- apply or develop Seifert--van Kampen, using null-homotopy of both attaching
  circles to compute the free product of the two torus groups;
- develop singular Mayer--Vietoris or a cellular comparison to compute the
  displayed homology groups;
- supply the concrete torus fundamental-group and singular-homology
  computations required by those arguments.

Mathlib currently provides neither the required topological van Kampen theorem
nor a singular Mayer--Vietoris sequence.
