# Proof Outline: t92J05

The canonical Lean attempt is `lean/Main.lean`. The genus-two relator is a
genuine presented-group word, with its elementary commutator normalization
compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t92J05.md`

## Compiled progress

- `apm_t92J05_commutator_self` sanity-checks the commutator encoding.
- `apm_t92J05_genusTwoRelator_eq_one` proves the defining relator vanishes in
  the quotient, while `apm_t92J05_genusTwo_generators_generate` proves the four
  canonical elements generate it.
- `apm_t92J05_genusTwo_surface_relation` records the expanded two-commutator
  relation on those generators.
- Mathlib's fundamental-groupoid product theorem has been identified for the
  `S² × S¹` clause.
- `apm_t92J05_fundamentalGroup_prod_equiv` specializes product preservation to
  a based multiplicative-group equivalence using path-class projections.
- `apm_t92J05_product_group_of_subsingleton_left` collapses a trivial sphere
  factor and transports a circle-group equivalence to the frozen product.

## Remaining boundary

- Compute `π₁(S²)=1` and `π₁(S¹)=ℤ` for the concrete metric spheres;
  all product and basepoint transport is compiled.
- Construct the antipodal cover of projectivization and compute `π₁(RP²)`.
- Formalize compact oriented surface classification and Seifert--van Kampen,
  yielding the standard genus-two presentation.

## Hop 4 bridge statements

- `apm_t92J05_bridge_projectivePlane_fundamentalGroup` identifies the
  fundamental group of the concrete real projective plane with
  `Multiplicative (ZMod 2)` at every basepoint.
- `apm_t92J05_bridge_sphere_circle_fundamentalGroups` states the two factor
  computations needed by the compiled product route: the metric two-sphere
  has subsingleton fundamental group and the complex unit circle has
  fundamental group `Multiplicative ℤ`.
- `apm_t92J05_bridge_genusTwo_fundamentalGroup` states the missing surface
  classification/Van Kampen identification with the verified presented
  group.

These three contracts supply the three frozen clauses; the middle one plugs
directly into `apm_t92J05_product_group_of_subsingleton_left`.
