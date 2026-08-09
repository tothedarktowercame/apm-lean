# Proof Outline: b94J01

The Lean proof has completed the cyclic-product criterion and the theorem that
finite subgroups of a field's unit group are cyclic.

For the finite-abelian-group clause, Mathlib supplies an unordered product of
prime-power cyclic factors. A local helper now additionally proves that every
list satisfying the frozen invariant-factor predicate has product equal to
`Nat.card G`.

`apm_b94J01_invariantFactors_eq_nil_of_card_eq_one` also proves that an
admissible list for a group of cardinality one must be empty: any nonempty list
would contain a factor at least two dividing a product equal to one.

`apm_b94J01_existsUnique_invariantFactors_of_card_eq_one` completes this edge
case, constructing the empty-product equivalence with `MulEquiv.ofUnique` and
packaging the required `∃!` statement.

## Remaining boundary

One sorry remains, now only for nontrivial groups: normalize the primary factors
into a divisibility chain and prove uniqueness of that chain. The argument requires
recovering the entries from p-primary torsion ranks; Mathlib currently has no
packaged invariant-factor theorem at this level.

## Hop 4 bridge statement

`apm_b94J01_bridge_1` states existence and uniqueness of the normalized
invariant-factor list under the exact remaining hypothesis `Nat.card G ≠ 1`.
A case split on cardinality combines it with the compiled cardinality-one
helper, so no cyclic-product or field-unit-group facts are included in the
bridge.
