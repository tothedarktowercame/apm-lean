# Proof Outline: b94J01

The Lean proof has completed the cyclic-product criterion and the theorem that
finite subgroups of a field's unit group are cyclic.

For the finite-abelian-group clause, Mathlib supplies an unordered product of
prime-power cyclic factors. A local helper now additionally proves that every
list satisfying the frozen invariant-factor predicate has product equal to
`Nat.card G`.

## Remaining boundary

One sorry remains: normalize the primary factors into a divisibility chain and
prove uniqueness of that chain. The missing uniqueness argument requires
recovering the entries from p-primary torsion ranks; Mathlib currently has no
packaged invariant-factor theorem at this level.
