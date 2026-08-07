# Proof Outline: t91J01

The theorem is fully proved in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J01.md`

## Formal proof

1. A hypothetical continuous surjection would make the irrational unit
   interval compact. Its image in `ℝ` would therefore be closed, contradicting
   density of the irrationals at the rational point `1/2`.
2. Reuse the Cantor-set nullity proof from sibling `a95J06`.
3. Scale the Cantor set by `1/2`. For each rational `q`, the translations `b`
   for which `x/2 + b = q` form an affine image of this null set.
4. Their countable union is null and hence cannot cover `(0,1/2)`, whose
   Lebesgue measure is positive. Choose `b` outside that union.
5. The map `x ↦ x/2 + b` is continuous and injective, lies in `(0,1)`, and is
   irrational at every Cantor-set point by the choice of `b`.
