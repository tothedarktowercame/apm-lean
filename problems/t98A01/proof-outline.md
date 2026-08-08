# Proof Outline: t98A01

This bundle contains a compiling partial Lean formalization.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t98A01.md`

## Compiled progress

- the promoted connected-sum definition computes the printed surface data as
  `(false, 11)`;
- the requested homeomorphism then reduces to `Homeomorph.refl`;
- its Euler characteristic computes to `-9`;
- equal orientable genera together with five-sheet Euler multiplicativity force
  both genera to be `1`.
- `t98A01_circleFive_isAddQuotientCoveringMap` uses Mathlib's dedicated
  `AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero` theorem to identify
  `x ↦ 5 • x` as the quotient covering by its five-torsion kernel.
- The corresponding circle covering-map and surjectivity statements are
  compiled, and the three connected-sum tail conjuncts are now assembled in
  the main theorem.

## Remaining boundary

- promote the compiled circle quotient cover to the product map
  `(x,y) ↦ (5x,y)`, identify its fibers with the five-torsion kernel, prove
  their `Nat.card` is five, and package kernel translations as deck
  homeomorphisms;
- prove finite-cover Euler-characteristic multiplicativity for the promoted
  polygon surfaces;
- connect homeomorphism of orientable polygon presentations to equality of
  their genus parameters.
