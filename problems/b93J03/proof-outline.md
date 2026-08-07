# Proof Outline: b93J03

The Lean proof is partial in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b93J03.md`

## Completed formal steps

- The commuting family is converted to an indexed family of endomorphisms.
- Mathlib's simultaneous generalized-eigenspace decomposition proves that the
  supremum of common generalized eigenspaces is top.
- A nonzero common generalized eigenspace is extracted by the standalone
  proved helper `apm_b93J03_exists_nonzero_simultaneous_maxGenEigenspace`.

## Remaining bridge

Prove a nonzero common ordinary eigenspace for the commuting nilpotent parts,
then perform dimension induction through the quotient by that eigenline and
assemble a `Fin (finrank k V)` basis whose matrices satisfy
`Matrix.BlockTriangular id`. `Eigenspace/Pi.lean` does not package this basis
construction, and the available Lie-theorem API presupposes a triangularizable
Lie-module instance.

Closer hop 2 also checked `Basis.flag`: it constructs a maximal submodule
chain from a basis, but Mathlib has no converse constructor producing a basis
from an invariant chain. Thus it does not shorten the quotient-basis bridge.

Closer hop 3 checked the Lie-span route more precisely. Algebraic closure does
give `LieModule.instIsTriangularizableOfIsAlgClosed`, and the span of the
commuting family can be shown abelian with
`LieSubalgebra.isLieAbelian_lieSpan_iff`. The available solvable Lie theorem,
however, assumes characteristic zero. Its characteristic-free nilpotent
variant assumes the entire module action is nilpotent, which is false for
families containing nonzero scalar maps. Consequently the frozen theorem in
positive characteristic still requires the direct common-kernel and quotient
induction.
