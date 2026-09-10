# Finite formulas realize the coefficient-general operators

This module proves that the existing finite subdivision and prism formulas
realize to the reviewed R-linear operators. The commutative ring `R`, vertex
types, spaces and simplex index types are universe zero. Simplex index types
have `Fintype`; spaces have `TopologicalSpace`. Integer weights encode finite
signed formulas, while realized arrows have source `ModuleCat.of R R` and
target actual `ModuleCat R` chains.

`realize` sums ordered-vertex generators. Its singleton, additive, signed-sum,
bind, cone and boundary equations are proved directly. Induction on the
existing finite recursion proves `finiteVertexSubdivision_realize` and
`finiteVertexPrism_realize`, using the reviewed coefficient-general cone,
subdivision and prism without duplicating their constructions.

`postcomposeFiniteVertexChain_realize` compares finite postcomposition with
affine realization followed by actual singular postcomposition.
`subdivision_realize` and `prism_realize` therefore identify realization of
the finite formulas with the singular simplex generator followed by the
reviewed operator. These equations run from finite realization to actual
operator application. No coefficient-change theorem or integral homology
conclusion is used.

All four integer/rational standard-edge equations compile; seven printed
axiom audits are included. Imports are `CoefficientFiniteRealization` and
`CoefficientSingularPrism`. The Lean file is an exact promotion of
`/tmp/CoefficientFiniteOperators.lean`, SHA256
`cfe5ab726fdc46212ff59c922057fb8f97b077305150dffbbf8ca5daf48a2852`.

The next step is to apply subordinate-support factorization to construct
small-chain restrictions, prove their actual inclusion equations and assemble
the restricted homotopy. This module does not establish those restrictions,
eventual smallness, homology comparison, excision or frozen consumer closure.
