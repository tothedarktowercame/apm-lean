# Proof Outline: b99A04

The Lean proof now closes parts (a)--(c) and leaves one boundary in the final
finite-module classification.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b99A04.md`

## Formalized

- Simplicity of the standard column module by an explicit rank-one matrix.
- Concrete column left ideals, transported from `Finsupp.lsingle` through an
  explicit column-coordinate linear equivalence.
- Independence, supremum `⊤`, and equivalence of every column with the
  standard module.
- Every nonzero column-action range is a copy of the standard module, using
  injectivity of a nonzero linear map from a simple module.

## Remaining Boundary

Use the matrix ring's isotypic decomposition for a finite module `W`, then
identify its abstract simple constituent with the concrete standard module.
The intended direct bridge chooses a nonzero vector in the constituent and
uses the proved column supremum to obtain a column acting nontrivially; the
preceding action-range equivalence then identifies the constituent with `V`.
