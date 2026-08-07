# Proof Outline: b99A04

The Lean proof closes all four parts, including the finite-module
classification.

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
- Every finite-dimensional module is finite over the matrix ring. Each of its
  abstract simple constituents is transported to a simple ideal of the regular
  module, identified with a concrete column by matrix-ring isotypy, and hence
  identified with the standard module. `IsIsotypicOfType.linearEquiv_fun` then
  supplies the requested finite power.

## Remaining Boundary

None.
