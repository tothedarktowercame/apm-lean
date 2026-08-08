# Proof Outline: m98J02

The canonical Lean attempt is `lean/Main.lean`. It proves the support-addition
clause and isolates the missing test-function-topology constructions.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98J02.md`

## Compiled progress

- `apm_m98J02_hasCompactSupport_add` proves compactly supported distributions
  are closed under addition by using the union of compact support witnesses.
- The support predicate is also proved closed under zero, negation,
  subtraction, and real scalar multiplication.
- `apm_m98J02_solvesT_add_homogeneous` proves that adding a homogeneous
  solution preserves an inhomogeneous equation.
- `apm_m98J02_translateTest` constructs the translated test function
  `y ↦ φ (x + y)`. Its smoothness and compact support are proved using
  composition and `HasCompactSupport.comp_homeomorph`.

## Remaining boundary

- Construct the regular distribution `φ ↦ ∫ f φ` as a continuous linear map
  on Mathlib's test-function LF topology.
- Construct a cutoff test function and package the iterated distribution
  pairing as the requested convolution; translation is already compiled.
- Prove convolution regularity and commutation with the encoded differential
  operator.
- Construct a nonzero homogeneous regular distribution; the compiled addition
  lemma then produces the distinct solution `w'`.
