# Proof Outline: b98A03

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The polynomial constant-term membership criterion is now proved in full.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A03.md`

## Compiled progress

- For `u ∈ Q` with `comap Q = P`, `eval₂ u p ∈ Q` iff `p.coeff 0 ∈ P`.
- The reverse direction is proved by the decomposition
  `p = divX(p) * X + C(p.coeff 0)`.

## Remaining bridge

Use the criterion and the singleton-adjoin range theorem to prove equality of
the two contractions to `R[u]`. Separately characterize the ideal supremum
conductor elementwise, then transport the minimal-subalgebra hypothesis into
the final equalities with `Ideal.map P`, `Q₁ ⊓ Q₂`, and the conductor.
