# Proof Outline: b98A03

The frozen theorem has a complete, sorry-free formalization in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A03.md`

## Compiled progress

- For `u ∈ Q` with `comap Q = P`, `eval₂ u p ∈ Q` iff `p.coeff 0 ∈ P`.
- The reverse direction is proved by the decomposition
  `p = divX(p) * X + C(p.coeff 0)`.
- Every eligible ideal lies below the conductor supremum.
- If `u ∈ Q₁ ∩ Q₂`, the two contractions to `R[u]` are equal: represent each
  adjoin element by `aeval u p` and apply the constant-term criterion twice.
- The elementwise conductor is constructed as an ideal and proved equal to the
  supremum definition by its greatest-eligible-ideal property.
- A conductor element represented by `r ∉ P` forces primes `Q₁` and `Q₂`
  above `P` to coincide, using primality on the products `r * x`.
- Under the minimal-subalgebra hypothesis, adjoining any element of `Q₁ ∩ Q₂`
  gives the bottom subalgebra, so every such element lies in the algebra-map
  range. This proves `map P = Q₁ ∩ Q₂`; prime separation then proves that
  this intersection is the conductor.

## Remaining bridge

None.
