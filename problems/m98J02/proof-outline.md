# Proof Outline: m98J02

The competition attempt is `lean/Main.lean` (`apm_m98j02`). It states part (d)
as printed: every `f ∈ C²(ℝ²)`. See `problem.md`, "Interpretation note".

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98J02.md`
- out-of-competition finding: `out-of-competition/` (narrow reading, closed)

## Compiled progress

- (a) Compactly supported distributions are closed under addition, zero,
  negation, subtraction and scalar multiplication.
- (b)–(c) `apm_m98J02_bridge_2`: for compactly supported `u` and any `v`,
  the convolution `u * v` exists as a distribution, defined by a cutoff
  pairing. Cutoff independence and uniqueness are proved too.
- Tools for (d) that carry over from the narrow reading: regular
  distributions of compactly supported continuous functions, the nonzero
  homogeneous solution (the constant 1), and `solvesT_add_homogeneous`.

## Open: `apm_m98J02_partD`

Informal route (`informal-solution.md`, part (d)):

1. Define `J₀` as the power series `Σ (-1)ᵏ (z/2)^{2k} / (k!)²`. Mathlib has
   no Bessel functions. Then define `E₊` on the cone
   `Γ₊ = {y > 0, 3x > 2y}`, and `E₋(p) = -E₊(-p)`.
2. `T E₊ = δ₀` in the `solvesT` sense. This is a Riemann-function computation
   in the characteristic coordinates of `2∂ₓ² + 3∂ₓ∂ᵧ`.
3. For a smooth cutoff `χ(x)` and `f₊ = χ f`, `f₋ = (1 - χ) f`, the integrals
   `E₊ * f₊` and `E₋ * f₋` range over compact triangles near each point, so
   they define continuous functions.
4. `∂^α (E± * f±) = E± * ∂^α f±` for `|α| ≤ 2`, which gives `C²`.
5. Pairing with `Tᵗ φ` and Fubini give `T w = f`. The constant 1 gives `w'`.

Steps 1–2 are the hard part; the rest follows the pattern of the
narrow-reading proof.
