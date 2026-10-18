# Proof Outline: m02J02

`lean/Main.lean` proves `apm_m02j02` with no `sorry` (closed by the solve
loop in df7cf59b9; axioms `propext`, `Classical.choice`, `Quot.sound`).

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J02.md`

## What is proved

`apm_m02j02_IsH10Basis s e de`: every `e n` lies in `H¹₀(s)` (with weak
derivative `de n`), the pairs `(e n, de n)` are linearly independent, and their
finite linear combinations are dense in `H¹₀(s)` in the `H¹` graph norm.

- (a) `Ω = (0,1)`: the sines `sin((n+1)πx)`.
- (b) `Ω = (0,∞)`: the odd Hermite functions `h_{2n+1}`.
- (c) `Ω = ℝ`: all Hermite functions `h_n`.

## How "basis" is read

The Lean statement reads "basis" as a linearly independent family with dense
span. The revised informal solution (7de364a86) reads it as an orthonormal basis
of the Hilbert space `H¹₀(Ω)`. In (a) the two agree up to normalisation,
because the sines are `H¹`-orthogonal. In (b) and (c) they differ: the Hermite
functions are not `H¹`-orthogonal and, in their natural order, not a Schauder
basis of `H¹(ℝ)`. The informal solution applies Gram–Schmidt to them, and the
Lean statement does not state that step. See the header of `lean/Main.lean`.
