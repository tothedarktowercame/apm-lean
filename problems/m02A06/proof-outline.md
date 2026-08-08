# Proof Outline: m02A06

## Hop 4 gap audit

Outcomes A and B both failed. The nonlinear Green operator has now been made
explicit as

```lean
apm_m02a06_greenTransform ε f u x =
  exp (-x) + ∫ y in Ici 0, G x y * (f y + ε * u y ^ 2)
```

The boundary comment in `Main.lean` records the precise missing theorem
`apm_m02a06_greenTransform_fixedPoint`: existence and uniqueness of a fixed
point in the stated ball, together with the frozen ODE regularity, boundary,
and decay properties. Proving it requires the moving-domain Green identity
and the complete sup-norm contraction assembly; no packaged result was found.

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A06.md`

## Compiled progress

- Proved positivity of the ball radius `2 * (1 + C)`.
- Derived the strict contraction constant `4 * ε * (1 + C) < 1` from the
  frozen smallness hypothesis.
- Proved the quadratic Lipschitz estimate on the frozen ball.
- Defined the explicit half-line kernel
  `G(x,y) = (exp(-|x-y|) - exp(-(x+y)))/2`.
- Proved kernel symmetry, both zero-boundary identities, nonnegativity, and
  the pointwise upper bound `G ≤ 1/2` for nonnegative arguments.
- Proved the two explicit smooth formulas for the regions `y ≤ x` and
  `x ≤ y`, removing the absolute value before differentiation.
- Proved the sharper domination `G(x,y) ≤ exp(-|x-y|)/2`, matching
  Mathlib's available integrable exponential tails.

## Remaining bridge

Construct the moving-domain parameter integral from the two compiled kernel
branches, differentiate both pieces twice including their boundary terms, and
prove decay and the kernel-mass sup-norm estimate. The result must then be
bundled in a complete sup-norm function space before the compiled arithmetic
and nonlinear estimates can be fed to the contraction API. Mathlib supplies
the scalar exponential tail integrals but no theorem assembling this
half-line Green operator.
