# Proof Outline: a96J07

## Problem and statement repair

For an entire `f`, evaluate the integral of
`f z / ((z-a)(z-b))` around the positively oriented circle of radius `R`,
then use that identity to prove Liouville's theorem.

The TeX condition `b < R` is ill-typed because `b : ℂ`. The informal solution
and symmetry between the poles establish the intended condition `‖b‖ < R`.
The formal statement also makes the necessary branch condition `a ≠ b`
explicit; the coincident-pole case is instead Cauchy's derivative formula.

## Contour evaluation

1. Apply Mathlib's circle Cauchy integral formula separately at `a` and `b`.
2. On the circle, neither denominator vanishes because both poles are strictly
   inside.
3. Use
   `1/((z-a)(z-b)) = (1/(a-b)) (1/(z-a) - 1/(z-b))` and circle-integral
   linearity.
4. Obtain
   `∮ f z / ((z-a)(z-b)) dz = 2πi (f a - f b)/(a-b)`.

The algebra and circle-integrability structure reuse the proven pattern from
`problems/a92J06/lean/Main.lean`.

## Liouville from the evaluated integral

Fix `a ≠ 0` and specialize the second pole to zero. On the radius-`R` circle,
the reverse triangle inequality gives
`R - ‖a‖ ≤ ‖z-a‖`, while `‖z‖ = R`. Thus the normalized ML estimate is

`‖(2πi)⁻¹ ∮ f z / ((z-a)z) dz‖ ≤ M / (R - ‖a‖)`.

The contour identity identifies the left side with
`‖(f a - f 0)/a‖`. Given `ε > 0`, choose
`R = ‖a‖ + (M/ε + 1)`; the right side is at most `ε`. Hence the quotient is
zero, so `f a = f 0`. The case `a = 0` is immediate. This proves constancy
without invoking Mathlib's packaged Liouville theorem.

## Lean formalization

- File: `lean/Main.lean`
- Main theorem: `ApmCanaries.A96J07.apm_a96J07`
- Status: complete (0 sorries)
- Validation: `lake env lean problems/a96J07/lean/Main.lean` exits 0

## References consulted

- Canonical TeX: `apm/a96J07.tex`
- Harvested informal proof: `informal-solution.md`
- Reused contour pattern: `problems/a92J06/lean/Main.lean`
- Compared packaged Liouville interface: `problems/a94J05/lean/Main.lean` and
  `Mathlib.Analysis.Complex.Liouville`
- Checked but not reused: the open-component construction in
  `problems/a96J04/lean/Main.lean`
