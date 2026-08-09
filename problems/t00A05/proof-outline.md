# Proof Outline: t00A05

The closedness calculation and the unit-circle period are compiled in
`lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A05.md`

## Statement-review boundary

The frozen `apm_t00a05_IsC2` predicate does not state that the parametrization
is injective, an embedding, or has winding number one. Its positive signed-area
condition fixes orientation only. An orientation-preserving repeated traversal
retains the image equations and positivity but multiplies the angle-form
period. Consequently the universal `-2π` conclusion is false without a
single-traversal/degree-one hypothesis.

Concretely, let `γ₀` be the intended smooth counterclockwise parametrization
of the displayed level-set component and periodically extend it. Then
`γ₂(t) = γ₀(2*t mod 2π)` is closed and smooth, has exactly the same image, and
therefore satisfies both pointwise equations in `apm_t00a05_IsC2`. Its signed
area is twice the positive signed area of `γ₀`, so the frozen orientation
condition still holds. The line integral is likewise traversed twice and is
`-4π`, contradicting the asserted universal value `-2π`.

Hop 4 therefore adds no bridge declaration: any bridge strong enough to prove
the frozen final conjunct would be false. The main theorem remains untouched.
