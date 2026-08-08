# Proof Outline: t94A10

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94A10.md`

## Compiled progress

- `apm_t94a10_radial_sq_pos` proves the squared radius is positive away from
  the origin.
- `apm_t94a10_radial_sqrt_ne_zero` discharges the denominator's nonvanishing.
- `apm_t94a10_radial_denominator_pos` and
  `apm_t94a10_radial_denominator_ne_zero` strengthen this to the full cubed
  denominator used by the frozen formula.
- `apm_t94a10_radial_sq_eq_norm_sq` reuses Mathlib's
  `EuclideanSpace.real_norm_sq_eq` to identify the coordinate radial square
  with `‖x‖ ^ 2`.
- `apm_t94a10_radial_denominator_eq_one_of_norm_eq_one` consequently
  normalizes the solid-angle denominator to one on the unit sphere, preparing
  the still-missing period computation.
- `apm_t94a10_ambientExtension_apply_of_isOmega` rewrites the arbitrary
  ambient extension to the frozen solid-angle formula at punctured points.

## Remaining bridge

1. Prove `apm_t94A10_bridge_solidAngle_closed` using `extDeriv_apply` and the
   explicit quotient derivative.
2. Prove `apm_t94A10_bridge_solidAngle_not_exact`. Since Mathlib currently
   has no suitable surface-form integration type, this contract states the
   specialized `4π` sphere-period/Stokes obstruction directly in the file's
   genuine `IsOmega`/`IsExact` vocabulary. The same infrastructure gap is
   recorded by siblings `t01J06`, `t02A05`, and `t94J07`.
