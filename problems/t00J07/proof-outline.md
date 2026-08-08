# Proof Outline: t00J07

The Lean statement concretely models `RP²`, the closed disk, their attaching
quotient, its fundamental group, and integral singular homology.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J07.md`

## Formal progress

- `apm_t00j07_attach_glue` proves that the quotient identifies each boundary
  point of the disk with its prescribed image under the attaching map.
- `apm_t00j07_circleToDisk_injective` proves the concrete boundary inclusion
  is faithful, and `apm_t00j07_norm_circleToDisk` identifies its image as
  norm-one points.
- `apm_t00j07_diskCenter_ne_boundary` proves the chosen disk-center basepoint
  is disjoint from the attaching circle before quotienting.
- `apm_t00j07_center_eqvGen_iff` proves that the center remains a singleton
  equivalence class under the generated attaching relation.
- `apm_t00j07_basepoint_ne_left` therefore separates the quotient basepoint
  from every point in the attached `RP²` summand.

## Remaining boundary

The two missing computations are now stated explicitly as
`apm_t00J07_bridge_nullhomotopic_attachment_invariants` and
`apm_t00J07_bridge_essential_attachment_invariants`. They retain the embedding
hypothesis and compute the complete packaged fundamental-group and integral
singular-homology invariant for each attaching homotopy class. Proving these
contracts is exactly the remaining van Kampen/cellular-homology work; once
proved, the two implications in the frozen theorem follow immediately.
