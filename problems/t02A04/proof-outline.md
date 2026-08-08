# Proof Outline: t02A04

The space is encoded as the quotient of a solid torus and a disk by the
`(1,2)` attaching curve.  The compiled lemma
`apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve` verifies that every
boundary point of the disk is identified with its prescribed image.

Closer hop 2 packages this attachment as a continuous gluing cocone: the
canonical solid-torus and disk maps are continuous and their restrictions to
the attaching circle agree.

Closer hop 3 adds `apm_t02a04_gluedDesc`, its restriction equations, and
`apm_t02a04_gluedDesc_unique`, proving the quotient's full function-level
continuous pushout universal property.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A04.md`

## Remaining boundary

The standard argument retracts the solid torus to its circle factor, observes
that the attaching map has degree two, identifies the result up to homotopy
with `ℝP²`, computes its rational homology, and applies the Lefschetz
fixed-point theorem.  Mathlib currently has no packaged chain connecting this
explicit quotient to a cell attachment, no rational homology computation for
that attachment, and no topological Lefschetz fixed-point theorem.

Searches of Mathlib, `LEMMA-INDEX.md`, solved and partial sibling artifacts,
`ConstructionTargets/`, and git history found no reusable replacement.  The
statement is unchanged and appears mathematically non-trivial and sound.
