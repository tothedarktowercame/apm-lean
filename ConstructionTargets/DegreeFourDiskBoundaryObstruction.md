# Degree-four disk boundary obstruction

This target proves the disk-extension half of the obstruction without assuming
a degree or no-zero theorem. A zero-free continuous complex-valued map on the
closed unit disk normalizes to a circle-valued map, and radial contraction of
the disk gives a literal homotopy from its normalized boundary loop to a
constant. Consequently, if that normalized boundary is `z ↦ z^4`, the
fourth-power circle map is null-homotopic.

The first missing shared theorem is now precise:

`degreeFour` is not homotopic to any constant circle map.

The compiled covering-space files provide path lifts and invariance of endpoint
winding under a free loop homotopy, but the repository has only completed the
concrete power-map generator calculation for degree five. It has no compiled
endpoint-winding calculation for the fourth-power loop. This target therefore
does not assert degree, non-nullhomotopy, an interior zero, or the frozen final
theorem.
