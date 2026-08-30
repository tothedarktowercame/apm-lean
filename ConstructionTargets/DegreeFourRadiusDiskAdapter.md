# Degree-four radius-disk adapter

This target instantiates the unit-disk winding obstruction in the coordinates
used by frozen `t94J06`.

It sends a unit-disk point `w` to `r w`, restricts a radius-`r` boundary
cylinder along `z ↦ r z`, and normalizes its nonzero complex values to
`Circle`.  Positivity of `r` proves directly that the normalized initial
endpoint `(r z)^4` is exactly `z^4`; the terminal endpoint is the normalized
boundary of the rescaled disk map.

`exists_zero_in_closedBall_of_degreeFour_boundaryHomotopy` therefore accepts
the same continuous map, positive radius, nonzero cylinder, and two endpoint
equations as the frozen bridge and returns a zero in the original closed disk.
No degree predicate or additional topological premise is introduced.
