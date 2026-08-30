# Circle exponential path lift

`Circle.isCoveringMap_exp` is already available in Mathlib.  This target uses
its generic `IsCoveringMap.liftPath` construction rather than postulating a
lift or a winding number.

For a continuous path `gamma : C(I, Circle)`, a real number `a`, and the
endpoint equation `gamma 0 = Circle.exp a`, it provides:

- `lift`, the canonical continuous real lift;
- `lift_zero`, its prescribed initial value;
- `exp_lift` and `exp_lift_one`, the pointwise and endpoint projection
  equations;
- `exp_lift_one_eq_start` for a closed path; and
- `existsUnique_endpointWinding`, which feeds that endpoint equality into
  `CircleWindingUniqueness.exp_eq_iff_existsUnique_endpointWinding`.

Thus the continuous lifting and the integral endpoint arithmetic are now
connected without assuming winding existence or degree classification.  This
does not yet discharge frozen `t97J08`: its normalized loop is parameterized
on all of `ℝ`, and its bridge asks for a periodic homotopy to
`Circle.exp (n * t)`.  The remaining producer must convert that periodic
real-line datum to a unit-interval circle path and then construct the required
homotopy/classification; the endpoint lift supplied here is one input to that
argument, not the argument itself.
