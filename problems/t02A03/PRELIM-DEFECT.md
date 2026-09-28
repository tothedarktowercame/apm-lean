# Prelim ambiguity and concrete reading

Part (b) says only that the boundary is a “standardly embedded genus two
surface” and that the removed curve goes around a hole “in the same way” as
the core circle in part (a). Those words determine the intended homeomorphism
type, but they do not specify a subset of `ℝ³` from which Lean can construct
`W` and `C` definitionally.

`Main.lean` therefore makes the nearest faithful concrete choice: `W` is the
closed radius-`1/4` regular-neighborhood model of an explicitly parametrized
planar figure-eight spine, and `C` is its explicitly parametrized left core
circle. The new theorem states the missing homotopy equivalences from the
actual complements to `T²` and `T² ∨ S¹`, followed by the requested
fundamental-group and homology computations. No retraction is assumed as a
hypothesis.
