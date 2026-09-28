# Refutation of `apm_m96a02`

The first frozen conjunct omits `[Nonempty M]`.  Instantiate it with `M :=
Empty` and its standard `MetricSpace` and `CompleteSpace` instances.  Its only
self-map is a contraction with constant zero, vacuously, but the demanded
`xstar : Empty` cannot exist.

`Refutation.lean` contains the exact frozen proposition and proves its
negation.  It compiles with the pinned project dependencies and uses no
placeholders.

There is also an independent endpoint defect in the ODE clause: the equation
is imposed only on `Ioo 0 1`, while uniqueness includes the unconstrained value
at `1`.  The empty-space counterexample already refutes the conjunction, so the
compiled proof uses only that simpler defect.
