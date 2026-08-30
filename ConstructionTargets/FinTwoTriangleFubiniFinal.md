# Finite two-coordinate triangle Fubini calculation

This target discharges `EuclideanTriangleMeasureFubini.FinTwoTriangleFubini`.
It transports `volume` on `Fin 2 → ℝ` through Mathlib's volume-preserving
`finTwoArrow` equivalence, applies Bochner Fubini to the measurable triangular
indicator, and identifies its fibres with `0 ≤ y ≤ 1-x` for `0 ≤ x ≤ 1`.

The result instantiates `FrozenTriangleMeasureAdapter`; the already-proved
elementary iterated integral then gives
`frozenTriangleSetIntegral (fun _ => 2) = 1`.  No Stokes theorem, circle-period
statement, or frozen final theorem is used.
