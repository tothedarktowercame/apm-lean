# HomotopySquareTimeTelescope

This target telescopes the already compiled fixed-strip equality across the
finite time grid. `adjacent_strip_evaluate_compatible` uses arbitrary
subdivision evaluation independence on the common horizontal row; it does not
identify the two label certificates definitionally.

`first_bottom_evaluate_eq_bottom` performs the finite induction, alternating
`bottom_evaluate_eq_top` with the adjacent-row compatibility theorem.
`chosen_endpoint_evaluations_eq` then identifies the first bottom evaluation
with the final top evaluation. `firstStrip_rowPath` and `lastStrip_rowPath`
separately verify that these chosen subdivisions lie over the original paths
`p` and `q`, using the grid endpoint coordinates and the relative homotopy
equations.

This packet stops before arbitrary endpoint subdivisions and before descending
the equality through the path-homotopy quotient.
