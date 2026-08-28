# Evaluation across one homotopy-grid strip

The normalized endpoint equations are converted into one-sided prefix and
suffix equations matching the three factors in
`TwoOpenDescentDatum.evaluate`.  Combining those equations with the finite
strip ladder gives `bottom_evaluate_eq_top`: the bottom and top row
subdivisions of one fixed time strip have equal evaluations.

This target does not iterate across all time strips and does not claim general
path-homotopy invariance.  The next step is finite telescoping in the time-grid
index, followed by the already proved independence of the subordinate
subdivision chosen for each endpoint path.
