# Varying target-chart nullity assembly

This target transports null image patches from their varying extended target
charts into one explicitly chosen extended target chart.  It does not define
a measure on the manifold.

The analytic input is Mathlib's `contDiffOn_ext_coord_change`, restricted to
the actual overlap.  The remaining steps are monotonicity of null sets and a
countable-union decomposition.  The principal conclusion is
`fixed_extChartAt_null_of_countable_patch_decomposition`.

The exported layers are:

* `extChartCoordinateNull_inter_source`, transport from one varying extended
  chart into a fixed extended chart after restricting to their overlap;
* `fixed_extChartAt_null_of_countable_patch_decomposition`, assembly for a
  countable indexed union;
* `fixed_extChartAt_null_of_countable_centers`, the set-indexed form; and
* `fixed_extChartAt_null_of_chartPairPatch_range`, the direct consumer of the
  range equation produced by `CountableExtendedChartRangeDecomposition`.

Thus the remaining Sard input is local: prove each literal chart-pair image
patch null in its own target extended chart.  No measurability of the patches
and no measure on the manifold are introduced.
