# First-nonzero-jet kernel-parameter containment

This module turns the lower-order vanishing carried by a first-nonzero-jet locus into the exact set containment required by the implicit-function source-dimension reduction.

For positive `i`, the first-nonzero `(i+1)`-jet locus lies in the zero level of every scalarized fixed-direction `i`-jet. If an `ImplicitFunctionData` left coordinate is that scalarized jet and its base point lies in the locus, the locus restricted to the chart source is contained in the image of the fixed-left-coordinate inverse-chart kernel parameterization.

Instantiating this containment with the compiled scalarized-jet data, applying lower-dimensional critical-image nullity, and treating the separate first-derivative rank-normal-form case remain downstream.
