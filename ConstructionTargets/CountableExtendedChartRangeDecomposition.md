# Countable extended-chart range decomposition

For a continuous map between manifolds with a second-countable source, this
target defines the patch

`(extChartAt I x).source ∩ f ⁻¹' (extChartAt J (f x)).source`.

It proves that each patch is a neighborhood of its center, selects a countable
set of centers whose patches cover the source, and proves the literal equality
between the full range and the union of the corresponding image pieces.  It
also records the exact source/target coordinate equation on each patch.

This closes only the source-cover and set-decomposition layer.  The selected
target chart varies with the center.  Applying
`ChartCoordinateDimensionDropNullity` patchwise would additionally require a
whole-space differentiable extension of each local coordinate representative,
or a differentiable-on variant of the Euclidean dimension-drop theorem.
Combining the resulting null statements would then require either a single
target chart containing all pieces or proved coordinate-change transport into
one common additive-Haar measure.  No such target-chart atlas or measure
comparison is asserted here, so this file proves no global range nullity,
nonsurjectivity, or manifold Sard theorem.
