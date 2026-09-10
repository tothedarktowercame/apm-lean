# Intrinsic sphere-cap C1 graph-area comparison

This module completes the comparison between the reviewed C1 graph-density
integrals and both the ambient and intrinsic Hausdorff measures of the literal
strict Euclidean sphere caps.

`subtype_measure` applies Hausdorff-measure preservation to the actual subtype
coercion isometry. Its image of the subtype universe is the underlying ambient
set, giving equality between the intrinsic Hausdorff measure of the whole
subtype and the ambient Hausdorff measure of that set.

Rewriting this equality with the reviewed ambient upper and lower strict-cap
formulas gives the same reciprocal-height integral for both intrinsic cap
measures. Upper and lower examples compile in dimensions two and three, and
all three final audits use only standard axioms.

The equality runs from each graph-density integral through the constructed
coordinate-isometry image and ambient Hausdorff transport to the literal
Euclidean cap set and its intrinsic subtype Hausdorff measure.

The remaining route proves that the equator has zero `d`-dimensional
Hausdorff measure, assembles the two strict caps into the whole sphere,
determines the Euclidean Hausdorff-to-volume normalization, and evaluates the
coordinate moments required by the named consumers. This module contains no
equator, whole-sphere mass, numerical normalization, moment, Stokes, period,
or consumer-closure claim.
