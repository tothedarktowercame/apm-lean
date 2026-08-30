# Frozen simplex-integral adapter

The pointwise frozen specifications for alpha and beta define linear maps from
the base point into the finite-dimensional spaces of continuous alternating
forms. This file bundles those maps and proves their differentiability.
Gamma is pointwise constant and is differentiable for that reason. The three
exterior-derivative conclusions are then obtained unconditionally from
`ExteriorDerivativeSimplexCalculus` as `frozen_extDerivs`.

The remaining local integration seam is explicit. The earlier leaf evaluates
the iterated-coordinate triangle integral, while the frozen statement uses a
Lebesgue set integral on `EuclideanSpace ℝ (Fin 2)`. The missing theorem is the
measure-preserving/Fubini identification
`FrozenTriangleMeasureAdapter`. Assuming exactly that equality gives
`frozen_triangle_integral_of_adapter`; no integral value or exterior derivative
is assumed inside the adapter.

No circle-period or non-differential statement appears here.
