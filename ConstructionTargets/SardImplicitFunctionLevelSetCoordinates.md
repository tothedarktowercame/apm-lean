# Implicit-function level-set coordinates

This module records the exact level-set identity supplied by Mathlib's
`ImplicitFunctionData` chart.

Equality of `leftFun` to a value is precisely equality of the first chart
coordinate to that value. The second theorem retains this description after
intersecting with the source of `toOpenPartialHomeomorph`, which is the form
needed to transport a localized hypersurface into kernel coordinates.

The scalarized-jet chart must next expose its underlying
`ImplicitFunctionData`; transporting each localized nonzero-jet stratum to the
strictly lower-dimensional kernel and applying source induction remain
downstream.
