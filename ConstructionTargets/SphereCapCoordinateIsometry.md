# L2-to-Euclidean coordinate isometry

This module constructs an explicit linear isometric equivalence from
`WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)` to
`EuclideanSpace ℝ (Fin (d+1))`.

The forward map appends the scalar height as the last Euclidean coordinate.
Its inverse recovers the first `d` coordinates with `Fin.castSucc` and the
height with `Fin.last d`. The construction proves linearity and both inverse
laws directly from these coordinate formulas.

Norm preservation follows by splitting the Euclidean coordinate sum with
`Fin.sum_univ_castSucc` and identifying it with the two L2 norm-square
formulas. The resulting `coordinateIsometry` therefore satisfies
`coordinateIsometry d z i.castSucc = z.fst i` and
`coordinateIsometry d z (Fin.last d) = z.snd`. Dimension-two and
dimension-three instances compile, and all five requested audits use only
standard axioms.

The identification runs exactly from the native L2 graph representation to the
appended-coordinate Euclidean representation, with the displayed inverse.
The remaining work proves the images of the native upper and lower caps are
the literal Euclidean strict caps and transports the subtype and ambient
Hausdorff measures. This module contains no cap-image, measure transport,
normalization, equator, moment, or consumer-closure claim.
