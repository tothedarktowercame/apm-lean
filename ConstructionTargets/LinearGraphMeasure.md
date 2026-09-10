# Linear graph range and Hausdorff determinant comparison

For every natural dimension d and real continuous linear functional ell on EuclideanSpace ℝ (Fin d), this module constructs the actual graph map into WithLp 2 (E d × ℝ). Its underlying value is (x, ell x). Explicit Borel structures are used on the domain and ambient space, with the induced structure on the range.

Projection to the first coordinate proves graph injectivity and hence range dimension d. `rangeIsometry` is constructed from the standard orthonormal basis of that range, reindexed by the proved dimension equality. `rangeMap` restricts the actual graph map to its range; `coordinateMap` follows it with the constructed linear isometry to E d.

`distortion` is the absolute determinant of coordinateMap. Its positivity follows from coordinate injectivity and the determinant kernel criterion. `range_measure` transports intrinsic range Hausdorff measure through the actual isometry, then applies same-dimensional Haar distortion. `image_measure` uses the isometric subtype inclusion to identify the ambient graph image measure with the intrinsic one. Both equations hold for every set, without a measurability assumption, with factor ENNReal.ofReal(distortion).

Dimension-two and dimension-three examples and ten standard-only axiom audits are included. The source exactly matches fixture SHA256 9f9be05c41ec8cc25a059a8cfe4b9b2b51843cc62b0fd720b0019251aa3cf15e.

The determinant factor remains unevaluated. The zero functional is allowed without a separate hypothesis, but its factor is not explicitly computed. Identifying the factor with sqrt(1+norm(ell)^2), nonlinear area transport, numerical sphere normalization and consumer closure remain downstream. No numerical Hausdorff-to-volume normalization or graph-density value is assumed.
