# Exact linear graph Hausdorff distortion

For every natural dimension d and continuous real linear functional ell on EuclideanSpace ℝ (Fin d), this module evaluates the determinant factor of the reviewed LinearGraphMeasure construction. It retains the actual WithLp 2 ambient metric, explicit Borel structures, graph range and constructed orthonormal range isometry.

`inner_coordinate` transports inner products through that range isometry and the actual L2 graph, obtaining inner(x,y)+ell(x)*ell(y). With the Euclidean orthonormal basis, `gram_equation` identifies the Gram matrix with identity plus the outer product of the functional coefficients. `matrix_gram` identifies it with the transpose-product of the coordinate matrix. The rank-one determinant lemma and orthonormal-basis dual-norm identity give det(coordinateMap)^2 = 1+norm(ell)^2. Taking the nonnegative square root proves `distortion_eq`.

`image_measure` and `range_measure` substitute this value into the reviewed ambient and intrinsic Hausdorff equations. Their factor is ENNReal.ofReal(sqrt(1+norm(ell)^2)); both apply to every set, with no measurability, positive-dimension or nonzero-functional assumption. `zero_distortion` explicitly evaluates the zero-functional factor as one. Dimension-two and dimension-three examples are included.

Seventeen standard-only axiom audits cover ten new results and seven reviewed geometric and measure inputs. The source exactly matches fixture SHA256 729e0334f324ce77a9f5369547d7631c4c03362b5c4a8fa34b80aa28afc242ff. The Gram determinant and range identification are proved, not supplied.

Nonlinear differentiable graph area transport, sphere-chart measure assembly and Euclidean Hausdorff numerical normalization remain downstream. No sphere mass, Stokes, period or consumer-closure conclusion is claimed.
