# Orthogonal equivariance of the actual radial pair comparison

`ConstructionTargets.CoefficientOrthogonalRadial` proves that the actual radial relative-homology comparison intertwines orthogonal disk actions in every natural-number dimension and homology degree, including zero.

The geometry is real: Q is a real linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`. Coefficients independently use any Type 0 commutative ring R and `ModuleCat.of R R`. No coefficient characteristic or nonemptiness restriction is imposed.

`closedAction`, `openAction` and `boundaryAction` apply Q to the actual closed-disk, open-disk and unit-sphere subtypes. Norm preservation proves boundary preservation; injectivity proves preservation of the punctured open disk. `radial_square` proves commutation with `halfDiskMap`, using real linearity. `boundary_square` proves compatibility with the actual closed-disk boundary homeomorphism.

`closedPair`, `openPair` and `radialPair` are the actual categorical cokernel maps from `CoefficientRadialPair`. Pair-map composition transports the geometric square to `relative_square`. `radial_naturality` says that the closed-pair homology action followed by `radialIso.hom` equals `radialIso.hom` followed by the open-pair homology action. `radial_inverse_naturality` gives the reverse intertwining equation with `radialIso.inv`. Both hold in every degree. `closed_projection` and `open_projection` identify each pair map after the actual cokernel projection in every chain degree.

`negation_one` identifies the one-dimensional negation action with the reviewed literal disk reflection. Integer and rational specializations and an explicit zero-dimensional rational example are included, retaining empty boundary and punctured subspaces.

The Lean source is promoted byte-for-byte from `/tmp/CoefficientOrthogonalRadial.lean`, SHA256 `31cf135ff217e502e6e51acb81d6ee20e5a69a093c768cbd6b83e53ed9fc0193`, including thirteen axiom audits.

The height-preserving ambient sphere action, hemisphere-coordinate and excision squares, and sphere-to-disk and sphere-shift equivariance remain downstream. This packet claims no signed sphere action or consumer closure.
