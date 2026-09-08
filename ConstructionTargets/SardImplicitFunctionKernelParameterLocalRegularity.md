# Implicit-function kernel-parameter local regularity

This module upgrades base-point regularity of the exact fixed-left-coordinate inverse-chart kernel parameter to regularity throughout an open parameter neighborhood.

For a nonzero finite differentiability order, `ContDiffAt` at the right base coordinate is eventually stable. Extracting an open neighborhood from that filter statement gives both the retained `ContDiffAt` order and `DifferentiableAt` at every point of the neighborhood.

The downstream Sard induction must restrict the kernel target slice and corresponding source chart neighborhood compatibly, then apply lower-dimensional critical-image nullity and local aggregation.
