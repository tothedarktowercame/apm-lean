# Projected-chart residual-slice zero derivative

`hasFDerivAt_zero_residual_comp_slice` packages the chain-rule step for a
residual target coordinate along a chart slice.

Given derivatives of the ambient map and slice parameterization, exact
vanishing of `Q.comp (D.comp J)` yields zero Frechet derivative for the
residualized slice. Rank-specific work is therefore confined to that linear
identity.
