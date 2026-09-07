# Constant-coordinate slice flatness

This module promotes two compiled chain-rule interfaces for transporting derivative flatness to coordinate slices.

When `p ∘ s` is constant, uniqueness of the Fréchet derivative shows that `P.comp J = 0`, so the derivative of the slice lies in the kernel of the coordinate derivative. If a residual derivative `H` vanishes on that kernel, the chain rule then gives zero derivative for the residual map restricted to the slice.

These abstract chain-rule lemmas consume the local residual-flatness result through their `hflat` premise when specialized by the next consumer; they do not duplicate its rank argument.

The next consumer step is to specialize the slice to the inverse local rank chart at fixed derivative-range coordinate, use the chart's exact first-coordinate formula and local residual derivative flatness, then apply Taylor-cover nullity and assemble the rank/source-dimension induction.
