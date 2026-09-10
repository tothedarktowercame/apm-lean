# Codiagonal kernel normalization over R

Promoted unchanged from `/tmp/CoefficientCodiagonalKernel.lean`, SHA256 `1a17d9517ba4d962caf3a5ccd1d9031165d1e4d78cdc69592c678f1a69773d1a`.

R is a Type 0 commutative ring, with no domain, nontriviality or field assumption. `sumMap` is the actual ModuleCat R map from Bool → R to R adding the false and true coordinates. `signedMap` sends r to the function with false coordinate r and true coordinate -r. Their composite is zero.

`kerEquiv` explicitly identifies the linear-map kernel with R. `kernelIso` transports this through `ModuleCat.kernelIsoKer` to the actual categorical kernel. Its forward map is kernel inclusion followed by evaluation at false. Its inverse followed by kernel inclusion is exactly `signedMap`; `inverse_false` and `inverse_true` record the two coordinate equations. Both inverse laws are proved.

The convention is false-coordinate-positive and true-coordinate-negative. The integer example checks coefficient 1 at false; the rational example checks coefficient 1/2 at true, yielding -1/2. Ten standard-only axiom audits are included.

The imported sphere-shift dependency was reviewed at commit `0a94275eecb3e7a059de4816cb4a8b06c8d7e339`, PASS `invoke-1789014962618-17854-ab60e27b`. This module banks only categorical codiagonal kernel normalization.

The geometric identification of the one-dimensional disk-boundary H0 inclusion with this codiagonal remains downstream, as do the two-dimensional boundary inclusion kernel and circle H1 and S2 H1/H2 calculations. No geometric H0-map identification, general signed naturality, sphere endpoint calculation or frozen closure is claimed. No consumer placeholders change.
