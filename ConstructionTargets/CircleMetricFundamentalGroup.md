# Fundamental groups of concrete circle models

`CircleMetricFundamentalGroup.lean` transports the explicit winding-one class
from the canonical `Circle` through a homeomorphism, retaining its literal
basepoint. It specializes the construction to both circle encodings used by
the frozen corpus:

- `Metric.sphere (0 : ℂ) 1`;
- `{z : ℂ // ‖z‖ = 1}`.

The homeomorphisms send the distinguished point `⟨1, by simp⟩` to `1`.
Consequently the module provides an explicit nonidentity fundamental-group
class, its proof of inequality with `1`, and `Nontrivial` instances at the
exact basepoints required by `t91A05` and `t97J03`.

The proof uses the multiplicative winding equivalence from
`CircleUniversalCover`; no additive/opposite-group conversion is introduced.
