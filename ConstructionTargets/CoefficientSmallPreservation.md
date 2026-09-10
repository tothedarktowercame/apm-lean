# Coefficient-general preservation of small chains

This module constructs restrictions of the reviewed subdivision and prism
on the actual `CoefficientSmallPath.coverSmallChains`, with its actual
inclusion into singular chains. The commutative ring R, topological space X
and family index type are universe zero. Chains use `ModuleCat.of R R`.
The indexed subset family U need not be open or cover X; no nonemptiness
or connectedness is assumed.

`subdivision_lift` and `prism_lift` use finite support geometry, the
factorization from `CoefficientFiniteRealization`, and operator identification
from `CoefficientFiniteOperators`. Coproduct descent constructs
`subdivisionDegree` and `prismDegree`. Their inclusion equations identify
these restrictions with the reviewed absolute operators, rather than
assuming preservation.

Degreewise monomorphisms from `CoefficientSmallH0` allow cancellation of
the inclusion to prove differential compatibility and assemble `subdivision`
as a chain map. The same inclusion equations transfer the prism identity
with sign `dT + Td = subdivision - identity`. The zero-degree equation is
exported separately. `smallHomotopy` is an actual homotopy from restricted
subdivision to identity, and `homotopy_inclusion` proves compatibility of
its adjacent-degree components with the reviewed absolute homotopy.

Integer and rational interval-cover homotopies and inclusion equations are
included, along with ten printed axiom audits. The Lean file is an exact
promotion of `/tmp/CoefficientSmallPreservation.lean`, SHA256
`34e1ff8e04ab92a58bd10885eda306555232290e02657d2d222608bb9225b08f`.

Eventual smallness of iterated subdivision, positive-degree small-chain
comparison, relative excision and sphere suspension remain before rational
S2 H1/H2. This packet claims none of those results or frozen consumer closure.
