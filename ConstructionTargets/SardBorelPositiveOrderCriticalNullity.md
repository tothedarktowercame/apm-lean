# Borel positive-order critical-nullity interface

`BorelPositiveOrderCriticalNullityAtDimension` is a separately named predicate
for admissible finite orders at least one. It quantifies over finite-dimensional
real normed spaces, Borel targets with additive Haar measures, arbitrary source
sets, and pointwise ambient regularity. Source and target universes are independent.

`borelPositiveOrderCriticalNullity_iff_highOrder` gives a logical equivalence
from this positive-order predicate to the same obligation restricted to orders
at least two. The forward implication restricts the order range. The reverse
implication splits positive orders into order one and orders at least two,
using the reviewed `orderOne_criticalImage_zero` in the former case.

`borelPositiveOrderCriticalNullity_zero` proves the zero-source-dimension
base case by restricting the reviewed `borelClassicalCriticalNullity_zero`.
These two reviewed theorems are the observed declaration dependencies.

This is not an equivalence with, replacement for, or proof of
`BorelClassicalCriticalNullityAtDimension`, which also quantifies over order
zero. That existing predicate and all its consumers remain unchanged. No
general positive-dimensional nullity theorem is proved here. Analytic results
using the broader induction hypothesis cannot simply be applied with this
restricted predicate: they need new proofs with explicit order-positivity
checks at each induction application.

The source matches `/tmp/SardBorelPositiveOrderCriticalNullityProbe.lean`,
SHA-256 `8f4624e74293eb3149555805ea7cbf530ae7f12b088a7e2efc51c6913f095329`.
Both theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Intended consumers are t93A04 and shared Sard foundations for t01A08, t01J04,
t92J07, and t96J05. No frozen consumer closes here. Higher-order analytic
induction must be adapted, complementary cases proved, and the resulting
theorem connected to the smooth frozen consumer. The ledger and frozen
consumer are unchanged.

The boundary would be failure of the positive-order split, either reviewed
order-one or zero-source theorem under its hypotheses, or a requirement for
nonstandard axioms.
