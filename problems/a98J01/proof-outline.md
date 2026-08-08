# Proof Outline: a98J01

The canonical Lean attempt now avoids the long simple-function/Egorov proof.

- `apm_a98j01_polish_refinement` applies `Measurable.exists_continuous` to
  make the measurable function continuous in a finer Polish topology.
- `MeasureTheory.borel_eq_borel_of_le` proves that this refinement has the
  same Borel sets, allowing Lebesgue inner regularity to be reused.
- `apm_a98j01_homeomorph_of_compact_to_T2` localizes the compact-to-Hausdorff
  continuous-bijection theorem from solved sibling `t92J02`, using
  `Equiv.toHomeomorphOfContinuousClosed`.
- The main theorem installs the refined topology and its matching
  `BorelSpace` instance, then uses
  `MeasurableSet.exists_isCompact_diff_lt` to choose the large compact set.
- Compactness transfers to the ordinary topology through the continuous
  identity supplied by the topology inequality.
- On subtype `K`, the two induced topologies are kept explicit. The identity
  from the refined compact subtype to the ordinary Hausdorff subtype is a
  homeomorphism, so its continuous inverse transports the refined continuity
  of `f` to ordinary `ContinuousOn f K`.
