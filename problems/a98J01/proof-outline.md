# Proof Outline: a98J01

The canonical Lean attempt now avoids the long simple-function/Egorov proof.

- `apm_a98j01_polish_refinement` applies `Measurable.exists_continuous` to
  make the measurable function continuous in a finer Polish topology.
- `MeasureTheory.borel_eq_borel_of_le` proves that this refinement has the
  same Borel sets, allowing Lebesgue inner regularity to be reused.
- `apm_a98j01_homeomorph_of_compact_to_T2` localizes the compact-to-Hausdorff
  continuous-bijection theorem from solved sibling `t92J02`, using
  `Equiv.toHomeomorphOfContinuousClosed`.

## Follow-up Needed

- Choose a compact subset of `Icc a b` in the refined topology with complement
  of measure less than `ε`.
- Transport compactness to the ordinary topology via the continuous identity.
- Instantiate the compiled compact-to-Hausdorff helper for the two induced
  topologies on subtype `K`, then transport refined continuity of `f` back to
  ordinary `ContinuousOn f K`.
