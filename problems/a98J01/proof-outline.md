# Proof Outline: a98J01

The canonical Lean attempt now avoids the long simple-function/Egorov proof.

- `apm_a98j01_polish_refinement` applies `Measurable.exists_continuous` to
  make the measurable function continuous in a finer Polish topology.
- `MeasureTheory.borel_eq_borel_of_le` proves that this refinement has the
  same Borel sets, allowing Lebesgue inner regularity to be reused.

## Follow-up Needed

- Choose a compact subset of `Icc a b` in the refined topology with complement
  of measure less than `ε`.
- Transport compactness to the ordinary topology via the continuous identity.
- Use compact-to-Hausdorff homeomorphism machinery on the subtype to transport
  refined continuity of `f` back to ordinary `ContinuousOn f K`.
