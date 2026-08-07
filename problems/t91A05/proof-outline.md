# Proof Outline: t91A05

Regard the boundary inclusion and a hypothetical retraction as continuous
maps. Functoriality of `FundamentalGroupoid.map` shows that the induced map on
fundamental groups is injective; this step is compiled locally.

Mathlib proves the closed disk contractible via
`Metric.contractibleSpace_closedBall`, hence its fundamental group is trivial.
It remains to prove that the fundamental group of the unit circle is
nontrivial. The standard identification with `Multiplicative ℤ`, or an
integral first-homology computation followed by functoriality, would finish.
Neither computation is currently packaged in Mathlib or a closed sibling.

Checked Lean state: exit 0; one `sorry` remains.
