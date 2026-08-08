# Proof Outline: t91A05

Regard the boundary inclusion and a hypothetical retraction as continuous
maps. Functoriality of `FundamentalGroupoid.map` shows that the induced map on
fundamental groups is injective; this step is compiled locally.

`apm_t91a05_no_retraction_of_subsingleton_fundamentalGroup` now packages the
entire contradiction from a subsingleton target fundamental group and a
nontrivial source fundamental group. Thus no group-theoretic assembly remains.

`apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial` specializes
this to the exact frozen metric disk and boundary. It bundles the subtype
inclusion, installs closed-ball contractibility and the resulting
simply-connected/fundamental-group subsingleton instances, and converts the
raw continuous retraction statement directly.

It remains only to prove that the fundamental group of the exact unit metric
circle is nontrivial. The standard identification with `Multiplicative ℤ`, or an
integral first-homology computation followed by functoriality, would finish.
Neither computation is currently packaged in Mathlib or a closed sibling.

Checked Lean state: exit 0; one `sorry` remains.
