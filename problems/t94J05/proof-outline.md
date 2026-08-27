# Proof Outline: t94J05

The frozen theorem is encoded in `lean/Main.lean`. Two elementary topology
bridges are now compiled: a nonsurjective map factors through a missed point's
complement, and a null-homotopy of that factor descends to the sphere-valued
map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J05.md`

## Compiled progress

- Nonsurjective maps factor continuously through a missed-point complement.
- A complement-valued null-homotopy descends through subtype inclusion.
- `apm_t94J05_nullhomotopic_to_northPole` moves an arbitrary constant endpoint
  to the fixed north pole using path connectedness of `S³`.
- `apm_t94J05_contractibleSpace_complement` identifies the complement of any
  sphere point with its orthogonal complement via stereographic projection and
  transports the vector space's contractibility instance.
- `apm_t94J05_nullhomotopic_of_not_surjective` assembles factorization,
  contractibility, descent, and endpoint normalization to prove the full frozen
  conclusion for every nonsurjective map.
- `FixedTargetChartDimensionDropNullity` applies Euclidean
  `DifferentiableOn` image nullity to the literal source-chart image of every
  chart-pair patch and assembles those patches in a fixed target chart.
- For the concrete models, `simp` proves the strict finrank inequality
  `2 < 3`, while `hf.of_le` lowers the frozen `ContMDiff` hypothesis from
  order `⊤` to order `1`.
- `FixedChartNullForcesNonsurjectivity` contradicts positivity of the nonempty
  open north-pole chart target if the map were surjective. The existing
  nonsurjective-map theorem then supplies the frozen null-homotopy.

## Result

The frozen theorem is fully proved with no executable placeholders. The proof
uses an explicit add-Haar measure on the three-dimensional target model; it
does not introduce a measure on the sphere or assume nonsurjectivity.
