# t96J05: local radial-level specification defect

The frozen consumer is locally refuted, not closed. No specification repair
is selected here and this record does not terminate the topology campaign.

## Reviewed evidence

- Author: codex-12, row `t96j05-frozen-nonempty-radial-level-closure-probe-refill30`.
- Independent PASS: codex-10, `invoke-1788996921425-17341-4294c07a`.
- Preservation checkpoint PASS: `invoke-1788998095915-17369-ba4af7bc`.
- Exact fixture: [Counterexample.lean](Counterexample.lean), copied unchanged
  from `/tmp/T96J05Counterexample.lean`; SHA-256
  `5b874708cbb48d5809086f47de315a08d98c5d89e55f66d3f40582dedd47bcf8`.
- Frozen `problems/t96J05/lean/Main.lean` SHA-256:
  `3d0fa97de254e35aec83f46ae213d8c066c78281a7f102230377d3927c811a48`.
  It is unchanged, with one executable placeholder before and after.
- The fixture preserves the frozen definition prefix, including its exact
  smooth-order expression. It has zero placeholders. Compilation audits
  `T96J05Counterexample.counterexample` using only `propext`,
  `Classical.choice` and `Quot.sound`, without warnings.

## Exact obstruction

Take the centered unit circle in real Euclidean dimension two, with manifold
dimension one. It is nonempty, connected and satisfies the literal frozen
embedded-smooth-submanifold predicate. Every point has norm one. Thus every
inhabited radial level has radius one and is homeomorphic to the entire circle.
The requested dimension-zero ChartedSpace would make that level discrete,
hence make the circle discrete. Connectedness would then identify its two
distinct explicitly constructed antipodal points, a contradiction.

Sard nullity cannot guarantee an attained regular radius: all other radii in
this example have empty fibers. The frozen positive inhabited-level helper
does not supply regularity. Its historical missing-infrastructure comments
are retained in Main, but are not the current mathematical diagnosis.

## Decision still required

A corrected statement requires an explicit specification decision about
hypotheses ensuring attained regular levels or permitting empty levels.
Neither alternative is silently adopted or proved by this preservation row.
The banked Euclidean regular-fiber atlas, smooth inclusion and tangent-image
geometry remain valid under their own regular-value hypotheses and do not
repair this false attained-level conclusion. Manifold-source/global atlas
transport and the other consumers' obligations remain separate.

This is evidence preservation, neither another consumer closure nor a repair.
All older local counterexamples and uncovered cases remain, including the
t94J08 S0 refutation and reduced-S0/one-dimensional local-index obligations.
