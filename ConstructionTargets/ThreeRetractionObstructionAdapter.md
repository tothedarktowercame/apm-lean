# Three retraction obstruction adapter

This target packages the three independent arguments used by frozen `t01A03`:

- the middle-circle inclusion cannot be a retract when its induced integral
  `H₁` map is zero, because the compiled `circleSingularH1Generator` is nonzero;
- a retract inclusion must be injective on fundamental groups, contradicting
  the frozen wedge hypothesis;
- a connected ambient space cannot retract onto a disjoint union of two
  nonempty circles.

`three_retraction_obstructions_categorical` combines exactly those hypotheses
and accepts the middle-circle zero map as the same categorical `ModuleCat`
morphism equality used by frozen `apm_t01a03_H1map`. It does not assume an
obstruction conclusion, a zero map beyond the frozen middle-circle hypothesis,
or any additional wedge presentation fact.

The target depends only on the canonical `CircleSingularHomology` target. The
experimental version imported a Klein-bottle target solely to reuse a generic
functorial injectivity lemma; that lemma is proved locally here, avoiding an
unrelated t95J02 dependency.
