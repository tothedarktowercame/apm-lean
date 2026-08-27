# Proof Outline: ftriangleSmoke

The hypotheses identify `a` with `3` and `b` with `4`. Rewriting by those
hypotheses reduces the frozen conclusion to the closed real-number computation
`3 ^ 2 + 4 ^ 2 = 25`, which Mathlib's `norm_num` tactic proves directly.

Closer hop 1 closes the only `sorry`. The theorem statement is unchanged, and
the proof introduces no definitions, axioms, or opaque constants.
