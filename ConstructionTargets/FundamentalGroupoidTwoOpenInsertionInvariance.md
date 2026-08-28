# FundamentalGroupoidTwoOpenInsertionInvariance

This target continues the proof-carrying single-vertex insertion. It proves
the inserted tuple has the original endpoints through the canonical
`Fin.succAbove` old-index embedding.

The next step is monotonicity of `Fin.insertNth` at an arbitrary interior
position.  `Fin.monotone_iff_le_succ` reduces this to adjacent indices, so the
proof needs only the old adjacent inequalities before and after the insertion
and the two stored inequalities on either side of the inserted value.  The
remaining fields are segment membership, dependent `composeFin`
normalization, and evaluation invariance.  No such equality is assumed here.
