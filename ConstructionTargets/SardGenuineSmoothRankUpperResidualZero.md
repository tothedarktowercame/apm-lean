# Actual smooth rank-upper residual derivative — 2026-09-09

GO: `/tmp/SardGenuineSmoothRankUpperResidualZero.lean` compiles with no
warnings, no placeholders and only propext, Classical.choice, Quot.sound.

The theorem constructs its chart by invoking
SardGenuineSmoothProjectedRankChart.exists_genuine_smooth_projected_rank_chart.
Its only initial mathematical premise is global genuine-infinity smoothness.
The output retains basepoint membership, the exact first-coordinate identity,
forward and inverse smoothness, and actual complementary residual-slice
regularity. At any target point (r,z), a rank bound at y=e.symm(r,z) implies
that the actual residual map has zero derivative at z.

The proof derives the range projection's derivative surjectivity from the
smooth chart and its inverse, via the existing first-coordinate theorem.
Fixed-first-coordinate inverse-slice constancy supplies the zero projected
slice derivative. The existing rank-upper annihilation lemma then annihilates
the complementary derivative, and the residual composition lemma produces
HasFDerivAt with zero. No annihilation, chart or inverse regularity is assumed.
C1 smoothness consequences are used solely by derivative lemmas; there is no
C1 induction premise and no nullity premise.

This produces derivative-zero data on the actual rank-upper slice subset.
Local-domain nullity induction, dimension and base cases, rank-stratum image
assembly and manifold transport remain. The frozen t93A04 consumer stays at
one placeholder. Neither unconditional Sard nor consumer closure is claimed.

Promote only ConstructionTargets/SardGenuineSmoothRankUpperResidualZero.lean
and its matching .md note. Verify fixture and source hashes; compile fixture
and promoted module separately; run lake build on the new module; check the
statement hash, standard axioms, zero executable placeholders, unchanged
consumer and git diff --check. Commit only these two files. No DAG or ledger
edits and no alteration of the existing producers.
