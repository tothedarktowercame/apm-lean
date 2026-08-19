# Solved-lemma similarity channels

Population: 900 proved helper lemmas; validation set: 26 known duplicate pairs from 24 clusters.

## Gate: recovery of known duplicates

| Channel | Rule | Recall | Gate |
|---|---|---:|---|
| Constant set | Jaccard >= 0.72 | 22/26 (84.6%) | FAIL |
| Structural | exact fingerprint | 26/26 (100.0%) | PASS |
| MiniLM | cosine >= 0.88 | unavailable | NOT RUN |

The constant-set channel fails the required recovery gate and its novel results must not be trusted as primary findings. Four known pairs have empty or insufficient lexical external-declaration sets. The structural channel passes. MiniLM is explicitly secondary and could not run because the host has the cached model but no `sentence_transformers`, `transformers`, `torch`, or `numpy` runtime; no substitute text score was invented.

## Top structural novel candidates and hand audit

| Pair | Constant Jaccard | Audit | Reason |
|---|---:|---|---|
| `a96J10:apm_a96J10_q_analytic|a97A06:apm_a97A06_F_analytic` | 1.00 | not duplicate | same AnalyticOn shape, but q is exp's dslope while F is a different quotient function |
| `a96J02:continuous_convolution_indicator|a99J02:apm_continuous_convolution_indicator` | 1.00 | duplicate | same statement; top infinity notation differs |
| `a96J02:continuous_overlapMeasure|a99J02:apm_continuous_overlapMeasure` | 1.00 | duplicate | same statement after unfolding identical subtraction maps |
| `a96J02:continuous_overlapSet|a99J02:apm_continuous_overlapSet` | 1.00 | duplicate | same statement over identically defined overlapSet wrappers |
| `a96J02:continuous_subtractionMap|a99J02:apm_continuous_subtractionMap` | 1.00 | duplicate | local maps have identical definitions fun t => x - t |
| `a96J02:convolution_indicator_eq_overlapReal|a99J02:apm_convolution_eq_overlapReal` | 1.00 | duplicate | same equality after unfolding identical subtraction maps |
| `a96J02:translation_symmDiff_tendsto_zero|a99J02:apm_translation_symmDiff_tendsto_zero` | 1.00 | duplicate | same limit; nhds notation and local map names differ |

Hand-audited precision: 6/7 (85.7%). This is a purposive top-ranked sample, not an unbiased corpus estimate.

## Method

Constant sets reuse `statement-deps.py` identifier extraction and transitive traversal through problem-local definitions, then compare basename sets by Jaccard. The structural fingerprint records conclusion head, binder count, hypothesis count, and operator/constant multisets. MiniLM is out-of-domain natural-language evidence and is never primary.
