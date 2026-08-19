# Frozen-statement dependency map

This directory contains a reproducible descriptive map of the encoded APM
corpus and its recorded obstructions:

- `frozen-statement-dependencies.json` is the machine-readable artifact.
- `frozen-statement-dependencies.md` is its generated summary.
- This README explains the method, evidence coverage, and limits.

The map does not estimate implementation cost or predict which infrastructure
will close a problem. Reference demand, recorded obstruction demand, and cost are
different quantities. For example, `t01A07` had no statement-level machinery
classification and still took five commits to close. The two-open
simply-connected theorem took eight dispatches, seven commits, and two
no-commit stops across five distinct walls; its prior estimate of six to twelve
commits was consistent with the observed work. Costs must be measured from
completed work rather than inferred from dependency counts.

## Validation: description, not infrastructure prediction

The map was tested against the 27 problem bundles that actually import one or
more of the 20 `ConstructionTargets` modules. Their transitive imports provide
38 observed problem--module edges: a cumulative record of infrastructure used
in real formalizations. A predicted edge means that the statement layer names
a declaration owned by the imported module, or that a recorded obstruction
area maps to that module under the mapping frozen in commit `a1e99ab` before
scoring.

| Layer | Scorable problems | Observed edges | Predicted edges | Precision | Recall | Problems with any correct prediction |
|---|---:|---:|---:|---:|---:|---:|
| Frozen statement | 27 | 38 | 8 | 6/8 (75.0%) | 6/38 (15.8%) | 6/27 |
| Blocked consumer | 17 | 23 | 16 | 3/16 (18.8%) | 3/23 (13.0%) | 2/17 |

The frozen-statement result is a clean negative result. Statements are static,
yet the object layer recovered only 15.8% of realised infrastructure edges. It
describes what encoded theorems are about; it does not predict what must be
built to prove them.

The blocked-consumer score has a different interpretation. Obstruction records
describe the current wall, whereas imports accumulate every earlier wall
already passed. Scoring a moving frontier against a cumulative history is
structurally misaligned. The 13.0% recall therefore does not refute the blocked
layer as a forward signal, but neither does it validate it. It remains useful
as a description of what attempts reported being stopped by, and no claim that
it predicts future infrastructure is supported by present evidence.

Measured history is the only infrastructure-use signal validated here. The
adjacent `realized-construction-targets` artifacts report transitive consumers
and historical changed-line cost for all 20 modules. Imports establish realised
use, not causal necessity, and changed lines remain an imperfect cost unit, but
both are observations rather than forecasts.

Future structured obstruction records carry `date` and `at_commit`. Those
fields make it possible to reconstruct the imports and obstruction frontier at
the same historical point and run a temporally aligned validation. Most legacy
records lack that provenance, so the fairer test cannot be run retrospectively.
This is a concrete reason to keep recording structured obstructions beyond
bookkeeping.

## Evidence layers

The artifact keeps three kinds of evidence separate:

1. **Objects:** declarations reached from the frozen Lean theorem signature by
   following problem-local definitions. This is high-confidence evidence about
   what the encoded statement names, but not a proof that every reached
   declaration is missing or blocking.
2. **Techniques:** machinery mentioned in `informal-solution.md`. Proof methods
   such as Mayer--Vietoris or van Kampen often appear only here because
   statements name mathematical objects while proofs name techniques. This is
   weaker evidence and never contributes to object requirements.
3. **Blocked consumers:** current obstruction records from `status.json`.
   Structured records take precedence over legacy prose. These counts describe
   reported blockers; validation above does not establish them as a scheduling
   signal.

An obstruction's `areas_are` field is `necessary` when all named areas are
jointly required, `alternatives` when any one named area suffices, and
`ambiguous` when the record does not justify either interpretation. The current
scalar discriminator cannot express a mixed formula such as `A ∧ (B ∨ C)`.
No concrete record requiring that extension has yet been found; such a record
should remain `ambiguous` until the schema is extended.

## Coverage

Coverage must accompany every count:

- Corpus: 475 bundles.
- Encoded and classified frozen statements: 448/475; 27/475 are not encoded,
  and 0 encoded bundles remain unclassified.
- Any obstruction evidence: 266/475 bundles.
- Non-complete bundles with obstruction evidence: 197/319.
- Structured obstruction records: 136/266 obstruction-bearing bundles.
- Structured, non-complete obstruction records: 121/197
  obstruction-covered non-complete bundles, or 121/319 of all non-complete
  bundles.
- Explicit structured `areas: []`: 77 bundles. This is a positive finding that
  the recorded blocker names no tracked area, not missing data.
- Unmigrated legacy obstruction records: 130/266 obstruction-bearing bundles.

The leading blocked-consumer counts are singular homology 24/197,
fundamental group 15/197, and covering space 14/197. Their necessary-only and
inclusive counts are identical. The complete area table, including all
denominators and necessary/alternative bands, is in the generated Markdown.

## Why four sampling regimes were used

Legacy obstruction prose was migrated by reading, not by a more elaborate
keyword matcher. Four regimes tested different failure modes:

1. The original lexical pass established the 266/475 evidence ceiling but
   both missed synonyms and mistook negation for assertion.
2. The shortest-record tranche tested narrowly stated blockers. It yielded 26
   necessary, 0 alternative, and 4 ambiguous records.
3. The longest-record adversarial tranche targeted multi-route prose most
   likely to open the necessary/alternative band. It yielded 29 necessary, 1
   alternative, and 0 ambiguous records. The alternative record, `a03J05`,
   opened one-wide bands for complex analysis, Fourier analysis, and measure
   integration.
4. The stratified tranche sorted the remaining 170 records by preserved-prose
   length, split them into four equal-index strata, and selected ten from each
   with seed `20260819`. It yielded 19 necessary, 0 alternative, and 21
   ambiguous records. It changed no tracked-area count.

The leading three areas retained the same order and zero-width bands under all
four regimes. That establishes stability of the descriptive ranking, not its
ability to predict which infrastructure should be built. It also does not show
that their costs are equal, that every consumer needs the same lemma, or that
the unmigrated records contain no further consumers.

## Extrapolation and stopping rule

The 40-record stratified tranche is used as an equal-allocation estimator over
the four prose-length strata. Applied to the 130 unmigrated records, its point
estimates are:

| Outcome | Sample | Expected among remaining 130 |
|---|---:|---:|
| Ambiguous | 21/40 | 68.25 |
| Necessary/adjudicable | 19/40 | 61.75 |
| Alternatives | 0/40 | 0 |

No record in this sample added a blocked consumer to a tracked area. Therefore
the empirical point estimate is zero new consumers for each tracked area and no
change in ordering. This is an estimate, not a claim that the remainder is
empty. With zero observed additions in 40 trials, the approximate 95% rule-of-
three upper bound is 7.2% per pre-specified event, or about 9.4 of the remaining
130 records. This bound is not simultaneous across all areas and ignores
within-stratum dependence.

The extrapolation predicts that further migration will predominantly produce
roughly 68 ambiguous records and roughly 62 adjudicable records outside the
tracked taxonomy, while leaving the leading order unchanged. Its later
performance is checkable against the retained 130 records. That prediction,
rather than an unmeasured assertion of diminishing returns, is the reason to
stop migration now.

## Record-quality ceiling

The principal remaining limitation is the source data, not the extraction
method. Many ambiguous records contain only a numeric `closer_hop` or similarly
sparse historical metadata. No amount of lexical sophistication can recover a
missing explanation, and forcing such records into an area would replace an
explicit evidence gap with false precision. In this map, `ambiguous` therefore
often measures record sparsity rather than subtle Boolean structure.

The map describes the corpus and its recorded blockers. It cannot tell us why
undocumented work stopped, reliably infer proof obligations from a declaration
reference, predict which infrastructure will be used, or predict implementation
cost.

## Regeneration

From the repository root:

```sh
python3 scripts/migrate-ranked-obstructions.py
python3 scripts/extract-frozen-statement-map.py
git diff --check
```

The migration script is idempotent and preserves the reviewed tranche choices
explicitly. The extractor reads all problem bundles and rewrites both generated
artifacts. Review any resulting `status.json` diff before committing; the
migration script encodes human adjudications and is not a general-purpose
automatic classifier.
