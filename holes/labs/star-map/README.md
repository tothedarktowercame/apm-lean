# Prelim star map

`extract.py` compiles each registered proof with `DepDump.lean.txt` appended and writes the
Mathlib constants it reaches to `deps/<id>.tsv`, walking through this repository's own modules.
`deps/` is regenerable and not committed: run `python3 extract.py -j 6`, about 30 minutes.

`cluster.py` groups problems by rare shared constants into 14 subject-sized communities.  It is
kept as a coarse view.  Clusters reflect how the Lean proofs were written, and they merge unrelated
ideas, so they are not the skill layer.

## Skills

`concepts.tsv` lists 112 named skills in 13 areas, each with a regex for prose and, where one
exists, a regex for Lean constants.  `build.py` ties them to problems and writes `star-map.json`
and `STAR-MAP.md`.  It needs `scipy`.  Tiers:

| tier | meaning | tags | blind sample: really used |
|---|---|---|---|
| both | informal side names it, Lean proof reaches a matching constant | 752 | 22 of 25 |
| named | no Lean match, but 3+ mentions, or a mention plus a mark8 warrant or the statement | 744 | 18 of 25 |
| passing | any other mention | 771 | not sampled alone; all mentions without Lean: 12 of 25 |
| lean | Lean constant only, no informal mention | 1016 | 6 of 25 |
| untagged | control: skills from the problem's own area with no tag | | 1 of 25 |

`both` and `named` are the study tags.  470 of 484 problems carry at least one, 271 at least three.
The Lean tier mostly records how a proof was formalised, such as a manifold proof passing through
Hilbert space lemmas, so it is not a study tag.

The reader saw problem and solution only, without tiers (`sample-*.tsv`).  `named` was defined
after the first sample showed the informal tier was mixed, then tested on fresh rows
(`sample2-*.tsv`).  Samples of 25 give wide error bars, and three word-match faults the second
sample exposed (Jensen's formula, Sturm-Liouville, "fixed point") were fixed after it, so the
figures describe the map just before those fixes.  Skills are written by hand, so a topic missing
from `concepts.tsv` cannot appear; the first sample's control suggests few rows are missed per
area, but 1 of 25 over 11,486 control rows is a weak estimate.

mark8 alignment: 2,454 steps were judged on 347 problems and 636 were matched to a Lean
declaration, of which 340 have a judge reason that rejects the match.  So 296 links are credible,
and `build.py` uses only those for Lean links.  Warrant text from all steps feeds the prose side.

Prerequisite edges and a learner layer are not built.
