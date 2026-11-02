# Prelim star map

`extract.py` compiles each registered proof with `DepDump.lean.txt` appended and writes the
Mathlib constants it reaches to `deps/<id>.tsv`, walking through this repository's own modules.
`deps/` is regenerable and not committed: run `python3 extract.py -j 6`, about 30 minutes.

`cluster.py` groups problems by rare shared constants (2 to 12% of proofs), weighted by inverse
document frequency, with Louvain communities on a top-8 neighbour graph.  It needs `networkx`.
Output: `clusters.json`.  This is a first pass at skills: subject-sized, not yet stars.
Clusters reflect how the Lean proofs were written, which can differ from how a person sees a
problem.  Prerequisite edges, the mark8 informal alignment and a learner layer are not built.
