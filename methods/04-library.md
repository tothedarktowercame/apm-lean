# 4. Library work

Some leaves are too big for a seat, and some facts are needed by several
problems. Both are library work. The library is `ConstructionTargets/`: 1118
Lean files, about 266,000 lines as of 2026-11-05. 136 problems import it.
It is a `lean_lib` in `lakefile.toml`, so its modules build to oleans and can be
imported. Until 2026-07-30 it was not one. Every proof in it was
unreachable from the problems it had been written for, and nothing reported an
error until a problem tried to `import` one.

## When a leaf becomes library work

A blueprint author marks a leaf **LIBRARY** when either of these holds:

- its estimate is over about 200 lines and it cannot be split further at the
  problem level, because the missing piece is a general theory (manifold Sard,
  singular homology of a quotient, classification of surfaces);
- another open problem needs the same fact.

The author must say what foundation is missing. Hiding it inside a leaf of
ordinary size only moves the failure to a seat.

## Choosing what to build: the foundation ranking

Library work goes to whatever closes the most problems. After each batch of
blueprints, the LIBRARY leaves are grouped by the foundation they need, and
each foundation is scored by the number of problems whose **only** remaining
gaps it would close (alone, or together with foundations ranked above it).
The 2026-10-13 ranking put the following foundations at the top:

- Sard's theorem on manifolds, which four problems needed;
- the rational homology of RPⁿ and CPⁿ with Lefschetz traces;
- cell-attachment homology with van Kampen.

The rule behind this (from `docs/TN-topology-foundational-programs.md`): a
library program builds only what open problems need, builds each shared step
once, and the first consumers of a new piece are model cases (a sphere, a
Euclidean pair) before the problem that motivated it. Every milestone has to
compile and have a consumer. No milestone may assume its final consumer's theorem.

## Splitting a library result

A library family is split the same way as a problem blueprint. It gets the same
statement-first procedure, the same C1-C10 checks, and the same compile gate.
The packet is [`tools/library-split-preamble.md`](tools/library-split-preamble.md).
The differences:

- The family's sketch is `ConstructionTargets/Module.blueprint.md` (42 such
  files), beside `Module.lean`. It names the consuming problems.
- The leaves are dispatched as `P = CT.Module`. The seat file is a copy of
  `ConstructionTargets/Module.lean` with the leaf in a seat area. The tooling
  (`lemmatool.py`, `next.sh`) handles both cases.
- When a module changes, `merge_lemmas.sh` builds it and recompiles every
  `Main.lean` that changed, because a module's change can break problems that
  import it.

The first library split (a97J08, 2026-10-13) turned one 300-600-line boundary
lemma into about fifteen leaves of 30-150 lines. All of them were proved within
hours.

## Module or inline

A finished library result is published in one of two ways:

- **As a module** in `ConstructionTargets/`, when other problems import it or
  may do so. This is the default.
- **Inlined** into the problem's `Blueprint.lean`, when only that problem uses
  it and the pieces were proved as separate lemma files. `t00J02` was closed this
  way. Its side-sign, circle-degree and transport lemmas were merged into the
  blueprint, and the problem then imports only modules that already existed.
  The result is one large file, but no module build and no new import edge on
  the landing path.

## Hazards specific to the library

- `ConstructionTargets` modules can contain `sorry`: 17 files did at the
  time of writing, as open library leaves. A problem that imports such a
  module and uses one of its open lemmas shows `sorryAx` in its axioms and
  stays open, even when its own file has no `sorry`. Counting `sorry` in
  `Main.lean` is therefore not enough. The landing script's `#print axioms`
  check is what catches this.
- Do not import `SphereCap*` or `LinearGraphMeasure`. They install a second
  `MeasurableSpace` instance on `EuclideanSpace`, and Mathlib's measure results
  then fail to apply.
- Before writing a leaf, search the library for a sorry-free result that
  already says it. One leaf asked for the manifold Sard theorem that the library
  had already proved (`T93A04ManifoldWork.null_critical`).
