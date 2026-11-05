# 1. Statements and the registry

A formal proof is only as good as its statement. A Lean theorem can compile
with no `sorry` and still fail to answer the problem: it may prove a special
case, or assume what it was meant to prove, or have hypotheses that can never
hold. This step makes the statement fixed and checked before any proof
counts.

## Encoding

`problems/P/problem.md` is the authority: the problem as set on the exam.
The Lean statement in `problems/P/lean/Main.lean` is the theorem `apm_P`
(sometimes several theorems, one per part), plus whatever definitions it needs,
in the same file.

Encoding choices that came up often:

- Multi-part problems ("compute X; show Y") become one theorem per part, or one
  conjunction. A "compute" part states the answer.
- "Describe" or "draw" parts are encoded as the mathematical fact the
  description has to get right (for example, a homotopy equivalence to a named
  model space).
- `(⊤ : WithTop ℕ∞)` in Mathlib's smoothness classes means analytic, not
  C^∞. Natural-number subtraction, `x / 0 = 0` and `Real.sqrt` of a negative
  number change a statement's meaning without any error.
- `EuclideanSpace` has a pointwise order. A bare `<` on it is not the order
  you may have meant.

## Grading

An outside grader reads `problem.md` and the statement, and grades it. The
grader is an agent that did not write the statement and may not edit
anything. The prompt is in
[`holes/labs/statement-registry/grade-prompt.md`](../holes/labs/statement-registry/grade-prompt.md):

- **faithful**: states what the problem asks (reasonable encoding choices are fine);
- **stronger**: states more;
- **narrower**: a special case, or an extra hypothesis (the grader must say which);
- **hypothesis-carries-core**: a hypothesis supplies the main content;
- **vacuous**: the conclusion is trivial or the hypotheses cannot hold.

Faithful and stronger statements are admitted. A narrower statement is
admitted only where the problem text itself is defective: false as printed,
or ambiguous in a way that forces a choice. The defect is written up in the
problem directory and named in the registry entry (`prelim_defect`). Anything
else goes back for a statement repair, which is graded again.
The grades and their evidence are in `holes/labs/statement-registry/`.

## The fingerprint

`scripts/statement-registry.py` computes a fingerprint for each registered
theorem. It takes the text from `theorem NAME` up to the first `:=` at bracket
depth 0, plus every definition in the same file that the statement uses,
directly or through other definitions. It strips comments, normalises
whitespace, and takes the sha256. Following definitions matters. In one
problem the theorem header stayed byte-identical while a definition it used
changed.

    python3 scripts/statement-registry.py check P     # does Main.lean still match?
    python3 scripts/statement-registry.py status P    # registered | mismatch | unregistered

The registry refuses a statement that reaches an `axiom`, an `opaque`, or a
`sorry` inside a definition. A registered entry that later turns out to be
wrong is revoked with a reason, and the revocation is kept (`revoked` in
`STATEMENTS.json`; 19 so far).

## Repairs

When a blueprint author finds the registered statement false, or finds that
it does not say what `problem.md` says, they write `RevisedMain.lean`. It
contains the smallest change the problem text justifies, and the
counterexample goes in `BLUEPRINT.md`. The revision is graded like any other
statement. Making a statement narrower so that it is easier to prove is never
a repair. Narrower results that were proved anyway are kept in
`holes/labs/out-of-competition/` and do not count.
