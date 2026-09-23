# The margin apparatus for Lean proofs

claude-7, 2026-09-23.

The rendered proofs at `wip/prelims/` set the informal argument and the Lean
proof on one page, at a Tufte measure with a permanently free margin. Joe's
brief for that margin: *explain the problems*, using the Lean layer as
scaffolding — "not necessarily for teaching people how to think like a computer,
but maybe as scaffolding for teaching people how to think at all" — by relating
the main concepts in the Lean proof to the concepts in the informal proof.

This note records what is built, what it deliberately does not claim, and the
one interface the missing half will arrive through.

## What the apparatus is

`scripts/render-lean-proofs.py` cuts each `problems/<id>/lean/Main.lean` at its
top-level declarations and emits, per declaration, a `\apmgloss{...}` followed by
that declaration's highlighted listing. `\apmgloss` is semantic, not
typographic: the article preamble makes it a `\marginpar`, which LaTeXML renders
as a note and `tuftify.py` lifts into the Tufte margin; the book preamble sets it
inline, because a 1,600-page book has no margin column and 5,382 floating
marginpars would fight the page on every spread.

So the margin has a slot beside every declaration in every Lean proof, and the
question is only what goes in it.

## What goes in it now

Two things, both exact, neither inferred.

**Structure.** "Reuses `apm_a94J02_density`, `apm_a94J02_H`." A token match of
the declaration's body against the names the same file declares earlier. This is
a dependency edge, not a guess: it says how the formal proof hangs together,
which is the part of "how the Lean concepts relate" that is knowable without a
concept model. On a fifteen-lemma proof it is the difference between a wall of
tactics and a visible skeleton.

**Author-supplied cross-references.** 62 of the informal solutions end with a
`**Mathlib cross-refs:**` line naming the results the prose leans on. That line
is already a human-authored bridge between the two registers, and it becomes the
opening margin note of the Lean section.

Plus the section's own census: how many declarations, and whether the audit
found a `sorry`.

## What is NOT built, and why it is not

The mapping proper — *this phrase in the prose corresponds to that Mathlib
lemma* — is not computed. Nothing here infers it, and nothing here pretends to.

Doing it honestly needs two things that do not exist yet:

1. the **superpod scope mining**, which is slated but not run; and
2. a **model of the patterns** the proofs are instances of, built on top of it.

Guessing in the meantime would be worse than leaving the margin structural. A
margin note that says "this is the compactness step" when it is not is more
expensive to unlearn than an empty margin is to read past. The related trap is
recorded in futon6's `holes/` notes: a measurement taken through the wrong entry
point produced a confident, wrong figure that had to be retracted. The same
applies to a concept mapping asserted without the corpus behind it.

## The interface

`render-lean-proofs.py` reads `report/lean-annotations.json` if it exists:

```json
{
  "a94J02/apm_a94J02_exists_fat_compact":
    "The \"fat Cantor set\" of the informal proof. Nowhere dense, so it has empty
     interior, but positive measure -- the two properties the prose asks for.",
  "a94J02/apm_a94J02_density": "..."
}
```

Key is `<problem id>/<declaration name>`; value is LaTeX, set in the margin
ahead of the structural note. Populating it needs no change to any script, so
the scope-mining work can land as data.

Two things worth settling when it does:

- **What a note is for.** A gloss that names the informal counterpart ("this is
  the fat Cantor set") is a different object from one that explains the tactic
  ("`gcongr` closes a chain of monotone inequalities"). The first teaches the
  mathematics, the second teaches Lean. Joe's brief points at the first.
- **Coverage.** 6,730 declarations, 2,891 of them already carrying a docstring
  written by whoever formalised them. Those docstrings are in English and often
  say exactly what the step does; they are the obvious seed corpus for the
  mapping, and they are already in the listing where the author put them. The
  open question is whether a note should repeat one, paraphrase it, or only fire
  where a docstring is absent.

---

## How were these proofs actually developed?

claude-7, 2026-09-23, answering Joe's question: is the Lean proof a translation
of the informal one, or independent of it?

Neither, uniformly. There are three regimes, and they are distinguishable from
the files themselves.

| | proofs | informal file has a ```lean block | git order |
|---|---|---|---|
| nl-proof-harvest | 311 | 0 / 311 | informal first, 311/311 |
| daily batch | 86 | 86 / 86 | 36 informal-first, 32 same commit, 18 Lean-first |
| proof-frame import | 48 | 3 / 48 | all one commit |
| hand-written / other | 41 | 5 / 41 | mixed |
| imported | 15 | 0 / 15 | mostly informal-first |

**Independent by design (311, 62%).** `storage/apm/run-nl-proof-harvest.py`
dispatches one prompt per problem whose last instruction is: *"This is Stage-1
only: do NOT write Lean, do NOT call lake, do NOT hand to Codex."* The agent
reads the problem `.tex` and nothing formal. `algorithms/apm-nl-proof-harvest.md`
states the intent: the NL harvest and the Lean formalization "are now
**independent stages writing to the same canonical surface**", decoupled because
the 5/day cadence had been gated by the Lean stage rather than by the prose.
Every one of the 311 carries the provenance comment, none contains Lean, and in
all 311 the informal file entered the repo before any `lean/Main.lean`.

**Co-generated (86, 17%).** The earlier daily batch,
`futon3c/dev/futon3c/dev/apm_conductor_v3.clj`, `make-informal-lean-prompt`: one
Claude reply produces *informal proof + Lean 4 theorem statement + Mathlib
cross-references* together, from the problem statement, with no proofs and no
tools. All 86 carry a ```lean block, because the prompt asked for one. Codex
closed the `sorry`s afterwards on its own track; note that the Codex prompts
pass the informal proof as a **path** (`maybe-section "Informal outline"`), not
as injected text -- available if the agent looks, not in context by default.

**Formal-to-informal (48, 10%).** The proof-frame workspace import, which is the
Stage 1-4 shape, and whose Stage 4 heading is literally "FORMAL-TO-INFORMAL
REVISION". Here the prose was revised *after* the formalization. `a00J03` is one
of these -- so it is the least representative page in the collection to judge
the apparatus by.

### What this means for the margin notes

Anchors per proof are near-identical across the three regimes: **1.76**
(harvest), **1.73** (daily batch), **1.88** (proof-frame). So the name matches
are not an artefact of the prose and the Lean having been written in one breath;
they survive the population where Lean was explicitly forbidden.

They are not fully independent either, and the route matters. The harvest prompt
injected `futon3c/data/apm-formalization-patterns.edn`, whose own header says it
was "extracted from 19 proved + 2 partial overnight proofs ... from
ApmCanaries/Frames/*/Main.lean". Mathlib names reached the Lean-free prose
through that library. The agreement between a prose citation and the problem's
Lean proof is therefore evidence about a shared vocabulary, not two independent
witnesses to the same mathematics.

One caveat on the git column: it records when a file entered `apm-lean`, not
when it was written. The harvest wrote to `futon3c/data/apm-informal-proofs/`
and was imported afterwards. It is corroborating rather than primary evidence --
the prompts are the primary evidence.
