# APM Problem Bundle Spec

Date: 2026-05-01
Status: draft

## Purpose

This document defines the canonical on-disk shape for APM proof work in
`apm-lean`.

The immediate goal is to stop handing off disconnected Lean files with
`sorry` holes and instead hand off self-contained problem bundles that
include:

- the problem statement
- the best available informal solution
- the proof outline / blocker notes for formalization
- the Lean files
- machine-readable provenance and status

`apm-lean` is the owner of these bundles.

`futon6` may continue to own generic proof-workflow tooling, but it should
not remain the only home of APM-specific context.

## Canonical Layout

Each APM problem lives at:

```text
problems/<problem-id>/
```

The bundle layout is:

```text
problems/<problem-id>/
  problem.tex
  problem.md
  informal-solution.md
  proof-outline.md
  proof-plan.edn
  changelog.edn
  workspace.json
  receipt.json
  status.json
  lean/
    Main.lean
    Scratch.lean
```

For problems with multiple competing historical frames during migration, use
the transition layout:

```text
problems/<problem-id>/
  README.md
  status.json
  candidates/
    <frame-id>/
      problem.tex
      problem.md
      informal-solution.md
      proof-outline.md
      proof-plan.edn
      changelog.edn
      workspace.json
      receipt.json
      status.json
      lean/
        Main.lean
        Scratch.lean
```

Legacy `lean-proofs/<problem-id>/` material reconciles into the same problem
root in one of two ways:

```text
problems/<problem-id>/
  problem.tex
  problem.md
  informal-solution.md
  proof-outline.md
  status.json
  lean/
    Main.lean
    ...
```

Use that layout when the legacy Lean directory is the only known source for
the problem.

```text
problems/<problem-id>/
  ...
  historical/
    legacy-lean-proofs/
      README.md
      status.json
      problem.tex
      lean/
        Main.lean
        ...
```

Use that archival layout when a canonical frame-derived bundle already exists
and the old `lean-proofs` tree should be preserved for comparison or salvage.

## File Roles

### `problem.tex`

The canonical raw problem statement source copied from `apm/<problem-id>.tex`
when available.

### `problem.md`

Human-readable problem statement and bundle overview.

This file must be readable without opening any other repo.

### `informal-solution.md`

Best-effort worked mathematical solution in prose.

This is the primary handoff artifact for a human reader who wants the
mathematics before the Lean formalization details.

### `proof-outline.md`

Formalization-oriented outline:

- dependency structure
- key lemmas
- proof strategy
- identified blockers
- intended Lean landing points

This file exists because a worked solution and a Lean-oriented proof plan are
related but not identical.

### `proof-plan.edn`

Machine-readable plan imported from the frame workspace when present.

### `changelog.edn`

Machine-readable attempt history imported from the frame workspace when
present.

### `workspace.json`

Imported provenance from the original frame workspace when present.

This is historical metadata, not the canonical source of truth after import.

### `receipt.json`

Imported proof-frame receipt when present.

This preserves the trace back to the old `futon6` receipt model.

### `status.json`

Canonical status summary for the imported bundle.

Required fields:

```json
{
  "schema": "apm-problem-bundle.v1",
  "problem_id": "a00J01",
  "bundle_root": "problems/a00J01",
  "source": {
    "workspace_metadata": "...",
    "receipt": "...",
    "problem_tex": "..."
  },
  "lean": {
    "main": "lean/Main.lean",
    "scratch": "lean/Scratch.lean",
    "sorry_count_main": 2,
    "sorry_count_scratch": 0,
    "sorry_count_total": 2
  },
  "artifacts": {
    "has_problem_tex": true,
    "has_problem_md": true,
    "has_informal_solution": true,
    "has_proof_outline": true,
    "has_proof_plan": true,
    "has_changelog": true,
    "has_workspace_metadata": true,
    "has_receipt": true
  },
  "classification": "partial",
  "imported_at": "2026-05-01T00:00:00Z"
}
```

For legacy-only imports, the source block must identify the origin explicitly:

```json
{
  "source": {
    "kind": "legacy-lean-proofs",
    "legacy_lean_root": "/abs/path/to/lean-proofs/a01A11",
    "problem_tex": "/abs/path/to/apm/a01A11.tex"
  }
}
```

### `lean/Main.lean`

Primary Lean development for this bundle.

### `lean/Scratch.lean`

Frame-local or bundle-local scratch space.

## Invariants

1. A Lean file must not be handed off by itself.
2. Every `lean/Main.lean` must sit next to at least:
   - `problem.md`
   - `informal-solution.md`
   - `proof-outline.md`
   - `status.json`
3. All paths stored in `status.json` must be repo-relative.
4. Imported historical paths from `futon6` may be preserved inside
   `workspace.json` / `receipt.json`, but the bundle itself must remain usable
   without resolving those old paths.
5. `ApmCanaries/Frames/...` remains legacy storage during migration; new
   handoff-ready APM work should target `problems/<problem-id>/`.
6. Legacy `lean-proofs/...` material must not remain detached from a problem
   bundle once reconciled; it either becomes the canonical bundle for a
   legacy-only problem or is preserved under `historical/legacy-lean-proofs/`.

For duplicate-frame problems in transition:

7. `problems/<problem-id>/status.json` must describe the candidate set.
8. each candidate frame gets its own bundle under `candidates/<frame-id>/`.
9. the importer must not silently collapse multiple historical frames into one
   bundle before a winner-selection rule exists.

## Migration Policy

### First-pass import

The first-pass importer is allowed to:

- copy existing frame-local Lean files
- copy raw `proof-plan.edn`, `changelog.edn`, `workspace.json`, `receipt.json`
- synthesize `problem.md`, `informal-solution.md`, and `proof-outline.md`
  from existing workspace material

The first-pass importer is not required to:

- normalize all historical naming
- deduplicate multiple frames for the same problem
- decide the final canonical winner among competing proof attempts

### Legacy reconciliation

The legacy reconciliation pass is allowed to:

- import `lean-proofs/<problem-id>/` into a standalone bundle when no frame
  bundle exists
- preserve overlapping `lean-proofs/<problem-id>/` trees as archival material
  under `historical/legacy-lean-proofs/`
- synthesize placeholder `informal-solution.md` and `proof-outline.md` files
  when no richer source material exists

The legacy reconciliation pass is not required to:

- invent a synthetic `futon6` frame id
- claim that archival legacy Lean is the canonical winner over a frame bundle

### Human follow-up expected

Imported bundles are expected to be cleaned up later:

- merge duplicate frames
- replace generated prose wrappers with edited handoff-quality prose
- promote reusable lemmas out of bundle-local scratch when warranted
- choose one canonical winner for duplicate-frame problems once reviewed

### Candidate-set status

When a problem has multiple frames, the top-level problem status file must use
the candidate-set schema:

```json
{
  "schema": "apm-problem-candidate-set.v1",
  "problem_id": "a00J02",
  "bundle_root": "problems/a00J02",
  "layout": "candidate-set",
  "candidate_count": 3,
  "frame_ids": [
    "apm-v2-a00J02-1774988700000",
    "apm-v2-a00J02-1774990100000",
    "apm-v2-a00J02-1774990402922"
  ],
  "recommended_latest_frame_id": "apm-v2-a00J02-1774990402922",
  "selected_frame_id": null,
  "imported_at": "2026-05-01T00:00:00Z"
}
```

## Ownership Boundary

- `apm-lean` owns the canonical APM problem bundle.
- `futon6` owns generic workflow tools that may generate bundle content.
- Rob / LeanDojo should receive bundle-local material from `apm-lean`, not
  split references across repos.

## Acceptance Check

A problem bundle is handoff-ready only if:

1. `status.json` exists.
2. `lean/Main.lean` exists.
3. `problem.md` exists.
4. `informal-solution.md` exists.
5. `proof-outline.md` exists.
6. the bundle is understandable without opening `futon6`.

For candidate-set problems, no top-level handoff is ready until either:

1. one candidate has been selected as canonical, or
2. the consumer explicitly agrees to inspect the candidate subdirectories.
