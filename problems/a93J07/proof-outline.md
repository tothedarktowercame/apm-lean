# Proof Outline: a93J07

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'a93J07'
 :frame-id 'Apm_v2_a93J07_1775570229422'
 :goal ""
 :terms []
 :strategy []
 :checkpoints [{:stage 1 :status :pending}
               {:stage 2 :status :pending}
               {:stage 3 :status :pending}
               {:stage 4 :status :pending}]
 :lean {:module-root 'ApmCanaries.Frames.A93J07.Apm_v2_a93J07_1775570229422'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a93J07'
  :frame-id 'Apm_v2_a93J07_1775570229422'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a93J07/Apm_v2_a93J07_1775570229422/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a93J07/Apm_v2_a93J07_1775570229422/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A93J07/Apm_v2_a93J07_1775570229422/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A93J07/Apm_v2_a93J07_1775570229422/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]

## Closer hop 1

The limit is now proved analytic, and locally uniform convergence is proved to
eventually preserve nonvanishing on any compact circle where the limit is
nonzero. These lemmas were recovered from historical commit `b898439`.

That commit also records the remaining route: use
`DiffContOnCl.ball_subset_image_closedBall` to prove that every finite-order
zero of the limit forces a nearby zero of all sufficiently late approximants.
The zero-free hypothesis rules this out. An infinite-order zero makes the
analytic limit locally zero, and the identity theorem propagates this across
the preconnected domain.

## Closer hop 2

The historical zero-persistence argument is now localized as
`apm_a93J07_zero_persistence`. It isolates a finite-order zero, obtains a
positive minimum of the limit norm on a surrounding circle, transfers the
lower bound to late approximants by uniform convergence, and applies
`DiffContOnCl.ball_subset_image_closedBall` to force a nearby zero.

For the main theorem, choose a zero of the limit if it is not zero-free. If
its analytic order is infinite, the analytic identity theorem propagates
local vanishing throughout the preconnected domain. If its order is finite
and positive, zero persistence contradicts the hypothesis that every
approximant is zero-free. Hence the theorem is complete and sorry-free.
