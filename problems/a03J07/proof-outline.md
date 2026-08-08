# Proof Outline: a03J07

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'a03J07'
 :frame-id 'apm-v2-a03J07-1774988886868'
 :goal ""
 :terms []
 :strategy []
 :checkpoints [{:stage 1 :status :pending}
               {:stage 2 :status :pending}
               {:stage 3 :status :pending}
               {:stage 4 :status :pending}]
 :lean {:module-root 'ApmCanaries.Frames.A03J07.Apm_v2_a03J07_1774988886868'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a03J07'
  :frame-id 'apm-v2-a03J07-1774988886868'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a03J07/apm-v2-a03J07-1774988886868/proof-plan.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A03J07/Apm_v2_a03J07_1774988886868/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A03J07/Apm_v2_a03J07_1774988886868/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]

## Closer hop 1 — complete

Rotate the upper half-plane to the right half-plane by setting
`g(w) = f(I*w)`. The supplied uniform bound gives the order-zero exponential
growth hypothesis and boundedness on the positive real axis. The original
real-axis estimate becomes the imaginary-axis estimate for `g`. Apply
`PhragmenLindelof.right_half_plane_of_bounded_on_real`, then rotate the target
point back. This packaging is adapted from the already solved sibling
`b99A01`.
