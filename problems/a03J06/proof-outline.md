# Proof Outline: a03J06

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

Closer hop 1 found no packaged polynomial-growth Liouville theorem. The
compiled helper `apm_a03J06_growth_cauchy_bound`, adapted from sibling
`aunk04`, now establishes the arbitrary-radius estimate

```text
‖iteratedDeriv k f 0‖ ≤ k! * (A * R^m) / R^k       (1 < R).
```

The remaining proof must let `R → ∞` to make every coefficient above
degree `m` vanish, then use analytic Taylor-series uniqueness to identify `f`
globally with the finite polynomial formed from its first `m + 1`
coefficients. Mathlib's Cauchy estimate and Taylor power-series APIs provide
the separate ingredients but not this assembled reconstruction theorem.

## Imported Proof Plan

```clojure
{:problem-id 'a03J06'
 :frame-id 'apm-v2-a03J06-1774988835460'
 :goal ""
 :terms []
 :strategy []
 :checkpoints [{:stage 1 :status :pending}
               {:stage 2 :status :pending}
               {:stage 3 :status :pending}
               {:stage 4 :status :pending}]
 :lean {:module-root 'ApmCanaries.Frames.A03J06.Apm_v2_a03J06_1774988835460'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a03J06'
  :frame-id 'apm-v2-a03J06-1774988835460'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a03J06/apm-v2-a03J06-1774988835460/proof-plan.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A03J06/Apm_v2_a03J06_1774988835460/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A03J06/Apm_v2_a03J06_1774988835460/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]
