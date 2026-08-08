# Proof Outline: a92J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

Closer hops 1--2 compiled three parts of the theorem's interface:

- `apm_a92J01_memLp_mono_on_unitMeasure` proves the complete finite-measure
  inclusion `Lᵖ ⊆ Lʸ` for `q < p` using `MemLp.mono_exponent`.
- `apm_a92J01_discontinuousCounterexample_memLp` proves that the explicit
  indicator belongs to every `Lᵖ` over the restricted unit measure.
- `apm_a92J01_discontinuousCounterexample_not_continuousOn` proves the
  indicator is not continuous on `[0,1]`: epsilon-delta continuity at `1/2`
  is contradicted by a point `1/2 + min (δ/2) (1/4)` immediately to its right.

The remaining work is to reduce the sequence and real-line power-law
counterexamples to Mathlib's p-series and improper-power-integrability
criteria, including the `ENNReal.ofReal` exponent conversions. The complete
indicator conjunct is now available by pairing the two compiled helpers.

Closer hop 3 proves the common scalar threshold arithmetic:
`apm_a92J01_p_exponent_lt_neg_one` shows the `p`th-power exponent is below
`-1`, while `apm_a92J01_neg_one_le_q_exponent` shows the `q`th-power exponent
is at least `-1`. The remaining gap is therefore only the formal conversion
from the concrete `MemLp` goals to the p-series and tail-integral criteria.

## Imported Proof Plan

```clojure
{:problem-id 'a92J01'
 :frame-id 'apm-v2-a92J01-1774989024995'
 :goal ""
 :terms []
 :strategy []
 :checkpoints [{:stage 1 :status :pending}
               {:stage 2 :status :pending}
               {:stage 3 :status :pending}
               {:stage 4 :status :pending}]
 :lean {:module-root 'ApmCanaries.Frames.A92J01.Apm_v2_a92J01_1774989024995'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a92J01'
  :frame-id 'apm-v2-a92J01-1774989024995'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a92J01/apm-v2-a92J01-1774989024995/proof-plan.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A92J01/Apm_v2_a92J01_1774989024995/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A92J01/Apm_v2_a92J01_1774989024995/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]
