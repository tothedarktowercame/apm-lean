# Proof Outline: aunk02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show a holomorphic function that is real on a disk inside Ω is real on all of Ω."
 :terms [{:name "open mapping principle"
          :meaning "A non-constant holomorphic map sends open sets to open subsets of ℂ."
          :needed-because "If f(non-constant) took a disk into ℝ, the image would have to be open in ℂ; the only way out is that f is constant, hence real everywhere."}
         {:name "identity theorem"
          :meaning "Holomorphic functions that agree on a set with a limit point coincide everywhere on the domain."
          :needed-because "Once we know f equals its complex conjugate on a disk, the equality propagates to all of Ω."}
         {:name "complex conjugation trick"
          :meaning "Define g(z)=\overline{f(\bar z)}; real-valuedness means f=g on the disk."
          :needed-because "Converts the hypothesis “f is real on the disk” into an equality of holomorphic functions so that the identity theorem applies."}]
 :strategy [{:id :s1
             :formal-dependency "open_mapping_principle"
             :informal-dependency "Use open mapping to show a holomorphic map that hits only ℝ on a disk must be constant."
             :why-this-now "Constancy on the disk is the bridge to extend real-valuedness."
             :lean-target "Complex.open_mapping_theorem"
             :mathlib-status "Available in Mathlib for non-constant holomorphic maps."}
            {:id :s2
             :formal-dependency "identity_theorem"
             :informal-dependency "Apply the identity theorem to f and its conjugate-defined twin."
             :why-this-now "Yields that f equals its conjugate on all of Ω, i.e., f is real everywhere."
             :lean-target "Complex.eq_of_eq_on_ball"
             :mathlib-status "Identity theorem is implemented for holomorphic maps."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'aunk02'
  :frame-id 'apm-v2-aunk02-1775005869003'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/aunk02/apm-v2-aunk02-1775005869003/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/aunk02/apm-v2-aunk02-1775005869003/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/Aunk02/Apm_v2_aunk02_1775005869003/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/Aunk02/Apm_v2_aunk02_1775005869003/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]
