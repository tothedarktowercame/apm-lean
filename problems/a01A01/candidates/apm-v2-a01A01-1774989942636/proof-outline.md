# Proof Outline: a01A01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'a01A01'
 :frame-id 'apm-v2-a01A01-1774989942636'
 :goal "Construct nonnegative spikes (on [0,1] and on R^n) whose integrals vanish but whose pointwise limsup is +∞ everywhere."
 :terms ['dyadic-partition 'spike-functions 'limsup 'vanishing-integral 'Rn-tiling]
 :strategy ["Partition the domain into finer and finer dyadic intervals (or cubes) and assign to each cell a spike whose height grows like 2^{level/2} and whose support is the full cell."
            "Enumerate all spikes stage by stage so that every point is hit by exactly one spike at each level, forcing the limsup to diverge."
            "Compute the integral of each spike (height × measure) and note it equals 2^{-level/2} (or 2^{-level·n/2}), hence converges to 0."
            "Extend the construction from [0,1] to R^n by tiling R^n with dyadic cubes and repeating the same amplitude/volume tradeoff."]
 :checkpoints [{:stage 1 :status :completed :notes "Explicit dyadic spike construction and verification for [0,1] and R^n recorded in execute.md."}
               {:stage 2 :status :completed :notes "Dependency table (dyadic coverage, indicator integrals, geometric decay, countable ordering) written."}
               {:stage 3 :status :completed :notes "Lean lemma `tendsto_inv_sqrt_two_pow` added and build succeeds."}
               {:stage 4 :status :completed :notes "No additional prose changes needed beyond Stage 1."}]
 :lean {:module-root 'ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774989942636'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774989942636'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}
 {:kind :stage1-completed
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774989942636'
  :summary "Wrote the dyadic spike construction on [0,1] and R^n, verifying limsup = +∞ and integrals -> 0."}
 {:kind :stage2-completed
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774989942636'
  :summary "Cataloged the supporting facts (dyadic coverage, indicator integrals, geometric decay, countability)."}
 {:kind :stage3-completed
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774989942636'
  :summary "Implemented the Lean lemma `tendsto_inv_sqrt_two_pow` and confirmed `lake build`."}
 {:kind :stage4-completed
  :problem-id 'a01A01'
  :frame-id 'apm-v2-a01A01-1774989942636'
  :summary "Reviewed the formal insight and found the prose already captured the necessary decay argument."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Construction on \\([0,1]\\).*  For each integer \\(m\\ge 1\\) and each \\(0\\le j<2^{m}\\),
let
\\[
I_{m,j} = \left[\frac{j}{2^{m}},\frac{j+1}{2^{m}}\right)
\quad\text{and}\quad
f_{m,j}(x) =
\begin{cases}
2^{m/2}, & x\in I_{m,j},\\
0, & \text{otherwise.}
\end{cases}
\\]
Enumerate these functions as \\(\{f_k\}\\) by listing all pairs \\((m,j)\\) in lexicographic order
(first increasing \\(m\\), then increasing \\(j\\)).

Each \\(f_{m,j}\\) is nonnegative and its integral is easy to compute:
\\(\int_0^1 f_{m,j} = 2^{m/2} \cdot |I_{m,j}| = 2^{m/2} \cdot 2^{-m} = 2^{-m/2}\\).
Because \\(m\\to\infty\\) along the sequence, these integrals converge to \\(0\\).

Fix \\(x\in[0,1]\\).  For every level \\(m\\) there is exactly one index \\(j\\)
with \\(x \in I_{m,j}\\).  On that interval we have \\(f_{m,j}(x)=2^{m/2}\\),
so along the subsequence consisting of levels \\(m\\) the function values grow without bound.
Hence \\(\limsup_{k\to\infty} f_k(x)=\infty\\) for every \\(x\in[0,1]\\),
while \\(\int_0^1 f_k\to 0\\).

*Adapting to \\({\\mathbf R}^n\\).*  Tile \\({\\mathbf R}^n\\) with dyadic cubes
\\[
Q_{m,\\mathbf{k}} = \prod_{i=1}^{n}\left[k_i 2^{-m}, (k_i+1)2^{-m}\right)
\quad (m\ge 1, \\mathbf{k}\in {\\mathbf Z}^n).
\\]
For each cube define
\\(
F_{m,\\mathbf{k}} = 2^{mn/2} \cdot \mathbf{1}_{Q_{m,\\mathbf{k}}}.
\\)
Listing all pairs \\((m,\\mathbf{k})\\) in a countable order produces a sequence
\\(\{F_k\}\\) of nonnegative functions on \\({\\mathbf R}^n\\) with
\\(\int_{{\\mathbf R}^n} F_{m,\\mathbf{k}} = 2^{mn/2} \cdot 2^{-mn} = 2^{-mn/2} \to 0\\).
For any fixed \\(x\in {\\mathbf R}^n\\), each level \\(m\\) contains
exactly one cube that contains \\(x\\); its value there is \\(2^{mn/2}\\),
so the pointwise limsup is still \\(+\infty\\).  Thus both requirements are met on \\({\\mathbf R}^n\\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| Label | Statement / role | Dependencies | Why it's used now | Intended Lean target / search terms |
|-------|------------------|--------------|-------------------|--------------------------------------|
| D1 | Dyadic intervals/cubes cover the domain and shrink with level | basic measure theory | ensures each point lies in exactly one cell per level, so limsup is driven by the level index | `intervals`, `dyadic`, `cubical-tiling` |
| D2 | Integral of a spike equals height × measure of its support | definition of integral of indicators | lets us compute \(\int f_k\) explicitly | `measure_mul`, `indicator_integral` |
| D3 | The sequence \(2^{-m/2}\) (and \(2^{-mn/2}\)) tends to \(0\) | geometric-series decay | shows the integrals vanish along the ordered sequence | `tendsto_pow_atTop_nhds_0_of_abs_lt_1` |
| D4 | Ordering of spikes by level is countable | countability of \({\\mathbf N}\times {\\mathbf Z}^n\) | makes the construction a bona fide sequence | `Nat.lex`, `countable_pi` |

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a01A01/apm-v2-a01A01-1774989942636/proof-plan.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A01A01/Apm_v2_a01A01_1774989942636/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A01A01/Apm_v2_a01A01_1774989942636/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

Formal target: prove the geometric-decay fact used in Stage 1, namely that
powers of \(1/\sqrt{2}\) (or \((1/\sqrt{2})^n\)) tend to zero.  Mathlib
provides `tendsto_pow_atTop_nhds_0_of_abs_lt_1`, so we just instantiate it with
\(a=1/\sqrt{2}\).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No further adjustments were needed: the formal lemma only confirmed the decay of
\(2^{-m/2}\), which the prose argument already relied on implicitly.
