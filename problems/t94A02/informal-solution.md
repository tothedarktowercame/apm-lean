# Informal Solution: t94A02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The problem looks like a metric version of Urysohn’s lemma,
but most students either invoke the abstract normal-space theorem (massive
overkill) or try the naive formula
`dist(x,A)/(dist(x,A)+dist(x,B))` without checking that the denominator stays
positive. That breaks as soon as one set is empty or as soon as a point belongs
to both fibers. The real issue is to exploit that in ℝ the distance to a closed
set vanishes exactly on the set, so we can normalize those distances safely.

**Key insight.** Wrap the distance-to-a-set construction into a single
continuous nonnegative function that is strictly positive away from the set.
When a set is empty, force the “distance” to be the constant `1`, so the
denominator can never vanish and the empty fiber condition becomes automatic.

**Complete proof.** For a subset `S ⊆ ℝ`, define
```
    d_S(x) = { 1,                          if S = ∅,
             { inf_{s∈S} |x − s|,          otherwise.
```
The function `x ↦ inf_{s∈S} |x − s|` is 1-Lipschitz, hence continuous and
nonnegative; when `S` is closed and nonempty, `d_S(x)=0` iff `x∈S`. When `S` is
empty, `d_S` is the constant map `1`. For closed, disjoint `A,B ⊆ ℝ`, set
```
    f(x) = d_A(x) / (d_A(x) + d_B(x)).
```
If `A = ∅` (resp. `B = ∅`) the denominator equals `1 + d_B(x)` (resp.
`d_A(x) + 1`), while if both sets are nonempty the denominator cannot be `0`,
because `d_A(x)+d_B(x)=0` would force `x∈A∩B`. Therefore `f` is continuous as a
quotient of continuous functions with a positive denominator. Because both
`d_A,d_B` are nonnegative, we have `0 ≤ f(x) ≤ 1`, so the image of `f` lies in
`[0,1]`. If `x∈A` then `d_A(x)=0` and thus `f(x)=0`. Conversely, if `f(x)=0`
the denominator is positive, hence `d_A(x)=0`, putting `x` in `A`. The same
argument with the complement yields `f^{-1}(1)=B`. Consequently, `f` is the
desired continuous map.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `continuous_infDist_pt`: ensures `x ↦ inf_{a∈A}|x-a|` is continuous and
  nonnegative, giving continuity of each `d_S`.
- `IsClosed.mem_iff_infDist_zero`: converts the algebraic condition
  `d_A(x)=0` (or `d_B(x)=0`) into set membership, which handles the fibers.
- `distTo_add_pos` (custom): shows `d_A(x)+d_B(x) > 0` everywhere by appealing
  to disjointness (otherwise both distances would vanish simultaneously).
- Basic algebraic lemmas (`div_eq_zero_iff`, `div_eq_one_iff_eq`): identify the
  fibers of the quotient once the denominator is nonzero.

Lean target: `separate_closed_sets` inside
`ApmCanaries.Frames.T94A02.Apm_v2_t94A02_1775009748581.Main`.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t94A02/apm-v2-t94A02-1775009748581/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t94A02/apm-v2-t94A02-1775009748581/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/T94A02/Apm_v2_t94A02_1775009748581/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/T94A02/Apm_v2_t94A02_1775009748581/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

Implementation steps:
1. Define `distTo S x` as above, and prove helper lemmas: nonnegativity,
   continuity, and `distTo S x = 0 ↔ x ∈ S` when `S` is closed.
2. Prove that for disjoint closed `A,B`, the denominator `distTo A x + distTo B x`
   is strictly positive for every `x`, covering the empty-set cases explicitly.
3. Define `sepFun A B x = distTo A x / (distTo A x + distTo B x)` and prove it is
   continuous, lands in `[0,1]`, and has the prescribed fibers.
4. Package the result as `separate_closed_sets` with no `sorry`, then confirm
   via `lake build`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean development follows the prose verbatim: `distTo` matches the informal
construction, and the only extra bookkeeping is the empty-set branch that keeps
the denominator positive. That issue was already highlighted in Stage 1’s
“Why it’s hard” paragraph, so no further adjustments are needed.
