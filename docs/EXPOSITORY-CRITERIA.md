# Expository proofs: criteria, two variants, and a worked example

Draft, claude-9 with Joe, 2026-11-12. Status: criteria are a first proposal;
the sources section is checked against primary texts where marked.

## Why

The informal solutions in `problems/*/informal-solution.md` are graded by an
ad hoc prelim rubric, and many were written by models. They are usually
correct in substance, but they are often unclear: drafting left in, slips
papered over, the main idea placed where the proof never uses it. The Lean
proofs are checked but hard to read. This note proposes criteria for
expository proofs, in two variants:

- **Prelim**: short, clear, factual. What an examiner should see.
- **Teaching**: longer, still clear, more detailed; it anticipates and
  answers a reader's questions. Out of place in an exam, suited to course
  notes that teach a reader how to pass the prelim.

In both, the Lean proof is the factual check: the prose makes no claim the
Lean proof does not support.

## Sources

See the verified notes in `~/notes/expository-proof-sources.md` (to be
folded in here). In brief:

- Dutilh Novaes: a proof as a dialogue between Prover and a Skeptic who
  checks every step; the function of proof as *explanatory persuasion*
  (showing why, not only that); explanatoriness relative to the audience.
  The two variants are the same Prover facing two Skeptics.
- Pease, Aberdein and Martin (2019): an empirical study of explanation in
  mathematical conversations; explanation occurs throughout practice, not
  only inside proofs. Supports explanation around the proof in the teaching
  variant.
- Mejia-Ramos, Fuller, Weber, Rhoads and Samkoff (2012): a model of proof
  comprehension with local and holistic dimensions. Used below as the test
  for the teaching variant: a reader should be able to answer its kinds of
  question from the text alone.
- Presentation order (Leron 1983, Lamport 1995/2012): deferred.

## Criteria

| | Prelim variant | Teaching variant |
|---|---|---|
| Skeptic | an examiner who knows the field | a student preparing for the prelim |
| Steps | every step justified; standard steps named, not shown | the same, plus why this step and not another |
| Main idea | stated once, in one sentence, before it is used | stated first, motivated by the cases that fail |
| Drafting | none | wrong turns kept only when they teach, marked as such |
| Definitions | as needed for the check | every term a student might misread is pinned down |
| Questions | none anticipated | the likely questions asked and answered in place |
| Factual check | every claim supported by the Lean proof | the same |
| Test | the Skeptic cannot object | a reader can answer comprehension questions of each kind (meaning of terms, logical status, justification of steps, main idea, structure, transfer, examples) from the text |

Kinds of unclarity to look for (from a01A01; to be extended by reading more
problems):

1. **Drafting left in**: false starts and corrections inside the solution
   ("Let me use a better indexing", "Wait, this over-complicates things").
2. **A slip papered over**: a claim that does not hold as stated, patched by
   a phrase ("by convention") that contradicts an earlier definition.
3. **The idea placed where the proof does not use it**: the explanation
   appears in a preface; the proof itself never says why its choices work.
4. **Wrong quantifier strength in a remark**: "irrelevant for a.e." where
   the claim is for every x.

## Worked example: a01A01

**Problem.** Find nonnegative functions f_k on [0,1] with
limsup_k f_k(x) = ∞ for every x and ∫ f_k → 0. Adapt the argument to ℝ^d.

**What is unclear in the current solution** (`problems/a01A01/informal-solution.md`):

- Kind 1: the "Key Insight" section tries height n with width 1/n (integral
  1), height 1 (limsup 1), cells of width 1/n² with an index formula it then
  abandons ("Wait, this over-complicates things"), before the proof starts.
- Kind 2: Claim 2 uses half-open intervals [j/n, (j+1)/n), which miss
  x = 1, then says "x = 1 is in I_{n,n-1} by convention". The Lean proof
  uses closed intervals; overlaps at endpoints do no harm, since the proof
  only needs every x to lie in *some* interval of each block.
- Kind 3: "big on different small sets at different times" is in "Why It's
  Hard"; the proof never says why height √n with width 1/n is right.
- Kind 4: "irrelevant for a.e. statement", where the claim is for every x.

### Prelim variant

For n ≥ 1 and 0 ≤ j < n let I_{n,j} = [j/n, (j+1)/n]. List the pairs (n, j)
block by block, (1,0), (2,0), (2,1), (3,0), …, and let f_k = √n · 1_{I_{n,j}}
for the k-th pair.

*Integrals.* ∫_0^1 f_k = √n · (1/n) = 1/√n. Block n has only n pairs, so
n → ∞ as k → ∞, and ∫ f_k → 0.

*Limsup.* Fix x ∈ [0,1]. The intervals of block n cover [0,1], so for each n
some k in block n has f_k(x) = √n. Hence f_k(x) ≥ √n for infinitely many k,
for every n, and limsup_k f_k(x) = ∞.

*ℝ^d.* For m ≥ 1 tile [−m, m]^d by cubes of side 1/m (there are (2m²)^d) and
list them block by block in m. Put height m^{d/2} on each cube: the integral
is m^{d/2} · m^{−d} = m^{−d/2} → 0. Each x lies in [−m, m]^d for all large m,
and then in some cube of block m, where the function is m^{d/2}. So the
limsup is ∞ everywhere.

### Teaching variant

**The tension.** We want functions that are eventually huge at *every* point
but whose total area goes to zero. A function that is large on a fixed set A
of positive measure has integral at least (its height) × m(A), so the large
values cannot stay in one place. The bumps have to move: large on small sets,
with the small set sweeping across [0,1] again and again.

**Choosing height and width.** Sweep [0,1] with n intervals of width 1/n, and
give each bump height h_n. Its area is h_n / n.

- Height 1: area 1/n → 0, but every value is at most 1, so the limsup is 1.
- Height n: values grow, but the area is n · (1/n) = 1 and does not tend to 0.
- We need h_n → ∞ and h_n / n → 0. Any such choice works; h_n = √n is one.

*Question: is √n special?* No. Height log(n+1) or n^{0.9} work equally well.
The construction needs only h_n → ∞ and h_n = o(n).

**The construction.** For n ≥ 1 and 0 ≤ j < n let I_{n,j} = [j/n, (j+1)/n].
Block n is the sweep I_{n,0}, …, I_{n,n−1}. List the blocks one after another
and let f_k = √n · 1_{I_{n,j}}, where (n, j) is the k-th interval in the list.

*Question: why closed intervals?* So that every point of [0,1], including 1,
lies in some interval of each block. A point j/n lies in two intervals of
block n; that does no harm, since we only need *at least one*.

**The integrals tend to 0.** ∫ f_k = √n · (1/n) = 1/√n. Blocks 1, …, n contain
1 + 2 + ⋯ + n = n(n+1)/2 intervals in all, so the block number of f_k grows
like √(2k) and ∫ f_k → 0.

**The limsup is infinite at every point.** Fix x ∈ [0,1] and any n. Block n
covers [0,1], so one of its intervals contains x, and the corresponding f_k
has f_k(x) = √n. This happens in every block, so for every bound M some f_k
with arbitrarily large k has f_k(x) ≥ M. That is limsup_k f_k(x) = ∞.

*Question: what is liminf_k f_k(x)?* 0, at every point: within each block,
x lies in at most two of the n intervals, so f_k(x) = 0 for all other k.
The sequence oscillates between 0 and ever larger values at every point.
(This is consistent with Fatou's lemma, which gives ∫ liminf f_k ≤
liminf ∫ f_k = 0.)

*Question: how does this relate to the typewriter sequence?* Without the
height factor, f_k = 1_{I_{n,j}} is the standard example of a sequence that
tends to 0 in L¹ but converges at no point. The height factor makes the
failure as strong as possible.

**Adapting to ℝ^d.** Two routes.

1. *Cubes.* For m ≥ 1 tile [−m, m]^d by cubes of side 1/m and list the cubes
   block by block in m, with height m^{d/2}. A cube has volume m^{−d}, so the
   integral is m^{−d/2} → 0. A point x lies in [−m, m]^d once m ≥ max|x_i|,
   and from then on in some cube of every block.
2. *A product (the route the Lean proof takes).* Run the one-dimensional
   construction on the whole line in the first coordinate (in Lean, block n
   cuts each of about n unit intervals [z, z+1] around 0 into n pieces of
   height √n), and multiply by e^{−x_i²} in the others:
   g_k(x) = f_k(x_1) · ∏_{i ≥ 2} e^{−x_i²}. The integral factors as
   ∫ f_k · π^{(d−1)/2} → 0, and at a fixed x the Gaussian factor is a fixed
   positive number, so the limsup is still ∞.

*Question: why does route 2 work although the bumps no longer have small
support in ℝ^d?* Only the area matters for the integral, and only the
behaviour at each fixed point matters for the limsup. The Gaussian factor
keeps the area finite without ever being 0.

**Lean cross-check.** `problems/a01A01/lean/Main.lean` (no `sorry`): the
one-dimensional functions are `apm_a01A01_typewriter1d` (closed intervals
`Icc`, height `Real.sqrt` of the stage; Lean lists the intervals through the pairing
`Nat.unpair` rather than block by block, but each stage still contains every
interval of its sweep exactly once); the ℝ^d functions are
`apm_a01A01_typewriterEuclidean`, a product of `apm_a01A01_typewriterLine` in
the first coordinate with `Real.exp (-t ^ 2)` in the others. The limsup is
stated in the equivalent form ∀ M N, ∃ k ≥ N, M ≤ f_k(x).

## Next

- Read about ten more problems across a, b, m and t and extend the list of
  kinds of unclarity.
- Fold the verified source notes into the Sources section.
- Presentation order, as a separate note.
