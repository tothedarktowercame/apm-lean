# Proof Outline: a93A03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that weak convergence plus norm convergence forces strong convergence, and deduce the liminf inequality for norms in a Hilbert space."
 :terms [{:name "weak convergence"
          :meaning "⟪h_n, k⟫ → ⟪h, k⟫ for every k ∈ H."
          :needed-because "Gives control of inner products needed to expand ‖h_n - h‖²."}
         {:name "polarization / parallelogram identity"
          :meaning "Express ‖u-v‖² in terms of norms and inner products."
          :needed-because "Allows turning weak convergence of inner products plus norm limits into norm differences."}
         {:name "liminf inequality"
          :meaning "Take liminf on both sides of nonnegative expressions to relate ‖h‖² to liminf ‖h_n‖²."
          :needed-because "Part (b) follows from the inequality derived in (a) without assuming norm convergence."}]
 :strategy [{:id :s1
             :formal-dependency "`InnerProductSpace` identities for norms"
             :informal-dependency "Stage 1 expression of ‖h_n - h‖²"
             :why-this-now "Prove (a) by expanding ‖h_n - h‖² = ‖h_n‖² + ‖h‖² - 2 Re⟪h_n,h⟫ and taking limits."
             :lean-target "weakConvergence_norm_eq_strong"
             :mathlib-status "All ingredients exist: `norm_sq_eq_inner`, weak convergence definition, limit lemmas."}
            {:id :s2
             :formal-dependency "Fatou-type inequality for liminf with nonnegative sequences"
             :informal-dependency "Stage 1 bound 0 ≤ ‖h_n‖² - 2 Re⟪h_n,h⟫ + ‖h‖²"
             :why-this-now "Derive (b) by taking liminf on inequality from (a) without norm convergence hypothesis."
             :lean-target "weakConvergence_norm_le_liminf"
             :mathlib-status "Need existing lemmas about liminf ≥ limit of infima; standard in Mathlib for real sequences."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a93A03'
  :frame-id 'apm-v2-a93A03-1775002487121'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the reader-facing solution, highlighting polarization identity and weak lower semicontinuity."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured lemma dependencies and Lean targets for parts (a) and (b)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean strategy; still need to mechanize polarization identity and liminf argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* Weak convergence only controls inner products, not norms. Students often misremember that weak convergence is “almost” strong convergence and try to interchange limits inside ‖·‖. The trap is forgetting that without norm control there is no reason for ‖h_n‖ to approach ‖h‖; conversely, even with norm convergence one must still exhibit a quantitative estimate, not just quote general Banach-space lore.

*Key insight.* Expand the square of the difference by the polarization identity:
\[
\|h_n-h\|^2 = \|h_n\|^2 + \|h\|^2 - 2\operatorname{Re}\langle h_n,h\rangle.
\]
Weak convergence pins down the mixed inner product, so if the norms also converge then every term on the right has a limit and the left forces \(\|h_n-h\|\to 0\). Dropping the norm-convergence hypothesis while keeping the nonnegativity of the left-hand side yields \(\|h\|^2 \le \liminf \|h_n\|^2\), i.e. the lower semicontinuity of the norm with respect to weak convergence.

*Complete proof.* Let \((h_n)\) converge weakly to \(h\) in a Hilbert space \(H\).

(a) Suppose additionally that \(\|h_n\|\to \|h\|\). For every \(n\), the polarization identity gives
\[
\|h_n-h\|^2 = \|h_n\|^2 + \|h\|^2 - 2\operatorname{Re}\langle h_n,h\rangle.
\]
By weak convergence, \(\langle h_n,h\rangle \to \langle h,h\rangle = \|h\|^2\). By hypothesis, \(\|h_n\|^2\to\|h\|^2\). Taking limits in the displayed identity yields \(\lim_{n\to\infty}\|h_n-h\|^2 = 0\), hence \(\|h_n-h\|\to 0\).

(b) For each \(n\) the same identity implies the nonnegative inequality
\[
0 \le \|h_n-h\|^2 = \|h_n\|^2 + \|h\|^2 - 2\operatorname{Re}\langle h_n,h\rangle.
\]
Rearranging and taking \(\liminf\) on both sides gives
\[
\|h\|^2 \le \liminf_{n\to\infty} \bigl(2\operatorname{Re}\langle h_n,h\rangle - \|h_n\|^2\bigr) + \liminf_{n\to\infty}\|h_n\|^2.
\]
Because \(\operatorname{Re}\langle h_n,h\rangle\to\|h\|^2\), the first term on the right tends to \(2\|h\|^2 - \limsup\|h_n\|^2\), and the inequality simplifies to
\[
\|h\|^2 \le \liminf_{n\to\infty} \|h_n\|^2.
\]
Taking square roots preserves the inequality (all norms are nonnegative), yielding \(\|h\| \le \liminf \|h_n\|\).

*What connects.* These arguments are the Hilbert-space versions of general Banach-space facts: norms are weakly lower semicontinuous, and equality of norms together with weak convergence forces strong convergence (often called the Kadec–Klee property) in uniformly convex spaces. The same estimates power exam staples like showing that the projection onto a closed convex set exists (via minimizing \(\|x-h\|\)), or proving the Banach–Saks property. Keep the polarization identity handy on prelims; it linearizes norm questions into inner-product limits.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Node:* Weak convergence definition → *Needs:* Basic Hilbert inner product continuity to justify \(\langle h_n,h\rangle\to\langle h,h\rangle\). *Lean target:* reuse `WeaklyConvergentSeq`.
- *Node:* Polarization identity → *Needs:* `norm_sq_eq_inner`. *Why now:* rewrites \(\|h_n-h\|^2\) to expose convergent pieces.
- *Node:* Limit/liminf bookkeeping → *Needs:* Facts that limits distribute over sums and nonnegative sequences satisfy Fatou’s lemma. *Lean target:* use `tendsto_add`, `liminf_le_limsup`, `Real.sqrt_le_sqrt`. Search terms: `norm_sq_eq_inner`, `weak_tendsto`, `liminf_le_iff`.

**Stage 3 — LEAN FORMALIZATION**

Plan: formalize weak convergence as `WeaklyConvergentSeq hₙ h := ∀ k, Tendsto (fun n => ⟪hₙ n, k⟫_ℝ) atTop (𝓝 ⟪h, k⟫)`. Step (a) becomes `lemma weakConvergence_norm_eq_strong`. After unfolding, combine `norm_sq_eq_inner` with limit rules and the hypothesis `Tendsto (fun n => ‖hₙ n‖)`. For (b), start with `have hineq : 0 ≤ ‖hₙ n - h‖^2` and rewrite it as a real inequality; convert to a nonnegative real sequence and apply Fatou’s lemma / liminf properties. Mathlib already contains weak lower semicontinuity lemmas for Hilbert spaces; if a gap appears, recast liminf as an infimum over tails and use `IsLUB`. Main technical burden: juggling coercions between ℝ and ℂ via `IsROrC`, and invoking `IsROrC.reCLM` when extracting real parts.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof reconstructs (a) and (b), back-port two remarks: (1) the polarization identity is the sole structural input — no compactness or reflexivity sleight-of-hand — highlighting why Hilbert geometry matters; (2) the lower semicontinuity argument is an explicit Fatou application on the nonnegative sequence \(\|h_n-h\|^2\). These comments keep the prose synced with the mechanized certificate and point readers to reusable tactics for other weak/strong convergence problems.
