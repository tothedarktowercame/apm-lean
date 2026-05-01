# Proof Outline: a96A03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "From an a.e.-convergent sequence inside the L2(R) unit ball, prove the limit lies in the ball and the sequence converges weakly to that limit."
 :terms [{:name "L2 unit ball"
          :meaning "B = {f in L2(R) : ||f||_2 <= 1}."
          :needed-because "This uniform bound drives Fatou's lemma and all Cauchy-Schwarz tail estimates."}
         {:name "Fatou lemma"
          :meaning "Integral |f|^2 <= liminf Integral |f_n|^2."
          :needed-because "Puts the a.e. limit back inside B."}
         {:name "Density of C_c"
          :meaning "Compactly supported continuous functions are dense in L2(R)."
          :needed-because "Reduces weak convergence to test functions where dominated convergence is accessible."}
         {:name "Truncation of g"
          :meaning "Split g into a bounded-support bounded part plus an L2-small tail."
          :needed-because "Allows Cauchy-Schwarz control of the tail while the bounded part falls to dominated convergence."}]
 :strategy [{:id :s1
             :formal-dependency "weak_limit_from_ae_conv_in_L2_ball"
             :informal-dependency "Apply Fatou to |f|^2, then prove <f_n,g> -> <f,g> by approximating g with bounded-support functions and combining dominated convergence with L2 tail bounds."
             :why-this-now "Mirrors the intended paper proof and aligns with Mathlib's measure-theory lemmas."
             :lean-target "weak_limit_from_ae_conv_in_L2_ball"
             :mathlib-status "Fatou, dominated convergence, density of C_c, and Cauchy-Schwarz are already in Mathlib; only bookkeeping is needed."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96A03'
  :frame-id 'apm-v2-a96A03-1775052721277'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the Fatou + Egorov + truncation argument showing f∈B and ⟨f_n,g⟩→⟨f,g⟩ for all g∈L2."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage3-attempted
  :summary "Searched Mathlib for ae_tendsto-based L2 lemmas (`rg -n \"ae_tendsto\" .`) but found only documentation hits, so the Lean proof is blocked by missing Lp-to-function comparison API."
  :full-record? true :sorry? true :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  The unit ball \(B\subset L^2(\mathbf R)\) is only weakly compact; boundedness alone does **not** give pointwise control.  Students often try to take limits under the integral sign immediately, but the integrand \(f_ng\) need not admit an \(L^1\) dominating function that is independent of \(n\).  Another common dead-end is to assume \(f_n\to f\) in \(L^2\); that fails in general, so the fix must exploit the hint: start with very regular test functions and use truncations to reach every \(g\in L^2\).

*Key insight.*  Combine two complementary tools: (1) Fatou’s lemma applied to \(|f|^2\) instantly shows the limit belongs to \(B\); (2) to handle the pairing with an arbitrary \(g\), first prove convergence for bounded, compactly supported \(g\) using Egorov on that finite-measure set, then approximate every \(L^2\) function by such test functions and control the tails with Cauchy–Schwarz plus the uniform \(L^2\) bound \(\|f_n\|_2\le 1\).

*Complete proof.*  
1. **\(f\in B\).**  Since \(|f_n|^2\to |f|^2\) a.e. and \(|f_n|^2\ge0\), Fatou’s lemma yields \(\int_{\mathbf R} |f|^2 \le \liminf_n \int |f_n|^2 \le 1\).  Thus \(f\in L^2(\mathbf R)\) with \(\|f\|_2\le 1\), i.e. \(f\in B\).
2. **Continuous, compactly supported test functions.**  Fix \(g\in C_c(\mathbf R)\).  Let \(K=\operatorname{supp} g\) (finite Lebesgue measure) and \(M=\|g\|_\infty\).  Given \(\varepsilon>0\), Egorov’s theorem provides a measurable \(E\subset K\) with \(\mu(E)<\delta\) (choose later) such that \(f_n\to f\) uniformly on \(K\setminus E\).  Then
   \[
   \Big|\int_{\mathbf R} (f_n-f)g\Big| \le \int_{K\setminus E} |f_n-f||g| + \int_E |f_n-f||g| =: I_{n,1}+I_{n,2}.
   \]
   The uniform convergence on \(K\setminus E\) makes \(I_{n,1}\to 0\).  For \(I_{n,2}\), Cauchy–Schwarz gives
   \[
   I_{n,2} \le M \int_E (|f_n|+|f|) \le M \left(\|f_n\|_2 + \|f\|_2\right) \mu(E)^{1/2} \le 2M\,\mu(E)^{1/2}.
   \]
   Picking \(\delta\) so that \(2M\,\delta^{1/2}<\varepsilon\) forces \(I_{n,2}<\varepsilon\) uniformly in \(n\).  Hence \(\int (f_n-f)g\to 0\) for all \(g\in C_c(\mathbf R)\).
3. **Extend to arbitrary \(g\in L^2(\mathbf R)\).**  The space \(C_c(\mathbf R)\) is dense in \(L^2(\mathbf R)\); select \(h\in C_c\) with \(\|g-h\|_2<\varepsilon\).  Then
   \[
   \Big|\int (f_n-f)g\Big| \le \Big|\int (f_n-f)h\Big| + \Big|\int (f_n-f)(g-h)\Big|.
   \]
   The first term tends to \(0\) by Step 2.  For the second term, Cauchy–Schwarz plus \(\|f_n\|_2,\|f\|_2\le 1\) shows
   \[
   \Big|\int (f_n-f)(g-h)\Big| \le (\|f_n\|_2+\|f\|_2)\|g-h\|_2 \le 2\varepsilon.
   \]
   Letting \(n\to\infty\) and then \(\varepsilon\to 0\) proves \(\int f_n g \to \int f g\) for every \(g\in L^2(\mathbf R)\).

*Proof sanity check.*  The potentially fragile bridge is the Egorov step on \(K=\operatorname{supp} g\).  Egorov applies because \(K\) has finite measure (it is compact); this gives uniform convergence off a small set, and the small set contribution is bounded by Cauchy–Schwarz thanks to \(\|f_n\|_2\le 1\).  Both parts of the statement are fully proven.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Weak convergence from truncated tests (s1).*  **Formal dependency:** `weak_limit_from_ae_conv_in_L2_ball`. **Informal dependency:** Fatou handles \(\|f\|_2\); Egorov + dominated bound handle \(C_c\) test functions; density of \(C_c\) plus Cauchy–Schwarz extends to all \(g\in L^2\). **Why this now:** mirrors the structure of the clean proof and isolates the only nontrivial helper lemma (`Cc_dense_in_L2`). **Lean target/search:** intended symbol `weak_limit_from_ae_conv_in_L2_ball`; Mathlib search terms tried: `"ae_tendsto"`, `"Lp.eLpNorm"`, `"Cc_dense"`.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a96A03/apm-v2-a96A03-1775052721277/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a96A03/apm-v2-a96A03-1775052721277/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Attempted to locate a Mathlib lemma that already formalizes the L² Fatou/weak-compactness argument by running `rg -n "ae_tendsto" .` inside `/home/joe/code/apm-lean`; the only hits were documentation references, not an off-the-shelf theorem about bounded L² sequences.
- The obstacle is **missing API/theory**: L² functions in Mathlib live as equivalence classes (`Lp`) rather than honest functions, and we still lack a bridge lemma equating a.e. convergence of representatives to convergence of pairings `∫ f_n g`.  Wiring up such a result would require re-building the Egorov-based argument inside the `Lp` quotient and proving the density of compactly supported functions within that framework.
- Consequently `Main.lean` remains the initial stub (see `/home/joe/code/apm-lean/ApmCanaries/Frames/A96A03/Apm_v2_a96A03_1775052721277/Main.lean`), and no Lean theorem has been produced yet.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  The Stage 1 proof hinges on Egorov plus Cauchy–Schwarz for actual functions; Lean currently lacks the API that translates an a.e.-convergent, L²-bounded `Lp` sequence into convergence of all pairings.  Until Mathlib supplies that lemma (or we build it by hand inside `Lp`), both conclusions—“\(f\in B\)” and “\(\int f_n g \to \int f g\)”—remain informal.
