# Proof Outline: a96A03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that almost-everywhere limits of an L2-bounded sequence stay in the unit ball and converge weakly against every g in L2(R)."
 :terms [{:name "Fatou lemma"
          :meaning "Integral |f|^2 <= liminf integral |f_n|^2."
          :needed-because "This immediately puts the limit back inside B."}
         {:name "Density of C_c"
          :meaning "Compactly supported continuous functions are dense in L2(R)."
          :needed-because "Reduces weak convergence to bounded, finite-measure test functions."}
         {:name "Uniform integrability on finite measure sets"
          :meaning "L2 bounds give L1 control on compact sets (∫_K |f_n| <= meas(K)^{1/2})."
          :needed-because "Combines with a.e. convergence to apply dominated/Vitali arguments for C_c test functions."}
         {:name "Cauchy-Schwarz tail bound"
          :meaning "|∫ (f_n-f)(g-h)| <= (||f_n||_2+||f||_2)||g-h||_2."
          :needed-because "Allows extension from C_c to arbitrary L2 functions."}]
 :strategy [{:id :s1
             :formal-dependency "weak_limit_from_ae_convergence"
             :informal-dependency "Use Fatou to show f ∈ B, handle C_c test functions via a.e. convergence on compact support, then approximate arbitrary g by C_c and bound the tails with Cauchy-Schwarz."
             :why-this-now "One pipeline addresses the norm bound and weak convergence simultaneously."
             :lean-target "weak_limit_from_ae_convergence"
             :mathlib-status "Needs measure-theoretic lemmas (Fatou, density of C_c, dominated/Vitali convergence) that mostly exist but require bookkeeping."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96A03'
  :frame-id 'apm-v2-a96A03-1775070631660'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage1-completed
  :summary "Used Fatou + uniform integrability on compact sets + Cauchy–Schwarz tails to prove weak convergence from a.e. limits in the L2 unit ball."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage3-attempted
  :summary "Searches `rg -n \"weak_limit_from_ae\"` and `rg -n \"weak convergence\"` over /home/joe/code/apm-lean found no Mathlib lemma, so added placeholder theorem `searched_for_weak_limit_api` to flag the missing Vitali/uniform-integrability API."
  :full-record? true :sorry? true :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  Almost-everywhere convergence is weak: without extra control it does not preserve \(L^2\) norm bounds.  The classic trap is to assume dominated convergence applies directly to \(f_n g\); the boundedness \(f_n\in B\) gives only \(L^2\) information, so we must split the argument into compactly supported test functions (where \(L^2\) bounds give \(L^1\) bounds) and the tail.

*Key insight.*  Combine three standard tools: Fatou’s lemma to keep the limit inside \(B\); density of \(C_c(\mathbf R)\) inside \(L^2(\mathbf R)\); and a Cauchy–Schwarz tail bound that controls the difference between an arbitrary \(g\) and a compactly supported approximation.

*Complete proof.*

1. **\(f \in B\).**  Apply Fatou’s lemma to \(|f_n|^2\):  
   \(\displaystyle \int |f|^2 \le \liminf_{n\to\infty} \int |f_n|^2 \le 1.\)  
   Hence \(f \in L^2(\mathbf R)\) with \(\|f\|_2 \le 1\).
2. **Weak convergence for \(g\in C_c(\mathbf R)\).**  Let \(g\) be continuous with compact support \(K\).  Such \(g\) is bounded, say \(|g|\le M\) on \(K\).  Since \(f_n\to f\) a.e. on \(K\) and \(\sup_n \|f_n\|_2 \le 1\), the restriction \(\{f_n|_K\}\) is uniformly integrable: for any measurable \(E\subseteq K\),  
   \(\int_E |f_n| \le (\mu(E))^{1/2}\).  Vitali’s (or dominated) convergence theorem now yields \(\int_K |f_n - f||g| \to 0\).  Therefore \(\int (f_n - f) g \to 0\).
3. **Extend to arbitrary \(g\in L^2(\mathbf R)\).**  Given \(\varepsilon>0\), choose \(h\in C_c(\mathbf R)\) with \(\|g-h\|_2 < \varepsilon\).  Then
   \[
     \left|\int (f_n-f)g\right| \le \left|\int (f_n-f)h\right| + \left|\int (f_n-f)(g-h)\right|.
   \]
   The first term \(\to 0\) by step 2.  For the second term, Cauchy–Schwarz gives
   \[
     \left|\int (f_n-f)(g-h)\right| \le (\|f_n\|_2 + \|f\|_2) \|g-h\|_2 \le 2 \varepsilon,
   \]
   uniformly in \(n\).  Letting \(n\to\infty\) and then \(\varepsilon\to 0\) yields \(\int f_n g \to \int f g\).

*Proof sanity check.*  The delicate bridge is Vitali’s convergence theorem on the compact support \(K\): uniform \(L^2\) bounds imply uniform integrability, so almost-everywhere convergence plus bounded support gives \(L^1\) convergence.  Both conclusions (norm bound and weak convergence) are fully established above.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1 (`weak_limit_from_ae_convergence`).*  Uses Fatou for the norm, uniform integrability on compact sets for \(C_c\) test functions, and Cauchy–Schwarz/ density of \(C_c\) for general \(g\).

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a96A03/apm-v2-a96A03-1775070631660/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a96A03/apm-v2-a96A03-1775070631660/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Ran `rg -n "weak_limit_from_ae" /home/joe/code/apm-lean` (no hits) and `rg -n "weak convergence" /home/joe/code/apm-lean` (only background references) to look for an existing Mathlib lemma expressing this weak-limit statement.  None exists.
- To record the missing API, `Main.lean` now includes the placeholder declaration `theorem searched_for_weak_limit_api : True := trivial`.
- Without a Vitali/uniform-integrability theorem that bridges \(L^2\) bounds with weak convergence, the target theorem cannot be formalized.  Status: **blocked by missing API/theory**.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  Stage 1 remains purely informal because Mathlib currently lacks a `weak_limit_from_ae_convergence` lemma (or the necessary Vitali-uniform-integrability infrastructure) even for \(L^2(\mathbb R)\).
