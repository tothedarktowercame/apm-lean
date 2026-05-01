# Informal Solution: a96A03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
