# Proof Outline: a94A01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Identify the limit of characteristic functions and describe when χ_{E_n} → χ_E in L^p."
 :terms [{:name "pointwise limit of indicators"
          :meaning "Since each f_n takes values in {0,1}, any pointwise limit belongs to {0,1}."
          :needed-because "Allows us to define the limiting set E = {x : f(x)=1}."}
         {:name "dominated convergence theorem"
          :meaning "Bounded convergence (|f_n g| ≤ |g|) gives limit of integrals."
          :needed-because "Yields part (b)."}
         {:name "symmetric difference"
          :meaning "‖χ_{E_n}-χ_E‖_p^p = μ(E_n Δ E)."
          :needed-because "Translates L^p convergence into measure conditions."}]
 :strategy [{:id :s1
             :formal-dependency "Pointwise limits of {0,1}-valued functions"
             :informal-dependency "Stage 1 definition of E"
             :why-this-now "Show f equals χ_E almost everywhere."
             :lean-target "limit_indicator_is_indicator"
             :mathlib-status "Mathlib already has measurability of indicator functions; need a lemma about eventual constant values."}
            {:id :s2
             :formal-dependency "Dominated convergence theorem"
             :informal-dependency "Stage 1 identification of f"
             :why-this-now "Derive convergence of integrals for every integrable g."
             :lean-target "indicator_integral_limit"
             :mathlib-status "DomConv exists; straightforward after measurability."}
            {:id :s3
             :formal-dependency "Symmetric-difference measure formula"
             :informal-dependency "Stage 1 expression for f"
             :why-this-now "Provide necessary/sufficient condition for L^p convergence."
             :lean-target "indicator_Lp_convergence"
             :mathlib-status "Need lemma ‖χ_A - χ_B‖_p^p = μ(A Δ B)."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a94A01'
  :frame-id 'apm-v2-a94A01-1775002871618'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full measure-theoretic argument and L^p criterion using symmetric differences."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Logged lemma dependencies (indicator limits, DCT, symmetric difference)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean tasks (ae-limit lemma, DCT application, L^p distance); code still pending."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The limit of characteristic functions can oscillate unless you check that the limit exists almost everywhere. Once you do, it’s tempting to assert that the limit is again an indicator, but you still have to produce the set, justify its measurability, and handle the “almost everywhere” caveat. For part (b), the subtlety is that the indicator sequence is only bounded in \(L^∞\), so you must use dominated convergence with an arbitrary integrable \(g\). Students also forget that \(L^p\) convergence of indicators is equivalent to the measure of the symmetric difference tending to zero; omitting that calculation loses the “necessary and sufficient” part.

*Key insight.* Define \(E = \{x : f(x)=1\}\). Because each \(f_n\) takes only the values \(0,1\), the pointwise limit \(f(x)\) also lies in \(\{0,1\}\). Therefore \(f = \chi_E\) almost everywhere. With \(|\chi_{E_n} g| ≤ |g|\) and \(g ∈ L^1\), dominated convergence yields \(\int g\chi_{E_n} \to \int g\chi_E\). Finally, \(\|\chi_{E_n} - \chi_E\|_p^p = \int |\chi_{E_n} - \chi_E|^p = \mu(E_n Δ E)\), so \(L^p\)-convergence holds iff the symmetric difference has measure going to zero.

*Complete proof.*
1. **Definition of the limit set.** Put \(E = \{x : f(x)=1\}\). Each \(f_n\) is measurable and takes only \(0\) or \(1\); hence the pointwise a.e. limit \(f\) is measurable and \(f(x) ∈ \{0,1\}\) almost everywhere. On the set where the limit exists, \(f(x)=1\) iff the sequence \(f_n(x)\) eventually equals 1, so \(f = \chi_E\) almost everywhere; measurability follows because \(f\) is measurable and \(E = f^{-1}(\{1\})\).
2. **Integral convergence.** Fix \(g ∈ L^1(\mathbf R)\). For every \(n\), \(|g(x) f_n(x)| ≤ |g(x)|\), and \(|g(x) f(x)| ≤ |g(x)|\). Since \(|g|\) is integrable and \(f_n→f\) pointwise a.e., dominated convergence gives \(\int g f_n → \int g f\), i.e. \(\int_{E_n} g → \int_E g\).
3. **\(L^p\) criterion.** For \(1≤p<∞\) we have
\[
\|\chi_{E_n}-\chi_E\|_p^p = \int |\chi_{E_n}-\chi_E|^p = \int |\chi_{E_n}-\chi_E| = \mu(E_n Δ E),
\]
because \(\chi_{E_n}-\chi_E\) takes values \(-1,0,1\). Thus \(\|\chi_{E_n}-\chi_E\|_p → 0\) iff \(\mu(E_n Δ E) → 0\). This gives necessary and sufficient conditions for \(L^p\)-convergence.

*What connects.* These facts are part of the general philosophy that pointwise limits of projection-valued random variables remain projection-valued. The symmetric-difference trick is ubiquitous: it is exactly the metric that makes \(L^p\) convergence of indicators equivalent to convergence in measure. This appears again in measure-theoretic topology (“metricizing convergence in measure”) and in probability (convergence of events). Dominated convergence with indicators is also a staple: whenever you have bounded characteristic functions multiplying an \(L^1\) function, DCT is the go-to tool.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Indicator limits:* need a lemma that a pointwise limit of \(\{0,1\}\)-valued functions is itself \(\{0,1\}\)-valued and measurable. *Lean target:* `limit_indicator_is_indicator`.
- *Dominated convergence:* requires measurability of \(g\chi_{E_n}\) and the domination \(|g\chi_{E_n}| ≤ |g|\). *Lean target:* `indicator_integral_limit`. Search terms: `tendsto_integral_of_dominated_convergence`.
- *Symmetric difference formula:* rely on \( \int |\chi_A-\chi_B| = μ(A Δ B) \). *Lean target:* `indicator_Lp_convergence`. Search terms: `indicator`, `measure_symmDiff`, `Lpnorm_sub`. 

**Stage 3 — LEAN FORMALIZATION**

Plan: encode sequences of measurable sets `Eₙ`; define `fₙ := Set.indicator (μ:=volume) Eₙ (fun _ => (1:ℝ))`. Prove `ae_limit_indicator`: if `Tendsto fₙ f` a.e., then `f = Set.indicator E`. For part (b), apply `tendsto_integral_of_dominated_convergence` with dominating function `|g|`. For the \(L^p\) criterion, prove the helper lemma `indicator_Lp_distance` showing `‖χ_{Eₙ}-χ_E‖_{L^p}^p = μ(Eₙ Δ E)`. Stage 3 remains in progress because these lemmas still need to be coded in `Main.lean`; no sorrys have been added yet.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After coding, cite the exact Mathlib lemmas used (especially the DCT statement and the symmetric-difference/L^p identity) so the write-up mirrors the formal certificate and flags any additional hypotheses (σ-finiteness of Lebesgue measure, etc.).
