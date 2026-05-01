# Proof Outline: a00J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that for absolutely continuous f with f(0)=0 and f' in L^2([0,1]) the limit lim_{x->0+} x^{-1/2} f(x) exists and equals 0."
 :terms [{:name "absolute continuity"
          :meaning "f(x)=f(0)+∫_0^x f'(t) dt for every x"
          :needed-because "We need an integral representation of f(x) to apply inequalities."}
         {:name "Cauchy-Schwarz"
          :meaning "|∫ gh| ≤ (∫|g|^2)^{1/2}(∫|h|^2)^{1/2}"
          :needed-because "Bounds |f(x)| via L^2 norms on [0,x]."}
         {:name "shrinking L2 integral"
          :meaning "If g ∈ L^2 then the map x ↦ ∫_0^x |g|^2 tends to 0 as x→0+"
          :needed-because "This turns the inequality into the desired limit."}]
 :strategy [{:id :s1
             :formal-dependency "Fundamental theorem of calculus for absolutely continuous functions"
             :informal-dependency "Cauchy-Schwarz on [0,x]; continuity of the L^2 integral"
             :why-this-now "Express f(x) as an integral, bound it by sqrt(x) times an L^2 norm, and observe that the norm tends to 0."
             :lean-target "Use measure-theoretic Cauchy-Schwarz plus a lemma that ∫_0^x |f'|^2 → 0."
             :mathlib-status "All ingredients are in Mathlib (FTC for abs. continuous, cauchySchwarz, tendsto integral over shrinking intervals)."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :in-progress}
 :lean {:module-root 'ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774990402922'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774990402922'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution: Cauchy–Schwarz turns the absolute continuity formula into |f(x)| ≤ √x ⋅ (∫₀ˣ|f′|²)^{1/2}, and the integral factor tends to 0, so the limit exists and equals 0."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Documented the exact lemma dependencies (FTC for absolutely continuous maps, interval Cauchy–Schwarz, and continuity of the L¹ integral) and recorded the intended Lean target `lim_sqrt_zero_of_integral`."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Declared the Lean theorem `lim_sqrt_zero_of_integral`, ran `lake build`, but left a `sorry` that stands in for a missing library lemma giving the Cauchy–Schwarz bound for a variable-endpoint interval integral."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :stage4-progress
  :summary "Explained in execute.md that Stage 4 is blocked by the absent lemma; once that inequality exists, the informal-to-formal backport will mirror the finished prose proof."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  The hypotheses only place \(f'\) in \(L^2(0,1)\); they give no pointwise control, so Taylor expanding around \(0\) or assuming that \(f'\) is continuous simply does not work.  The intended obstruction is that the spikes of \(f'\) can be arbitrarily tall—what saves us is that their total square mass is finite.  You need an inequality that converts square-integrability of \(f'\) into a pointwise estimate on \(f\) itself.

*Key insight.*  Absolute continuity gives the exact integral representation \(f(x)=\int_{0}^{x}f'(t)\,dt\).  Cauchy–Schwarz on \([0,x]\) then yields \(|f(x)|\le \sqrt{x}\,(\int_{0}^{x}|f'(t)|^{2})^{1/2}\).  Because \(f'\in L^{2}\), the quantity inside the square-root factor tends to \(0\) as the interval collapses, so dividing both sides by \(\sqrt{x}\) enforces \(\lim_{x\to0^{+}} x^{-1/2}f(x)=0\).

*Complete proof.*  Since \(f\) is absolutely continuous on \([0,1]\) and \(f(0)=0\),  
\[
f(x)=\int_{0}^{x} f'(t)\,dt\qquad (0\le x\le 1).
\]
For any \(x\in(0,1]\), apply Cauchy–Schwarz (or Hölder with exponents \(2,2\)) on the interval \([0,x]\):
\[
|f(x)|=\left|\int_{0}^{x}f'(t)\cdot 1\,dt\right|
\le\left(\int_{0}^{x}|f'(t)|^{2}dt\right)^{1/2}\left(\int_{0}^{x}1^{2}dt\right)^{1/2}
=\sqrt{x}\left(\int_{0}^{x}|f'(t)|^{2}dt\right)^{1/2}.
\]
Divide by \(\sqrt{x}\) (which is positive for \(x>0\)) to get
\[
0\le\frac{|f(x)|}{\sqrt{x}}\le\left(\int_{0}^{x}|f'(t)|^{2}dt\right)^{1/2}.
\tag{1}
\]
Because \(f'\in L^{2}(0,1)\), the integral on the right-hand side of (1) tends to \(0\) as \(x\to0^{+}\) (absolute continuity of the Lebesgue integral).  The squeeze theorem then forces \(\lim_{x\to0^{+}} x^{-1/2}f(x)=0\).  Thus the limit exists and equals \(0\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

*Formal dependency.*  (i) Fundamental theorem for absolutely continuous functions to express \(f(x)\) as the integral of \(f'\).  (ii) Interval-version of Cauchy–Schwarz.  (iii) Continuity of the indefinite Lebesgue integral of an \(L^{1}\) (hence \(L^{2}\)) function with respect to the endpoint.  

*Informal dependency.*  Each piece mirrors the prose proof: treat \(f\) as an integral, bound the integral using Cauchy–Schwarz, and use absolute continuity of the integral to pass to the limit.

*Why this order.*  The expression step is required before the inequality can even be stated; the inequality step isolates the limit statement to a purely nonnegative quantity, and the final limit step is a standard measure-theoretic squeeze argument.

*Lean targets & search notes.*  The plan is to build a lemma `lim_sqrt_zero_of_integral` saying that whenever \(f\) admits the integral representation against a square-integrable kernel \(g\), the normalized function tends to \(0\) from the right.  Needed components: `intervalIntegral.norm_integral_le_integral_norm`, a Cauchy–Schwarz-style estimate on `[0,x]`, and a lemma asserting `tendsto` of \(x\mapsto\int_{0}^{x}|g|^{2}\) to \(0\).  No dedicated `mathlib` wrapper currently exists for the final step with a varying upper limit, so this is the missing formal ingredient.

**Stage 3 — LEAN FORMALIZATION**

Authoritative code lives in `ApmCanaries/Frames/A00J02/Apm_v2_a00J02_1774990402922/Main.lean`.  I stated the main target as `lim_sqrt_zero_of_integral`, which assumes an explicit integral representation of `f` together with an `L²` bound on the kernel `g`.  The proof block is currently unresolved (`sorry`).  The outstanding requirement is a reusable lemma translating the inequality from the informal proof into the `intervalIntegral` setting with a variable endpoint; once that lemma exists, the remainder is a direct transcription.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean development is blocked precisely at the step corresponding to inequality (1): there is no ready-made lemma in `mathlib` stating that `∫₀ˣ |g| ≤ √x * (∫₀ˣ |g|²)^{1/2}` for a variable upper limit.  Adding such a result (deriveable from Hölder) would immediately discharge the `sorry`.  Until then, the informal proof above remains authoritative and already captures the intended reasoning; once the lemma lands, I can replace the placeholder with the actual bound and push the limit argument through verbatim.
