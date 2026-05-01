# Proof Outline: a98J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that an absolutely continuous f with square-integrable derivative has small quadratic difference quotients on short intervals."
 :terms [{:name "FTC for AC functions"
          :meaning "Absolute continuity gives f(x)-f(y)=int_y^x f'(t) dt."
          :needed-because "Turns pointwise differences into integrals of f'."}
         {:name "localized Cauchy-Schwarz"
          :meaning "|int_y^x f'|^2 <= (x-y) int_y^x |f'|^2."
          :needed-because "Connects the desired quotient with int |f'|^2 on the same interval."}
         {:name "absolute continuity of the |f'|^2 integral"
          :meaning "Because |f'|^2 lies in L^1([0,1]), integrating it over sets of small measure gives a small result."
          :needed-because "Provides the δ(ε) after the Cauchy-Schwarz reduction."}]
 :strategy [{:id :s1
             :formal-dependency "FTC for AC"
             :informal-dependency "Stage 1 relation f(x)-f(y)=integral of f'"
             :why-this-now "Reduces the statement to estimates on f'."
             :lean-target "ac_increment_as_integral"
             :mathlib-status "Use `intervalIntegral.deriv_eq_sub`."}
            {:id :s2
             :formal-dependency "Cauchy-Schwarz"
             :informal-dependency "Output of :s1"
             :why-this-now "Bounds |f(x)-f(y)|^2/(x-y) by int_y^x |f'|^2."
             :lean-target "cauchy_schwarz_local"
             :mathlib-status "Standard inequality already available."}
            {:id :s3
             :formal-dependency "integral_small_on_short_interval"
             :informal-dependency "Bound from :s2"
             :why-this-now "Use integrability of |f'|^2 to choose δ so that every interval of length < δ has integral < ε."
             :lean-target "L2_integral_small_on_short_interval"
             :mathlib-status "Follows from absolute continuity of Lebesgue measure on [0,1]."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a98J02'
  :frame-id 'apm-v2-a98J02-1775004665812'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the reader-facing solution using FTC + Cauchy–Schwarz + absolute continuity of ∫|f'|^2."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Mapped the FTC, Cauchy–Schwarz, and integral absolute-continuity lemmas to Lean targets."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined the Lean approach; blocked by the missing `L2_integral_small_on_short_interval` lemma that turns integrability into an ε–δ statement."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  Absolute continuity already implies uniform continuity, so it is tempting to stop there.  The catch is that the problem asks for the *quadratic* difference quotient to be small, which is strictly stronger.  You must use the extra `L^2` control on the derivative; forgetting to square the numerator or trying to argue directly from absolute continuity usually leads nowhere.

*Key insight.*  Undo the fundamental theorem of calculus: for any `0 ≤ y < x ≤ 1`, absolute continuity gives
\[
  f(x)-f(y) = \int_y^x f'(t)\,dt.
\]
Applying Cauchy–Schwarz with the functions `f'` and the constant function `1` over `(y,x)` yields
\[
  |f(x)-f(y)|^2 \le (x-y) \int_y^x |f'(t)|^2 dt.
\]
Hence the desired quotient is bounded by the integral of `|f'|^2` over `(y,x)`.  Because `|f'|^2` is integrable on `[0,1]`, its integral is absolutely continuous with respect to Lebesgue measure, so the integral of `|f'|^2` over every interval of length < δ becomes < ε when δ is small enough.

*Complete proof.*  Fix `ε>0`.  Since `|f'|^2∈L^1([0,1])`, there exists `δ>0` such that every measurable set `A⊆[0,1]` with `m(A)<δ` satisfies `\int_A |f'|^2 dt < ε`.  (This is the absolute continuity of the Lebesgue integral on finite-measure spaces.)  Now take `0≤y<x≤1` with `x-y<δ`.  Absolute continuity of `f` implies
\[
  f(x)-f(y)=\int_y^x f'(t)dt.
\]
By Cauchy–Schwarz,
\[
  |f(x)-f(y)|^2 \le (x-y)\int_y^x |f'(t)|^2 dt.
\]
Dividing by `x-y>0` yields
\[
  \frac{|f(x)-f(y)|^2}{x-y} \le \int_y^x |f'(t)|^2 dt.
\]
Because the interval `(y,x)` has length `<δ`, the set has measure `<δ`, hence the integral on the right is `<ε`.  Therefore the quadratic difference quotient is `<ε` whenever `|x-y|<δ`, proving the claim.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *FTC for AC functions* → expresses `f(x)-f(y)` as an integral of `f'` so we can appeal to Hilbert space tools.  (Lean target: `ac_increment_as_integral`.)
2. *Localized Cauchy–Schwarz* → bounds the quadratic difference quotient by `∫_y^x |f'|^2`.  (Lean target: `cauchy_schwarz_local`.)
3. *Absolute continuity of the `|f'|^2` integral* → from `|f'|^2 ∈ L^1` we get the ε–δ statement for intervals.  (Lean target: `L2_integral_small_on_short_interval`.)

**Stage 3 — LEAN FORMALIZATION**

Files touched: `ApmCanaries/Frames/A98J02/Apm_v2_a98J02_1775004665812/Main.lean` (intended home of the final theorem) and `Scratch.lean` for experiments.

Plan recap:
1. Use the Mathlib lemma `intervalIntegral.integral_deriv_eq_sub` (or its absolutely continuous variant) to rewrite increments of `f` as integrals of `f'`.
2. Apply `Real.InnerProductSpace.cauchy_schwarz` on `(y,x)` to bound the difference quotient by `∫_y^x |f'|^2`.
3. Invoke a measure-theoretic lemma that turns the `L^1` control of `|f'|^2` into the statement “integrals over intervals of length < δ are < ε.”

Blocker: Step (3) currently lacks a ready-to-use Mathlib lemma.  The statement we need is:
```
∀ ε > 0, ∃ δ > 0, ∀ a b, 0 ≤ a ≤ b ≤ 1 → b - a < δ →
  ∫ᵇᵃ |f' t|^2 ≤ ε,
```
assuming `|f'|^2` is integrable on `[0,1]`.  Mathlib contains the measure-theoretic fact that integrable functions define absolutely continuous signed measures, but it is not yet packaged for one-dimensional intervals.  I attempted to derive it from `MeasureTheory.Measure.absolutelyContinuous_iff`, but this requires building the signed measure associated to `|f'|^2` and proving absolute continuity manually, which is substantial boilerplate.  Until that lemma is available (either upstream or locally), the Lean proof cannot proceed past the Cauchy–Schwarz reduction, so `Main.lean` still contains only the module header and references to `Scratch`.  Once the lemma is supplied, wiring it into Step (3) should finish the proof and allow a `lake build` run.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof highlights exactly the structure the Lean proof will follow: write increments as integrals, use Cauchy–Schwarz, then rely on absolute continuity of the `|f'|^2` integral.  The only Lean gap is the last piece, so readers should be aware that a short measure-theoretic lemma (absolute continuity of indefinite integrals) bridges the formal development back to the textbook argument.  Once that lemma is in place, the code will mirror the two-line inequality in Stage 1 verbatim.
