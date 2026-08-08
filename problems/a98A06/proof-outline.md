# Proof Outline: a98A06

## Closer hop 1 completion

The theorem is closed without changing its statement.  Set `g z = z * f z`.
On the neighborhood supplied by the hypothesis, its norm is bounded by
`|C| * sqrt ‖z‖`, so `squeeze_zero'` proves that `g` is continuous at zero.
It is differentiable on the punctured plane, hence
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
makes it analytic at zero and therefore entire.  Finally `dslope g 0` is
entire by `Complex.differentiableOn_dslope`, and away from zero its defining
difference quotient simplifies to `f`.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that an analytic f on C\\{0} whose weighted modulus |f(z)||z|^{1/2} stays bounded near 0 extends holomorphically across 0."
 :terms [{:name "bounded product"
          :meaning "From |f(z)||z|^{1/2} <= C on a punctured disc we get |z f(z)| <= C r^{1/2} for |z|<r."
          :needed-because "Producing a bounded holomorphic function on the punctured disc lets us invoke Riemann's removable theorem."}
         {:name "Riemann removable singularity theorem"
          :meaning "Any holomorphic function on a punctured disc that is bounded extends holomorphically over the centre."
          :needed-because "Apply it to g(z)=z f(z) to build an analytic extension G with G(0)=0."}
         {:name "zero factoring / analytic division"
          :meaning "If G is analytic and G(0)=0 then G(z)=z*H(z) with H analytic."
          :needed-because "Defining H(0)=G'(0) yields the desired extension of f."}]
 :strategy [{:id :s1
             :formal-dependency "riemannRemovable"
             :informal-dependency "Bound g(z)=z f(z) on a small punctured neighbourhood"
             :why-this-now "Once g is bounded, the removable-singularity theorem gives an analytic G with G=z f on punctured disc."
             :lean-target "extend_z_mul_f"
             :mathlib-status "Available in Mathlib as `IsHolomorphic.bounded_implies_removable`. "}
            {:id :s2
             :formal-dependency "analytic_division_by_z"
             :informal-dependency "Output of :s1 (extension for zf with zero at 0)"
             :why-this-now "Factor the zero to define H so that H=z^{-1}G agrees with f away from 0, showing f extends analytically."
             :lean-target "extend_f_via_factor"
             :mathlib-status "Mathlib supports factoring zeros through `HasFPowerSeriesAt`. "}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a98A06'
  :frame-id 'apm-v2-a98A06-1775004274108'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the reader-facing proof with the weighted-bound trick and clarified why the bound on z f(z) forces the limit zero."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the dependency chain (bounded product → removable theorem → dslope division) and mapped it to Lean targets."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Implemented the bounding and extension lemmas in Scratch; final Lean glue (dslope EqOn and lake build) still pending."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it's hard.*  The hypothesis only controls the weighted product \(|f(z)||z|^{1/2}\) near the puncture.  Students often try to apply Riemann's theorem directly to \(f\), but that requires \(|f|\) to be bounded, not \(|f||z|^{1/2}|\.  The real trick is to modify \(f\) so that the weight becomes an honest bound that decays at the puncture; without that observation one keeps running into diverging estimates.

*Key insight.*  Multiply by a single power of \(z\).  The function \(g(z)=z\,f(z)\) is analytic on the punctured disc, and the weighted bound implies \(|g(z)| \le C\,|z|^{1/2}\).  Hence \(g\) is actually bounded (and even tends to zero) on a small punctured neighbourhood, so Riemann's theorem extends \(g\) across the origin.  The quotient \(g(z)/z\) is then analytic because \(g\) vanishes at \(0\), so it extends \(f\).

*Complete proof.*  Let \(N\) be an open neighbourhood of \(0\) on which \(|f(z)||z|^{1/2} \le C\).  Choose \(r>0\) such that the closed disc \(\overline{B}(0,r)\) lies inside \(N\).  On \(\overline{B}(0,r)\setminus\{0\}\) define \(g(z)=z f(z)\); then
\[
|g(z)|=|z|\,|f(z)|=\bigl(|f(z)||z|^{1/2}\bigr)|z|^{1/2}\le C\,r^{1/2}.
\]
Thus \(g\) is bounded on the punctured disc, so by Riemann's removable singularity theorem it extends to an analytic function \(G\) on \(\overline{B}(0,r)\).  The above estimate shows \(G(0)=\lim_{z\to 0}g(z)=0\).

Now set \(F(z)=\frac{G(z)-G(0)}{z-0}\) for \(z\ne 0\) and \(F(0)=G'(0)\); this is the standard "difference quotient" (the `dslope` of Mathlib) of \(G\) at \(0\), hence it is analytic on \(B(0,r)\).  For \(0<|z|<r\) we have
\[
F(z)=\frac{G(z)-0}{z}=\frac{z f(z)}{z}=f(z),
\]
so \(F\) extends \(f\) across the origin.  Therefore \(f\) has a removable singularity at \(0\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Weighted bound ⇒ bounded product.*  From \(|f(z)||z|^{1/2}|\le C\) on a small disc we deduce that \(g(z)=z f(z)\) is bounded there.  This supplies the hypothesis for Riemann's removable-singularity theorem.  (Lean target: `bound_z_mul`.)
2. *Riemann's theorem for \(g\).*  Apply Mathlib's `Complex.differentiableOn_update_limUnder_of_bddAbove` to extend \(g\) across the origin, obtaining an analytic \(G\) with \(G(0)=0\).  (Lean target: `extend_z_mul_f`.)
3. *Divide by \(z\).*  Analytic functions that vanish at a point admit a derivative-style quotient (Mathlib's `dslope`).  Using `Complex.differentiableOn_dslope`, we conclude that \(F(z)=dslope\,G\,0\) is analytic on the disc and satisfies \(F=g/z=f\) off the origin.  (Lean target: `extend_f_via_dslope`.)

**Stage 3 — LEAN FORMALIZATION**

Files touched: `ApmCanaries/Frames/A98A06/Apm_v2_a98A06_1775004274108/Main.lean` and its scratch sibling.

Plan:
- Encode the local hypothesis as the existence of \(r>0\) and \(C\ge 0\) with \(|f(z)||z|^{1/2}|\le C\) for \(|z|<r\).
- Define \(g(z)=z f(z)\) and prove it is holomorphic on the punctured ball plus bounded there; package this as `holomorphicOn_zmul` together with a `BddAbove` witness.
- Invoke `Complex.differentiableOn_update_limUnder_of_bddAbove` on the closed ball to extend \(g\) to an analytic \(G\); prove separately (using the weight bound) that the limiting value is zero.
- Use `Complex.differentiableOn_dslope` to turn \(G\) into the desired extension of \(f\), and finish with an `EqOn` statement.

Current status: tactics compiled and the scaffolding lemmas (`bound_z_mul`, `extend_z_mul_f`) are drafted in `Scratch.lean`, but the final combination still needs polishing before we can run `lake build`.  No `sorry` blocks have been merged into `Main.lean` yet; Stage 3 remains **in progress** while we finish the boundedness and dslope glue.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The analytic extension produced in Lean is exactly the dslope of the bounded extension of \(z f(z)\), so the informal proof emphasises the same structure: manufacture a bounded holomorphic function, extend it, then divide by \(z\).  The key caution for readers is to check that the extension actually vanishes at the origin; once that is noted, both the textbook argument and the Lean development collapse to the same two-line calculation.
