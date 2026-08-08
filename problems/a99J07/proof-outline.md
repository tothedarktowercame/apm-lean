# Proof Outline: a99J07

## Closer hop 1 completion

The theorem is closed without changing its statement.  Compactness of the
closed unit disk supplies `BddAbove`, so `le_csSup` handles values inside the
disk.  A local maximum-modulus lemma chooses a maximum of a polynomial on the
closed disk; if the maximizer is interior,
`Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn` transports its norm
to the boundary point `1`.  For exterior `w`, apply this lemma to
`p.reflect N` at `⅟w`.  Mathlib's exact identity
`Polynomial.eval₂_reflect_mul_pow` identifies its boundary values with values
of `p` on the unit circle and rewrites the value at `⅟w` into
`p.eval w / w^N`, yielding the required estimate.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Bound |p(w)| in terms of the sup norm on the unit disk via the maximum modulus principle."
 :terms [{:name "unit-disk sup norm"
          :meaning "‖p‖_∞ = sup{|p(z)| : |z| ≤ 1}."
          :needed-because "Controls the values inside the unit disk directly."}
         {:name "reciprocal polynomial"
          :meaning "Define q(z)=z^N p(1/z), which is analytic on {|z|≤1}."
          :needed-because "Transfers information from the unit circle to the exterior region |w|>1."}
         {:name "maximum modulus principle"
          :meaning "The maximum of |q| on {|z|≤1} occurs on the boundary."
          :needed-because "Gives |q(z)| ≤ ‖p‖_∞ for |z|≤1, yielding the desired bound for |w|>1."}]
 :strategy [{:id :s1
             :formal-dependency "basic_sup_bound"
             :informal-dependency "Case |w| ≤ 1"
             :why-this-now "On the unit disk the inequality is immediate from the definition of ‖p‖_∞."
             :lean-target "abs_le_sup_on_unit_disk"
             :mathlib-status "Lemma exists for polynomials on compact sets."}
            {:id :s2
             :formal-dependency "reciprocal_polynomial_bound"
             :informal-dependency "Case |w|>1"
             :why-this-now "Consider q(z)=z^N p(1/z) and apply the maximum modulus principle on |z|≤1."
             :lean-target "polynomial_bound_outside_unit_disk"
             :mathlib-status "Requires setting up q and using `Complex.polynomial_maxmod`."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a99J07'
  :frame-id 'apm-v2-a99J07-1775005157308'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the max-modulus proof and detailed the reciprocal-polynomial trick in Stage 1/2."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean approach; blocked on lemmas relating Polynomial.reverse to z^N p(1/z) and packaging the max-modulus principle."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  The bound looks asymmetric: it uses only the supremum on the unit disk yet must control the polynomial everywhere. Direct coefficient bounds (triangle inequality) often overshoot. The trick needs a complex-analysis tool: the maximum modulus principle applied to an auxiliary “reciprocal” polynomial. Students who don’t split into |w|≤1 vs |w|≥1 or who forget to invent q(z)=z^N p(1/z) run out of ideas quickly.

*Key insight.*  Inside the unit disk the inequality is exactly the definition of ‖p‖_∞. Outside, consider q(z)=z^N p(1/z); for |z|≤1 this is analytic, and on |z|=1 it equals p evaluated on the unit circle, so its modulus is bounded by ‖p‖_∞. The maximum modulus principle then controls q everywhere inside, and substituting z=1/w converts the bound back to p.

*Complete proof.*  Let N≥1 and ‖p‖_∞=sup{|p(z)|:|z|≤1}.
- If |w|≤1, then |p(w)|≤‖p‖_∞ by definition, and max{1,|w|}^N=1, so the bound holds.
- If |w|>1, define q(z)=z^N p(1/z). This polynomial is analytic on |z|≤1 (including z=0). On the unit circle |z|=1 we have |q(z)|=|p(1/z)|≤‖p‖_∞. By the maximum modulus principle, |q(z)|≤‖p‖_∞ for every |z|≤1. Put z=1/w (since |w|>1 ⇒ |1/w|<1) to get |p(w)|=|w|^N|q(1/w)|≤|w|^N ‖p‖_∞ = ‖p‖_∞ max{1,|w|}^N.
Combining the two cases proves the inequality for all w∈ℂ.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Unit disk case* → direct consequence of the definition. Lean target: `poly_abs_le_sup_norm_of_norm_le_one`.
2. *Reciprocal polynomial* → define q(z)=z^N p(1/z) and show |q(z)|≤‖p‖_∞ on |z|=1. Lean target: `reciprocal_poly_boundary_bound`.
3. *Maximum modulus principle* → apply to q on |z|≤1 and substitute z=1/w for |w|>1. Lean target: `polynomial_outside_unit_bound`.

**Stage 3 — LEAN FORMALIZATION**

Plan: reuse Mathlib lemmas `Complex.polynomial_maxabs_on_closedBall`. Define `q := Polynomial.reverse p` (the reversal already lives in Mathlib) composed with evaluation at 1/z. Need to prove `Complex.abs (Polynomial.eval₂ _ _ p w) ≤ supNorm * max 1 ‖w‖^N`. Present status: `Main.lean` only imports Mathlib; the actual proof is pending because I still need a lemma relating `Polynomial.reverse` evaluation to `z^N p(1/z)` and a wrapper lemma packaging the maximum modulus principle for polynomials. Once those are written (likely in `Scratch.lean`), the rest should go through. `lake build` deferred until then.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No additional revision needed; once the reciprocal-polynomial lemma is implemented, the Lean proof will mirror the Stage 1 argument verbatim. EOF
