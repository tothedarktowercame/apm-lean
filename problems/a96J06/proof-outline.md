# Proof Outline: a96J06

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

`ConstructionTargets.SchwarzEquality.eqOn_deriv_mul` provides the required
equality case of Schwarz's lemma. The new bundled polynomial
`apm_a96J06_poly` comes with a compiled evaluation identity and a proof that
its coefficient at `N` is exactly `c N`. This makes the final contradiction
available once the normalized map is shown to equal the identity on the unit
disk.

The remaining formal work is assembling the rescaled unit-disk self-map from
the negated existential, proving its derivative at zero is one, and promoting
the resulting equality on an open disk to polynomial equality using
`Polynomial.eq_of_infinite_eval_eq`. The main theorem therefore remains
partial with one `sorry`; its statement is unchanged.

## Imported Proof Plan

```clojure
{:goal "Show any polynomial of the form p(z)=z+Σ_{n≥2} c_n z^n expands some point in every disk."
 :terms [{:name "normalization"
          :meaning "Scale the disk of radius r to the unit disk via q(z)=p(rz)/r."
          :needed-because "Lets us apply Schwarz’s lemma on the unit disk."}
         {:name "Schwarz lemma"
          :meaning "Maps of the unit disk fixing 0 with |q(z)|≤|z| must be rotations; higher coefficients vanish."
          :needed-because "Gives the contradiction when a higher coefficient is nonzero."}
         {:name "contradiction setup"
          :meaning "Assume |p(z)|≤r on the disk |z|≤r and derive properties of q."
          :needed-because "Allows us to negate the desired conclusion."}]
 :strategy [{:id :s1
             :formal-dependency "Normalization of the disk"
             :informal-dependency "Stage 1 normalization"
             :why-this-now "Reduce the general r>0 case to a self-map of the unit disk."
             :lean-target "normalize_polynomial_unit_disk"
             :mathlib-status "Scaling polynomials is straightforward in Mathlib."}
            {:id :s2
             :formal-dependency "Schwarz lemma"
             :informal-dependency "Stage 1 contradiction setup"
             :why-this-now "Conclude that the normalized map must be a rotation, forcing coefficients to vanish."
             :lean-target "schwarz_contradiction"
             :mathlib-status "Schwarz lemma already exists for holomorphic functions."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96J06'
  :frame-id 'apm-v2-a96J06-1775003321530'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Explained the Schwarz-lemma contradiction showing p expands every disk."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the normalization + Schwarz rigidity lemma dependencies."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean plan (normalize + apply Schwarz); implementation still pending."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The conclusion feels geometric (“the polynomial must stretch every disk”), so it’s tempting to chase inequalities on coefficients. The right tool is analytic: normalize the disk to the unit disk and apply Schwarz’s lemma. Students often forget to rescale, so they can’t bring Schwarz to bear.

*Key insight.* Assume towards contradiction that some disk is mapped inside itself: 
\(|p(z)|≤r\) for all \\(|z|<r\\). After the change of variables \\(q(w)=p(r w)/r\\), we get a holomorphic self-map of the unit disk fixing 0 with derivative 1 at 0. Schwarz’s lemma then forces \\(q(w)=e^{iθ}w\\). But the polynomial has a nonzero higher-order term, contradicting the conclusion of Schwarz’s lemma. Thus every disk must contain a point expanded beyond its radius.

*Complete proof.* Suppose there is an \\(r>0\\) with \\(|p(z)|≤r\\) whenever \\(|z|≤r\\). Define
\[
q(w)=\frac{p(r w)}{r}= w + \sum_{n=2}^N c_n r^{n-1} w^n.
\]
Then \(q\) is holomorphic on the unit disk, satisfies \(q(0)=0\), and by construction \(|q(w)|≤1\) for \(|w|≤1\). Schwarz’s lemma yields \(|q(w)|≤|w|\) and \(|q'(0)|≤1\). Here \(q'(0)=1\); hence equality holds, so Schwarz’s lemma forces \(q(w)=e^{iθ}w\). Comparing coefficients shows every higher-order coefficient must vanish, contradicting the assumption \(c_N\ne 0\). Therefore our supposition is false, and for every \(r>0\) there exists \(|ζ|<r\) with \(|p(ζ)|>r\).

*What connects.* This is a baby case of the Open Mapping Theorem plus Schwarz’s lemma. It is the analytic version of “a non-linear polynomial cannot be a self-map of a disk fixing the center with derivative 1.” The same trick appears whenever we study automorphisms of the disk or prove rigidity theorems (e.g., for bounded holomorphic functions with fixed points).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Normalization lemma:* rescale the disk to unit size and rewrite \(p\) as \(q(w)=p(rw)/r\). Needed to bring Schwarz’s lemma to the party.
- *Schwarz rigidity:* if a holomorphic self-map of \(\mathbb D\) fixes 0 and has \(|q'(0)|=1\), then it is a rotation. Needed for the contradiction with the nonzero higher coefficient.
- *Contradiction conclusion:* equality of coefficients between \(q\) and the rotation forces \(c_n=0\) for \(n≥2\), contradicting \(c_N\ne0\).

**Stage 3 — LEAN FORMALIZATION**

Closer hop 2 compiles `apm_a96J06_hasDerivAt_zero` and
`apm_a96J06_rescaled_hasDerivAt_zero`, fully discharging differentiability and
derivative normalization for the rescaled map. The remaining implementation
is to extract a closed-unit-ball mapping from the negated witness, apply the
affine equality case beneath `ConstructionTargets.SchwarzEquality`, and turn
the resulting open-disk identity into polynomial coefficient equality.

Plan: (1) implement the normalization lemma in `Main.lean` (scaling the polynomial and the disk). (2) Invoke Mathlib’s Schwarz lemma (`Complex.Analytic.schwarz_sublemma`) to deduce rigidity of `q`. (3) Conclude coefficient vanishing using polynomial extensionality. Stage 3 remains in progress; these lemmas still need to be formalized.

Closer hop 3 completes the assembly. Negating the conclusion gives a bound by
the closed radius-`r` ball. After rescaling, the map sends the open unit disk
to the closed unit ball, fixes zero, and has derivative one. Mathlib's
`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` therefore identifies it
with the identity throughout the disk. Scaling back gives equality between
`apm_a96J06_poly N c` and `X` on the infinite family `r/(n+2)`. The theorem
`Polynomial.eq_of_infinite_eval_eq` makes the polynomials equal, while their
coefficients at `N` are respectively `c N ≠ 0` and zero, a contradiction.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof is finished, ensure the written proof cites the precise normalization and Schwarz lemmas used, emphasizing the rigidity argument.
