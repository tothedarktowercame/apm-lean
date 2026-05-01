# Proof Outline: m96A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "From the bilinear identity <Ax,y>=<x,By> on a Hilbert space, prove that B is linear and bounded, and consequently that A is bounded."
 :terms [{:name "Riesz representation"
          :meaning "Every continuous functional x ↦ <x,z> corresponds uniquely to z ∈ X."
          :needed-because "The hypothesis already expresses the functionals x ↦ <Ax,y> via vectors By, giving additivity of B."}
         {:name "Uniform boundedness principle"
          :meaning "If a family of bounded operators is pointwise bounded, their norms are uniformly bounded."
          :needed-because "Applied to T_y(x)=<Ax,y> to prove B is bounded (hence continuous)."}
         {:name "Adjoint norm identity"
          :meaning "Once B is bounded, ||Ax|| = sup_{||y||=1} |<Ax,y>| = sup |<x,By>| <= ||B||·||x||."
          :needed-because "Shows A is bounded (hence continuous) after B is established."}]
 :strategy [{:id :s1
             :formal-dependency "bilinear_identity_forces_linear"
             :informal-dependency "Use the relation with sums and scalars in the second slot to show B respects addition and homogeneous scaling."
             :why-this-now "Linearity of B is the foundation for the later functional-analytic arguments."
             :lean-target "B_is_linear"
             :mathlib-status "Follows from properties of the inner product (linearity in the first slot)."}
            {:id :s2
             :formal-dependency "uniform_bound_from_pointwise_bounds"
             :informal-dependency "Consider T_y(x)=<Ax,y>; for each x the family {T_y} is pointwise bounded because x ↦ Ax is a vector. Uniform boundedness yields sup_{||y||=1}||T_y||<∞, i.e. B bounded."
             :why-this-now "Establishes continuity of B."
             :lean-target "B_is_bounded"
             :mathlib-status "Requires invoking Banach-Steinhaus for dual functionals."}
            {:id :s3
             :formal-dependency "adjoint_bound_implies_A_bounded"
             :informal-dependency "With B bounded, compute ||Ax|| via sup_{||y||=1}|<Ax,y>| = sup |<x,By>| <= ||B||·||x||."
             :why-this-now "Completes the argument by giving continuity of A."
             :lean-target "A_is_bounded"
             :mathlib-status "Straight use of the adjoint identity once B is known bounded."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'm96A04'
  :frame-id 'apm-v2-m96A04-1775053034904'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage1-completed
  :summary "Explained why B must be linear, then used Banach–Steinhaus plus the adjoint norm identity to show B and A are continuous."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage3-attempted
  :summary "Searches `rg -n \"UniformBoundedness\"` and `rg -n \"Banach\"` over /home/joe/code/apm-lean revealed no API for Banach–Steinhaus, so the Lean proof of `bilinear_identity_forces_bounded` is blocked by missing Uniform Boundedness infrastructure."
  :full-record? true :sorry? true :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  The statement looks innocuous—“\(B\) behaves like the adjoint of \(A\)”—yet nothing is assumed about boundedness.  Students often try to declare “\(B\) is the adjoint” without proving that it is linear, or they implicitly assume the Uniform Boundedness Principle without checking pointwise boundedness.  The trap is that \(A\) may be wildly discontinuous, so every continuity assertion has to be deduced from the inner-product identity itself.

*Key insight.*  Treat \(y \mapsto By\) as the Riesz representative of the functional \(x \mapsto \langle Ax, y\rangle\).  This immediately gives linearity of \(B\).  Once the full family of functionals \(T_y(x)=\langle Ax, y\rangle\) is in hand, the Uniform Boundedness Principle furnishes a common bound for \(\|By\|\), yielding continuity of \(B\).  Finally, \(A\) inherits boundedness from \(B\) via the supremum formula \(\|Ax\|=\sup_{\|y\|=1}|\langle Ax,y\rangle|\).

*Complete proof.*

1. **(a) \(B\) is linear.**  Fix \(y_1,y_2\in X\) and scalars \(\alpha,\beta\).  For every \(x\in X\),
   \[
     \langle x, B(\alpha y_1+\beta y_2)\rangle = \langle A x,\alpha y_1+\beta y_2\rangle = \alpha \langle A x,y_1\rangle + \beta \langle A x,y_2\rangle = \langle x, \alpha B y_1 + \beta B y_2\rangle.
   \]
   By the nondegeneracy of the inner product, \(B(\alpha y_1+\beta y_2)=\alpha B y_1 + \beta B y_2\).  Thus \(B\) is linear.

2. **(b) \(B\) is continuous.**  For each \(y\in X\) define the bounded linear functional \(T_y:X\to\mathbf C\) by \(T_y(x)=\langle Ax,y\rangle=\langle x,By\rangle\).  Consider the family \(\mathcal T=\{T_y: y\in X\}\) acting on the Banach space \(X\).  For every fixed \(x\in X\),
   \[
     \sup_{\|y\|\le 1} |T_y(x)| = \sup_{\|y\|\le 1} |\langle Ax,y\rangle| = \|Ax\| < \infty.
   \]
   Hence \(\mathcal T\) is pointwise bounded.  The Uniform Boundedness Principle yields \(M<\infty\) with \(\|T_y\|\le M\|y\|\) for all \(y\).  But \(\|T_y\|=\|By\|\) (the norm of the representing vector), so \(\|By\|\le M\|y\|\).  Therefore \(B\) is a bounded (hence continuous) linear operator.

3. **(c) \(A\) is continuous.**  For any \(x\in X\),
   \[
     \|Ax\| = \sup_{\|y\|=1} |\langle Ax,y\rangle| = \sup_{\|y\|=1} |\langle x,By\rangle| \le \sup_{\|y\|=1} \|x\|\cdot \|By\| \le \|x\| \cdot \|B\|.
   \]
   Thus \(\|Ax\|\le \|B\|\cdot \|x\|\) for all \(x\), which is precisely the boundedness (continuity) of \(A\).

*Proof sanity check.*  The fragile step is the application of the Uniform Boundedness Principle: we must verify that \(x\mapsto T_y(x)=\langle Ax,y\rangle\) is pointwise bounded in \(y\).  This follows from the Cauchy–Schwarz inequality because each \(Ax\) is an honest vector with finite norm.  All three subparts (a)–(c) are fully proved above.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1 (`bilinear_identity_forces_linear`).*  Linear dependence of the inner product in the second slot forces \(B\) to respect sums/scalars.  This is immediate once we rewrite \(\langle Ax, \alpha y_1 + \beta y_2\rangle\) two ways.
- *s2 (`uniform_bound_from_pointwise_bounds`).*  Family \(\mathcal T=\{T_y\}\) of linear functionals is pointwise bounded (Cauchy–Schwarz).  Banach–Steinhaus gives a uniform bound on \(\|T_y\|\), which is exactly \(\|By\|\); hence \(B\) is bounded/continuous.
- *s3 (`adjoint_bound_implies_A_bounded`).*  With \(B\) bounded, take suprema over the unit sphere to obtain the operator norm inequality \(\|Ax\|\le \|B\|\|x\|\).  This is the standard estimate for an adjoint.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/m96A04/apm-v2-m96A04-1775053034904/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/m96A04/apm-v2-m96A04-1775053034904/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Searched Mathlib for an existing Uniform Boundedness lemma suitable for linear functionals by running `rg -n "UniformBoundedness" /home/joe/code/apm-lean` and `rg -n "Banach" /home/joe/code/apm-lean`.  Neither search revealed a usable API that turns pointwise bounds on \(T_y(x)=\langle Ax,y\rangle\) into a global operator-norm bound for the representing vectors \(By\).
- Without such a lemma, the planned Lean theorem `bilinear_identity_forces_bounded` cannot even be stated cleanly: `B : X -> X` has no linear structure yet, and there is no ready-made `BanachSteinhaus` theorem specialized to Hilbert-space inner products.
- Consequently `Main.lean` remains the autogenerated stub; the formal proof is **blocked by missing API/theory** (specifically, a Uniform Boundedness/ Banach–Steinhaus statement for families of inner-product functionals).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  Stage 1 proves all three claims informally, but Lean currently lacks the Banach–Steinhaus/Uniform Boundedness infrastructure needed to show that \(\sup_{\|y\|=1}\|By\|\) is finite.  Until that lemma is available, none of the Stage 1 conclusions (boundedness of \(B\), hence of \(A\)) can be certified formally.
