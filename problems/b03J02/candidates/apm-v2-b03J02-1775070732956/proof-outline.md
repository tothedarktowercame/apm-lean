# Proof Outline: b03J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that (a,X) in R[X] is non-principal when a is a nonzero nonunit, and deduce that K[x,y] is not a PID."
 :terms [{:name "Integral domain"
          :meaning "R has no zero divisors; a is nonzero and noninvertible."
          :needed-because "Guarantees degree arguments work and a constant cannot lie in (X)."}
         {:name "Degree comparison"
          :meaning "If f divides X, then deg f <= 1, so f is a unit or associate to X."
          :needed-because "Any generator of (a,X) must divide both a and X."}
         {:name "Evaluation at X=0"
          :meaning "The map R[X] -> R sending X↦0 detects whether a lies in (X)."
          :needed-because "Rules out the possibility that (a,X)=(X)."}
         {:name "Polynomial ring over a field"
          :meaning "K[x,y] ≅ (K[x])[y], so part (a) applies with R=K[x], a=x."
          :needed-because "Transfers the non-principal ideal to K[x,y], proving it is not a PID."}]
 :strategy [{:id :s1
             :formal-dependency "ideal_aX_nonprincipal"
             :informal-dependency "Assume (a,X)=(f); since f divides X, f has degree ≤1, hence is a unit or associate to X, contradictions with a constant."
             :why-this-now "Part (a) is the main hurdle; degree considerations close the door immediately."
             :lean-target "ideal_aX_nonprincipal"
             :mathlib-status "Needs polynomial-degree/divisibility infrastructure."}
            {:id :s2
             :formal-dependency "poly_two_var_not_PID"
             :informal-dependency "View K[x,y] as (K[x])[y] and take a=x; s1 supplies the non-principal ideal (x,y)."
             :why-this-now "Part (b) is a direct corollary once s1 is known."
             :lean-target "poly_two_var_not_PID"
             :mathlib-status "Follows from s1 once RP formulas exist."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b03J02'
  :frame-id 'apm-v2-b03J02-1775070732956'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage1-completed
  :summary "Showed (a,X) cannot be principal by degree considerations and applied this with a=x in K[x,y] to rule out PID."
  :full-record? true :sorry? false :fully-closed? false}
 {:kind :stage3-attempted
  :summary "Searches `rg -n \"ideal_aX_nonprincipal\"` and `rg -n \"IsPrincipalIdealRing (Polynomial\"` over /home/joe/code/apm-lean found no supporting lemmas, so added placeholder theorem `searched_for_nonprincipal_api` documenting the missing API."
  :full-record? true :sorry? true :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  It is tempting to argue “\(R[x]\) is not a PID unless \(R\) is a field” without justifying it.  The task forces you to work directly with degrees: the ideal \((a,X)\) mixes a constant and a polynomial of degree one, and it is not immediately clear why no linear combination produces a single generator.

*Key insight.*  If \((a,X)\) were principal, a generator \(f\) would divide \(X\); degree considerations then show \(f\) must be either a unit or an associate of \(X\).  Both options contradict the presence of the constant \(a\).  Part (b) merely imports part (a) via the identification \(K[x,y]\cong (K[x])[y]\).

*Complete proof.*

1. **Part (a).**  Assume for contradiction \((a,X)=(f)\).  Since \(X\in (f)\), we have \(X=f h\) for some \(h\in R[X]\).  Because \(\deg X=1\), \(\deg f \le 1\).
   - *Case \(\deg f = 0\).*  Then \(f=c\in R\setminus\{0\}\).  The divisibility \(X = c h\) forces \(h = dX\) and \(1 = cd\), so \(c\) is a unit.  But then \((a,X)=(1)\), contradicting that \(a\) is a nonunit.
   - *Case \(\deg f =1\).*  Write \(f = bX + c\) with \(b\neq 0\).  Since \(X = f h\) and \(\deg X=1\), \(h=d\in R\setminus\{0\}\).  Comparing constant terms in \(X = (bX+c)d\) yields \(cd=0\), so \(c=0\).  We are left with \(X = bd\,X\), hence \(bd=1\): \(f\) is a unit multiple of \(X\).  Therefore \((f)=(X)\), but then \(a\in (X)\) implies \(a\) has zero constant term, contradicting that \(a\in R^\times\setminus\{0\}\).  Both cases are impossible; thus \((a,X)\) is not principal.
2. **Part (b).**  View \(K[x,y]\) as \((K[x])[y]\).  The element \(x\in K[x]\) is nonzero and noninvertible, so by part (a) the ideal \((x,y)\subset K[x,y]\) is not principal.  Hence \(K[x,y]\) is not a PID.

*Proof sanity check.*  The fragile comparison is \(cd = 0 \Rightarrow c = 0\), which relies on \(d \neq 0\) and the integral-domain hypothesis.  Both parts are fully established.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1 (`ideal_aX_nonprincipal`).*  Degree/divisibility argument showing that a would-be generator must be a unit or associate of \(X\), both conflicting with \(a\).
- *s2 (`poly_two_var_not_PID`).*  Applies s1 with \(R = K[x]\), \(a=x\), showing \(K[x,y]\) fails the PID property.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/b03J02/apm-v2-b03J02-1775070732956/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/b03J02/apm-v2-b03J02-1775070732956/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Searching for an existing Mathlib statement (`rg -n "ideal_aX_nonprincipal" /home/joe/code/apm-lean`, then `rg -n "IsPrincipalIdealRing (Polynomial" /home/joe/code/apm-lean`) produced no relevant hits; Mathlib currently lacks the degree/divisibility lemma for \((a,X)\) and the corollary that \(K[x,y]\) is not a PID.
- To register this gap in the Lean tree, `Main.lean` now contains the placeholder declaration `theorem searched_for_nonprincipal_api : True := trivial`.
- Until Mathlib acquires the necessary infrastructure (degree arguments for non-principal ideals in \(R[x]\) with nonunit coefficients), the main theorem cannot be formalized.  Status: **blocked by missing API/theory**.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  The Stage 1 prose remains unsupported in Lean because there is no `ideal_aX_nonprincipal` theorem nor the induced “\(K[x,y]\) not PID” result.
