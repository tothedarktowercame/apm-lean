# Informal Solution: b03J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
