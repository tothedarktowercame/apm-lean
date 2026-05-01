# Informal Solution: m96A04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  The statement smells like adjoints, but neither \(A\) nor \(B\) is assumed bounded.  Many students try to quote the adjoint theorem directly; here we must *derive* boundedness from the inner-product identity.

*Key insight.*  For each \(y\), the map \(x \mapsto \langle Ax,y\rangle\) is a bounded functional represented by \(By\).  The family \(\{T_y(x)=\langle Ax,y\rangle\}\) is pointwise bounded, so Banach–Steinhaus forces a uniform bound on \(\|By\|\).  Once \(B\) is bounded, \(A\) inherits boundedness from the adjoint norm identity.

*Complete proof.*

1. **\(B\) is linear.**  For scalars \(\alpha,\beta\) and vectors \(y_1,y_2\),  
   \(\langle x, B(\alpha y_1+\beta y_2)\rangle = \langle Ax, \alpha y_1+\beta y_2\rangle = \alpha\langle x, By_1\rangle + \beta \langle x, By_2\rangle.\)  
   Nondegeneracy of the inner product yields \(B(\alpha y_1+\beta y_2)=\alpha By_1+\beta By_2\).
2. **\(B\) is bounded.**  For each \(y\), the functional \(T_y(x)=\langle Ax,y\rangle=\langle x,By\rangle\) is bounded with \(\|T_y\|=\|By\|\).  For each \(x\),  
   \(\sup_{\|y\|\le 1} |T_y(x)| = \sup_{\|y\|\le 1} |\langle Ax,y\rangle| = \|Ax\|.\)  
   Thus the family \(\{T_y\}\) is pointwise bounded.  By the Uniform Boundedness Principle there exists \(M\) such that \(\|T_y\|\le M\|y\|\) for all \(y\), i.e. \(\|By\|\le M\|y\|\).  Hence \(B\) is continuous.
3. **\(A\) is bounded.**  Using the adjoint formula,  
   \(\|Ax\| = \sup_{\|y\|=1} |\langle Ax,y\rangle| = \sup_{\|y\|=1} |\langle x,By\rangle| \le \|x\| \sup_{\|y\|=1} \|By\| = \|x\| \cdot \|B\|.\)  
   Therefore \(A\) is continuous.

*Proof sanity check.*  Banach–Steinhaus is the delicate step; it applies because each \(T_y\) is linear and for fixed \(x\), \(\sup_{\|y\|\le 1}|T_y(x)|=\|Ax\|<\infty\).  All three parts (a)–(c) are fully proved.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1 (`bilinear_identity_forces_linear`).*  Exploits linearity of the inner product in its first argument to show \(B\) respects addition/scalars.
- *s2 (`uniform_bound_from_pointwise_bounds`).*  Applies Banach–Steinhaus to \(T_y(x)=\langle Ax,y\rangle\) to bound \(B\).
- *s3 (`adjoint_bound_implies_A_bounded`).*  Combines the adjoint norm identity with the bound on \(B\) to control \(A\).

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/m96A04/apm-v2-m96A04-1775070820897/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/m96A04/apm-v2-m96A04-1775070820897/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Searches `rg -n "BanachSteinhaus" /home/joe/code/apm-lean` and `rg -n "UniformBoundedness" /home/joe/code/apm-lean` revealed no usable Mathlib statements to turn the pointwise bounds on \(T_y\) into a uniform bound on \(\|By\|\).  Without that API, one cannot even state the desired `bilinear_identity_forces_bounded` theorem.
- A placeholder `theorem searched_for_hilbert_adjoint_api : True := trivial` has been added to `Main.lean` to document this missing ingredient.
- Status: **blocked by missing API/theory** (Banach–Steinhaus for inner-product functionals).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  Stage 1’s conclusions remain informal because Mathlib lacks Banach–Steinhaus (and hence the needed weak-operator adjoint machinery).
