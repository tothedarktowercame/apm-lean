# Informal Solution: a93J05

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* Double periodicity often tempts people to treat \(f\) like a function on the torus and to assert boundedness without proof. The only available periodicity directions are \(1\) and \(i\), so one must justify that every point of \(\mathbf C\) is reached by translating a single compact set by integral combinations of these vectors. Forgetting that step makes the subsequent appeal to Liouville circular. Another trap is thinking that the quotient \(\mathbf C/(\mathbf Z + i\mathbf Z)\) is compact “by definition”; here we must work inside \(\mathbf C\) and keep the argument elementary.

*Key insight.* Take the closed unit square \(Q = \{x+iy : 0 \le x, y \le 1\}\). The periodicity hypothesis says that translating \(Q\) by integers in the \(x\)-direction and imaginary integers in the \(y\)-direction tiles the plane without overlaps. Therefore every value of \(f\) occurs already on \(Q\). Since \(Q\) is compact and \(f\) is continuous (entire functions are continuous), the restriction \(f|_Q\) is bounded and this bound propagates to the whole plane. Liouville’s theorem then forces \(f\) to be constant.

*Complete proof.*  
1. Let \(Q = \{x+iy : x,y \in [0,1]\}\). Being the continuous image of the compact rectangle \([0,1]^2 \subset \mathbf R^2\), the set \(Q\) is compact.  
2. For any \(z = x + iy\in \mathbf C\), choose the integers \(n = \lfloor x \rfloor\) and \(m = \lfloor y \rfloor\). The point \(w = z - (n+mi)\) has real and imaginary parts in \([0,1)\), hence lies in \(Q\), and the periodicity assumption gives \(f(z) = f(w)\). Thus the image of \(f\) is the same as the image of \(f|_Q\).  
3. The restriction \(f|_Q\) is continuous on a compact set, so \(|f|\) attains a maximum \(M\) on \(Q\). The previous step forces \(|f(z)| \le M\) for *all* \(z \in \mathbf C\); therefore \(f\) is bounded on the entire complex plane.  
4. A bounded entire function is constant by Liouville’s theorem. Hence every pair of points \(z,w\) satisfies \(f(z)=f(w)\), so \(f\) is constant.

*Proof sanity check.* The delicate step is Step 2, where we use the floors of the real and imaginary parts to move any \(z\) back into the unit square. The inequalities \(0 \le x - \lfloor x \rfloor < 1\) and \(0 \le y - \lfloor y \rfloor < 1\) ensure \(w \in Q\), and the given periodicity with affine shifts \(n+mi\) gives \(f(z)=f(w)\); no other hidden assumptions enter the argument. All parts (a single statement) are fully proved.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `lattice_periodic_entire_const` (goal): relies on `range_bounded_of_periodic` plus Liouville’s theorem (`Differentiable.apply_eq_apply_of_bounded`).  
  - *Formal dependency*: the Lean theorem `lattice_periodic_entire_const`.  
  - *Informal dependency*: Step 3–4 above (boundedness + Liouville).  
  - *Why this now*: once we know the range is bounded, Liouville finishes the job in one line.  
- `range_bounded_of_periodic`: packages two ingredients—`fundamentalDomain_isCompact` (image of the unit square is compact) and `exists_fundamentalDomain_translate` (floors move any point into that square)—to show the range of \(f\) is bounded.  
- `fundamentalDomain_isCompact`: identifies the fundamental domain with the continuous image of \([0,1]^2\).  
- `exists_fundamentalDomain_translate`: uses floor functions to reduce any point to the fundamental domain.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a93J05/apm-v2-a93J05-1775050465617/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a93J05/apm-v2-a93J05-1775050465617/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Implemented `fundamentalDomain_isCompact`, `exists_fundamentalDomain_translate`, `exists_value_in_fundamentalDomain`, `range_bounded_of_periodic`, and the main theorem `lattice_periodic_entire_const` inside `/home/joe/code/apm-lean/ApmCanaries/Frames/A93J05/Apm_v2_a93J05_1775050465617/Main.lean`.
- The proof mirrors the informal strategy: construct the compact fundamental domain as a continuous image, pull any point back into it via floors, deduce a uniform bound on `Set.range f`, and apply `Differentiable.apply_eq_apply_of_bounded`.
- `lake build ApmCanaries.Frames.A93J05.Apm_v2_a93J05_1775050465617.Main` now succeeds (only style warnings remain), giving a verified equivalence between the natural-language argument and Lean.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

`matched` — The Lean theorem `lattice_periodic_entire_const` certifies exactly the statement in Stage 1 (“An entire function that is 1-periodic in both real and imaginary directions is constant.”). The discussion in Step 3 (boundedness via the unit square) and Step 4 (Liouville) is now formally justified.
