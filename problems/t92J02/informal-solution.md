# Informal Solution: t92J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.**  Compactness arguments force you to manipulate entire open covers, but part (a) only gives a cover of the image, not the preimage.  Part (b) then layers Hausdorff separation on top of that: you must remember that “compact in Hausdorff implies closed” in order to convert the surjective map into a homeomorphism.  Many prelim solutions either try to push compactness forward directly (which fails) or forget to prove the inverse is continuous.

**Key insight.**  Pull every open cover of the target back to the source, use compactness of the source to get a finite subcover, and then push those finitely many sets forward again.  In the Hausdorff setting this shows the map is closed; a continuous bijection that is also closed automatically has a continuous inverse, hence is a homeomorphism.

**Complete proof.**
(a) Let `f : X → Y` be continuous and let `K ⊆ X` be compact.  Take an open cover `{V_i}` of `f(K)`.  For each `i`, the preimage `f⁻¹(V_i)` is open in `X`, and the sets `{f⁻¹(V_i) ∩ K}` cover `K`.  Compactness provides finitely many indices `i₁,…,i_m` whose preimages still cover `K`.  Apply `f` to each set: `{V_{i_j}}_{j=1}^m` is a finite subcover of `f(K)`, so `f(K)` is compact.
(b) Now let `f : X → Y` be continuous, bijective, with `X` compact and `Y` Hausdorff.  If `C ⊆ X` is closed, then `C` is compact, so by (a) `f(C)` is compact; in a Hausdorff space every compact set is closed, so `f` is a closed map.  A bijective closed map has a closed inverse-image operator: for every closed `C ⊆ X`, `f(C)` is closed in `Y`, hence the inverse `f^{-1}` pulls closed sets back to closed sets.  Consequently `f^{-1}` is continuous and `f` is a homeomorphism.

**What connects.**  This is the standard toolkit for topological conjugacy problems: “continuous bijection + compact domain + Hausdorff codomain” appears in spectral theory, manifold theory, and any time you glue spaces using quotient maps.  The closed-map trick is the same one used to show proper maps between Hausdorff spaces are closed.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Compactness via covers → part (a).**  Uses the definition of compactness (finite subcovers) together with functoriality of preimages under continuous maps (`IsCompact.image`).
- **Compact subset of Hausdorff is closed.**  Needed to turn the finite-subcover result into the statement “`f` is closed”.
- **Closed bijection ⇒ homeomorphism.**  Once `f` is closed, the inverse map preserves closed sets, so the inverse is continuous and gives a homeomorphism.  Mathlib lemmas `IsCompact.image` and `IsClosed.isCompact` feed directly into this closed-map argument.

**Stage 3 — LEAN FORMALIZATION**

- Added `image_of_compact_isCompact` and `homeomorph_of_compact_to_T2` in `ApmCanaries/Frames/T92J02/Apm_v2_t92J02_1775008678104/Main.lean`.  The first is a thin wrapper around `IsCompact.image`.  The second equips `X` with the compact structure coming from `IsCompact univ`, proves `f` is a closed map by reusing part (a), identifies the inverse’s closed preimages, and packages everything into a `Homeomorph`.
- Ran `lake build` from `/home/joe/code/apm-lean`; it completed successfully (global warnings are pre-existing files noted in the log).  No `sorry` remain in the frame-local files.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof forced an explicit expression for the inverse’s preimage of a closed set (`g ⁻¹' C = f '' C`), which sharpens the informal argument: once you see that equality, continuity of the inverse is immediate.  That perspective is now reflected in Stage 1’s explanation of why closed maps give homeomorphisms.
