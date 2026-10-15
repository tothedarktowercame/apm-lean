# Blueprint for t97J04 (claude-14, 2026-10-15)

Statement graded faithful 2026-10-13 (repair batch 3): X is the literal genus-two
octagon plus a disk on the meridian edge 4. Answers: π₁ = ⟨a,b,d | [a,b]⟩;
H = ℤ, ℤ³, ℤ, 0.

The 2026-10-13 blueprint (now in old-2026-10-13/) needed X ≃ₕ T²∨S¹. Two seats
stopped on it because it had no explicit maps. This replaces it.

## Route

X ≅ Xc := (W ∪_word D²) ∪_c D², where:
- W is the orbit-indexed wedge of four circles (PolygonSurfacePiOne);
- word = polygonBoundaryWedgeLoop P, with P the standard genus-two pairing (t92J05);
- c = the edge-4 leg pushed into W ∪_word D².

Part A proves π₁ and homology of `Cell γ := Y ∪_γ D²` once, for any γ : C(Circle, Y):
- open cover: outer = Y ∪ annulus 1/3 < |z| ≤ 1, inner = |z| < 2/3;
- A1–A6 are the geometric facts (A4 is the radial retraction, as in t99A01 succ_retract/deform);
- A7 is van Kampen through TwoOpenAttachOneCell's kernel lemma;
- A8–A11 are integral Mayer–Vietoris consequences (IntegralMV, via IntegralSingularHomologyComparison).

Part B applies Part A twice:
- B1: the homeomorphism X ≅ Xc. Both directions lift through quotient maps; no Hausdorffness is needed.
- B2/B3: coordinates come from the banked GenusTwoSurfacePiOne (B8 wedge coordinates, W1 boundary word).
- B4/B5: pure group theory.
- B6–B9: homology. word_* = 0 by Hurewicz, c_* is injective by collapse, and H₁ uses collapse coordinates.
- B10/B11: H₀, and homology invariance under homeomorphism.

Assembly, `Xc_piOne` and the final theorem are sorry-free over the leaves.

## Leaves (23)

Part A:
- cell_cover
- cell_inner_contractible
- cell_overlap_hequiv
- cell_outer_hequiv
- cell_overlap_loop
- cell_pathConnected
- cell_piOne
- cell_H1
- cell_H2_of_injective
- cell_H2_of_zero
- cell_H_high

Part B:
- X_homeomorph
- word_loopClass_coords
- cLoop_loopClass
- cOrbit_label
- two_step_quotient
- presentation_algebra
- W_homology
- word_H1_zero
- cLoop_H1_injective
- Xc_H1
- H0_of_pathConnected
- H_of_homeomorph

## Checked

- Every leaf statement was checked true by hand. A4 holds for any Y. A8 needs Y path connected for H₀ injectivity. A9 needs no connectivity.
- Edge 4 has sign false (`decide`), so the octagon traverses c backwards. B1 is existential, so the meridian disk maps via conjugation.
- `cOrbit_label` (orbit of edge 4 ↦ generator 2) is its own leaf. If it turns out false (label 3), swap the generator in presentation_algebra.
