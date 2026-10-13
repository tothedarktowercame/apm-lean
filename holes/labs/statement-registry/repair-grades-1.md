# Repair grades, batch 1 (proposed revisions in holes/labs/blueprints/<id>/RevisedMain.lean)

Read-only grading. Each revision was compared against problems/<id>/problem.md, the current
problems/<id>/lean/Main.lean, and the triage note that motivated it. Nothing was built.

| id | current Main.lean | revision grade | TRUE? | classification | remaining defect |
|---|---|---|---|---|---|
| t01J05 | FALSE (no `T2Space`; the circle with a doubled point gives χ = −1) | faithful (slightly stronger, because the orientation hypothesis is vacuous) | yes | correction | none for fidelity. `apm_t01J05_IsOrientation` is still an always-true fibrewise choice. This is harmless, since the claim holds without orientability |
| t03J05 | FALSE: (b) fails for non-Hausdorff X. (a) can be met by a tangential touching, so it is unfaithful | faithful. (a) is a mod-2 count backed by a topological transverse-crossing certificate | yes | correction | (a) still never defines an intersection number. The count is a certificate, and `% 2 = 1` follows mechanically from the crossing condition plus the compiled product lemma. The conjunct `eulerCharacteristic true 2 = -2` is `rfl` decoration |
| t94A06 | FALSE (infinite-dimensional model; Kupka's Sard counterexample on ℓ²) | faithful | yes | correction | none. The model `I` may have corners, so a proof must handle boundary charts (extension, or the derivative-within form of Sard). That is a proof-side point, not a statement defect |
| t95J05 | FALSE (raw `μH[3]` = (6/π)·σ, so the encoded value is −6π) | faithful (forms encoded as σ-densities) | yes | correction | (a) reduces to antipodal invariance of the density. The fact that the antipode preserves the orientation of S³ is built into the density representation. `∃!` is trivial in that representation. This is an acceptable encoding choice |
| t99J03 | FALSE (`Surface true 0` is the disk, so S² is matched by neither branch) | narrower: (a) is faithful and true; (c) is tautological, so not encoded | yes | correction | (c) is `rfl`: χ is a formula in the genus parameter and is never an invariant of X. The statement therefore encodes (a) only. Fidelity for (c) is lost; it does not affect truth. (b) is not formalisable |
| t93A03 | vacuous: `hspine` contradicts H₂ ≅ ℤ² (tame case), and if it held it would carry the core | faithful | yes | correction | none. The collar hypotheses are tameness only (standard balls satisfy them, and they say nothing about π₁), so they do not carry the core |

## Evidence notes

### t01J05
- Counterexample checked. Take n = 1 and X = two copies of S¹ glued along S¹∖{p}. X is compact, a smooth boundaryless 1-manifold with identity transitions, and dθ is a nowhere-zero `ContMDiffSection`. Mayer–Vietoris on the cover by the two circles, U ∩ V ≅ interval:
  - H₁: 0 → ℚ² → H₁(X) → H₀(U∩V) = ℚ → ℚ² is injective, so H₁(X) = ℚ².
  - H₀ = ℚ.
  - `apm_t01J05_eulerCharacteristic 1 X` = 1 − 2 = −1 ≠ 0.

  So the current statement is false.
- The revision adds exactly `[T2Space X]` (theorem lines `[TopologicalSpace X] [T2Space X]`). Every definition is unchanged. Compact, T2 and locally Euclidean give second countable and paracompact, so a Riemannian metric exists. The dual vector field is nowhere zero, Poincaré–Hopf gives χ = 0, and the rational Betti sum is finite and equals χ. The statement is true.
- The proof file is not carried over: the revision is the statement with `sorry`. The compiled n = 0 branch of the current Main.lean still applies verbatim, because the revision only adds a hypothesis.

### t03J05
- (b) counterexample checked. Each embedded circle in the orientable F* has an annulus neighbourhood, so aᵢ×aᵢ has a neighbourhood U ≅ T²×ℝ². That neighbourhood embeds openly in ℝ³×ℝ = ℝ⁴. Glue a copy of ℝ⁴ along U₁ (around a₁×a₁) and along U₂ (around b₁×b₁). The result X is a smooth, connected, non-Hausdorff 4-manifold, and F*×F* sits in it as an open subset. Both tori factor through a contractible ℝ⁴, so they are homotopic. This works for any witness, so the current ∃ is false.
- With `[T2Space X]`, (b) is true. Take S = b₁×b₁ (or b₂×b₂). It is compact, hence closed in X. Excision gives H₂(X, X∖S; ℤ/2) ≅ H₂(N, N∖S) ≅ H₀(S) = ℤ/2. The pairings with the three tori are:
  - a₁×a₁ ↦ 1 and a₂×a₂ ↦ 0 (disjoint);
  - b₁×b₁ ↦ its self-intersection, which is 0 (trivial normal bundle);
  - using b₂×b₂ instead separates a₂×a₂ from b₁×b₁.

  All three pairs are separated.
- (a): `apm_t03J05_IsSingleTransverseCrossing A₁ B₁` requires `range a ∩ range b = {p}`, together with a chart `e : U ≃ₜ E2` that sends the two ranges to the coordinate axes. With it, the product tori meet only at (p,p), in complementary coordinate 2-planes of the chart e×e. That is a transverse single point, so the mod-2 intersection number is 1 and the integer intersection number is ±1 ≠ 0. This strengthens the current statement, and the standard a₁, b₁ on the genus-2 polygon witness it.
- Residual: no intersection-number invariant is defined. The (a) conclusion `Nat.card … % 2 = 1` is a consequence of the certificate rather than an independent assertion. This is acceptable, since the certificate is the standard proof.

### t94A06
- Counterexample checked. Kupka (1965) gives a C^∞ map k : ℓ² → ℝ whose critical values contain [0,1]. Take X = ℓ²×ℓ² and f = (k x, k y, 0). Then f_s meets the axis exactly where (kx, ky) = −s, and it is transverse there iff dk(x) ≠ 0 and dk(y) ≠ 0. So every s ∈ −[0,1]² is bad, a set of positive measure. The current statement is false.
- The revision adds exactly `[FiniteDimensional ℝ E]`. With `SecondCountableTopology X` there are countably many charts, and the condition reduces to Sard for (f₀,f₁) : X → ℝ² (f_s is transverse iff −s is a regular value). The statement is true, and the family f + (s₀,s₁,0) is a correct answer to "find a family".

### t95J05
- Normalisation checked. The isodiametric normalisation gives μH[3] = (2³/ω₃)·Leb₃ = (6/π)·Leb₃ on 3-dimensional sets, so μH[3] = (6/π)·σ on S³. The current value is therefore (1/2)(6/π)(−2π²) = −6π ≠ −π², and the statement is false.
- The integrand is (x₂³ − 4x₁)·x₁ (0-indexed `x 1`, `x 0`):
  - restricting dx₂∧dx₃∧dx₄ to the outward-oriented S³ gives x₁·σ;
  - ∫x₂³x₁ dσ = 0 by odd symmetry;
  - ∫x₁² dσ = σ(S³)/4 = π²/2.

  So the sphere integral is −2π², and half of it is −π². The hint repair (vol B⁴ = π²/2) is correct.
- `μHE[3] := addHaarScalarFactor volume μH[3] • μH[3]` exists in the pinned Mathlib (`Mathlib/Geometry/Euclidean/Volume/Measure.lean`). Hausdorff measure on the subtype metric agrees with the ambient one, so μHE[3] on S³ is σ. The revised statement is true.
- The diff is only the measure in `t95J05Integral`, so the classification is correction.

### t99J03
- Counterexample checked. In the current `SurfaceRel true 0` the relation is `∃ j < 0, …`, which is empty, so `Surface true 0` is the closed disk. Take X = S² (compact, T2, connected, with a smooth `𝓡 2` structure). X is not homeomorphic to the disk. It is also not homeomorphic to any Σ_g (g ≥ 1) or N_k, which are not simply connected. Both disjuncts fail, so the current statement is false.
- The revision changes only the genus-0 branch. It identifies `edgePoint 2 0 t` = e^{iπt} with `edgePoint 2 1 (1−t)` = e^{iπ(2−t)} = e^{−iπt}, so each boundary point is glued to its conjugate. That is the word a a⁻¹, whose quotient is S². The other branches are unchanged:
  - orientable g ≥ 1: edges 4j ↔ 4j+2 and 4j+1 ↔ 4j+3, reversed, i.e. ∏[a,b];
  - nonorientable: edges 2j ↔ 2j+1 in the same direction, i.e. ∏aa.

  With this, (a) (existence and uniqueness of the normal form for smooth compact connected surfaces) is true. Using smooth instead of triangulated surfaces is equivalent up to homeomorphism, by Radó plus smoothing.
- Part (c): `apm_t99J03_eulerCharacteristic true g = 2 - 2 * g` and `… false k = 2 - k` are literally the definition (`rfl`). The conjuncts carry no content, so (c) is tautological as encoded. This matters for fidelity, not truth. Problem (c) asks for "classified by orientability and χ", with χ an invariant of X. Here χ is a label on the normal-form index, and the only extra content is that 2−2g and 2−k are injective, which is arithmetic. A faithful (c) needs χ(X) defined from X, for example as the alternating sum of singular-homology ranks, together with "X ≃ₜ Y ⇔ same orientability ∧ χ(X) = χ(Y)". As revised, the statement covers (a) only, so it is narrower.

### t93A03
- Current statement checked. `hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine` is impossible for tame balls: H₂ of the closed sum is ℤ², while H₂(S¹∨S¹) = 0. The theorem is therefore vacuous on every tame instance. In any case `¬SimplyConnected` is derived from `hspine` alone (`apm_t93a03_connectedSum_not_simplyConnected_of_piOne_equiv`), so the hypothesis also carries the core.
- The revision drops the spine and the first conjunct. It keeps the genuine quotient construction (identical definitions) and adds `hcollar₁/₂ : ∃ ψ : closedBall 0 2 → Summand, IsEmbedding ψ ∧ ψ ∘ inclusion = φ`.
- The collar does not carry the core:
  - it is a pure tameness condition (by invariance of domain, φ(D) sits as a round ball inside the open 3-cell ψ(B₂), so φ(S²) is bicollared);
  - it is satisfied by any ball inside a coordinate chart;
  - it says nothing about π₁.

  It only ensures that the quotient is the honest (S¹×S²)#(S¹×S²). The topological disc theorem, together with the orientation-reversing self-homeomorphism of S¹×S², makes that sum independent of the chosen balls and of the gluing orientation.
- The conclusion `¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂)` is exactly the prelim claim (π₁ = F₂), so the revision is true and faithful.
