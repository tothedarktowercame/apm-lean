# Repair grades, batch 2 (proposed RevisedMain.lean statements)

Read-only. Nothing was built and nothing was edited apart from this file. For each problem I compared the proposed `holes/labs/blueprints/<id>/RevisedMain.lean` with `problems/<id>/problem.md`, with the current `problems/<id>/lean/Main.lean`, and with the triage note that motivated the repair.

| id | current statement | revision grade | TRUE? | change | remaining defect |
|---|---|---|---|---|---|
| t96A08 | vacuous (confirmed) | faithful | yes | correction | none of substance. `hreachable` (path-connectedness) and the `f : M → ℝ` codomain fix are correct and kept |
| t03J01 | true, but hypothesis-carries-core (confirmed) | stronger (acceptable) | yes | improvement (the two statements have the same truth value, and the revision is strictly harder to prove) | J₂ now ranges over every separating curve, including curves that bound a disc. This is fine. The prelim's "twice-punctured sphere" is still corrected to a twice-punctured torus |
| t01J04 | FALSE (lacks second countability) and also too weak (unlinked atlas) | faithful | yes | correction | none. `RegularSpace Y` is redundant (it follows from T2 plus local compactness) but harmless |
| t01J06 | part (c) trivially true (confirmed, `Refute.lean`) | faithful | yes | correction | "why is i*ω closed" in (b) is explanation and is not encoded. That is acceptable |
| t95J03 | true but narrower (the S² slot held a disc; confirmed, `Refute.lean`) | faithful | yes | correction (domain); the old statement was true | "surface" is read as connected and closed. Connectedness is needed, because K⊔K ∈ S₂ otherwise |

## t96A08

**The current statement is vacuous.** `IsPiecewiseSmoothPath := Continuous γ ∧ ∃ breaks : Finset ℝ, ∀ t ∈ Icc 0 1, t ∉ breaks → ContMDiffAt … γ t`. Suppose that in a chart ω(p₀)(v) = c ≠ 0. Take γ₂ = chart⁻¹(p₀ + g(t)v) with g(t) = ε·t(1+sin(1/t))/(1+sin 1). This path is continuous, smooth off the break {0}, and has g(0)=0 and g(1)=ε. Its derivative g′ ~ −ε·cos(1/t)/t is not integrable near 0. So ω(γ₂)(γ₂′) is not interval-integrable, and Lean's `∫ t in 0..1` returns 0. The straight segment γ₁ has integral ≈ εc ≠ 0. So `hindependent` forces ω ≡ 0, and in that case f = 0 proves the conclusion. I re-derived this independently, and it agrees with triage-2.

**The revision** uses `∃ n (cuts : Fin (n+1) → ℝ), StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last n) = 1 ∧ ∀ i : Fin n, ContMDiffOn … γ (Icc (cuts i.castSucc) (cuts i.succ))`.
- This is the standard textbook notion (Lee: a continuous curve with a subdivision such that γ is smooth on each closed subinterval). The choice n = 0 is impossible, because it would need cuts 0 = 0 = 1, so there is at least one segment.
- Smoothness up to the endpoints of each closed segment makes the integrand bounded and piecewise continuous, so it is integrable. This removes the vacuity. For example, on ℝⁿ an exact ω = dh satisfies `hindependent` with ω ≠ 0.
- `ContMDiffOn` on `Icc` implies `ContMDiffAt` at interior points, so the unrestricted `mfderiv` in `LineIntegral` is the true velocity off the finitely many cuts.
- The statement is true by the usual proof: take a chart-convex neighbourhood (small ball ∩ range I, which is convex), append a chart segment, and differentiate in the endpoint. This shows f is C¹ with derivative ω, and since ω is smooth, f is smooth.
- The argument also works for Banach models and for `ModelWithCorners ℝ E E` with non-open convex range.

**Grade:** faithful. Part (a) is the smoothness of f, and part (b) is d f = ω. **Change:** correction.

## t03J01

**The current statement:**
- `CutsIntoTwicePuncturedTorus J := IsConnected Jᶜ ∧ HasPrimitiveClass J`
- `CutsIntoTwoOncePuncturedTori J := ¬IsConnected Jᶜ ∧ IsNullHomologous J`

The current statement is true, but `IsNullHomologous J₂` is the key step of (b). Given that hypothesis, (b) reduces to functoriality plus H₁(S¹) ≠ 0, which is what `apm_t03j01_no_retraction_of_curve_H1Map_zero` does. `HasPrimitiveClass J₁` supplies the dual class used in (a). Both are consequences of the connectivity conditions on a genus-2 surface, so the old and new statements have the same truth value. The revision is strictly harder to prove. That makes it an improvement rather than a correction of a false statement.

**The revision** reduces both predicates to `IsConnected Jᶜ` and `¬IsConnected Jᶜ`. X is compact, T2, path-connected and a smooth surface with H_* = (ℤ, ℤ⁴, ℤ, 0, …), so it is the orientable genus-2 surface Σ₂. Embedded topological circles in a surface are tame (Schoenflies).
- J₁: if J₁ does not separate, then χ = −2 with two boundary circles and a connected complement forces a twice-punctured torus. So the predicate is exactly the corrected prelim notion. A retraction exists: by classification J₁ is the standard a₁, then Σ₂ → T² (pinch the second handle) → S¹ (projection), composed with the inverse of the homeomorphism on a₁. This is true.
- J₂: every separating J₂ in Σ₂ is one of two kinds. It either cuts off two once-punctured tori (the prelim's case), or it bounds a disc. Both kinds are null-homologous, because J₂ bounds the closure of one complementary component. A retraction r would make id on H₁(J₂) = ℤ factor through 0. In the disc case J₂ is even null-homotopic. So ¬RetractsOnto J₂ holds for every separating curve. Note that Jᶜ ≠ ∅ automatically, so `¬IsConnected` really means "disconnected".

**"Stronger" is acceptable.** The extra disc-bounding curves make the claim strictly broader and still true, and they need no different argument. The prelim's χ defect (twice-punctured sphere → twice-punctured torus) is inherited correctly. The switch from `𝓘(ℝ, E2)` to `modelWithCornersSelf ℝ E2` is the same model with a different notation (neutral).

## t01J04

**The current statement is FALSE**, which triage-1 did not notice. It has no countability hypothesis on X. Counterexample:
- Take n = m = 1, X = Σ c : ℝ, ℝ (uncountably many lines; T2 and boundaryless, but not second countable), Y = ℝ, y = 0, U = (−½, ½), and f(c, x) = c + x².
- For any admissible V, the set cl V is compact and contains a neighbourhood of 0. Let s = max cl V > 0.
- On the sheet c = s, the preimage is {x : s + x² ∈ cl V} = {0}, an isolated point.
- No nonempty open subset of a 1-dimensional half-space is a single point, so f⁻¹(cl V) carries no half-space charted structure at all.

This is Sard failing for uncountably many critical values. So **`[SecondCountableTopology X]` is warranted**. It is the standard manifold convention, and it is exactly what the Sard step needs. Second countability of Y is not needed.

Separately, the old conclusion `∃ charts : ChartedSpace … S, IsManifold …` placed an abstract atlas on the subspace with no link to X's smooth structure (triage-1).

**The revised predicate** is `IsSmoothEmbeddedManifoldWithBoundary`: an atlas with values in the half-space (or Euclidean space when n = 0) on S = f⁻¹(cl V), `IsManifold`, `Subtype.val` `ContMDiff` into X, and injective `mfderiv` at every point. Together with the subspace topology, so that the inclusion is a topological embedding, this describes an embedded codimension-0 smooth submanifold with boundary. At interior points the inclusion is a local diffeomorphism. At boundary points the injective within-derivative on the half-space makes S locally a regular domain. Invariance of domain stops the chosen atlas from relabelling interior points as boundary points. This is what problem.md and its solution mean: a regular sublevel set {ρ∘f ≤ r}.

**The revision is true.** Take ρ = |·|² in a chart at y. By Sard (X is second countable and f is C^∞) there is a regular value r of ρ∘f with the ball of radius √r inside U. Set V = {ρ < r}, so cl V = {ρ ≤ r} ⊆ U. Then f⁻¹(cl V) = {ρ∘f ≤ r} is a regular domain in X. The cases where the preimage is empty or n = 0 are harmless.

**Grade:** faithful. **Change:** correction (false → true, and too weak → faithful).

## t01J06

**The current statement.** Parts (a) and (b) are faithful. I re-checked the coefficient of (a): for α = dx∧dy, the oriented coefficient Σ ±q_i α(Pe_j, Pe_k) evaluates to q₀·q₀q₂ + q₁·q₁q₂ + q₂·q₂² = q₂. So the integrand is (z+3)z, and ∫_{S²} (z² + 3z) dA = 4π/3. Part (c), `∃ zeta, zeta = projectionPullback alpha ∧ isJPullback p zeta alpha`, has no smoothness and no closedness, and `Refute.lean` proves it for every pointwise α by `rfl`. Part (c) is therefore vacuous, as triage-1 said.

**The revision of (c)** is `IsClosedProductExtension p alpha`: there exist an open W ⊆ E3×E2 containing S²×S¹ and Z : E5 → E5[⋀²]→ℝ with `ContDiffOn ⊤ Z W`, `extDeriv Z x = 0` on W, and j-pullback of the tangential restriction of Z equal to α.
- This is the standard ambient encoding of "a closed form on S²×S¹". A closed form on a neighbourhood restricts to a closed form. Conversely, a closed form on S²×S¹ pulls back along a tubular retraction to a closed form on a neighbourhood. So nothing is lost.
- It is true, with witness Z = pr₁*ρ*(i*ω) on W = (E3∖0)×E2, where ρ(x) = x/|x|. The form ρ*(i*ω) is closed because d commutes with pullback and i*ω is a top-degree form on S². At |q| = 1, dρ is the identity on T_qS², so the j-pullback gives α back. This uses `halpha`, because a non-smooth α would admit no smooth Z, so (c) is no longer a free `rfl`.

**Grade:** faithful. **Change:** correction. The only part not encoded is the "why closed" explanation in (b), which is acceptable.

## t95J03

**The current statement.** `T95J03SurfaceSpace (.orientable 0) = Surface true 0`, and `SurfaceRel true 0` is empty, so that slot is the closed disc (`Refute.lean`). `.nonorientable 0` is also a disc. So S² was absent from the domain, and a disc appeared twice. The theorem was still true, because the disc's finite covers are disjoint unions of discs and are never homeomorphic to a cover of K. So the old statement was narrower: it did not range over the closed surfaces.

**The revision:**
- The genus-0 orientable slot is now `Metric.sphere (0 : ℝ³) 1` = S².
- `.nonorientable` takes a `PNat` genus, which removes the bogus N₀.
- `Surface true (g+1)` uses the word a b a⁻¹ b⁻¹ per handle (the edge 4j glued to edge 4j+2 with the parameter reversed). This is Σ_{g+1}.
- `Surface false g` uses the word a a per crosscap. g = 1 is RP² (antipodal boundary identification), and g = 2 is K.
- So every connected closed surface appears exactly once.

**I checked the answer** (S_k = {T, K} for k even, {K} for k odd). It holds even though `T95J03IsKFoldCover` allows disconnected total spaces.
- Every k-fold cover E of K is compact, and each of its components E_i covers K with some degree d_i, where Σ d_i = k. Each E_i then has χ = 0, so it is T or K.
- If E is also a k-fold cover of F, then each component has χ = d′·χ(F). This forces χ(F) = 0, so F ∈ {T, K}.
- K is always in S_k (use the same cover twice).
- Covers of T are tori, and a torus covers K only with even degree, because the cover factors through the orientation double cover. So F = T needs k = Σ d_i with every d_i even, which means k is even.
- Conversely, for k even, T → T of degree k/2 followed by T → K of degree 2 is a connected k-fold cover of K by a torus. A degree-k self-cover of T gives the matching torus cover of T.
- S² and RP² have χ ≠ 0, so they are excluded.

Restricting to closed surfaces loses nothing:
- If F were noncompact, its finite covers would be noncompact.
- If F had boundary, its covers would have boundary.

Connectedness of F is needed, and it is the standard reading. For example, K⊔K would lie in S₂, because the connected double cover of each copy gives K⊔K, which is also the trivial double cover of K.

**Grade:** faithful. **Change:** correction (domain; the old statement was true but narrower).
