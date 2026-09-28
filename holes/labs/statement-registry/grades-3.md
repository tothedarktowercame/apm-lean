# Fidelity grades — list 3

Read-only review of problem.md against the current `theorem apm_<id>` (and the `apm_<id>_*` definitions it uses) in /home/joe/code/apm-lean. For REPAIRED items, the bank encoding and each listed repair commit were read with `git show`. Nothing was built or run.

| id | grade | one-line reason | repair classification |
|---|---|---|---|
| t00A05 | faithful | dω = 0 on the punctured domain, ∮C₁ = −2π, and every injective, counterclockwise C¹ parametrisation of the C₂ intersection gives −2π | — |
| t00J06 | vacuous | the conclusion allows a disconnected cover; the trivial cover `S × ℕ → S` with lift `x ↦ (f x, 0)` satisfies it, and the proof uses exactly that | — |
| t01A07 | narrower | part (b) is the mod-2 count (`Nat.card … % 2 = 0`) where the problem asks for the integer oriented intersection number (declared weakening) | c47897f6: correction (replaces the bank's opaque constant; narrower than problem.md, mod 2); 06c60dc2: improvement (pins the two intersection points) |
| t02A01 | hypothesis-carries-core | the encoding defines boundary components as fixed points of a commutator of translations in `ZMod n`, so the topology is in the definitions and the theorem is `abel` | — |
| t02A06 | stronger | (a) signs are correct and sum to 0; (c) degree is the actual map on H₃; (b) is strengthened from "no diffeomorphism" to "no homeomorphism" | f8f6a855: correction (three opaque placeholders replaced by concrete definitions; (b) strengthened) |
| t91A02 | hypothesis-carries-core | `HasFiniteCover` includes `χ(E) = sheets·χ(B)` as a conjunct, and `Surface g` is any compact connected space with χ := 2−g, so the result reduces to −14 ≠ −6k | — |
| t91A05 | stronger | no *continuous* retraction of the disk onto the circle, which covers the smooth/PL cases asked for | — |
| t91A08 | faithful | the real torus ℝ²/ℤ² with Haar integral: ∫β = 3, ∫g*β = 21 (det = 7), and g is not homotopic to id | 425ace9d: correction (removes the bank's opaque types, predicates and `axiom`); 4bbc8ab9: improvement (quotient torus, continuous form fields, Haar integral in place of evaluation at a basis) |
| t91J04 | faithful | nested closed bounded intervals `Icc (a n) (b n)` (a monotone, b antitone, a ≤ b) have nonempty intersection; there is no registered `apm_t91j04` | — |
| t92J03 | faithful | Baire: in a complete metric space, a countable intersection of open dense sets is dense | — |
| t92J09 | faithful | outward spherical parametrisation, the pullback of `x dy∧dz` evaluated on the tangent vectors, integral = 4π/3 | — |
| t93A04 | stronger (mild) | answers "yes" with a line transverse to f, which implies the preimage is a smooth submanifold; the domain is a finite-dimensional, Hausdorff, second-countable, boundaryless manifold | 26ed7b6b: correction (the bank's manifold type, smooth-map and submanifold predicates were `by sorry` definitions) |
| t94A05 | stronger | any charted space whose model is locally path-connected, which includes manifolds; there is no registered `apm_t94a05` | — |
| t94J03 | faithful | Tietze extension into ℝⁿ, and extension of Sⁿ-valued maps to an open neighbourhood | — |
| t94J08 | narrower | (a) only for n ≥ 1 (drops S⁰); (b) only for ambient dimension ≥ 2 and for fields on ℝ^{m+1} (index is local) | dff3d8c7: correction relative to the real bank 3c47a80a (a `DegreeTheory` hypothesis supplied the antipodal law), but it introduced a false n = 0 case; 5bbfd5c1: correction (n = 0 refuted: needs H₀(S⁰) ≅ ℤ) that also narrows (b) to m ≥ 1 |
| t95J01 | faithful | a closed continuous surjection with compact fibres from a Hausdorff space has a Hausdorff target | — |
| t96A03 | faithful | H₀ = ℤ, H₁ = 0, H₂ = ℤ³, Hₖ = 0 for k ≥ 3, on the actual quotient space, for every equator homeomorphism | — |
| t96J07 | narrower | fixed points are exactly the four axes; the local index is *defined* as sign det(I−df) in charts; "L(f)" appears only as the sum of indices, and the trace/homology Lefschetz number is never stated | 6f475b3c: correction (the bank was false at x = 0 because of parenthesisation; refuted by `apm_t96j07_not_fixed_axis_clause`) |
| t97J01 | faithful | adds `[T2Space X]`, without which the printed claim is false (identity on a non-Hausdorff space); the informal solution makes the same reading | — |
| t97J08 | narrower | (b) is faithful (∃! n: homotopy-defined degree = ∫f*β); in (a) β's formula is the definition, and `β = φ*α̂` is never stated | adc301ee: correction (the bank's closedness predicate and winding number were `by sorry` definitions) |

## Evidence notes

**t00A05.** `theorem apm_t00a05 : (∀ p : apm_t00a05_U, apm_t00a05_dOmega p.1 = 0) ∧ apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) = -2 * Real.pi ∧ (∀ γ, apm_t00a05_IsC2 γ → apm_t00a05_lineIntegral γ 0 (2 * Real.pi) = -2 * Real.pi)`.
- `dOmega` takes the three curl-type differences of the ω coefficients by `deriv`.
- `IsC2` requires: C¹; closed (`γ 0 = γ (2π)`); `InjOn γ (Ico 0 2π)`; both defining equations; and `0 < ∫ x y' − y x'`, which encodes counterclockwise.
- Values check: y dx − x dy on the unit circle gives −1, so ∮C₁ = −2π. The C₂ projection is a convex level set around the origin (`level (0,0) = 1 < 10`), so its winding number is 1 and ∮C₂ = −2π.
- Surjectivity onto the curve is proved, not assumed.

**t00J06.** The conclusion is `∃ X p, IsCoveringMap p ∧ (∀ s, (p ⁻¹' {s}).Infinite) ∧ ∃ lift, ∀ x, p (lift x) = f x`. It does not require X to be connected. The proof uses `refine ⟨ULift (S × ℕ), …, fun x ↦ Prod.fst x.down, …⟩` with lift `ULift.up (f x, 0)`. The genus-2 homology hypothesis `hS` is never used. The intended content (a lift to a connected infinite cover, via π₁(T²) → π₁(Σ₂) having abelian and hence infinite-index image) is absent.

**t01A07.** Current conclusion: `IsSmoothProjectiveHypersurface ∧ pointPlus ≠ pointMinus ∧ surface ∩ line = {pointPlus, pointMinus} ∧ Nonempty (Fin 2 ≃ intersection) ∧ Nat.card intersection = 2 ∧ Nat.card intersection % 2 = 0`.
- The header says "This is a declared weakening of the source's integer-valued oriented intersection request." The true integer answer is 0, because H₂(RP³; ℤ) = 0; it is not stated.
- Bank 59cc6c49: `opaque apm_t01a07_orientedIntersectionNumber … = 0`. An opaque constant says nothing that can be proved.
- 76595dc7 (an earlier header change, not in the list) introduced an ad hoc `localSign` (the sign of X·Y).
- c47897f6 drops that sign and moves to the mod-2 count: a correction of the bank's opaque defect, but narrower than problem.md.
- 06c60dc2 adds the explicit intersection set `{[1:1:0:0],[1:-1:0:0]}`: more content, closer to "compute".

**t02A01.** `boundaryMonodromy n a b := addRight a * addRight b * (addRight a)⁻¹ * (addRight b)⁻¹`, and `boundaryComponentCount := Nat.card {x // monodromy x = x}`.
- The theorem is `monodromy = 1 ∧ count = n`, closed by `ext; simp; abel`.
- Everything that makes this topology (regular cyclic cover ↔ ZMod n action, boundary loop = commutator, components = cycles of its monodromy) is in the definitions. Counting fixed points instead of cycles is only correct because the permutation is the identity.

**t02A06.** Current: (a) `∀ normal₁ normal₂, greatCircle normal₁ ≠ greatCircle normal₂ → ∃ e : Fin 2 ≃ intersection, localSign (e 0) = -localSign (e 1) ∧ signedIntersection e = 0`; (b) `¬Nonempty ((S2 × S2) ≃ₜ S4)`; (c) `∀ f : C(S3, T3), H3Map f = 0`.
- `localSign` = sign((n₁×n₂)·x). This matches sign((T₁×T₂)·x) for the tangents Tᵢ = nᵢ×x, so it is the correct local intersection sign.
- The answers (false, false, false) are correct.
- Bank 27da1a15 used `opaque apm_t02a06_orientedGreatCircleIntersection`, `opaque apm_t02a06_IsDiffeomorphism`, `opaque apm_t02a06_degree`. f8f6a855 made all three concrete: a correction, with (b) strengthened to homeomorphism.

**t91A02.** `structure apm_t91a02_Surface (genus) where Carrier … eulerCharacteristic : ℤ; euler_eq : eulerCharacteristic = 2 - genus`, and `HasFiniteCover E B := ∃ p sheets, IsCoveringMap p ∧ 0 < sheets ∧ E.eulerCharacteristic = sheets * B.eulerCharacteristic`.
- The theorem `¬HasFiniteCover E B` is closed by `omega` on −14 = k·(−6).
- Euler-characteristic multiplicativity, which is the argument the problem asks for, is a conjunct of the definition.
- The carrier is not tied to #16 RP² or #8 RP².

**t91A05.** `¬∃ g : Disk → Circle, Continuous g ∧ ∀ z, g (boundaryInclusion z) = z`. This is the topological version, which is stronger than smooth/PL. The bank f7ea2b22 has the same statement.

**t91A08.**
- Current definitions: `T91A08Torus := UnitAddCircle × UnitAddCircle`; `t91A08IsInduced beta := ∀ x v, beta (Cover x) v = 3 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)`; `t91A08IsPullback gamma beta := gamma p v = beta (g p) (Linear ∘ v)`; `t91A08Integral beta := ∫ p, beta p ![e₀, e₁]` (Haar measure, total mass 1).
- Conclusion: `Integral beta = 3 ∧ Integral gamma = 21 ∧ ¬Homotopic g id`.
- Bank d8f033b9 had `opaque apm_t91A08_TwoForm : Type`, `axiom apm_t91A08_twoFormNonempty`, and opaque `IsInduced`, `pullback` and `integral`, so (a) and (b) had no content.
- 425ace9d replaced these with a bilinear function and `integral := beta e₀ e₁`: a correction, though it made (a) and (b) evaluation at a basis.
- 4bbc8ab9 moved to the quotient torus, continuous form fields and a Haar integral: an improvement.

**t91J04.** The file has no `theorem apm_t91j04`; it is an old canary namespace, and grep finds no `apm_t91j04` anywhere. The theorem present is `nonempty_nested_inter (ha : Monotone a) (hb : Antitone b) (hAB : ∀ n, a n ≤ b n) : (⋂ n, Icc (a n) (b n)).Nonempty`. For nonempty closed bounded intervals, monotone/antitone endpoints are equivalent to nesting. "Using completeness" is a method instruction, not part of the statement.

**t92J03.** `[MetricSpace X] [CompleteSpace X] (hopen : ∀ n, IsOpen (U n)) (hdense : ∀ n, Dense (U n)) : Dense (⋂ n, U n)`.

**t92J09.** `param θ φ = (sinθ cosφ, sinθ sinφ, cosθ)`. ∂θ × ∂φ = sinθ·x points outward, so this is the boundary orientation. `pullbackOmega = ω(param)(dTheta, dPhi)`. The conclusion `sphereIntegral = 4/3 π` equals the volume of the ball, as expected.

**t93A04.** `ContMDiff … ∞ f → ∃ ℓ, IsSmoothLinePreimage f ℓ (f ⁻¹' ℓ)`, where `IsSmoothLinePreimage` requires ℓ = p + ℝv with v ≠ 0, and `range (mfderiv f x) ⊔ span {v} = ⊤` at every x with f x ∈ ℓ.
- Transversality implies the preimage is a submanifold, so the statement is slightly stronger than asked.
- Bank fb1e0bb7: `def T93A04SmoothManifold : Type := by sorry`, and similarly `IsT93A04SmoothMap` and `IsT93A04SmoothSubmanifold` were `by sorry`. 26ed7b6b is a correction; the current theorem text equals 26ed7b6b's.

**t94A05.** The file has no `theorem apm_t94a05` (old canary namespace). The theorem present is `connected_manifold_path_connected (H M) [ChartedSpace H M] [LocPathConnectedSpace H] [ConnectedSpace M] : PathConnectedSpace M`. This generalises manifolds, taking H = ℝⁿ.

**t94J03.** (a) `∀ f : C(A, ℝⁿ), ∃ F : C(X, ℝⁿ), ∀ a, F a = f a`; (b) `∀ f : C(A, Sⁿ), ∃ U, IsOpen U ∧ A ⊆ U ∧ ∃ F : C(U, Sⁿ), ∀ a, F ⟨a, _⟩ = f a`. `[NormalSpace X]` and `IsClosed A` are as in the source.

**t95J01.** `[T2Space X] (hcont) (hsurj) (hclosed : IsClosedMap π) (hcompact : ∀ y, IsCompact (π ⁻¹' {y})) : T2Space Y`. Reading "π⁻¹" as fibres is the only sensible reading.

**t96A03.** X is the quotient of `Sum S² S²` by the equivalence relation generated by `inl x ~ inr (h x)` on the equator, for an arbitrary homeomorphism h. The conclusion is H₀ ≅ ℤ, H₁ = 0, H₂ ≅ ℤ³, Hₖ = 0 for k ≥ 3. That is correct: four 2-cells attached along one circle. The header records that a reviewer's suggested ℤ² was wrong.

**t94J08.**
- Current (a): `∀ n, 1 ≤ n → HasDegree n antipodal ((-1)^(n+1))` on the sphere in ℝ^{n+1}, with degree taken as the actual map on integral Hₙ via an orientation iso.
- Current (b): for m ≥ 1, `HasLocalIndex v p r hlink d → HasLocalIndex (-v) p r hlinkNeg ((-1)^(m+1) * d)`.
- The list names 25bcef42 as the bank, but that commit's Main.lean is an empty canary namespace with no statement. The actual statement bank is 3c47a80a. Its `structure T94J08DegreeTheory` had a field `degree_antipodal_comp : degree k (antipodal ∘ u) = (-1)^k * degree k u`, which is the answer to both parts, supplied as a hypothesis.
- dff3d8c7 replaced that structure with homology degree. This is a correction of hypothesis-carries-core, but its n = 0 case asked for H₀(S⁰) ≅ ℤ and was false. The refutation is `diagnostic_refutes_frozen_theorem` in `holes/labs/topology-contract/evidence/t94j08-zero-sphere/T94J08ZeroSphereRefutation.lean`.
- 5bbfd5c1 restricts to `1 ≤ n` and `1 ≤ m`: a correction of the false case. The m ≥ 1 restriction in (b) is also a narrowing, since at m = 0 the old (b) was vacuously true rather than false.
- The classical S⁰ case and the 1-dimensional index case are no longer stated.

**t96J07.**
- Current conjunct 1: `∀ x, x ≠ 0 → (projectivelyEq x (A x) ↔ ∃ i, projectivelyEq x (axis i))`. The other conjuncts are `localIndex 0 = -1`, `localIndex 1 = 1`, `localIndex 2 = -1`, `localIndex 3 = 1`, and the sum = 0.
- `localIndex i` is `if 0 < ∏_{j≠i} (1 - (j+1)/(i+1)) then 1 else -1`, which is the correct chart formula. The values check: −6, +1/4, negative, positive.
- The global L(f) is only this sum. No trace-on-homology Lefschetz number is stated, and STATEMENT-REPAIR.md itself says it "adds no theorem comparing these definitions with an intrinsic projective derivative".
- Bank c769b0d3 had `(∀ x, x ≠ 0 → projectivelyEq x (A x) ↔ ∃ i, …)`, which parses with the ↔ outside the implication and is false at x = 0. The refutation `apm_t96j07_not_fixed_axis_clause` is kept in the file. 6f475b3c is a correction; the current theorem text equals 6f475b3c's.

**t97J01.** `[ConnectedSpace X] [ConnectedSpace Y] [T2Space X] (hp : IsCoveringMap p) (hfinite : ∀ y, (p ⁻¹' {y}).Finite) : T2Space Y`. The header and informal-solution.md both note that the printed claim is false without X Hausdorff (identity counterexample). Bank 742d4ad7 already had `[T2Space X]`.

**t97J08.**
- `t97J08Beta z v := (re z · im v − im z · re v) / (2π|z|²)`. This is the correct formula, but it is given as the definition; nothing states that it equals φ*α̂.
- Closedness is the coordinate cross-derivative equation.
- (b) is `∀ f, IsT97J08SmoothPuncturedLoop f → ∃! n : ℤ, IsT97J08WindingNumber f n ∧ (n : ℝ) = t97J08BetaIntegral f`, where the winding number is witnessed by a periodic unit-circle homotopy to `exp(i n t)`.
- Bank 1d344598 had `IsT97J08ClosedOneFormOnPuncturedPlane … := by sorry` and `t97J08WindingNumber … : ℤ := by sorry`. adc301ee is a correction; the current theorem text equals adc301ee's.
