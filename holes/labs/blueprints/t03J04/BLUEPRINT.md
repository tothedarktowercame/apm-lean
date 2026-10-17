# Blueprint for t03J04 (2026-10-17)

## Statement

`problems/t03J04/lean/Main.lean` is unregistered and has never been graded.
Earlier triage (triage-1, open-grades-2) called it "narrower-acceptable". I
grade it stricter. Each part is true as written, but (a)(i) is vacuous, and
(a)(ii) and (b) are weaker than the problem.

The repairs Main already made are fine and are kept:

- `n ≥ 1`. For n = 0, χ(T⁰) = 1.
- `X` connected. Otherwise extra components make χ(X) arbitrary.
- `T2Space X`. The doubled-point circle is a counterexample without it.
- Orientation dropped. This makes (b) stronger, and it stays true.

Part by part:

- **(a)(i) vacuous.** The conjunct says a function `Torus n → E n` is
  pointwise nonzero. Nothing makes it a vector field: there is no continuity,
  no smoothness, and no link to the charts. Any nonzero constant passes by
  `simp`. Also, the torus charts are free binders, so "smooth" would not even
  refer to the usual torus.
- **(a)(ii) weaker.** χ is defined as `Σ_{k ≤ n} (-1)^k finrank H_k`. But
  `finrank` is 0 on infinite-dimensional spaces, and the sum stops at n. So
  "= 0" does not certify that the homology is finite or vanishes above n. The
  repo's faithful notion, `HasEulerCharacteristic`, carries those
  certificates.
- **(b) weaker.** It has the same junk-value problem. A smaller point: it
  never shows the value 0 is attained.

`RevisedMain.lean` (compiles; its only `sorry` is the main theorem) makes
three changes:

1. **Pin the torus.** Keep the chart binder, and require
   `LieGroup (Model n) ∞ (Fin n → Circle)` for the pointwise group.
   - A topological group has at most one compatible Lie structure: a
     continuous homomorphism between Lie groups is smooth. So this is exactly
     the standard smooth torus.
   - `∞` is `C^∞` (`open scoped ContDiff`), not `ω`.
2. **(a)(i).** The constant field is `mulInvariantVectorField e₁`, the
   left-invariant field of the first coordinate vector. The statement asks
   that it be a `C^∞` section of the tangent bundle, and that its zeros be
   isolated, which is the problem's wording.
3. **(a)(ii) and (b).**
   - Use `HasEulerCharacteristic … 0`.
   - `X` now has the torus's own model. That is the same generality: ℝⁿ
     either way.
   - So `Tⁿ` is itself an admissible `X`. The last conjunct (`id` is a local
     diffeomorphism) records that 0 is attained. Together with (a)(ii), this
     answers "list all possible values" with {0}.
   - `BoundarylessManifold` is dropped, because the model has no boundary.

Outside grade: not yet requested. Install only after a `faithful` grade.

## Verdict

True. The answer to (b) is χ(X) = 0.

- φ is a k-sheeted covering with k ≥ 1.
- χ(Tⁿ) = k·χ(X).
- χ(Tⁿ) = 0, so χ(X) = 0.

## Route

**(a)(i).** Mathlib proves that invariant fields are `C^{minSmoothness 2}`.
The same proof gives `C^∞` for a `C^∞` Lie group (A1). Left translation is a
diffeomorphism, so the field is nowhere zero (A2). So there are no zeros to
isolate.

**(a)(ii).** No Künneth.

- Rational Mayer–Vietoris (`RP3Homology.rationalMayerVietoris`, banked and
  sorry-free) plus a linear-algebra lemma give
  χ(U ∪ V) = χ(U) + χ(V) − χ(U ∩ V), including finiteness of H_*(U ∪ V) (B1).
- Cover S¹ by two arcs. Their overlap is two disjoint arcs. This gives
  χ(S¹ × Y) = χ(Y) + χ(Y) − 2χ(Y) = 0 whenever χ(Y) exists (B6).
- Induct with `T^{m+1} ≃ₜ S¹ × T^m`, starting from χ(point) = 1. This
  assembly is sorry-free.

**(b).**

- φ is a k-sheeted cover with k > 0 (C1). X is compact, as the image of the
  torus.
- Euler multiplicativity for a k-sheeted cover of a base with a finite good
  cover (C2d). The proof is MV induction on the size of the family. Over each
  contractible piece the cover is trivial (C2a), so the preimage of a piece
  has χ = k (C2b).
- X has a finite good cover (C3, the gap).
- Uniqueness of χ (banked `SurfaceGroupBetti.hasEulerCharacteristic_unique`)
  gives k·c = 0, so c = 0. This assembly is sorry-free.

The banked covering transfer (`CoefficientCoveringTransfer`) is **not** used.
`transfer ≫ p_* = k` only makes p_* onto. It does not give χ(E) = kχ(B), as
the codex-13 STOP said. Some finiteness of the base is essential. Example:
S^∞ → RP^∞ is a double cover of spaces with finite rational homology, yet
χ = 1 on both, not 2 = 2·1.

## Leaves (16)

| leaf | content | est. lines | banked lemmas used |
|---|---|---|---|
| A1 `t03J04_mulInvariant_contMDiff` | invariant field is C^∞ on a C^∞ Lie group | 40–80 | Mathlib `contMDiff_mulInvariantVectorField` (copy, order ∞) |
| A2 `t03J04_mulInvariant_ne_zero` | invariant field of v ≠ 0 is nowhere zero | 30–60 | `inverse_mfderiv_mul_left`, `LieGroup.of_le` |
| B1a `t03J04_euler_les` | linear algebra: a bounded long exact sequence; C is finite and bounded; the alternating sum is 0 | 150–250 | `LinearMap.finrank_range_add_finrank_ker` |
| B1b `t03J04_mv_surjective_zero` | `H₀(U) ⊕ H₀(V) → H₀(X)` is onto | 60–150 | `CoefficientH0` generators / point classes |
| B1 `t03J04_hasEuler_mayerVietoris` | **layer 2** (B1a, B1b): χ(U∪V) = χU + χV − χ(U∩V) | 100–200 | `RP3Homology.rationalMayerVietoris`, `mvI`/`mvJ`, `ModuleCat.biprodIsoProd` |
| B2 `t03J04_hasEuler_of_homotopyEquiv` | homotopy invariance of χ | 40–80 | `CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv` |
| B3 `t03J04_hasEuler_unit` | χ(point) = 1 | 40–80 | Mathlib `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`, `isZero_…_of_totallyDisconnectedSpace` |
| B4 `t03J04_hasEuler_of_isEmpty` | χ(∅) = 0 | 30–60 | same |
| B5 `t03J04_circle_cover` | S¹∖{1}, S¹∖{−1}, and the open half-circles are contractible; the overlap is their disjoint union | 120–220 | `Circle.exp`, `ContractibleSpace` API |
| B6 `t03J04_hasEuler_circle_prod` | **layer 2** (B1, B2, B4, B5): χ(S¹ × Y) = 0 | 150–250 | `Homeomorph.Set.prod`, `t03J04_hasEuler_prod_contractible` (proved here) |
| C1 `t03J04_localDiffeo_isKSheeted` | φ is a k-sheeted cover, k > 0 | 100–200 | `IsCoveringMapOn.of_openPartialHomeomorph`, `isCoveringMap_iff_isCoveringMapOn_univ`, `t03J04_localDiffeo_surjective` (proved here) |
| C2a `t03J04_trivial_over_contractible` | a cover is trivial over a contractible open set | 120–250 | Mathlib `Topology/Homotopy/Lifting`, `CoveringLiftRestriction.card_lifts` |
| C2b `t03J04_hasEuler_prod_fin` | **layer 2** (B1, B4): χ(U × Fin k) = kχ(U) | 60–120 | — |
| C2c `t03J04_isKSheeted_restrictPreimage` | restriction of a k-sheeted cover | 30–60 | `IsCoveringMap.restrictPreimage` |
| C2d `t03J04_euler_mul_of_goodFamily` | **layer 3** (B1, B2, B4, C2a–c): multiplicativity over a finite good cover | 200–300 | — |
| C3 `t03J04_compact_manifold_goodCover` | **GAP**: a compact smooth manifold has a finite good cover | 2000+; own blueprint | none (not in Mathlib) |

These are independent and can start now: A1, A2, B1a, B1b, B2, B3, B4, B5,
C1, C2a and C2c. These wait on other leaves: B1 (on B1a, B1b), then B6 and
C2b, then C2d. C3 is independent but not seat-sized.

Sorry-free here:

- `t03J04_hasEuler_of_finrank` (trace of the identity is `finrank`)
- uniqueness of χ
- `t03J04_e1_ne_zero`
- `t03J04_prodContractible`
- `t03J04_torusSucc` (`T^{m+1} ≃ₜ S¹ × T^m`)
- `t03J04_hasEuler_torus_all` (χ(T^m) = [m = 0])
- the model-space `LocPathConnectedSpace` instance
- `t03J04_localDiffeo_surjective` (Main's proof)
- the main assembly

## Truth checks

- **A1, A2.** True for any C^∞ Lie group over ℝ. For n = 0, A2 is vacuous:
  `e₁` does not exist and NeZero excludes the case.
- **B1a.** Finiteness of `C k`:
  - k = 0: `C 0` is the image of `B 0`.
  - k ≥ 1: `C k` is an extension of `range d ⊂ A (k−1)` by `range g ⊂ C k`,
    both finite.
  - Vanishing: for k ≥ N+2, `B k = 0` makes `d (k−1)` injective into
    `A (k−1) = 0`.
  - The sum: it is the alternating sum along
    `0 → C(N+1) → A N → … → C 0 → 0`.
  - Hand-checked at N = 0: `c₁ − a₀ + b₀ − c₀ = 0`.
- **B1b.** True for every X, including empty X: point classes span H₀ and
  each point lies in U or V.
- **B1, B2, B3, B4.** Standard. U ∩ V may be empty.
- **B5.** In ℂ: (S¹∖{1}) ∩ (S¹∖{−1}) = {Im > 0} ⊔ {Im < 0}. Each set is
  `Circle.exp` of an open interval of length at most 2π.
- **B6.** Matches Künneth (χ = 0·χ(Y)). Also true for Y = ∅.
- **Torus induction.** χ(T⁰) = 1; for m ≥ 1, χ(T^m) = 0.
- **C1.**
  - The torus is compact and Hausdorff, and X is Hausdorff. A local homeo
    from a compact space to a Hausdorff one is a covering onto its image,
    and the image is all of X (clopen, X connected).
  - Fibres are finite, and their cardinality is locally constant, hence
    constant. k ≥ 1 by surjectivity.
  - n = 0: X is a point and k = 1.
- **C2a.**
  - k = 0 gives an empty preimage, which is fine.
  - B is locally path-connected, so the open U is too. A contractible U is
    simply connected, so the cover over U is trivial.
- **C2b.** k = 0: the product is empty and χ = 0.
- **C2d.**
  - The empty family gives B = ∅ and E = ∅.
  - Induction step: `{V ∩ U}` is again good, because its intersections are
    intersections of the original family.
  - Singleton step: χ(U) = 1 and χ(p⁻¹U) = k.
- **C3.** True: Bott–Tu Thm 5.1. A compact Hausdorff manifold is paracompact,
  so a Riemannian metric exists, and its geodesically convex balls give the
  cover. Finite intersections of convex sets are convex, hence contractible.
  For n = 0, X is finite and discrete, and the singletons are a good cover.

## Checks

- `RevisedMain.lean`: 0 errors. One `declaration uses sorry`, on `apm_t03j04`.
- `Blueprint.lean`: 0 errors. Exactly 16 `declaration uses sorry` warnings,
  on the 16 leaves at lines 81, 89, 110, 131, 140, 149, 156, 161, 169, 195,
  243, 257, 265, 271, 281 and 292.
- `#print axioms`:
  - `apm_t03j04`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
    `sorryAx` enters only through the leaves.
  - `t03J04_hasEuler_of_finrank`: no `sorryAx`.
- Byte-identical blocks between the two files, checked by script:
  - the definitions, from `open CategoryTheory Filter Topology` to before the
    blueprint section;
  - the statement of `apm_t03j04`, through `:= by`.
- Imported modules are sorry-free: `CP2RationalHomology`,
  `CoefficientContractiblePair`, `CoveringDegree`, `RationalLefschetz`,
  `SurfaceGroupBetti`. The two `sorry` hits in SurfaceGroupBetti are inside
  comments.
- Compile command used: `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean <file>`.

## Risks

- **C3 is a real gap.** It needs at least:
  - Riemannian metric existence (partition of unity);
  - geodesics / the exponential map;
  - Whitehead convex neighbourhoods;
  - convex ⇒ contractible.

  None of this is in Mathlib. Plan it as its own blueprint, or replace C3 by
  another finite-type input. Options considered and rejected as no cheaper:
  - **Transfer plus traces.** This needs a Lefschetz fixed-point or
    coincidence theorem on the torus, plus `H_*(Tⁿ) = Λ*(ℚⁿ)` naturally.
  - **Bieberbach group theory.** This needs asphericity, Hochschild–Serre,
    and torsion-freeness of π₁(X).
  - **ENR / tubular neighbourhood.**

  One cheaper variant is possible: C2d only needs nonempty intersections to
  be "evenly covered with finite-type homology", not contractible. That does
  not obviously make C3 easier.
- **Lie-group pin.** A grader may object to the `LieGroup` binder. It is
  satisfiable (by the standard product structure) and it is unique. But
  Mathlib has no `IsManifold`/`LieGroup` instance for pi types, so
  non-vacuity is argued, not proved, in Lean. The original Main had the same
  issue with its free `IsManifold` binder.
- **(a)(i) wording.** The field is given explicitly, not existentially. If a
  grader prefers "∃ smooth field with isolated zeros", the leaves still
  apply.
- **B1a and C2d are the largest seats.** If either runs long, split it:
  - B1a into finiteness/vanishing and the alternating sum;
  - C2d into the intersection-family lemma and the MV step.
- **B6 involves subtype-of-subtype work.** The intersection of the two pieces
  is split again inside `↥((U ∩ V) ×ˢ univ)`. State small homeomorphism
  lemmas first.
- **Lost fixture.** codex-13 compiled an `actual_finite_cover` (covering,
  surjective, finite fibres) in `/tmp/T03J04EulerDiagnostic.lean`. That file
  is gone, so C1 must be redone.

## Grade

Outside grade 2026-10-17: **faithful**, no changes required (`statement-registry/t03J04-repair-grade.md`). Installed as Main (c1b3bc0f5) and admitted (13c28cdc6). The statement block of `Blueprint.lean` is now identical to Main.
