# Blueprint for t91A02 (revision 2026-10-15, stage-1 pilot)

The previous blueprint (2026-10-13: χ(N16) = -14, χ(N8) = -6, χ-transfer,
all LIBRARY) is archived in `old-2026-10-15/`. Its one proved lemma,
`t91A02_hasEulerCharacteristic_unique`, is kept in the new file. The new route
does not use it.

## Verdict

The statement is true and unchanged; `apm_t91a02` is byte-identical to
`problems/t91A02/lean/Main.lean`. Mathematically: a 16-crosscap surface does
not cover an 8-crosscap surface because χ = -14 is not a multiple of -6.

## Route chosen: π₁ and rational b₁ of groups (no Euler characteristic)

`b₁(G) := finrank_ℚ (Additive G →+ ℚ)`.

1. Banked (`CoveringMonodromyCosets`): a connected cover E → B with fibres
   of size k makes π₁(E) ≅ an index-k subgroup H of π₁(B).
2. For any one-vertex `PairingData` P, π₁(P.Space) ≅ F_n ⧸ ⟪r⟫. Here n is
   the number of edge orbits, and r is rationally nonzero iff
   `attachingDegree P ≠ 0` (leaves T1 and T2).
3. Rank-only Reidemeister–Schreier: H ≅ H̃ ⧸ ⟪t₁..t_m⟫, where H̃ ≤ F_n has
   index k and 1 ≤ m ≤ k, and every tᵢ is a conjugate of r (leaf A3).
   Banked Schreier gives H̃ ≅ F_{(n-1)k+1}. With A1 and A2:
   `(n-1)k+1 ≤ b₁(H)+k`, `b₁(H) ≤ (n-1)k+1`, and `b₁(H)+1 ≤ (n-1)k+1` when r is
   rationally nonzero.
4. Apply this to N16 → N8: b₁(π₁N16) = 15 by the one-relator case. So
   7k+1 ≤ 15+k gives k ≤ 2, and 16 ≤ 7k+1 gives k ≥ 3. Contradiction (omega).

The H₂ of the cover is never needed. Upper and lower bounds on b₁ already
contradict each other.

## Alternatives considered (honest sizes)

| route | what is missing | estimate |
|---|---|---|
| (a) lift the cell structure, χ by counting cells | the homology of a multi-vertex, multi-face polygon complex (cellular = singular), plus building the lifted complex inside an abstract cover | 1200–2500 lines |
| (b) homology transfer | banked `CoefficientCoveringTransfer.rational_homology_projection` gives only p_*∘τ = k, so p_* is onto, which yields inequalities 15 ≥ 7. For an irregular cover, the χ formula needs Mayer–Vietoris additivity of χ, triviality of covers over disks, and χ of graph covers | 900–1500 |
| (c) π₁ + b₁ inequalities (**chosen**) | T1 (polygon van Kampen) is the only big piece; the rest is small algebra | 600–1100 total |
| (d) Z/2 counting | H₁(N_g;Z/2) = g; transfer mod 2 only gives inequalities. No exact relation without the work in (a) or (b) | — |

Why χ is not used: no banked result relates the χ of an abstract cover to
the χ of its base. All exact routes need the homology of the lifted cell
complex. The b₁ inequalities avoid this, and they are enough here.

## Leaves (each a top-level `lemma … := by sorry` with route docstring)

Algebra (generic, any group):

- `t91A02_b1_freeGroup` — Hom(F_n,ℚ) ≅ ℚⁿ, finite-dimensional of dimension n
  — 40–80 lines.
- `t91A02_b1_quotient_normalClosure_bounds` — given a finite S:
  b₁G ≤ b₁(G⧸⟪S⟫)+|S|, b₁(G⧸⟪S⟫) ≤ b₁G, and the bound drops by at least 1 if
  some φ is nonzero on S (rank–nullity for the evaluation map on S)
  — 100–180 lines.
- `t91A02_finiteIndex_relators` — H ≤ G⧸⟪r⟫ of index k>0 is H̃ ⧸ ⟪T⟫, with T
  nonempty, |T| ≤ k, and T made of conjugates of r (transversal argument)
  — 120–200 lines.

Topology (generic, any one-vertex `PairingData`):

- `t91A02_polygon_pi1_wedge_quotient` — π₁(P.Space,x) ≅ π₁(orbit
  wedge) ⧸ ⟪`polygonBoundaryFundamentalClass P`⟫ — **LIBRARY-sized**.
  - 150–300 lines if the t97A01 leaf `P.Space ≃ₜ Cell(polygonBoundaryWedgeLoop P)`
    lands first (then this is `cell_piOne` + `cell_facts` + a basepoint
    change).
  - 400–700 lines if it generalizes the genus-two van Kampen specialization
    in `GenusTwoSurfacePiOne` over P.
  - Should be split further when dispatched (see Risks).
- `t91A02_polygonBoundary_freeWord` — the wedge π₁ is free on
  Fin (#orbits), and the boundary word is rationally nonzero iff
  `attachingDegree P ≠ 0`. Uses banked free wedge plus Hurewicz leg
  coordinates — 120–250 lines.

Specific:

- `t91A02_standard_nonorientable_data` — standard g-crosscap data has g orbits
  and attaching degree −2 on each orbit (≠ 0) — 50–120 lines.

Sorry-free assemblies written here: `t91A02_b1_congr`, `t91A02_homCongr`,
`t91A02_b1_oneRelator`, `t91A02_b1_finiteIndex_bounds` (uses banked
`finiteIndexSubgroupFreeGroupEquiv`), `t91A02_quotientSingletonCongr`,
`t91A02_fundamentalGroupEquivOfHomeomorph` (copied from t97A01Closure),
`t91A02_polygon_presentation`, `t91A02_surface_pathConnected`,
`t91A02_surface_presentation`, `apm_t91a02`.

## Reuse

- **t98A01** (5-fold regular Σ_g → Σ_h with Σ_g ≅ Σ_h): uses T1, T2, A1–A3,
  `t91A02_b1_finiteIndex_bounds`, and the same cover → subgroup step.
  - It also needs an orientable twin of the crosscap data leaf: 2g orbits,
    attaching degree 0.
  - Lower bound: 10h−9 ≤ b₁(Σ_g) = b₁(Σ_h) ≤ 2h, so h ≤ 1. The disk case
    h = 0 has trivial π₁, so an index-5 subgroup is impossible. Hence h = 1.
  - Then b₁ ∈ [2g−1, 2g] forces g = 1, and χ = 0 = 5·0.
  - Regularity is not used.
- **t95J03** (who shares a k-fold cover with the Klein bottle): uses T1, T2,
  A1–A3, plus the banked path-component restriction for disconnected covers.
  - On each component, the lower bound against F plus the upper bound
    b₁ ≤ k_i against K (relator a²b², rationally nonzero), summed over
    components, gives (n_F−2)k + #components ≤ k. So n_F ≤ 2: F is T² or K,
    with RP² and S² excluded because their finite π₁ gives b₁ = 0 < 1.
  - The parity clause ("torus only for even k") needs an orientation
    character argument that these leaves do not supply.
- t91J05, t94J04, t96A01 (exact χ = k·χ for classification): these need the
  exact formula, which b₁ inequalities do not give. Exact χ stays stage-2
  work, via (a) or (b).

## Checks

- `lake env lean holes/labs/blueprints/t91A02/Blueprint.lean`: 0 errors;
  `declaration uses sorry` appears on exactly the 6 leaves.
- In a scratch copy, `#print axioms apm_t91a02` gives
  [propext, sorryAx, Classical.choice, Quot.sound]. sorryAx comes only through
  the leaves.
- The statement block was diffed against Main: identical.
- Edge cases checked by hand:
  - k > 0 is from the statement; n = 8 and 16 are > 0 for Schreier.
  - A3 with r = 1 is fine (T = {1}).
  - A1 with n = 0 is fine.
  - The attaching degree for crosscaps is −2 per orbit: all signs are
    `false` and each orbit is {2j, 2j+1}.
  - T1 is insensitive to the orientation of the boundary class, because
    ⟪c⟫ = ⟪c⁻¹⟫.

## Risks

- T1 is still large. Dispatch it after (or merge it with) t97A01's generic
  polygon ≅ Cell(word) leaf; otherwise split it into: radial-cover van Kampen
  (generalize genus-two aux lemmas), outer ≃ wedge transport, and matching
  the overlap generator to `polygonBoundaryFundamentalClass`.
- T2 has to align `finiteWedge_finSucc_fundamentalGroup_free`'s leg
  coordinates with `finiteWedgeLegFundamentalClassAtBase` and the Hurewicz
  coordinates. These live in two different files (GenusTwoSurfacePiOne and
  PolygonSurfaceHomology).
- A3's transversal bookkeeping in subtypes of subtypes may be fiddly. The
  statement is a plain existential, so the seat chooses its own encoding.
