# t96A06 blueprint (revised 2026-10-17)

The previous version (10-14 / 10-15) is in `old-2026-10-15/`.

## Verdict

The statement is true and faithful. `Main.lean` is unchanged.

Only one fact is still open: the descended map acts by multiplication by 4
on `H₃(ℝP³; ℚ)`. Everything else is already proved and sorry-free in
`Blueprint.lean`:

- H₀: trace 1;
- H₁ and H₂: trace 0;
- finiteness, and vanishing above degree 3;
- the identity has trace 1 on H₃;
- homotopy invariance;
- the Lefschetz sum `1 - 4 = -3`, and the non-homotopy argument.

All of this rests on the banked, sorry-free
`ConstructionTargets/RP3RationalHomology.lean`. It gives
`H_*(ℝP³; ℚ) = ℚ, 0, 0, ℚ` through the double cover `S³ → ℝP³` and the
transfer. Seats closed five of the old eight leaves on top of it.

The old leaf `trace_three` (100–150 lines) is now replaced by **8 small
leaves**, and the old proof of it is now a sorry-free assembly.

## Route

Write `x = (u, w)` with `u = x₀ + i x₁` and `w = x₂ + i x₃`.

1. **Lift (sorry-free).** Let `g x = F(x)/‖F(x)‖` on `S³`. Then
   `f̄ ∘ p = p ∘ g`, by the descent formula and the banked
   `proj_cover_aux_comp_radial`.
2. **Factor (leaf H).** Let `Q` be "square and renormalise" on the
   `(x₀, x₁)` plane: `u ↦ u²/|u|`, other coordinates fixed. Let
   `Q' = P ∘ Q ∘ P⁻¹` do the same on the `(x₂, x₃)` plane, where `P` swaps
   the two planes. Then `g ≃ Q ∘ Q'`. The two maps are never antipodal.
3. **Suspension (leaves N1, S1, S2, S4).** `Q` preserves norms and commutes
   with `x ↦ x/2`; we call such a map a "cone map". The banked sphere-shift
   naturality (`CoefficientOrthogonalSphere`) is proved for linear
   isometries, but its proof only uses those two properties. Leaf N1
   restates it for cone maps. From N1, I proved sphere-shift naturality for
   cone maps with no sorry. `Q` on `S^{n+1}` is the suspension of `Q` on
   `S^n` (S4). So `deg Q` is the same on `S³` as on `S¹`.
4. **Circle (leaves C1a, C1b, C2).** `deg Q = 2` on `S¹`. Use an
   angle-displacement cochain `W`. On each 1-simplex, `W` is
   `L(v₁) - L(v₀)` for a lift `L` through `t ↦ (cos 2πt, sin 2πt)`. `W`
   kills boundaries. Squaring doubles it. It is 1 on the standard loop. So
   on the one-dimensional `H₁(S¹; ℚ)`, squaring acts by 2.
5. **Assembly (sorry-free).** `Q'_* = P⁻¹_* · 2 · P_* = 2`, by the banked
   `permutation_inverse`. So `g_* = 4`. The banked
   `rational_homology_projection` gives `T ≫ p_* = 2`. So `p_*` is onto, and
   `p_* ≫ f̄_* = 4 · p_*` forces `f̄_* = 4`. Then the trace is
   `4 · finrank = 4`.

**Why this route and not the loop's.** The loop went for a regular-value
local-degree count. To get there it needed local homology at four
preimages, orientation signs from Jacobians, and an integral-to-rational
comparison of local generators. Its rows on Unit/Bool H₀ comparisons,
coproduct composites, and "sphere-shift local normalisation" are all
plumbing for that sign computation. The route here uses no local homology,
no signs, and no integral homology. Every degree is a scalar on a banked
one-dimensional rational group, and the only geometry is the circle
cochain.

The universal-coefficients bridge (t98A01, three leaves) is **not needed**.
Everything stays rational from the start. t98A01 still needs that bridge for
its own reasons.

The loop's older residual ("antipodal-quotient homeomorphism and two-sheeted
covering") is already closed by `RP3Homology.proj_cover`.

## Leaves

All 8 leaves are independent. No leaf uses another leaf's proof. Some
statements mention the definition `sqCone`, whose Prop fields are filled by
S1 and S2. That is a dependency in the statement only, not in the proof.

| leaf | content | est. lines | banked lemmas used |
|---|---|---|---|
| `T96A06_coneMap_sphereToDisk_naturality` (N1) | `CoefficientOrthogonalSphere.sphereToDisk_naturality` with the isometry `Q` replaced by a `ConeMap` | 150–250 | copy `CoefficientOrthogonalRadial` (radial square) and `CoefficientOrthogonalSphere` (coordinate and excision squares) line by line; `Q.norm_map` becomes `ψ.norm_map`, `Q.map_smul (1/2)` becomes `ψ.map_half`, injectivity becomes the norm |
| `T96A06_sqFun_continuous` (S1) | `u ↦ u²/‖u‖` (with `0 ↦ 0`) is continuous on `ℝ^{n+2}` | 40–100 | none; at `u = 0` the new coordinates are bounded by `‖u‖` |
| `T96A06_sqFun_norm_half` (S2) | it preserves norms and commutes with halving | 40–90 | `EuclideanSpace.norm_eq`; `(a²-b²)² + (2ab)² = (a²+b²)²` |
| `T96A06_sqCone_suspension` (S4) | `sphereAction (sqCone n) = boundaryAction (sqCone (n+1))` | 25–60 | `euclideanSnoc`, `euclideanInit`, `Fin.snoc` / `Fin.lastCases` |
| `T96A06_angleMap_isCoveringMap` (C1a) | `t ↦ (cos 2πt, sin 2πt)` into `S¹ ⊂ ℝ²` is a covering map | 40–100 | `CircleUniversalCover.circleCover_isCoveringMap` or `AddCircle.isCoveringMap_coe`, moved along `Circle ≃ₜ S¹` |
| `T96A06_circle_windingCochain` (C1b) | given C1a as a hypothesis: there is a cochain `W : C₁(S¹;ℚ) → ℝ` with `W ∘ d₂ = 0`, `W ∘ sq_# = 2W`, and a cycle `c` with `W c ≠ 0` | 150–250 | `IsCoveringMap.existsUnique_continuousMap_lifts`; build it like `CoefficientCoveringTransfer.transferDegree` (`Sigma.desc`, `generator_transfer`, `simplex_boundary`); `CoefficientH0.singularGenerator_boundary`, `SingularSubdivision.singularSimplexOfContinuousMap_face`, `singularGenerator_singularPostcomposition` |
| `T96A06_circle_degree_of_cochain` (C2) | given such `W` and `c`: squaring is `2 • 𝟙` on `H₁(S¹; ℚ)` | 80–150 | `CoefficientFirstReflection.topIso ℚ 0` (`H₁ ≅ ℚ`); `HomologicalComplex` `homologyι`, `descOpcycles`, `liftCycles` |
| `T96A06_liftMap_homotopic` (H) | `g ≃ Q4 ∘ Q4'` on `S³` | 80–150 | none; normalised straight-line homotopy; `permutation_apply` |

Sorry-free glue in the file:

- `ConeMap` with its four actions;
- `closedPair`, and `coneMap_sphereShift_naturality` (from N1 plus the
  banked `connecting_naturality` and `sphereShift_hom`);
- `sqCone`, and `sqSphere_degree` (induction: C1a/C1b/C2 for the base,
  N1 and S4 for the step);
- `liftMap`, `projC`, `lift_square`;
- `Q4_degree`, `perm_cancel`, `Q4'_degree`, `liftMap_degree`,
  `descent_degree`;
- `T96A06_polynomialDescent_trace_three`, the invariants, and `apm_t96a06`.

## Truth checks (by hand)

- **N1.** Each square in the banked chain of isomorphisms commutes on the
  nose at the level of pair maps. The facts used are: height is preserved;
  `‖ψ x‖ = ‖x‖` (so the disk, the punctured disk, the boundary, and
  `√(1-‖x‖²)` are all preserved); and `ψ(x/2) = ψ(x)/2`. The case `n = 0`
  is fine. The hypothesis `j ≠ 0` is the one the banked isomorphism already
  needs.
- **S1 / S2.** With `r = √(a²+b²)`: if `r > 0` the new plane coordinates
  have norm `r²/r = r`. If `r = 0` they are `0/0 = 0` in Lean, which is
  correct. Halving: `(N/4)/(r/2) = (N/r)/2`.
- **S4.** Coordinates 0 and 1 of `ℝ^{n+3}` are `castSucc` of coordinates
  0 and 1 of `ℝ^{n+2}`. The last coordinate is neither, since `n+2 ≥ 2`.
- **C1b.** Faces of `[v₀,v₁,v₂]` are `[v₁,v₂]`, `[v₀,v₂]`, `[v₀,v₁]` with
  signs `+ - +`. The terms `(L₂-L₁) - (L₂-L₀) + (L₁-L₀)` cancel. The
  complex is unnormalised, so the loop simplex is a cycle because
  `d σ = σ(v₁) - σ(v₀) = 0`. On `S¹` the cone map is exactly
  `(a,b) ↦ (a²-b², 2ab)`, because `r = 1` there.
- **C2.** `W` descends to `w : H₁ → ℝ` with `w[c] ≠ 0`. So `[c] ≠ 0`
  spans the one-dimensional `H₁`. `s_*[c] = λ[c]` and `w(s_*[c]) = 2w[c]`,
  so `λ = 2`.
- **H.** I checked the permutation conventions: `permutation e x j =
  x (e.symm j)`, with `e = swap 0 2 * swap 1 3`. They give
  `Q4' x = (u, w²/|w|)` and `Q4 (Q4' x) = (u²/|u|, w²/|w|)`. Also
  `g x = (u², w²)/‖(u², w²)‖`. If `g x = -Q4(Q4' x)`, then `u² = w² = 0`,
  which is impossible on `S³`.
- **Assembly.** `L(f̄) = 1 - 0 + 0 - 4 = -3`. The identity has H₃ trace 1,
  not 4, so `f̄` is not homotopic to the identity.

## Checks

- `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean holes/labs/blueprints/t96A06/Blueprint.lean`
  - 0 errors.
  - Exactly 8 `declaration uses sorry` warnings, at lines 297, 350, 355,
    369, 388, 404, 417 and 509. These are exactly the 8 leaves.
  - `#print axioms apm_t96a06`: `propext, sorryAx, Classical.choice,
    Quot.sound`.
- The statement block is byte-identical to `Main.lean`. Checked by script:
  the preamble from `open ConstructionTargets.ProjectiveSpaceTopology` up to
  `theorem apm_t96a06` (27 lines), and the 6-line theorem statement, both
  appear verbatim.
- Banked declarations are sorry-free (`#print axioms`: `propext,
  Classical.choice, Quot.sound` only): `rp3_rationalHomology`,
  `proj_cover`, `proj_cover_aux_comp_radial`, `rational_homology_projection`,
  `permutation_inverse`, `connecting_naturality`, `rp3RationalH0Iso`,
  `rp3PathConnectedSpace`, `CoefficientConnectedH0Map.mapIso_hom`, and
  `t96A06Polynomial_descends`. `t96A06Closure.lean` contains no `sorry`
  at all.

## Risks

- **C1b** is the biggest leaf. It has the most API friction: defining a
  linear map out of the chain coproduct, and the face-map bookkeeping. The
  transfer construction in `CoefficientCoveringTransfer` is a close
  template. If it runs long, split it into three: define `W` on generators;
  prove it kills `d₂`; prove naturality plus the loop.
- **N1** is mechanical, but it copies about 230 lines across two files. A
  seat should copy rather than rederive.
- **C2** uses the `HomologicalComplex` homology API (`homologyι`, opcycles).
  Elementwise reasoning in `ModuleCat` can be fiddly, but nothing is deep.
- The `ConeMap` type and `sqCone` are new local definitions, not banked.
  When the leaves close, bank Part B and Part C as a module (for example
  `ConstructionTargets/ConeMapSphereDegree.lean`). Other degree
  computations on spheres can reuse it.
