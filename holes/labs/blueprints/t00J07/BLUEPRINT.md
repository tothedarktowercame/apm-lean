# Blueprint for t00J07 (revision 2026-10-15)

The previous blueprint, with two LIBRARY contracts and no leaves, is in `old-2026-10-15/`.

## Verdict

The statement is true and faithful, and the frozen definitions and `apm_t00j07` are
byte-identical to `problems/t00J07/lean/Main.lean` (checked with diff). The embedding
hypothesis is never used. The answer holds for any loop `f`, so no Schoenflies step is needed.

## Route

1. **The problem space is literally `AttachTwoCell.Cell f`.** It uses the same sum
   `RP² ⊕ closedBall 0 1`, the same boundary map, and generating relations that differ
   only in their constructor names. `cellHomeo` is proved: the identity descends both ways.
2. **π₁(RP²) ≅ Z/2.** This part is copied verbatim from the closed t92J05 (Part A, about
   300 lines, sorry-free), as is path-connectedness.
3. **H_*(RP²).** The hemisphere chart `D² → RP²`, `z ↦ [Re z, Im z, √(1-|z|²)]`, is
   defined and proved continuous. It descends to a continuous bijection
   `Surface false 1 → RP²`, which is a homeomorphism by compact-to-T2. RP² is T2 via
   t92J05's antipodal-quotient homeomorphism and Mathlib's
   `t2Space_of_properlyDiscontinuousSMul_of_t2Space`. Then `standardPairingData_space_homeomorph`
   and `polygonQuotient_homology` give H₁ = Z/2, H₂ = 0 and H_{≥3} = 0.
4. **[f] and f_*.**
   - `hurewicz_loopClass_mem_range` is proved: the Hurewicz image of `[f]` equals
     f_*(circle class), by `moduleHurewicz_naturality`.
   - Null case: f_* = 0 by `singularHomology_map_eq_zero_of_nullhomotopic`. Hurewicz is
     injective on RP², so [f] = 1.
   - Essential case: [f] ≠ 1 by the free-versus-based loop comparison. Then Hurewicz is
     nonzero, so f_* ≠ 0.
5. **Assembly (sorry-free).**
   - `cell_piOne` with normal closure ⊥ or ⊤ gives π₁ = Z/2 or trivial.
   - `cell_H1` with range f_* = 0 or everything gives H₁ = Z/2 or 0.
   - Null H₂ comes from `cell_H2_of_zero`. Essential H₂ comes from `cell_H2_ker` and
     `ker_int_of_two_torsion`.
   - H₀ comes from `cell_pc`, and H_{≥3} from `cell_H_high`.
   - The basepoint is moved by `cellHomeo` and then `fundamentalGroupMulEquivOfPathConnected`.

## Leaves (9)

| Leaf | Statement | Est. size |
|---|---|---|
| `hemi_surjective` | Every line meets the closed upper unit hemisphere | ~70 |
| `hemi_respects` | `SurfaceRel false 1 x y → hemi x = hemi y` (`edgePoint 2 1 t = -edgePoint 2 0 t`) | ~40 |
| `hemi_eq_cases` | `hemi x = hemi y → x = y ∨ (‖x‖=1 ∧ y = -x)` (unit vectors, so the scalar is ±1; −1 forces the third coordinate to 0) | ~120 |
| `surfaceRel_one_antipodal` | For `‖x‖=1`, `EqvGen (SurfaceRel false 1) x (-x)` (split on arg ∈ [0,π] or (π,2π)) | ~80 |
| `rp2Polygon_homology` | `standardPairingData false 1`: H₁ ≅ ZMod 2 and IsZero H₂. Copy the g=3 pattern of `t97A01Closure.aabbcc_attachingDegree_named`: one orbit, degree ±2 | ~100 |
| `hurewicz_injective_of_zmod2` (GENERIC) | Path-connected X with π₁ ≅ Z/2 and H₁ ≅ Z/2: `moduleHurewicz x` is injective (`fundamentalGroupH1Hom_surjective`, then card) | ~50 |
| `nullhomotopic_of_loopClassAt_eq_one` (GENERIC) | `loopClassAt γ (γ 1) rfl = 1 → ∃ p, γ ≃ const p` (descend a rel-endpoint homotopy along `integerLoop 1`) | ~150 |
| `cell_H2_ker` (GENERIC, AttachTwoCell companion) | Same hypotheses as `cell_H2_of_zero` minus `hγ`: `H₂(Cell γ) ≅ ker γ_*` (copy the `cell_H2_of_zero` proof; δ is injective with image ker mvI₁) | ~120 |
| `ker_int_of_two_torsion` (GENERIC) | `M ≃ ℤ`, `φ : M → N` with `n+n=0` on N: `ker φ ≃ ℤ` | ~50 |

`cell_H2_ker`, `hurewicz_injective_of_zmod2`, `nullhomotopic_of_loopClassAt_eq_one` and
`ker_int_of_two_torsion` are problem-independent and worth banking in AttachTwoCell or a
Hurewicz utility module. The four hemisphere leaves together give `RP² ≃ₜ Surface false 1`,
which other RP² problems can reuse (t01A01, t00A02, t98A03, t96J06).

## Checks

- Compiles with 0 errors. The 9 `sorry` warnings are exactly the leaves.
- `#print axioms apm_t00j07` (scratch copy in /tmp) shows `sorryAx` only through the leaves.
  `cellHomeo` is axiom-clean apart from the standard axioms.
- Leaf truth was checked by hand, including the edge cases (x on the boundary, c = ±1, the
  t = 1 endpoint of the crosscap edges).

## Risks

- The `hemi_eq_cases` arithmetic (unit-norm vector, `Projectivization.mk_eq_mk_iff`) is the
  longest geometric leaf. It can be split further if a seat stalls.
- `nullhomotopic_of_loopClassAt_eq_one` needs the quotient `I → Circle` behind `integerLoop 1`.
  Check the definition in `CircleUniversalCover` first.
- `rp2Polygon_homology` depends on the `edgeOrbitContribution` and sign conventions. The degree
  may be −2, which is harmless.
