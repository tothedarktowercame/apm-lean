# Outside grades for new encodings (2026-11-01)

Problems with no Lean statement since the revert in 51a8a06e8, encoded by Codex seats, graded by read-only Claude subagents dispatched by claude-14 and given the printed problem and the Lean.

## t95A01

First grade: narrower. Parts 1 and 3 faithful; part 2 stated non-orientability through `IsOrientablePairing KleinPairing`, a sign check on data not tied to the space, so a torus would pass. claude-14 replaced that conjunct with `IsZero` of integral H₂ of the concrete `KleinBottle`, which is intrinsic for a closed surface. Compile: 0 errors, 1 sorry (the theorem).

Second grade: faithful. `KleinBottle` is `Surface false 2`, word aabb, one vertex, χ = 0. H₂(K; ℤ) = 0 is true and fails for orientable closed surfaces. A self-cover exists ((x,y) ↦ (2x,y)). Parts 1 and 3 faithful and true. Note: `E : Type` and `X : Type` are enough in parts 1 and 3; the grader accepted these.

## t99J02

Grade: faithful, first pass. All five parts present; "describe" and "give" became explicit claims and the named methods are dropped, as the docstring says. `Surface true 2` is the coinduced quotient of the disk with word aba⁻¹b⁻¹cdc⁻¹d⁻¹; the CW clause is concrete polygon data, not a Mathlib `CWComplex`, and the word is carried by `P`, not displayed. The connected sum is a homeomorphism to `ConnectedSum` of genuine tori, which rules out degeneracy. Presentation: the one-relator group on `Fin 4`, at every basepoint; abstract isomorphism. Homology: ℤ, ℤ⁴, ℤ, zero above 2. Clause 5 repeats clause 2, as disclosed. Compile: 0 errors, 1 sorry (the theorem).

## t00J05

First grade: false. The statement followed informal-solution.md in claiming that a line with spheres at the integers covers X. A covering is a local homeomorphism and X is everywhere two-dimensional, so a point of the open interval has no matching neighbourhood. The necklace is only homotopy equivalent to the universal cover.

Fix by lemma-1: the concrete cylinder Circle × ℝ with a disk capping each integer circle, an explicit projection to X, a covering claim, simple connectedness, and a homotopy equivalence to the necklace. Compile: 0 errors, 1 sorry (the theorem).

Second grade: faithful. Evenly covered sets checked, including at the cap circles; fibres are ℤ-indexed. Both homotopy types reduce to a countable wedge of S², and H₂ agrees. Part (b) true. Scope: a fixed standard curve; every essential embedded curve is tame and non-separating, so a torus homeomorphism plus radial extension gives a homeomorphism of X, as the docstring says. Stale: informal-solution.md still calls the necklace the universal cover.
