# t03J04 repair grade (2026-10-17)

Grader: read-only Claude subagent (outside grader).
Graded file: holes/labs/blueprints/t03J04/RevisedMain.lean (not installed).
Compared against: problems/t03J04/problem.md, problems/t03J04/informal-solution.md,
problems/t03J04/lean/Main.lean, ConstructionTargets/RationalLefschetz.lean.

**Grade: faithful.** No required changes. One optional generalization (n = 0), below.

## 1. Torus binders: `[ChartedSpace (HModel n) (Fin n → Circle)]` + `[LieGroup (Model n) ∞ …]`

- `LieGroup` extends `ContMDiffMul`, which extends `IsManifold`. So the binder gives
  a C^∞ atlas on the fixed product topology, and the pointwise group operations
  are smooth. `∞` under `open scoped ContDiff` is `((⊤ : ℕ∞) : WithTop ℕ∞)`, which
  is C^∞ and not ω. Every smoothness order in the file is `∞`.
- **Satisfiable, so the theorem is not vacuous.** Take the product of the stereographic
  `Circle` charts, model `ModelPi (fun _ ↦ EuclideanSpace ℝ (Fin 1))` with
  `ModelWithCorners.pi`. Smoothness into a pi-model is checked one coordinate at a
  time. Multiplication and inversion are smooth in each coordinate, because `Circle`
  is a Lie group for `𝓡 1` (Mathlib gives it at ω, so also at ∞). So the standard
  structure satisfies the binder. Mathlib has no pi `LieGroup` instance, but that
  does not matter: the theorem quantifies universally over the binder, so non-vacuity
  only needs one structure to exist, and one does. n = 1 is the same with one factor:
  `Fin 1 → Circle` with a one-factor `ModelPi`. Nothing degenerates.
- **Unique up to diffeomorphism.** Suppose two binder instances satisfy the hypothesis.
  The identity is then a continuous homomorphism between finite-dimensional real Lie
  groups, so it is smooth (Cartan), and the same holds for its inverse. So every
  admissible instance is the standard smooth Tⁿ, carried by the identity map. This
  improves on Main.lean, where an arbitrary `IsManifold` atlas on the topological
  torus could be exotic for n ≥ 5.

## 2. (a)(i): the fixed left-invariant field and "isolated zeros"

- Fixing the witness `mulInvariantVectorField e₁` is the standard way to encode "give
  an explicit example". It is the official answer (`\soln{Constant vector field.}`,
  and the informal solution's ∂/∂x₁). It makes no other conjunct trivial. In a
  general admissible atlas, e₁ is read in the chart at 1, so the field is some
  nonzero left-invariant field. That is still a constant field.
- Isolated zeros are encoded as `V q = 0 → ∀ᶠ y in 𝓝[≠] q, V y ≠ 0`. This is correct.
  It holds vacuously because the field is nowhere zero, and that is exactly the
  intended solution: the informal proof says the zero set is empty and the zeros are
  "vacuously isolated".
- The conjunct is no longer free. It requires the section q ↦ ⟨q, V q⟩ to be
  `ContMDiff … (Model n).tangent ∞`, which follows from
  `contMDiff_mulInvariantVectorField`. Since 3 ≤ ∞, the `minSmoothness ℝ 3`
  requirement is met. Proving nowhere-vanishing also takes real work:
  `mfderiv (g * ·) 1` must be shown invertible, because left translation is a
  diffeomorphism.

## 3. (a)(ii) and (b) via `HasEulerCharacteristic … 0`

- `HasEulerCharacteristic X v` = every rational singular homology group H_k(X; ℚ) is
  finite-dimensional, H_k = 0 above some bound, and the alternating trace of id
  equals v. Since trace(id) = finrank, this is the honest χ with finiteness
  certificates, and no junk value can arise.
- **Orientation dropped.** This makes (b) a stronger universal claim, and it is still
  true (covering argument below). The attaining example Tⁿ with id is oriented and
  orientation-preserving anyway.
- **Boundaryless dropped.** The model is `ModelWithCorners.pi` of
  `modelWithCornersSelf`, whose range is univ, so it has no boundary. Separately, a
  local diffeomorphism from the boundaryless Tⁿ cannot reach a boundary point, so
  nothing is lost.
- **Same model for X.** Every smooth n-manifold can be given an atlas into
  Fin n → ℝ¹ ≅ ℝⁿ, so this loses no generality. It also lets Tⁿ itself be an
  admissible X.
- **`T2Space X`** is the standard manifold convention, and it is needed. The circle
  with a doubled point is connected, locally diffeomorphic to S¹, and has χ = −1.
- **`ConnectedSpace X`** is needed and is implicit in the problem. Without it,
  X = Tⁿ ⊔ Sⁿ (n even) has χ = 2, and adding further components makes χ(X)
  unconstrained, or not finite. The source's single answer {0} only makes sense if X
  is connected, and the informal solution says "we take X connected" explicitly.
  This matches the t95J03 precedent: "surface" read as connected.
- **No compactness or second countability is assumed on X, and none is needed.**
  The range of φ is open (φ is a local homeomorphism) and compact, hence closed in
  the T2 space X. It is nonempty, so it is clopen, and since X is connected it is
  all of X. So X is compact and Hausdorff (and so second countable), and
  `HasEulerCharacteristic X 0` is a meaningful and true claim.
- **"List all possible values" = {0}.** The (b) conjunct gives χ(X) ∈ {0}. The final
  conjunct (`id` is a local diffeomorphism), together with (a)(ii), shows that 0 is
  attained by X = Tⁿ. Tⁿ does satisfy X's binders: the pi of T2 spaces is T2, the pi
  of connected spaces is connected, and `IsManifold` comes from `LieGroup`. The
  attainment conjunct is trivially provable, but attainment really is trivial
  mathematically, so this is not a defect.

## 4. Truth (sketch)

- **(a)(i):** smoothness comes from `contMDiff_mulInvariantVectorField`. Left
  translation by g is a diffeomorphism with inverse translation by g⁻¹, so its
  mfderiv at 1 is injective, and V g ≠ 0 because e₁ ≠ 0.
- **(a)(ii):** H_*(Tⁿ; ℚ) = Λ*(ℚⁿ) by Künneth. This is finite-dimensional and zero
  above n, and Σ(−1)^k C(n,k) = 0 for n ≥ 1.
- **(b):** φ is surjective (shown above), so X is compact. A proper local
  homeomorphism onto a connected Hausdorff space is a finite covering of some degree
  d ≥ 1. X is then a compact smooth manifold, so its rational homology is
  finite-dimensional and vanishes above n. The transfer gives χ(Tⁿ) = d·χ(X), so
  χ(X) = 0.
- **Last conjunct:** `IsLocalDiffeomorph` of id holds.

So the repaired statement is TRUE.

## Current Main.lean: are the claimed defects real? Confirmed.

- **(a)(i) trivially true and unfaithful.** It asks only that a function
  `Torus n → E n` be pointwise nonzero. That function has no link to the tangent
  bundle, and no continuity or smoothness is required. Main's own lemma
  `apm_t03J04_constantVectorField_ne_zero` proves it by `simp`. Its hypotheses are
  satisfiable, so it is not vacuous in that sense, but the conjunct encodes nothing.
- **(a)(ii) and (b) weaker.** The χ used there is `Σ_{k≤n} (-1)^k finrank H_k`, and
  `finrank` is 0 on infinite-dimensional spaces. So "= 0" certifies neither finite
  generation nor vanishing above n. The claims are true, but they assert less than
  "χ = 0". (b) also never shows that 0 is attained.
- **Torus binders unpinned.** The `IsManifold` atlas on the torus is arbitrary. This
  does not affect χ, which is topological, but it means "vector field on Tⁿ" does not
  refer to the standard smooth torus.

## Optional (not required)

- **n ≥ 1 (`NeZero n`)** is kept from Main. It is the conventional reading of
  "n-torus" (the source writes n factors of S¹, and the informal solution boxes
  χ = 0 for n ≥ 1), so it is acceptable. Dropping it costs little, though:
  - Define e₁ by `if i.val = 0 then … else 0`.
  - For n = 0 this gives the zero field on a point. Its zeros are isolated, because
    `𝓝[≠] q = ⊥` in a one-point space.
  - State the value in (a)(ii) and (b) as `if n = 0 then 1 else 0`.
  This would cover all of ℕ and needs no new argument.
