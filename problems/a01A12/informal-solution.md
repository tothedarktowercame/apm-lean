

# APM a01A12: Conformal mapping to a slit angle region

## Why It's Hard

The target region A is topologically and geometrically intricate: it's a wedge of opening angle π/2 (from arg z = -π/4 to arg z = π/4), with a slit removed along the real segment [0,1]. This slit creates a region that is simply connected but not convex, and no single elementary mapping handles both the angular constraint and the slit simultaneously. The construction requires a chain of conformal maps, each handling one geometric feature.

## The Key Insight

Build the map as a composition of four steps, each using a standard conformal building block:

1. **H → right half-plane**: rotation by -i
2. **Right half-plane → ℂ \ (-∞, 0]**: squaring (doubles the angle from π to 2π)
3. **ℂ \ (-∞, 0] → ℂ \ (-∞, 1]**: translation (shifts the branch cut)
4. **ℂ \ (-∞, 1] → A**: fourth root (quarters the angle from 2π to π/2, and maps the slit (−∞, 1] to the ray at angle π/4 together with [0, 1] on the real axis)

The fourth root is the crucial step: it maps the full slit plane (angle range (−π, π)) to the quarter-plane (angle range (−π/4, π/4)), and the branch cut (−∞, 0] maps to the rays at ±π/4, while the segment (0, 1] on the positive real axis maps to the segment (0, 1] on the positive real axis — which becomes the removed interval.

Wait — let me trace through more carefully.

## Complete Proof

### Part (a): Constructing the conformal map

We build φ: H → A as a composition φ = f₄ ∘ f₃ ∘ f₂ ∘ f₁.

**Step 1: f₁(z) = -iz maps H to the right half-plane P = {Re w > 0}.**

This is a rotation by -π/2. If z = x + iy with y > 0, then f₁(z) = -i(x+iy) = y - ix, which has real part y > 0. ✓

**Step 2: f₂(w) = w² maps P to ℂ \ (-∞, 0].**

The right half-plane has arg w ∈ (-π/2, π/2). Squaring doubles the argument: arg(w²) ∈ (-π, π). This covers all of ℂ except the negative real axis (which corresponds to arg = ±π). The map is conformal and bijective from P onto ℂ \ (-∞, 0]. ✓

**Step 3: f₃(ζ) = ζ + 1 maps ℂ \ (-∞, 0] to ℂ \ (-∞, 1].**

Translation by 1. The slit (-∞, 0] becomes (-∞, 1]. ✓

**Step 4: f₄(ξ) = ξ^{1/4} maps ℂ \ (-∞, 1] to A.**

Here ξ^{1/4} uses the principal branch (branch cut on (-∞, 0], argument in (-π, π)). But our domain is ℂ \ (-∞, 1], which has a different branch cut. Let me be more precise.

Define the fourth root on ℂ \ (-∞, 1] as follows. Write ξ = 1 + rе^{iθ}... actually, let me reconsider.

The domain of f₄ is ℂ \ (-∞, 1]. We need a branch of ξ^{1/4} on this domain. Since ℂ \ (-∞, 1] is simply connected, a holomorphic fourth root exists. Choose the branch with 1^{1/4} = 1 (positive real fourth root on (1, ∞)).

**What f₄ does to the boundary/slit:**

- The ray (1, ∞) (just above the slit) maps to (1, ∞)^{1/4} = (1, ∞) on the positive real axis.
- The negative real axis (-∞, 0): approaching from above, arg ξ → π, so arg(ξ^{1/4}) → π/4. Approaching from below, arg ξ → -π, so arg(ξ^{1/4}) → -π/4. These become the boundary rays of the wedge.
- The segment (0, 1] on the real axis (part of the branch cut): approaching from above, arg ξ → 0⁺ for ξ ∈ (0,1), and ξ^{1/4} ∈ (0, 1) on the real axis. But approaching from below, arg ξ → 0⁻ gives the same. Wait — (0,1] is NOT part of the branch cut (-∞, 1]. Let me reclarify.

The branch cut is (-∞, 1], so the removed set includes all of (-∞, 1]. So (0, 1] is removed. From above the branch cut (arg slightly positive for ξ near (0,1)), ξ^{1/4} approaches real values in (0,1). From below, also (0,1). So the segment (0,1] maps to the slit [0,1] on the real axis. But this is part of the *boundary* of the image, not the image itself.

Let me re-examine. The domain is ℂ \ (-∞, 1]. Points just above (-∞, 0) have argument near π; their fourth root has argument near π/4. Points just below (-∞, 0) have argument near -π; their fourth root has argument near -π/4. Points just above (0,1) have small positive argument; fourth root has small positive argument (near the positive real axis, above it). Points just below (0,1) have small negative argument; fourth root is near the positive real axis, below it.

So the image of ℂ \ (-∞, 1] under ξ^{1/4} is: {arg w ∈ (-π/4, π/4)} \ [0, 1], because:
- The full angle range (-π, π) maps to (-π/4, π/4) ✓
- The slit along (0, 1] (upper and lower shores of the branch cut from 0 to 1) maps to the upper and lower shores of [0, 1] on the real axis in the image — this creates the removed interval ✓
- The point ξ = 0 maps to w = 0 (excluded since 0 ∉ ℂ \ (-∞, 1]) ✓

So f₄ maps ℂ \ (-∞, 1] conformally onto A = {arg w ∈ (-π/4, π/4)} \ {w : 0 ≤ Re w ≤ 1, Im w = 0}. ✓

**The full composition:**

$$\varphi(z) = \left((-iz)^2 + 1\right)^{1/4} = (-z^2 + 1)^{1/4} = (1 - z^2)^{1/4}$$

Wait, let me compute: f₁(z) = -iz, f₂(f₁(z)) = (-iz)² = -z², f₃(f₂(f₁(z))) = -z² + 1 = 1 - z², f₄(f₃(f₂(f₁(z)))) = (1-z²)^{1/4}.

So:

$$\boxed{\varphi(z) = (1 - z^2)^{1/4}}$$

with the appropriate branch of the fourth root (the one that is positive real for z = 0: φ(0) = 1). ∎

**Verification at key points:**
- z = 0: φ(0) = 1^{1/4} = 1 ∈ A ✓
- z = i: φ(i) = (1-(-1))^{1/4} = 2^{1/4} ∈ (1, ∞) ⊂ A ✓
- z → ∞: 1-z² ~ -z², so φ(z) ~ (-z²)^{1/4} = |z|^{1/2} e^{i(arg(-z²))/4}. For z = iy (y → ∞): -z² = y², so φ(iy) = y^{1/2} → ∞ along the positive real axis ✓
- z = 1: 1-1 = 0, so φ(1) = 0 (boundary) ✓
- z = -1: same, φ(-1) = 0 ✓
- z = x ∈ (-1,1) real: 1-x² ∈ (0,1), so φ(x) = (1-x²)^{1/4} ∈ (0,1) — on the slit! This means the real interval (-1,1) maps to the slit (0,1] in A. But z ∈ H means Im z > 0, so z is not real. The real axis is the *boundary* of H, and (0,1] is the boundary slit of A. ✓

### Part (b): All conformal maps H → A

By the Riemann mapping theorem, any two simply connected proper subdomains of ℂ are conformally equivalent, and the group of conformal automorphisms of H is the group of Möbius transformations preserving H:

$$\text{Aut}(H) = \left\{z \mapsto \frac{az + b}{cz + d} : a,b,c,d \in \mathbb{R},\; ad - bc > 0\right\} \cong \text{PSL}(2, \mathbb{R}).$$

Therefore, the set of all conformal bijections H → A is:

$$\{\varphi \circ T : T \in \text{Aut}(H)\} = \left\{z \mapsto \left(1 - \left(\frac{az+b}{cz+d}\right)^2\right)^{1/4} : a,b,c,d \in \mathbb{R},\; ad-bc > 0\right\}.$$

This is a three-real-parameter family (PSL(2,ℝ) has dimension 3). ∎

## What Connects

**To the Schwarz-Christoffel formula.** The target region A, viewed as a "degenerate polygon" with vertices at 0 (interior angle 2π from the slit), 1 (interior angle 2π), and the wedge vertex at ∞ (angle π/2), could in principle be handled by the Schwarz-Christoffel formula. The explicit composition we gave is equivalent but more transparent.

**To Riemann mapping and uniformization.** Part (b) illustrates a general principle: once you have *one* conformal map to a target, the full family is obtained by precomposing with the automorphism group of the source. For H, this is PSL(2,ℝ); for the disk, it's the Blaschke rotations.

**To branch cuts and Riemann surfaces.** The fourth-root step is where the topology matters: ℂ \ (-∞, 1] is simply connected, supporting a single-valued branch of ξ^{1/4}. On the Riemann surface of ξ^{1/4}, the four sheets would give four different target wedges; we select one.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex UpperHalfPlane Set

noncomputable section

/-- The target region: the π/2-angle wedge minus the slit [0,1]. -/
def slitAngle : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ z.arg ∈ Ioo (-(π / 4)) (π / 4)} \
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0}

/-- The upper half-plane as a set. -/
def upperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

/-- Step 1: z ↦ -iz maps H to the right half-plane. -/
def step1 (z : ℂ) : ℂ := -I * z

/-- Step 2: w ↦ w² maps the right half-plane to ℂ \ (-∞, 0]. -/
def step2 (w : ℂ) : ℂ := w ^ 2

/-- Step 3: ζ ↦ ζ + 1 shifts the slit. -/
def step3 (ζ : ℂ) : ℂ := ζ + 1

/-- Step 4: ξ ↦ ξ^{1/4} with the principal branch. -/
def step4 (ξ : ℂ) : ℂ := ξ ^ (1 / 4 : ℂ)

/-- The full conformal map φ(z) = (1 - z²)^{1/4}. -/
def conformalMap (z : ℂ) : ℂ := (1 - z ^ 2) ^ (1 / 4 : ℂ)

/-- conformalMap equals the composition of the four steps. -/
lemma conformalMap_eq_comp (z : ℂ) :
    conformalMap z = step4 (step3 (step2 (step1 z))) := by
  sorry

/-- Step 1 maps H to the right half-plane. -/
lemma step1_maps_to_rhp :
    MapsTo step1 upperHalfPlane {w : ℂ | 0 < w.re} := by
  sorry

/-- Step 2 maps the right half-plane bijectively onto ℂ \ (-∞, 0]. -/
lemma step2_bijOn_rhp :
    BijOn step2 {w : ℂ | 0 < w.re} {ζ : ℂ | ¬(ζ.re ≤ 0 ∧ ζ.im = 0)} := by
  sorry

/-- Step 3 maps ℂ \ (-∞, 0] to ℂ \ (-∞, 1]. -/
lemma step3_maps_slit :
    MapsTo step3
      {ζ : ℂ | ¬(ζ.re ≤ 0 ∧ ζ.im = 0)}
      {ξ : ℂ | ¬(ξ.re ≤ 1 ∧ ξ.im = 0)} := by
  sorry

/-- Step 4 maps ℂ \ (-∞, 1] bijectively onto A. -/
lemma step4_bijOn_slitAngle :
    BijOn step4
      {ξ : ℂ | ¬(ξ.re ≤ 1 ∧ ξ.im = 0)}
      slitAngle := by
  sorry

/-- Part (a): φ is a conformal bijection from H onto A. -/
theorem conformalMap_bijOn :
    BijOn conformalMap upperHalfPlane slitAngle := by
  sorry

/-- φ is holomorphic on H. -/
theorem conformalMap_differentiableOn :
    DifferentiableOn ℂ conformalMap upperHalfPlane := by
  sorry

/-- φ has nonvanishing derivative on H (hence conformal). -/
theorem conformalMap_deriv_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv conformalMap z ≠ 0 := by
  sorry

/-- A Möbius transformation preserving H. -/
structure MoebiusH where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_pos : a * d - b * c > 0

/-- Apply a Möbius transformation. -/
def MoebiusH.apply (T : MoebiusH) (z : ℂ) : ℂ :=
  (T.a * z + T.b) / (T.c * z + T.d)

/-- Möbius transformations with positive determinant preserve H. -/
lemma MoebiusH.mapsTo (T : MoebiusH) :
    MapsTo T.apply upperHalfPlane upperHalfPlane := by
  sorry

/-- Part (b): every conformal bijection H → A is φ ∘ T
    for some T ∈ PSL(2, ℝ). -/
theorem all_conformal_maps_H_to_A
    {ψ : ℂ → ℂ} (hψ_bij : BijOn ψ upperHalfPlane slitAngle)
    (hψ_diff : DifferentiableOn ℂ ψ upperHalfPlane)
    (hψ_conf : ∀ z ∈ upperHalfPlane, deriv ψ z ≠ 0) :
    ∃ T : MoebiusH, ∀ z ∈ upperHalfPlane,
      ψ z = conformalMap (T.apply z) := by
  sorry

end
```

**Mathlib notes:**

- `Complex.arg` gives the argument in (-π, π]. The set `slitAngle` uses `z.arg ∈ Ioo (-(π/4)) (π/4)` for the wedge constraint and removes the real segment [0,1].
- `(1 - z^2) ^ (1/4 : ℂ)` uses `Complex.cpow` — the principal-branch complex power. The branch cut of `cpow` is on (-∞, 0], matching the standard convention.
- `BijOn f S T` is Mathlib's predicate for f being a bijection from S onto T.
- `MoebiusH` bundles the four real coefficients with the positive-determinant condition. `PSL(2,ℝ)` is not directly in Mathlib, so we use a concrete structure.
- `all_conformal_maps_H_to_A` states the full classification: every conformal bijection H → A factors as φ ∘ T for a unique Möbius transformation T.
