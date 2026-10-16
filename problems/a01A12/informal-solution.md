

# APM a01A12: Conformal mapping to a slit angle region

## Why It's Hard

The target region $A$ is topologically and geometrically intricate: it's a wedge of opening angle $\pi/2$ (from $\arg z = -\pi/4$ to $\arg z = \pi/4$), with a slit removed along the real segment $[0,1]$. This slit creates a region that is simply connected but not convex, and no single elementary mapping handles both the angular constraint and the slit simultaneously. The construction requires a chain of conformal maps, each handling one geometric feature.

## The Key Insight

Build the map as a composition of four steps, each using a standard conformal building block:

1. **$H$ → right half-plane**: rotation by $-i$
2. **Right half-plane → $\mathbb{C} \setminus (-\infty, 0]$**: squaring (doubles the angle from $\pi$ to $2\pi$)
3. **$\mathbb{C} \setminus (-\infty, 0] \to \mathbb{C} \setminus (-\infty, 1]$**: translation (shifts the branch cut)
4. **$\mathbb{C} \setminus (-\infty, 1] \to A$**: fourth root (quarters the angle from $2\pi$ to $\pi/2$, and maps the slit $(−\infty, 1]$ to the ray at angle $\pi/4$ together with $[0, 1]$ on the real axis)

The fourth root is the crucial step: it maps the full slit plane (angle range $(−\pi, \pi)$) to the quarter-plane (angle range $(−\pi/4, \pi/4)$), and the branch cut $(−\infty, 0]$ maps to the rays at $\pm\pi/4$, while the segment $(0, 1]$ on the positive real axis maps to the segment $(0, 1]$ on the positive real axis — which becomes the removed interval.

Wait — let me trace through more carefully.

## Complete Proof

### Part (a): Constructing the conformal map

We build $\varphi: H \to A$ as a composition $\varphi = f_{4} \circ f_{3} \circ f_{2} \circ f_{1}$.

**Step 1: $f_{1}(z) = -iz$ maps $H$ to the right half-plane $P = \{\operatorname{Re} w > 0\}$.**

This is a rotation by $-\pi/2$. If $z = x + iy$ with $y > 0$, then $f_{1}(z) = -i(x+iy) = y - ix$, which has real part $y > 0$. ✓

**Step 2: $f_{2}(w) = w^{2}$ maps $P$ to $\mathbb{C} \setminus (-\infty, 0]$.**

The right half-plane has $\arg w \in (-\pi/2, \pi/2)$. Squaring doubles the argument: $\arg(w^{2}) \in (-\pi, \pi)$. This covers all of $\mathbb{C}$ except the negative real axis (which corresponds to $\arg = \pm\pi$). The map is conformal and bijective from $P$ onto $\mathbb{C} \setminus (-\infty, 0]$. ✓

**Step 3: $f_{3}(\zeta) = \zeta + 1$ maps $\mathbb{C} \setminus (-\infty, 0]$ to $\mathbb{C} \setminus (-\infty, 1]$.**

Translation by 1. The slit $(-\infty, 0]$ becomes $(-\infty, 1]$. ✓

**Step 4: $f_{4}(\xi) = \xi^{1/4}$ maps $\mathbb{C} \setminus (-\infty, 1]$ to $A$.**

Here $\xi^{1/4}$ uses the principal branch (branch cut on $(-\infty, 0]$, argument in $(-\pi, \pi)$). But our domain is $\mathbb{C} \setminus (-\infty, 1]$, which has a different branch cut. Let me be more precise.

Define the fourth root on $\mathbb{C} \setminus (-\infty, 1]$ as follows. Write $\xi = 1 + rе^{i\theta}$... actually, let me reconsider.

The domain of $f_{4}$ is $\mathbb{C} \setminus (-\infty, 1]$. We need a branch of $\xi^{1/4}$ on this domain. Since $\mathbb{C} \setminus (-\infty, 1]$ is simply connected, a holomorphic fourth root exists. Choose the branch with $1^{1/4} = 1$ (positive real fourth root on $(1, \infty)$).

**What $f_{4}$ does to the boundary/slit:**

- The ray $(1, \infty)$ (just above the slit) maps to $(1, \infty)^{1/4} = (1, \infty)$ on the positive real axis.
- The negative real axis $(-\infty, 0)$: approaching from above, $\arg \xi \to \pi$, so $\arg(\xi^{1/4}) \to \pi/4$. Approaching from below, $\arg \xi \to -\pi$, so $\arg(\xi^{1/4}) \to -\pi/4$. These become the boundary rays of the wedge.
- The segment $(0, 1]$ on the real axis (part of the branch cut): approaching from above, $\arg \xi \to 0^{+}$ for $\xi \in (0,1)$, and $\xi^{1/4} \in (0, 1)$ on the real axis. But approaching from below, $\arg \xi \to 0^{-}$ gives the same. Wait — $(0,1]$ is NOT part of the branch cut $(-\infty, 1]$. Let me reclarify.

The branch cut is $(-\infty, 1]$, so the removed set includes all of $(-\infty, 1]$. So $(0, 1]$ is removed. From above the branch cut (arg slightly positive for $\xi$ near $(0,1)$), $\xi^{1/4}$ approaches real values in $(0,1)$. From below, also $(0,1)$. So the segment $(0,1]$ maps to the slit $[0,1]$ on the real axis. But this is part of the *boundary* of the image, not the image itself.

Let me re-examine. The domain is $\mathbb{C} \setminus (-\infty, 1]$. Points just above $(-\infty, 0)$ have argument near $\pi$; their fourth root has argument near $\pi/4$. Points just below $(-\infty, 0)$ have argument near $-\pi$; their fourth root has argument near $-\pi/4$. Points just above $(0,1)$ have small positive argument; fourth root has small positive argument (near the positive real axis, above it). Points just below $(0,1)$ have small negative argument; fourth root is near the positive real axis, below it.

So the image of $\mathbb{C} \setminus (-\infty, 1]$ under $\xi^{1/4}$ is: $\{\arg w \in (-\pi/4, \pi/4)\} \setminus [0, 1]$, because:
- The full angle range $(-\pi, \pi)$ maps to $(-\pi/4, \pi/4)$ ✓
- The slit along $(0, 1]$ (upper and lower shores of the branch cut from 0 to 1) maps to the upper and lower shores of $[0, 1]$ on the real axis in the image — this creates the removed interval ✓
- The point $\xi = 0$ maps to $w = 0$ (excluded since $0 \notin \mathbb{C} \setminus (-\infty, 1]$) ✓

So $f_{4}$ maps $\mathbb{C} \setminus (-\infty, 1]$ conformally onto $A = \{\arg w \in (-\pi/4, \pi/4)\} \setminus \{w : 0 \leq \operatorname{Re} w \leq 1, \operatorname{Im} w = 0\}$. ✓

**The full composition:**

$$\varphi(z) = \left((-iz)^2 + 1\right)^{1/4} = (-z^2 + 1)^{1/4} = (1 - z^2)^{1/4}$$

Wait, let me compute: $f_{1}(z) = -iz$, $f_{2}(f_{1}(z)) = (-iz)^{2} = -z^{2}$, $f_{3}(f_{2}(f_{1}(z))) = -z^{2} + 1 = 1 - z^{2}$, $f_{4}(f_{3}(f_{2}(f_{1}(z)))) = (1-z^{2})^{1/4}$.

So:

$$\boxed{\varphi(z) = (1 - z^2)^{1/4}}$$

with the appropriate branch of the fourth root (the one that is positive real for $z = 0$: $\varphi(0) = 1$). ∎

**Verification at key points:**
- $z = 0$: $\varphi(0) = 1^{1/4} = 1 \in A$ ✓
- $z = i$: $\varphi(i) = (1-(-1))^{1/4} = 2^{1/4} \in (1, \infty) \subset A$ ✓
- $z \to \infty$: $1-z^{2} \sim -z^{2}$, so $\varphi(z) \sim (-z^{2})^{1/4} = |z|^{1/2} e^{i(\arg(-z^{2}))/4}$. For $z = iy$ ($y \to \infty$): $-z^{2} = y^{2}$, so $\varphi(iy) = y^{1/2} \to \infty$ along the positive real axis ✓
- $z = 1$: $1-1 = 0$, so $\varphi(1) = 0$ (boundary) ✓
- $z = -1$: same, $\varphi(-1) = 0$ ✓
- $z = x \in (-1,1)$ real: $1-x^{2} \in (0,1)$, so $\varphi(x) = (1-x^{2})^{1/4} \in (0,1)$ — on the slit! This means the real interval $(-1,1)$ maps to the slit $(0,1]$ in $A$. But $z \in H$ means $\operatorname{Im} z > 0$, so $z$ is not real. The real axis is the *boundary* of $H$, and $(0,1]$ is the boundary slit of $A$. ✓

### Part (b): All conformal maps $H \to A$

By the Riemann mapping theorem, any two simply connected proper subdomains of $\mathbb{C}$ are conformally equivalent, and the group of conformal automorphisms of $H$ is the group of Möbius transformations preserving $H$:

$$\text{Aut}(H) = \left\{z \mapsto \frac{az + b}{cz + d} : a,b,c,d \in \mathbb{R},\; ad - bc > 0\right\} \cong \text{PSL}(2, \mathbb{R}).$$

Therefore, the set of all conformal bijections $H \to A$ is:

$$\{\varphi \circ T : T \in \text{Aut}(H)\} = \left\{z \mapsto \left(1 - \left(\frac{az+b}{cz+d}\right)^2\right)^{1/4} : a,b,c,d \in \mathbb{R},\; ad-bc > 0\right\}.$$

This is a three-real-parameter family ($\text{PSL}(2,\mathbb{R})$ has dimension 3). ∎

## What Connects

**To the Schwarz-Christoffel formula.** The target region $A$, viewed as a "degenerate polygon" with vertices at 0 (interior angle $2\pi$ from the slit), 1 (interior angle $2\pi$), and the wedge vertex at $\infty$ (angle $\pi/2$), could in principle be handled by the Schwarz-Christoffel formula. The explicit composition we gave is equivalent but more transparent.

**To Riemann mapping and uniformization.** Part (b) illustrates a general principle: once you have *one* conformal map to a target, the full family is obtained by precomposing with the automorphism group of the source. For $H$, this is $\text{PSL}(2,\mathbb{R})$; for the disk, it's the Blaschke rotations.

**To branch cuts and Riemann surfaces.** The fourth-root step is where the topology matters: $\mathbb{C} \setminus (-\infty, 1]$ is simply connected, supporting a single-valued branch of $\xi^{1/4}$. On the Riemann surface of $\xi^{1/4}$, the four sheets would give four different target wedges; we select one.

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

- `Complex.arg` gives the argument in $(-\pi, \pi]$. The set `slitAngle` uses `z.arg ∈ Ioo (-(π/4)) (π/4)` for the wedge constraint and removes the real segment $[0,1]$.
- `(1 - z^2) ^ (1/4 : ℂ)` uses `Complex.cpow` — the principal-branch complex power. The branch cut of `cpow` is on $(-\infty, 0]$, matching the standard convention.
- `BijOn f S T` is Mathlib's predicate for $f$ being a bijection from $S$ onto $T$.
- `MoebiusH` bundles the four real coefficients with the positive-determinant condition. `PSL(2,ℝ)` is not directly in Mathlib, so we use a concrete structure.
- `all_conformal_maps_H_to_A` states the full classification: every conformal bijection $H \to A$ factors as $\varphi \circ T$ for a unique Möbius transformation $T$.
