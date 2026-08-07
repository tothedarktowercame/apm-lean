import Mathlib

/-!
# APM t94J08 — antipodal degree and negation of a vector field

## Statement repairs

None.

## Encoding questions

Mathlib has no general Brouwer degree for maps of higher-dimensional spheres
and no local-index API for vector fields. `T94J08DegreeTheory` records exactly
the standard degree interface needed here on actual unit-sphere maps: the
identity has degree one, and postcomposition with the antipodal map multiplies
degree by `(-1)^k` on the sphere in `ℝ^k`. The vector field, its isolated zero,
and its normalized linking map are concrete Euclidean objects.
-/

open scoped ContDiff

noncomputable section

abbrev T94J08Euclidean (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev T94J08Sphere (k : ℕ) := Metric.sphere (0 : T94J08Euclidean k) 1

def t94J08Antipodal {k : ℕ} (x : T94J08Sphere k) : T94J08Sphere k :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

/-- The minimal standard laws for degree used by the problem. The parameter
`k` is the ambient dimension, so the sphere itself has dimension `k-1`. -/
structure T94J08DegreeTheory where
  degree : ∀ k : ℕ, (T94J08Sphere k → T94J08Sphere k) → ℤ
  degree_id : ∀ k : ℕ, degree k id = 1
  degree_antipodal_comp : ∀ (k : ℕ) (u : T94J08Sphere k → T94J08Sphere k),
    degree k (fun x ↦ t94J08Antipodal (u x)) = (-1 : ℤ) ^ k * degree k u

def t94J08HasIsolatedZero {n : ℕ}
    (v : T94J08Euclidean n → T94J08Euclidean n)
    (p : T94J08Euclidean n) : Prop :=
  v p = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ x, dist x p < ε → x ≠ p → v x ≠ 0

def t94J08NormalizedLink {n : ℕ}
    (v : T94J08Euclidean n → T94J08Euclidean n)
    (p : T94J08Euclidean n) (r : ℝ)
    (hlink : ∀ x : T94J08Sphere n, v (p + r • x.1) ≠ 0) :
    T94J08Sphere n → T94J08Sphere n :=
  fun x ↦ ⟨‖v (p + r • x.1)‖⁻¹ • v (p + r • x.1), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
      norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hlink x))]⟩

def t94J08LocalIndex {n : ℕ} (D : T94J08DegreeTheory)
    (v : T94J08Euclidean n → T94J08Euclidean n)
    (p : T94J08Euclidean n) (r : ℝ)
    (hlink : ∀ x : T94J08Sphere n, v (p + r • x.1) ≠ 0) : ℤ :=
  D.degree n (t94J08NormalizedLink v p r hlink)

theorem apm_t94j08 (D : T94J08DegreeTheory) :
    (∀ n : ℕ,
      D.degree (n + 1) (t94J08Antipodal : T94J08Sphere (n + 1) → _) =
        (-1 : ℤ) ^ (n + 1)) ∧
    ∀ (n : ℕ) (v : T94J08Euclidean n → T94J08Euclidean n)
      (hv : ContDiff ℝ ⊤ v) (p : T94J08Euclidean n)
      (hp : t94J08HasIsolatedZero v p)
      (r : ℝ) (hr : 0 < r)
      (hlink : ∀ x : T94J08Sphere n, v (p + r • x.1) ≠ 0)
      (hlinkNeg : ∀ x : T94J08Sphere n, (-v (p + r • x.1)) ≠ 0)
      (d : ℤ),
      t94J08LocalIndex D v p r hlink = d →
      t94J08LocalIndex D (fun x ↦ -v x) p r hlinkNeg =
        (-1 : ℤ) ^ n * d := by
  sorry
