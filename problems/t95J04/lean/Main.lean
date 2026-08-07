import Mathlib

/-! # APM t95J04: low-dimensional maps to spheres and six-manifolds

## Statement repairs

None.

## Encoding question

Mathlib does not bundle compact smooth manifolds by dimension with a uniform
model. We bundle their actual compact Hausdorff carriers. For the only
smooth-specific step in (a), a smooth map records the concrete Sard
consequence that it misses a point when the source dimension is smaller.
Null-homotopy, simple connectivity, and inequivalence are native topological
statements. For (b) we use `S⁶`, `S² × S⁴`, and `S³ × S³`.
-/

open scoped ContDiff Manifold

noncomputable section

structure T95J04CompactSmoothManifold (n : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : T2Space Carrier
  compact : CompactSpace Carrier

abbrev t95J04SphereType (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def t95J04Sphere (n : ℕ) : T95J04CompactSmoothManifold n where
  Carrier := t95J04SphereType n
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

structure T95J04SmoothMap {k n : ℕ}
    (M : T95J04CompactSmoothManifold k)
    (N : T95J04CompactSmoothManifold n) where
  toFun : M.Carrier → N.Carrier
  continuous_toFun :
    @Continuous M.Carrier N.Carrier M.topology N.topology toFun
  missesPoint_of_dim_lt : k < n → ¬Function.Surjective toFun

def IsT95J04NullHomotopic {k n : ℕ}
    {M : T95J04CompactSmoothManifold k}
    {N : T95J04CompactSmoothManifold n}
    (f : T95J04SmoothMap M N) : Prop :=
  let _ := M.topology
  let _ := N.topology
  ∃ y : N.Carrier,
    ContinuousMap.Homotopic ⟨f.toFun, f.continuous_toFun⟩
      (ContinuousMap.const _ y)

def IsT95J04SimplyConnected {n : ℕ}
    (M : T95J04CompactSmoothManifold n) : Prop :=
  let _ := M.topology
  Nonempty M.Carrier ∧ ∀ x : M.Carrier, Subsingleton (FundamentalGroup M.Carrier x)

def T95J04Diffeomorphic {n : ℕ}
    (M N : T95J04CompactSmoothManifold n) : Prop :=
  let _ := M.topology
  let _ := N.topology
  Nonempty (M.Carrier ≃ₜ N.Carrier)

def t95J04SphereSix : T95J04CompactSmoothManifold 6 := t95J04Sphere 6

def t95J04SphereTwoFourProduct : T95J04CompactSmoothManifold 6 where
  Carrier := t95J04SphereType 2 × t95J04SphereType 4
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

def t95J04SphereThreeProduct : T95J04CompactSmoothManifold 6 where
  Carrier := t95J04SphereType 3 × t95J04SphereType 3
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

theorem apm_t95j04 :
    (∀ (k n : ℕ), k < n →
      ∀ (M : T95J04CompactSmoothManifold k)
        (f : T95J04SmoothMap M (t95J04Sphere n)),
        IsT95J04NullHomotopic f) ∧
    IsT95J04SimplyConnected t95J04SphereSix ∧
    IsT95J04SimplyConnected t95J04SphereTwoFourProduct ∧
    IsT95J04SimplyConnected t95J04SphereThreeProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereSix t95J04SphereTwoFourProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereSix t95J04SphereThreeProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereTwoFourProduct
      t95J04SphereThreeProduct := by
  sorry
