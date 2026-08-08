import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t94J08 — antipodal degree and negation of a vector field

Degree is encoded by the map actually induced on integral top-dimensional
singular homology.  In particular, no abstract degree operation or law about
the antipodal map is assumed.  The local index is the same concrete homology
degree applied to the normalized linking map around an isolated zero.

## Statement repairs

None.

## Encoding questions

The choice of an orientation isomorphism from top homology to `ℤ` is explicit
in `t94J08HasDegree`.  Establishing that isomorphism and computing the
antipodal action are proof obligations, not structure fields.
-/

open CategoryTheory
open scoped ContDiff

noncomputable section

abbrev T94J08Euclidean (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev T94J08Sphere (k : ℕ) := Metric.sphere (0 : T94J08Euclidean k) 1

def t94J08Antipodal {k : ℕ} : C(T94J08Sphere k, T94J08Sphere k) :=
  ⟨fun x ↦ ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩, by fun_prop⟩

/-- Integral singular homology in the top dimension of `Sⁿ ⊂ ℝⁿ⁺¹`. -/
abbrev T94J08TopHomology (n : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (T94J08Sphere (n + 1))))

def t94J08TopHomologyMap (n : ℕ)
    (f : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- `f` has degree `d` when its actual induced map on top homology is
multiplication by `d`, relative to an orientation of the sphere. -/
def t94J08HasDegree (n : ℕ)
    (f : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
    (d : ℤ) : Prop :=
  ∃ orientation : T94J08TopHomology n ≅ ModuleCat.of ℤ ℤ,
    ∀ a : T94J08TopHomology n,
      orientation.hom (t94J08TopHomologyMap n f a) =
        d * orientation.hom a

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

/-- The local index is pinned to the degree of the actual continuous
normalized linking map; existence of that continuous map is part of the
assertion rather than hidden in an arbitrary integer-valued operation. -/
def t94J08HasLocalIndex {m : ℕ}
    (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1))
    (p : T94J08Euclidean (m + 1)) (r : ℝ)
    (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0)
    (d : ℤ) : Prop :=
  ∃ link : C(T94J08Sphere (m + 1), T94J08Sphere (m + 1)),
    (∀ x, link x = t94J08NormalizedLink v p r hlink x) ∧
    t94J08HasDegree m link d

/-- Negating the vector field composes its normalized linking map with the
antipodal map. -/
lemma t94J08NormalizedLink_neg {m : ℕ}
    (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1))
    (p : T94J08Euclidean (m + 1)) (r : ℝ)
    (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0)
    (hlinkNeg : ∀ x : T94J08Sphere (m + 1), (-v (p + r • x.1)) ≠ 0)
    (x : T94J08Sphere (m + 1)) :
    t94J08NormalizedLink (fun y ↦ -v y) p r hlinkNeg x =
      t94J08Antipodal (t94J08NormalizedLink v p r hlink x) := by
  apply Subtype.ext
  simp [t94J08NormalizedLink, t94J08Antipodal, norm_neg, smul_neg]

theorem apm_t94j08 :
    (∀ n : ℕ,
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1))) ∧
    ∀ (m : ℕ)
      (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1))
      (hv : ContDiff ℝ ⊤ v) (p : T94J08Euclidean (m + 1))
      (hp : t94J08HasIsolatedZero v p)
      (r : ℝ) (hr : 0 < r)
      (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0)
      (hlinkNeg : ∀ x : T94J08Sphere (m + 1), (-v (p + r • x.1)) ≠ 0)
      (d : ℤ),
      t94J08HasLocalIndex v p r hlink d →
      t94J08HasLocalIndex (fun x ↦ -v x) p r hlinkNeg
        ((-1 : ℤ) ^ (m + 1) * d) := by
  /-
  CLOSER HOP 1 boundary. The new compiled lemma
  `t94J08NormalizedLink_neg` proves the exact pointwise identity needed for
  the second conjunct: normalization of `-v` is the antipodal map composed
  with normalization of `v`, including the dependent nonvanishing witnesses.

  Closing the homological step still requires two pieces not packaged by the
  current imports: the actual top-dimensional singular-homology computation
  for `T94J08Sphere (n+1)` (to construct the orientation isomorphism and
  compute the antipodal action), and multiplicativity of the scalar action
  encoded by `t94J08HasDegree`. The latter also requires proving independence
  from the existentially chosen orientation isomorphism before applying
  functoriality of `t94J08TopHomologyMap` to composition. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, sphere/degree siblings, Mathlib's
  singular-homology, sphere, antipodal, ModuleCat, and functoriality sources,
  and git history found no sphere homology generator or compiled degree API.
  -/
  sorry
