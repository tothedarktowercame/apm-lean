import ConstructionTargets.CoefficientSphereAntipodal
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

2026-09-09: restrict the ordinary-homology sphere degree to `1 ≤ n`, and
its local-index specialization to `1 ≤ m` (ambient dimension `m + 1 ≥ 2`).
`T94J08Sphere k` uses ambient dimension k, so the old n = 0 case was S⁰
and incorrectly demanded H₀(S⁰) ≅ ℤ. The exact old proposition's refutation
is retained under holes/labs/topology-contract/evidence/t94j08-zero-sphere/.
This is a newly frozen positive-dimensional branch, not closure of the old
statement. The classical S⁰ / one-dimensional local-index cases require a
separately elected reduced-homology encoding; they are outside this branch.

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

/-- The point-set antipodal map is an involution. This isolates all remaining
difficulty in its action on singular homology. -/
lemma t94J08Antipodal_comp_self {k : ℕ} :
    (t94J08Antipodal : C(T94J08Sphere k, T94J08Sphere k)).comp
      t94J08Antipodal = ContinuousMap.id _ := by
  ext x i
  simp [t94J08Antipodal]

/-- A unit sphere has no fixed point under the antipodal map. -/
lemma t94J08Antipodal_ne_self {k : ℕ} (x : T94J08Sphere k) :
    t94J08Antipodal x ≠ x := by
  intro h
  have hx : -x.1 = x.1 := congrArg Subtype.val h
  have hx0 : x.1 = 0 := by
    have hadd : x.1 + x.1 = 0 := neg_eq_iff_add_eq_zero.mp hx
    have hsmul : (2 : ℝ) • x.1 = 0 := by simpa [two_smul] using hadd
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  have := x.2
  simp [Metric.mem_sphere, hx0] at this

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

/-- The scalar equation does not depend on the chosen orientation
isomorphism. -/
lemma t94J08HasDegree_with_orientation {n : ℕ}
    {f : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))} {d : ℤ}
    (h : t94J08HasDegree n f d)
    (orientation : T94J08TopHomology n ≅ ModuleCat.of ℤ ℤ) :
    ∀ a : T94J08TopHomology n,
      orientation.hom (t94J08TopHomologyMap n f a) =
        d * orientation.hom a := by
  obtain ⟨orientation₀, h₀⟩ := h
  intro a
  have hmap : t94J08TopHomologyMap n f a = d • a := by
    apply (ConcreteCategory.bijective_of_isIso orientation₀.hom).1
    simpa using h₀ a
  rw [hmap]
  simp

/-- Degrees multiply under composition.  Unlike the same-orientation version
in sibling `t02A08`, this lemma first transports either existentially chosen
orientation to the other one. -/
lemma t94J08HasDegree.comp {n : ℕ}
    {g h : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))}
    {m d : ℤ} (hg : t94J08HasDegree n g m)
    (hh : t94J08HasDegree n h d) :
    t94J08HasDegree n (g.comp h) (m * d) := by
  obtain ⟨orientation, hgo⟩ := hg
  have hho := t94J08HasDegree_with_orientation hh orientation
  refine ⟨orientation, fun a ↦ ?_⟩
  have hcomp : t94J08TopHomologyMap n (g.comp h) =
      t94J08TopHomologyMap n h ≫ t94J08TopHomologyMap n g := by
    unfold t94J08TopHomologyMap
    simpa using
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom h) (TopCat.ofHom g)
  rw [hcomp]
  change orientation.hom
    (t94J08TopHomologyMap n g (t94J08TopHomologyMap n h a)) = _
  rw [hgo, hho]
  ring

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

/-- Why this unblocks `apm_t94j08`: this is the missing top-dimensional
singular-homology computation for metric spheres, including both an integral
orientation and the induced antipodal action.  Folding the conclusion with
`t94J08HasDegree` gives exactly the family used in the main proof. -/
theorem apm_t94J08_bridge_1 :
    ∀ n : ℕ, 1 ≤ n → ∃ orientation : T94J08TopHomology n ≅ ModuleCat.of ℤ ℤ,
      ∀ a : T94J08TopHomology n,
        orientation.hom
            (t94J08TopHomologyMap n
              (t94J08Antipodal :
                C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))) a) =
          ((-1 : ℤ) ^ (n + 1)) * orientation.hom a := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    refine ⟨ConstructionTargets.CoefficientSphereAntipodal.normalization ℤ m, ?_⟩
    intro a
    exact ConstructionTargets.CoefficientSphereAntipodal.scalar_equation ℤ m a

/-- Superseded: it omitted the zero-sphere and one-dimensional local-index cases. -/
theorem apm_t94j08_previous_encoding :
    (∀ n : ℕ, 1 ≤ n →
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1))) ∧
    ∀ (m : ℕ) (hm : 1 ≤ m)
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
  let hantipodal : ∀ n : ℕ, 1 ≤ n →
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1)) := by
  /-
  CLOSER HOP 2 boundary. Hop 1 compiled `t94J08NormalizedLink_neg`, the exact
  pointwise identity needed for the second conjunct.

  This hop goes beyond that boundary by proving orientation-independence in
  `t94J08HasDegree_with_orientation` and full degree multiplicativity in
  `t94J08HasDegree.comp`.  The proof first identifies the induced homology map
  intrinsically with integer scalar multiplication, transports it through any
  orientation isomorphism, and then applies functoriality of
  `t94J08TopHomologyMap`.  Consequently the entire local-index-negation
  conjunct is assembled below from the antipodal computation and the
  normalized-link identity.

  The sole remaining bridge is now the first conjunct: the actual top-
  dimensional singular-homology computation for `T94J08Sphere (n+1)`, needed
  both to construct an orientation isomorphism and compute the antipodal
  action. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, sphere/degree siblings, Mathlib's
  singular-homology, sphere, antipodal, ModuleCat, and functoriality sources,
  and git history found no sphere homology generator or compiled antipodal
  computation. This historical search preceded the 2026-09-09 specification repair.

  CLOSER HOP 3 goes beyond the prior boundary by compiling the antipodal
  map's full point-set involution identity and its fixed-point-freeness on
  every unit metric sphere. These facts show that no remaining continuity,
  inverse, or sphere-membership bookkeeping is hidden in the gap. A further
  search through the zero-sphere reduction in `t98J03`, categorical homology
  functor sources, and all sphere-degree siblings still found no orientation
  isomorphism for `H₀(S⁰)` (now refuted, not an API gap), or the positive-dimensional top-homology and
  induced antipodal action. The bridge therefore remains exactly the missing
  singular-homology computation, not a point-set lemma.
  -/
    exact apm_t94J08_bridge_1
  refine ⟨hantipodal, ?_⟩
  intro m hm v hv p hp r hr hlink hlinkNeg d hindex
  obtain ⟨link, hlink_eq, hdegree⟩ := hindex
  let anti : C(T94J08Sphere (m + 1), T94J08Sphere (m + 1)) :=
    t94J08Antipodal
  refine ⟨anti.comp link, ?_, (hantipodal m hm).comp hdegree⟩
  intro x
  change anti (link x) = t94J08NormalizedLink (fun y ↦ -v y) p r hlinkNeg x
  rw [t94J08NormalizedLink_neg v p r hlink hlinkNeg x]
  rw [hlink_eq x]

/-- Degree on the reduced zero-dimensional homology of the two-point sphere.
The difference `a 1 - a 0` is a generator of the augmentation kernel, so this
is a degree statement, rather than merely the point-set fact that the points
are exchanged. -/
def t94J08HasReducedDegreeZero (f : Equiv.Perm (Fin 2)) (d : ℤ) : Prop :=
  ∀ a : Fin 2 → ℤ, a 0 + a 1 = 0 →
    a (f.symm 1) - a (f.symm 0) = d * (a 1 - a 0)

/-- The one-dimensional local index, computed on the boundary `S⁰` of an
interval around the isolated zero. -/
def t94J08HasLocalIndexOne (v : ℝ → ℝ) (p r : ℝ) (d : ℤ) : Prop :=
  v p = 0 ∧ 0 < r ∧
    (∀ x, dist x p < r → x ≠ p → v x ≠ 0) ∧
    v (p - r) ≠ 0 ∧ v (p + r) ≠ 0 ∧
    (d : ℝ) = (Real.sign (v (p + r)) - Real.sign (v (p - r))) / 2

/-! ## Low-dimensional endpoint package -/

/-- The two low-dimensional endpoint computations omitted by the ordinary
top-homology encoding: the transposition acts by `-1` on reduced
zero-homology, and negating a real vector field negates its endpoint-sign
local index. -/
theorem apm_t94j08_low_dimensional :
    t94J08HasReducedDegreeZero (Equiv.swap (0 : Fin 2) 1) (-1) ∧
    ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (p r : ℝ) (d : ℤ),
      t94J08HasLocalIndexOne v p r d →
      t94J08HasLocalIndexOne (fun x ↦ -v x) p r (-d) := by
  constructor
  · intro a ha
    change a 0 - a 1 = (-1 : ℤ) * (a 1 - a 0)
    ring
  · intro v hv p r d h
    rcases h with ⟨hp, hr, hiso, hleft, hright, hindex⟩
    refine ⟨by simp [hp], hr, ?_, by simpa using hleft, by simpa using hright, ?_⟩
    · intro x hx hxp
      simpa using hiso x hx hxp
    · push_cast
      rw [Real.sign_neg, Real.sign_neg, hindex]
      ring

/-- The positive-dimensional part, with the exact smoothness parameter used
by the final statement.  This is already discharged by the construction
target and the compiled degree-composition argument. -/
theorem apm_t94j08_positive_dimensional :
    (∀ n : ℕ, 1 ≤ n →
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1))) ∧
    ∀ (m : ℕ) (hm : 1 ≤ m)
      (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1))
      (hv : ContDiff ℝ ∞ v) (p : T94J08Euclidean (m + 1))
      (hp : t94J08HasIsolatedZero v p)
      (r : ℝ) (hr : 0 < r)
      (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0)
      (hlinkNeg : ∀ x : T94J08Sphere (m + 1), (-v (p + r • x.1)) ≠ 0)
      (d : ℤ),
      t94J08HasLocalIndex v p r hlink d →
      t94J08HasLocalIndex (fun x ↦ -v x) p r hlinkNeg
        ((-1 : ℤ) ^ (m + 1) * d) := by
  let hantipodal : ∀ n : ℕ, 1 ≤ n →
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1)) := apm_t94J08_bridge_1
  refine ⟨hantipodal, ?_⟩
  intro m hm v hv p hp r hr hlink hlinkNeg d hindex
  obtain ⟨link, hlink_eq, hdegree⟩ := hindex
  let anti : C(T94J08Sphere (m + 1), T94J08Sphere (m + 1)) :=
    t94J08Antipodal
  refine ⟨anti.comp link, ?_, (hantipodal m hm).comp hdegree⟩
  intro x
  change anti (link x) = t94J08NormalizedLink (fun y ↦ -v y) p r hlinkNeg x
  rw [t94J08NormalizedLink_neg v p r hlink hlinkNeg x]
  rw [hlink_eq x]

/-- The antipodal degree formula in every dimension, together with the local
index formula for negating a vector field in every positive manifold
dimension.  Dimension zero is represented by the actual two-point sphere and
its transposition, rather than by the false ordinary-`H₀ ≅ ℤ` encoding. -/
theorem apm_t94j08 :
    t94J08HasReducedDegreeZero (Equiv.swap (0 : Fin 2) 1) (-1) ∧
    (∀ n : ℕ, 1 ≤ n →
      t94J08HasDegree n
        (t94J08Antipodal : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1)))
        ((-1 : ℤ) ^ (n + 1))) ∧
    (∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (p r : ℝ) (d : ℤ),
      t94J08HasLocalIndexOne v p r d →
      t94J08HasLocalIndexOne (fun x ↦ -v x) p r (-d)) ∧
    ∀ (m : ℕ) (hm : 1 ≤ m)
      (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1))
      (hv : ContDiff ℝ ∞ v) (p : T94J08Euclidean (m + 1))
      (hp : t94J08HasIsolatedZero v p)
      (r : ℝ) (hr : 0 < r)
      (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0)
      (hlinkNeg : ∀ x : T94J08Sphere (m + 1), (-v (p + r • x.1)) ≠ 0)
      (d : ℤ),
      t94J08HasLocalIndex v p r hlink d →
      t94J08HasLocalIndex (fun x ↦ -v x) p r hlinkNeg
        ((-1 : ℤ) ^ (m + 1) * d) := by
  obtain ⟨hzero, hone⟩ := apm_t94j08_low_dimensional
  obtain ⟨hanti, hhigh⟩ := apm_t94j08_positive_dimensional
  exact ⟨hzero, hanti, hone, hhigh⟩

#print axioms apm_t94j08

#print axioms apm_t94J08_bridge_1
