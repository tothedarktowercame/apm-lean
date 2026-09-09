import Mathlib
import ConstructionTargets.SphereAntipodalHomology
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


open ConstructionTargets.SphereHomology ConstructionTargets.SphereAntipodalHomology
open ConstructionTargets.SingularHomologyConcrete
open CategoryTheory.Limits
open scoped DirectSum

theorem diagnostic_no_zero_orientation :
    ¬Nonempty (T94J08TopHomology 0 ≅ ModuleCat.of ℤ ℤ) := by
  classical
  rintro ⟨o⟩
  letI : Fintype (Sphere 0) := Fintype.ofFinite _
  let e : T94J08TopHomology 0 ≅ ModuleCat.of ℤ (⨁ _ : Sphere 0, ℤ) :=
    directDiscreteH0Iso (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (Sphere 0) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : Sphere 0 => ModuleCat.of ℤ ℤ)
  have h := (e.symm ≪≫ o).toLinearEquiv.finrank_eq
  change Module.finrank ℤ (⨁ _ : Sphere 0, ℤ) = Module.finrank ℤ ℤ at h
  have hm : Module.finrank ℤ (⨁ _ : Sphere 0, ℤ) = Fintype.card (Sphere 0) := by
    calc
      _ = ∑ _ : Sphere 0, Module.finrank ℤ ℤ := by
        convert Module.finrank_directSum (R := ℤ) (fun _ : Sphere 0 => ℤ) using 1
      _ = ∑ _ : Sphere 0, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        convert Module.finrank_self ℤ using 1
      _ = _ := by simp
  have hi : Module.finrank ℤ ℤ = 1 := by convert Module.finrank_self ℤ using 1
  rw [hm, hi] at h
  have hne : sphereZeroPositive ≠ sphereZeroNegative := by
    intro he
    have he0 := congrArg (fun x : Sphere 0 => x.val 0) he
    norm_num [sphereZeroPositive, sphereZeroNegative] at he0
  have hc : 1 < Fintype.card (Sphere 0) := Fintype.one_lt_card_iff.mpr ⟨_,_,hne⟩
  omega

#print axioms diagnostic_no_zero_orientation

theorem diagnostic_refutes_frozen_theorem : ¬ ((∀ n : ℕ,
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
        ((-1 : ℤ) ^ (m + 1) * d)) := by
  intro h
  obtain ⟨orientation, _⟩ := h.1 0
  exact diagnostic_no_zero_orientation ⟨orientation⟩

#print axioms diagnostic_refutes_frozen_theorem
