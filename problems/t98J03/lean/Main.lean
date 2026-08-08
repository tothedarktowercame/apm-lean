import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t98J03 — integral homology of spheres

## Statement repairs

None.

## Encoding questions

None. `Sⁿ` is the actual unit metric sphere in `ℝⁿ⁺¹`, and homology is
Mathlib's integral singular homology. The disconnected zero-sphere is stated
separately from the positive-dimensional formula.
-/

open CategoryTheory

noncomputable section

abbrev apm_t98J03_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t98J03_H (n k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (apm_t98J03_Sphere n)))

lemma apm_t98J03_sphere_zero_coord (x : apm_t98J03_Sphere 0) :
    (x.1 0) = 1 ∨ (x.1 0) = -1 := by
  have hs : (x.1 0) ^ 2 = (1 : ℝ) := by
    have hx := x.2
    change x.1 ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1 at hx
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hx
    simpa using hx
  exact sq_eq_one_iff.mp hs

/-- The sign of the unique coordinate identifies the zero-sphere with two
points at the level needed to obtain finiteness. -/
def apm_t98J03_sphereZeroSign (x : apm_t98J03_Sphere 0) : Bool :=
  decide (x.1 0 = 1)

lemma apm_t98J03_sphereZeroSign_injective :
    Function.Injective apm_t98J03_sphereZeroSign := by
  intro x y hxy
  apply Subtype.ext
  ext i
  fin_cases i
  rcases apm_t98J03_sphere_zero_coord x with hx | hx <;>
    rcases apm_t98J03_sphere_zero_coord y with hy | hy
  · exact hx.trans hy.symm

  · have hx' : apm_t98J03_sphereZeroSign x = true := by
      simp [apm_t98J03_sphereZeroSign, hx]
    have hy' : apm_t98J03_sphereZeroSign y = false := by
      simp [apm_t98J03_sphereZeroSign, hy]
      norm_num
    rw [hx', hy'] at hxy
    contradiction
  · have hx' : apm_t98J03_sphereZeroSign x = false := by
      simp [apm_t98J03_sphereZeroSign, hx]
      norm_num
    have hy' : apm_t98J03_sphereZeroSign y = true := by
      simp [apm_t98J03_sphereZeroSign, hy]
    rw [hx', hy'] at hxy
    contradiction
  · exact hx.trans hy.symm

lemma apm_t98J03_sphereZeroSign_surjective :
    Function.Surjective apm_t98J03_sphereZeroSign := by
  intro b
  let x : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single 0 (if b then 1 else -1)
  have hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
    cases b <;> simp [x]
  refine ⟨⟨x, hx⟩, ?_⟩
  cases b <;> simp [apm_t98J03_sphereZeroSign, x] <;> norm_num

/-- The concrete metric zero-sphere really is the two-element type. -/
noncomputable def apm_t98J03_sphereZeroEquivBool :
    apm_t98J03_Sphere 0 ≃ Bool :=
  Equiv.ofBijective apm_t98J03_sphereZeroSign
    ⟨apm_t98J03_sphereZeroSign_injective,
      apm_t98J03_sphereZeroSign_surjective⟩

noncomputable instance apm_t98J03_sphereZero_finite :
    Finite (apm_t98J03_Sphere 0) :=
  Finite.of_injective apm_t98J03_sphereZeroSign
    apm_t98J03_sphereZeroSign_injective

lemma apm_t98J03_sphereZero_positive_homology_isZero
    (k : ℕ) (hk : 0 < k) : Limits.IsZero (apm_t98J03_H 0 k) := by
  exact
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ)
      (TopCat.of (apm_t98J03_Sphere 0)) (Nat.ne_of_gt hk)

theorem apm_t98j03 :
    Nonempty (apm_t98J03_H 0 0 ≅ ModuleCat.of ℤ (ℤ × ℤ)) ∧
    (∀ k : ℕ, 0 < k → Limits.IsZero (apm_t98J03_H 0 k)) ∧
    ∀ n : ℕ, 0 < n →
      Nonempty (apm_t98J03_H n 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t98J03_H n n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, k ≠ 0 → k ≠ n → Limits.IsZero (apm_t98J03_H n k) := by
  /-
  PARTIAL boundary (closer hop 1).

  A broader search found the useful endpoint API omitted by the imported
  notes: Mathlib's
  `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
  kills every positive-degree homology object of a totally disconnected
  space, and
  `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` identifies its
  zeroth homology with the coproduct of one coefficient object per point.
  Consequently the entire `n = 0` branch reduces concretely to proving that
  the metric sphere in `EuclideanSpace ℝ (Fin 1)` is the discrete two-point
  space and identifying the resulting two-object coproduct in `ModuleCat ℤ`
  with `ModuleCat.of ℤ (ℤ × ℤ)`.

  This does not address the positive-dimensional branch. Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/`, the sphere/homology siblings
  (`t02A06`, `t02A08`, `t94J08`, `t95J04`, `t96A03`), Mathlib's singular-set,
  singular-chain, homology, suspension, CW-complex, and reduced-homology
  sources, and git history found no suspension isomorphism, cellular-to-
  singular comparison, Mayer--Vietoris sequence, or compiled homology
  computation for metric spheres. Functoriality alone cannot produce either
  the top-dimensional generator or the off-degree vanishing. Thus even after
  the zero-sphere reduction, the frozen universal positive-dimensional claim
  still requires substantial missing algebraic-topology infrastructure. The
  statement is unchanged.

  CLOSER HOP 2: the positive-degree half of the zero-sphere branch now
  compiles rather than merely being reduced. `apm_t98J03_sphere_zero_coord`
  uses `EuclideanSpace.sphere_zero_eq` to prove that the unique coordinate is
  `1` or `-1`; the Boolean sign map is injective, hence the concrete sphere is
  finite and therefore discrete. The lemma
  `apm_t98J03_sphereZero_positive_homology_isZero` then applies Mathlib's
  `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` verbatim to
  close every degree `k > 0` for this actual metric-sphere encoding.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, sphere and
  homology siblings, Mathlib's coproduct normalization, suspension, reduced-
  homology, and singular-chain sources, and git history found no positive-
  dimensional computation. The remaining zero-dimensional task is to
  normalize the free-module coproduct on these two concrete points to
  `ℤ × ℤ`; the universal `n > 0` branch still needs the absent sphere
  homology machinery described above. The frozen statement is unchanged.

  CLOSER HOP 3 goes beyond that reduction by proving surjectivity of the
  Boolean sign map with the two explicit Euclidean points and packaging the
  resulting equivalence as `apm_t98J03_sphereZeroEquivBool`. Inspection of
  `ModuleCat.coprodIsoDirectSum` and `DFinsupp.linearEquivFunOnFintype` shows
  the remaining H0 normalization can now be assembled by reindexing that
  direct sum along this equivalence and identifying `Bool → ℤ` with
  `ℤ × ℤ`; this categorical coercion chain was not completed here.

  The decisive universal branch remains unchanged: neither the repository nor
  Mathlib contains singular homology of positive-dimensional metric spheres,
  a suspension isomorphism, Mayer--Vietoris, or a cellular-to-singular
  comparison. Therefore the bridge remains honestly open rather than being
  replaced by an unproved declaration.
  -/
  sorry
