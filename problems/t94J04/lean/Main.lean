import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces

/-!
# APM t94J04

## Statement repairs

The index `k` is required to be positive.  Mathlib represents infinite index
by `Subgroup.index = 0`; without `0 < k`, the statement would incorrectly
claim that all infinite-index subgroups of a genus-two surface group are
isomorphic.  The informal solution also explicitly assumes `k ≥ 1`.

## Encoding questions

The group is the actual Mathlib fundamental group of a compact connected
smooth surface; genus two and orientability are described under "Genus
encoding" below. Subgroups, their index, and the
resulting group isomorphism are all native.

## Genus encoding (revised 2026-10-12)

The source's "a closed orientable surface of genus 2" names a homeomorphism class, so the hypothesis is a
homeomorphism to the standard polygon model
`ConstructionTargets.Surfaces.Surface true g` (the 4g-gon with word
a₁b₁a₁⁻¹b₁⁻¹⋯). The earlier encoding by integral singular homology of a compact
smooth 2-manifold picks out the same class only via the classification of
surfaces, which the source uses as background and never asks for (Joe,
2026-10-12). The remaining manifold instances are kept; every closed
topological surface admits a smooth structure, so they exclude nothing.
-/

open CategoryTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94J04_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_t94J04_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- `a closed orientable surface of genus 2`: homeomorphic to the standard polygon model. -/
def apm_t94J04_isGenusTwoSurface
    (F : Type) [TopologicalSpace F] : Prop :=
  Nonempty (F ≃ₜ ConstructionTargets.Surfaces.Surface true 2)

lemma apm_t94J04_subgroups_equiv_of_index_one
    {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.index = 1) (hK : K.index = 1) : Nonempty (H ≃* K) := by
  rw [Subgroup.index_eq_one] at hH hK
  subst H
  subst K
  exact ⟨MulEquiv.refl _⟩

/-- The numerical part of the covering-surface argument: multiplying the
genus-two Euler characteristic by `k` gives the Euler characteristic of genus
`k+1`. -/
lemma apm_t94J04_eulerChar_cover_arithmetic (k : ℕ) :
    (2 : ℤ) - 2 * ((k : ℤ) + 1) = (k : ℤ) * (2 - 2 * 2) := by
  ring

/-- Equal positive subgroup indices already identify the underlying finite
coset spaces.  The missing topology must upgrade this sheet-level equivalence
to an isomorphism of the subgroups themselves. -/
lemma apm_t94J04_quotient_equiv_of_equal_positive_index
    {G : Type*} [Group G] (H K : Subgroup G) (k : ℕ) (hk : 0 < k)
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty ((G ⧸ H) ≃ (G ⧸ K)) := by
  have hH0 : H.index ≠ 0 := hH.trans_ne hk.ne'
  have hK0 : K.index ≠ 0 := hK.trans_ne hk.ne'
  letI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hH0
  letI : Finite (G ⧸ K) := Nat.finite_of_card_ne_zero hK0
  letI := Fintype.ofFinite (G ⧸ H)
  letI := Fintype.ofFinite (G ⧸ K)
  exact ⟨Fintype.equivOfCardEq (by simpa [Subgroup.index] using hH.trans hK.symm)⟩

/-- Why this unblocks `apm_t94j04`: this is the precise finite-index
surface-group classification missing from Mathlib. Its proof realizes both
subgroups as connected `k`-sheeted covers, computes both covering genera as
`k + 1`, and transports the resulting surface homeomorphism to fundamental
groups; the already compiled `k = 1` case is deliberately excluded. -/
theorem apm_t94J04_bridge_equal_index_subgroups
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_isGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 2 ≤ k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  sorry

theorem apm_t94j04
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_isGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 0 < k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  by_cases hk1 : k = 1
  · apply apm_t94J04_subgroups_equiv_of_index_one H K
    · simpa [hk1] using hH
    · simpa [hk1] using hK
  ·
    have hk2 : 2 ≤ k := by omega
    have hcosets : Nonempty
        ((FundamentalGroup F p ⧸ H) ≃ (FundamentalGroup F p ⧸ K)) :=
      apm_t94J04_quotient_equiv_of_equal_positive_index H K k hk hH hK
  /-
  Boundary (closer hop 1): the index-one edge case is now closed by
  `apm_t94J04_subgroups_equiv_of_index_one`.  For general positive `k`, the
  intended proof realizes each subgroup as the fundamental group of its
  connected `k`-sheeted covering surface, uses multiplicativity of Euler
  characteristic to compute genus `k+1`, and applies classification of closed
  orientable surfaces.

  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`, closed surface and
  covering artifacts, git history, and Mathlib's covering-space,
  fundamental-group, singular-homology, Euler-characteristic, surface,
  Schreier, and Nielsen--Schreier APIs found no subgroup--cover realization,
  finite-cover Euler-characteristic theorem, or surface-classification theorem
  for this concrete manifold.  `Subgroup.rank_le_index_mul_rank` and
  `subgroupIsFreeOfIsFree` concern free groups and do not apply to the
  one-relator genus-two surface group.  Moreover the frozen homology predicate
  must first be connected to an actual genus-two surface classification.
  Those topological bridges remain open.

  CLOSER HOP 2: the main theorem now genuinely dispatches `k = 1` through
  `apm_t94J04_subgroups_equiv_of_index_one`; the remaining `sorry` is confined
  to `k ≠ 1`.  The numerical genus computation is also compiled separately as
  `apm_t94J04_eulerChar_cover_arithmetic`, proving
  `2 - 2(k+1) = k(2 - 2·2)` over `ℤ`. Thus once a `k`-sheeted covering surface
  and Euler-characteristic multiplicativity are available, no arithmetic
  bridge remains.

  Going beyond the earlier free-group search, I inspected Mathlib's
  `FundamentalGroupoid` covering-lift machinery and the categorical
  `TopCat`/covering sources for a Galois correspondence between connected
  coverings and subgroups. The APIs lift maps and paths for a supplied cover,
  but do not construct a cover from an arbitrary subgroup. The singular
  homology functor likewise has no finite-cover transfer/Euler-characteristic
  comparison. Hence the unresolved branch still requires the same three
  absent topological assemblies: subgroup realization, Euler-characteristic
  multiplicativity, and orientable-surface classification. The frozen
  statement is unchanged.

  CLOSER HOP 3: `apm_t94J04_quotient_equiv_of_equal_positive_index` now
  compiles the full finite-sheet bookkeeping: positivity of the common index
  produces `Finite` instances for both coset types, and equal index produces
  an equivalence `(FundamentalGroup F p ⧸ H) ≃
  (FundamentalGroup F p ⧸ K)`.  The live branch also records `2 ≤ k`, so
  neither the residual arithmetic case split nor finiteness/cardinality of the
  sheets remains open.  This cannot be upgraded algebraically to `H ≃* K`:
  equal-index subgroups of a general group need not be isomorphic.  A final
  inspection of `Nat.finite_of_card_ne_zero`, subgroup quotient/index APIs,
  the repository's covering-profile artifacts, and the classification-related
  topology sources found no theorem connecting this coset equivalence to
  connected covering surfaces.  The unresolved bridge is exactly subgroup
  realization followed by Euler-characteristic multiplicativity and closed
  orientable-surface classification.  The frozen statement is unchanged.
  -/
    clear hk2 hcosets
    sorry
