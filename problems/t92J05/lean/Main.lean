import Mathlib
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.CircleMetricFundamentalGroup
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.Surfaces

/-!
# APM t92J05

## Statement repairs

None.

## Encoding questions

`RP²`, `S²`, and `S¹` are encoded as their actual projectivization and metric
spheres. The closed oriented genus-two surface is described under "Genus
encoding" below. Its asserted fundamental group is the actual presented group
on four generators with relator `[a₁,b₁][a₂,b₂]`.

## Genus encoding (revised 2026-10-12)

The source's "the closed oriented surface of genus 2" names a homeomorphism class, so the hypothesis is a
homeomorphism to the standard polygon model
`ConstructionTargets.Surfaces.Surface true g` (the 4g-gon with word
a₁b₁a₁⁻¹b₁⁻¹⋯). The earlier encoding by integral singular homology of a compact
smooth 2-manifold picks out the same class only via the classification of
surfaces, which the source uses as background and never asks for (Joe,
2026-10-12). The remaining manifold instances are kept; every closed
topological surface admits a smooth structure, so they exclude nothing.
-/

open CategoryTheory Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t92J05_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t92J05_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t92J05_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev apm_t92J05_S1 := Metric.sphere (0 : ℂ) 1
abbrev apm_t92J05_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t92J05_Model := 𝓘(ℝ, apm_t92J05_E2)

abbrev apm_t92J05_H (k : ℕ) (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

/-- `the closed oriented surface of genus 2`: homeomorphic to the standard polygon model. -/
def apm_t92J05_IsGenusTwoSurface
    (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (S ≃ₜ ConstructionTargets.Surfaces.Surface true 2)

/-- The commutator word on two generators of `FreeGroup (Fin 4)`. -/
def apm_t92J05_commutator (a b : Fin 4) : FreeGroup (Fin 4) :=
  FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ * (FreeGroup.of b)⁻¹

@[simp] lemma apm_t92J05_commutator_self (a : Fin 4) :
    apm_t92J05_commutator a a = 1 := by
  simp [apm_t92J05_commutator]

/-- The genus-two surface relator `[a₁,b₁][a₂,b₂]`. -/
def apm_t92J05_genusTwoRelator : FreeGroup (Fin 4) :=
  apm_t92J05_commutator 0 1 * apm_t92J05_commutator 2 3

abbrev apm_t92J05_genusTwoGroup :=
  PresentedGroup ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))

/-- The displayed genus-two relator is killed by the canonical quotient map. -/
@[simp] lemma apm_t92J05_genusTwoRelator_eq_one :
    PresentedGroup.mk ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))
      apm_t92J05_genusTwoRelator = 1 := by
  apply PresentedGroup.one_of_mem
  simp

/-- The four canonical elements really generate the encoded presented group. -/
lemma apm_t92J05_genusTwo_generators_generate :
    Subgroup.closure
      (Set.range (PresentedGroup.of : Fin 4 → apm_t92J05_genusTwoGroup)) = ⊤ := by
  exact PresentedGroup.closure_range_of _

/-- Expanded form of the single surface relation on the four canonical
generators. -/
lemma apm_t92J05_genusTwo_surface_relation :
    (PresentedGroup.of 0 : apm_t92J05_genusTwoGroup) *
      PresentedGroup.of 1 * (PresentedGroup.of 0)⁻¹ *
      (PresentedGroup.of 1)⁻¹ *
      (PresentedGroup.of 2 * PresentedGroup.of 3 *
        (PresentedGroup.of 2)⁻¹ * (PresentedGroup.of 3)⁻¹) = 1 := by
  change PresentedGroup.mk
    ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))
      apm_t92J05_genusTwoRelator = 1
  exact apm_t92J05_genusTwoRelator_eq_one

/-- The group-level specialization of Mathlib's product theorem for the
fundamental groupoid. This makes the based-point bookkeeping explicit. -/
def apm_t92J05_fundamentalGroup_prod_equiv
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) :
    FundamentalGroup (A × B) (a, b) ≃*
      FundamentalGroup A a × FundamentalGroup B b where
  toFun p := (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv p := Path.Homotopic.prod_projLeft_projRight p
  right_inv p := by
    ext
    · exact Path.Homotopic.projLeft_prod p.1 p.2
    · exact Path.Homotopic.projRight_prod p.1 p.2
  map_mul' p q := by
    apply Prod.ext
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projLeft
          (TopCat.of A) (TopCat.of B)).map_comp q p
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projRight
          (TopCat.of A) (TopCat.of B)).map_comp q p

/-- With a trivial first factor, the product calculation reduces exactly to
the second factor's fundamental group. -/
lemma apm_t92J05_product_group_of_subsingleton_left
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) [Subsingleton (FundamentalGroup A a)]
    (hB : Nonempty (FundamentalGroup B b ≃* Multiplicative ℤ)) :
    Nonempty
      (FundamentalGroup (A × B) (a, b) ≃* Multiplicative ℤ) := by
  letI : Unique (FundamentalGroup A a) := uniqueOfSubsingleton 1
  exact ⟨(apm_t92J05_fundamentalGroup_prod_equiv a b).trans
    ((MulEquiv.uniqueProd :
      FundamentalGroup A a × FundamentalGroup B b ≃*
        FundamentalGroup B b).trans hB.some)⟩

/-- Why this unblocks `apm_t92j05`: this is the missing antipodal-cover
identification of the fundamental group of the concrete real projective
plane. It supplies the first frozen conjunct directly at every basepoint. -/
theorem apm_t92J05_bridge_projectivePlane_fundamentalGroup :
    ∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃*
          Multiplicative (ZMod 2)) := by
  sorry

/-- Why this unblocks `apm_t92j05`: these are exactly the two factor
computations still needed by the already compiled product equivalence. The
metric two-sphere is simply connected and the complex unit circle has
fundamental group `ℤ`, uniformly in the chosen basepoints. -/
theorem apm_t92J05_bridge_sphere_circle_fundamentalGroups :
    (∀ x : apm_t92J05_S2,
      Subsingleton (FundamentalGroup apm_t92J05_S2 x)) ∧
    ∀ x : apm_t92J05_S1,
      Nonempty
        (FundamentalGroup apm_t92J05_S1 x ≃* Multiplicative ℤ) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · haveI : SimplyConnectedSpace apm_t92J05_S2 :=
      ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
        2 (by norm_num)
    exact inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))
  · haveI : PathConnectedSpace apm_t92J05_S1 := by
      have h1 : 1 < Module.rank ℝ ℂ := by
        rw [show Module.rank ℝ ℂ = 2 from Complex.rank_real_complex]
        norm_num
      have h : IsPathConnected (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
        isPathConnected_sphere h1 0 (by norm_num)
      exact (isPathConnected_iff_pathConnectedSpace.mp h)
    let pt : apm_t92J05_S1 :=
      ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle.symm 1
    have hpt :
        ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle pt = 1 :=
      ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle.apply_symm_apply
        1
    exact
      ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x pt).trans
        ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
            ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle pt).trans
          (by
            rw [hpt]
            exact ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt))⟩

/-- Why this unblocks `apm_t92j05`: this is the missing compact oriented
surface classification and Seifert--van Kampen theorem. The encoded genus-two
homology signature identifies the actual fundamental group with the verified
four-generator, one-relator presentation. -/
theorem apm_t92J05_bridge_genusTwo_fundamentalGroup :
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [PathConnectedSpace S] [ChartedSpace apm_t92J05_E2 S]
        [IsManifold apm_t92J05_Model ∞ S],
      apm_t92J05_IsGenusTwoSurface S → ∀ x : S,
        Nonempty
          (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  sorry

theorem apm_t92j05 :
    (∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃* Multiplicative (ZMod 2))) ∧
    (∀ x : apm_t92J05_S2 × apm_t92J05_S1,
      Nonempty
        (FundamentalGroup (apm_t92J05_S2 × apm_t92J05_S1) x ≃*
          Multiplicative ℤ)) ∧
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [PathConnectedSpace S] [ChartedSpace apm_t92J05_E2 S]
        [IsManifold apm_t92J05_Model ∞ S]
        (hS : apm_t92J05_IsGenusTwoSurface S) (x : S),
      Nonempty
        (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  /-
  CLOSER HOP 1 boundary. The elementary presentation normalization
  `apm_t92J05_commutator_self` is compiled above as a sanity check on the
  frozen relator encoding.

  Mathlib's `AlgebraicTopology.FundamentalGroupoid.Product` proves that the
  fundamental groupoid functor preserves products. Thus the middle clause can
  in principle be reduced to the fundamental groups of the metric two-sphere
  and complex unit circle. Searches found no packaged theorem that the former
  is trivial or that the latter is `ℤ`; the available `Circle`/`AddCircle`
  topology does not include the required fundamental-group computation.

  The first clause needs the antipodal universal cover of the projectivization
  and its deck group, or an independent CW computation of `π₁(RP²)`. Mathlib's
  projectivization is algebraic/topological, but no covering-map theorem links
  the unit sphere quotient to it and no projective-space fundamental-group
  theorem is present.

  The final clause is not determined by homology alone for arbitrary spaces;
  the manifold hypotheses invoke the classification of compact oriented
  surfaces, after which a cell decomposition and Seifert--van Kampen yield the
  displayed presentation. Mathlib provides neither surface classification nor
  a topological Seifert--van Kampen theorem. The homology record does not by
  itself construct an equivalence or presentation of `FundamentalGroup S x`.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, related
  artifacts (`t01A01`, `t01A04`, `t01J03`, `t03J01`, `t98J03`), Mathlib's
  fundamental-groupoid product, sphere, circle/AddCircle, projectivization,
  covering-map, presented-group, manifold, and singular-homology sources, and
  git history. Product preservation was found, but none of the factor/group or
  classification computations needed to apply it.

  CLOSER HOP 2: the algebraic target presentation is now certified beyond the
  earlier self-commutator sanity check. `apm_t92J05_genusTwoRelator_eq_one`
  proves the canonical quotient kills the displayed relator,
  `apm_t92J05_genusTwo_generators_generate` proves the four canonical elements
  generate the quotient, and `apm_t92J05_genusTwo_surface_relation` records
  the expanded two-commutator equation they satisfy. Thus no further
  presented-group normalization is hidden in the final clause. Renewed
  searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all topology
  artifacts, Mathlib's projectivization, sphere/circle, fundamental-groupoid,
  presented-group, manifold, and homology sources, and git history still found
  no factor fundamental-group computations, antipodal-cover theorem, surface
  classification, or Seifert--van Kampen theorem. Identifying the actual
  fundamental groups with the now-verified algebraic targets remains open;
  the frozen statement is unchanged.

  CLOSER HOP 3 compiles the based product specialization left implicit by the
  earlier hops. `apm_t92J05_fundamentalGroup_prod_equiv` constructs the
  multiplicative equivalence directly from `Path.Homotopic.projLeft`,
  `projRight`, and `prod`, with both inverse laws proved. The wrapper
  `apm_t92J05_product_group_of_subsingleton_left` then collapses a trivial
  first factor and transports any circle-group equivalence to the frozen
  product. Therefore the middle clause has no remaining product, basepoint,
  or categorical assembly: it needs only subsingleton `π₁(S²)` and the
  equivalence `π₁(S¹) ≃ Multiplicative ℤ`.

  Final searches of `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  Mathlib's product, sphere, circle, projectivization, covering, manifold,
  surface, Van Kampen, and singular-homology sources, topology siblings, and
  git history still found none of those factor computations, the antipodal
  projective cover, surface classification, or Seifert--van Kampen. Thus the
  three mathematical identification bridges remain open, but the product
  route is now completely compiled. The frozen statement is unchanged; no
  placeholder declaration was introduced.
  -/
  sorry
