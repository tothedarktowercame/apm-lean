import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.ManifoldFundamentalClass
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.TwoOpenFreeProductMappingCounitComponentIdentity
import ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison
import ConstructionTargets.CoefficientCompactComplementUnionToRelative
import ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare
import ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso
import ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence

/-! # Collared connected sums

The representation layer used by the integral homology computation.  This
first milestone fixes the collar, puncture, boundary, quotient, and radial
region types shared by `t98A02` and `t00A01`.
-/

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped Manifold

noncomputable section
namespace ConstructionTargets.CollaredConnectedSumHomology

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev I (n : ℕ) := modelWithCornersSelf ℝ (E n)
abbrev Disk (n : ℕ) (r : ℝ) := Metric.closedBall (0 : E n) r
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E n) 1

def unitToLarge (n : ℕ) : Disk n 1 → Disk n 2 := fun x =>
  ⟨x.1, Metric.closedBall_subset_closedBall (by norm_num) x.2⟩

def sphereToDisk (n : ℕ) : Sphere n → Disk n 1 := fun x =>
  ⟨x.1, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.2.le⟩

theorem continuous_unitToLarge (n : ℕ) : Continuous (unitToLarge n) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_sphereToDisk (n : ℕ) : Continuous (sphereToDisk n) :=
  continuous_subtype_val.subtype_mk _

/-- An embedded unit ball together with its specified radius-two extension. -/
structure BallCollar (n : ℕ) (M : Type) [TopologicalSpace M] where
  smallMap : Disk n 1 → M
  largeMap : Disk n 2 → M
  smallEmbedding : IsEmbedding smallMap
  largeEmbedding : IsEmbedding largeMap
  compatible : largeMap ∘ unitToLarge n = smallMap

namespace BallCollar

variable {n : ℕ} {M : Type} [TopologicalSpace M]

theorem largeMap_unitToLarge (c : BallCollar n M) (x : Disk n 1) :
    c.largeMap (unitToLarge n x) = c.smallMap x := by
  exact congrFun c.compatible x

/-- The manifold with the open unit ball removed. -/
abbrev Punctured (c : BallCollar n M) :=
  {x : M // x ∉ c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1}}

/-- The unit sphere, regarded as the boundary of the punctured manifold. -/
def boundaryMap (c : BallCollar n M) : Sphere n → Punctured c := fun s =>
  ⟨c.smallMap (sphereToDisk n s), by
    rintro ⟨y, hy, heq⟩
    have hys : y = sphereToDisk n s := c.smallEmbedding.injective heq
    subst y
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    exact (lt_irrefl (1 : ℝ)) (by simpa [sphereToDisk, hs] using hy)⟩

theorem continuous_boundaryMap (c : BallCollar n M) :
    Continuous c.boundaryMap := by
  apply Continuous.subtype_mk
  exact c.smallEmbedding.continuous.comp (continuous_sphereToDisk n)

/-- Radius-`r` points in the large collar, before mapping into the manifold. -/
def radialRegion (r : ℝ) : Set (Disk n 2) := {x | dist x.1 0 < r}

def radialHalf (c : BallCollar n M) : Set M := c.largeMap '' radialRegion (1 / 2)
def radialUnit (c : BallCollar n M) : Set M := c.largeMap '' radialRegion 1
def radialThreeHalves (c : BallCollar n M) : Set M :=
  c.largeMap '' radialRegion (3 / 2)
def radialTwo (c : BallCollar n M) : Set M := c.largeMap '' radialRegion 2

/-- The open radius-two part of the collar domain. -/
abbrev LargeInterior := {x : Disk n 2 // x ∈ radialRegion (n := n) 2}

theorem radialRegion_isOpen (r : ℝ) : IsOpen (radialRegion (n := n) r) := by
  change IsOpen ((fun x : Disk n 2 ↦ x.1) ⁻¹' Metric.ball 0 r)
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- The nested-subtype presentation of the large collar interior is the
ordinary open radius-two ball in the Euclidean model. -/
def largeInteriorHomeomorphBall :
    LargeInterior (n := n) ≃ₜ Metric.ball (0 : E n) 2 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by
    rw [Metric.mem_closedBall]
    exact x.2.le⟩, by
      change dist x.1 0 < 2
      exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk fun x ↦ by
      rw [Metric.mem_closedBall]
      exact x.2.le).subtype_mk fun x ↦ by
        change dist x.1 0 < 2
        exact x.2

/-- Restriction of the large collar map to its open interior. -/
def largeInteriorMap (c : BallCollar n M) : LargeInterior (n := n) → M :=
  fun x ↦ c.largeMap x.1

theorem largeInteriorMap_isEmbedding (c : BallCollar n M) :
    IsEmbedding c.largeInteriorMap := by
  exact c.largeEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem range_largeInteriorMap (c : BallCollar n M) :
    Set.range c.largeInteriorMap = c.radialTwo := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem largeInterior_isOpen_of_isOpenMap (c : BallCollar n M)
    (hopen : IsOpenMap c.largeInteriorMap) : IsOpen c.radialTwo := by
  rw [← c.range_largeInteriorMap]
  simpa only [Set.image_univ] using hopen Set.univ isOpen_univ

end BallCollar

inductive GlueRel {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Sum (c₁.Punctured) (c₂.Punctured) →
      Sum (c₁.Punctured) (c₂.Punctured) → Prop
  | boundary (s : Sphere n) :
      GlueRel c₁ c₂ (Sum.inl (c₁.boundaryMap s))
        (Sum.inr (c₂.boundaryMap s))

/-- The connected sum quotient, with the boundary relation oriented from the
first punctured summand to the second. -/
def ConnectedSum {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :=
  Quotient (Relation.EqvGen.setoid (GlueRel c₁ c₂))

noncomputable instance {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    TopologicalSpace (ConnectedSum c₁ c₂) :=
  TopologicalSpace.coinduced (fun z => Quotient.mk _ z) inferInstance

/-- Integral singular homology, in the representation used by the consumers. -/
abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The map on integral homology induced by the collar boundary inclusion. -/
noncomputable def boundaryHomologyMap {n : ℕ} {M : Type} [TopologicalSpace M]
    (c : BallCollar n M) (k : ℕ) : H k (Sphere n) ⟶ H k c.Punctured :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨c.boundaryMap, c.continuous_boundaryMap⟩)

/-- The genuine standard cover needed by Mayer--Vietoris: its two pieces
retract to the punctures and its overlap retracts to the gluing sphere.  The
equivalences are compatible with the cover inclusions: transported to the
sphere and the punctures, the inclusions `U ∩ V ⊆ U` and `U ∩ V ⊆ V` are
homotopic to the two collar boundary maps.  Without this, the Mayer--Vietoris
map out of `H (U ∩ V)` is unrelated to `boundaryHomologyMap`. -/
def HasStandardCover {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) : Prop :=
  ∃ U V : Set (ConnectedSum c₁ c₂),
    IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
    ∃ (e₁ : ContinuousMap.HomotopyEquiv U c₁.Punctured)
      (e₂ : ContinuousMap.HomotopyEquiv V c₂.Punctured)
      (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n)),
      ContinuousMap.Homotopic
        (e₁.toFun.comp
          ((ContinuousMap.inclusion Set.inter_subset_left).comp e₀.invFun))
        ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ ∧
      ContinuousMap.Homotopic
        (e₂.toFun.comp
          ((ContinuousMap.inclusion Set.inter_subset_right).comp e₀.invFun))
        ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩

namespace BallCollar

/-- **LIBRARY (B2a).** No retraction of the closed unit disk onto its boundary
sphere, from the sphere homology in `SphereHomology` (for `n + 1 = 1`, from
connectedness of the disk). -/
theorem largeInterior_isOpen_aux_euclidean_aux_noRetraction (n : ℕ) :
    ¬ ∃ r : Disk (n + 1) 1 → Sphere (n + 1),
      Continuous r ∧ ∀ s, r (sphereToDisk (n + 1) s) = s := by
  rintro ⟨r, hr, hri⟩
  by_cases hn : n = 0
  · subst n
    letI : ContractibleSpace (Disk 1 1) :=
      Metric.contractibleSpace_closedBall (by norm_num)
    let pneg : Sphere 1 :=
      ⟨EuclideanSpace.single 0 (-1), by simp [Sphere]⟩
    let ppos : Sphere 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [Sphere]⟩
    let f : Disk 1 1 → ℝ := fun x ↦ (r x).1 0
    have hf : Continuous f :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
        continuous_subtype_val).comp hr
    have hfneg : f (sphereToDisk 1 pneg) = -1 := by
      change (r (sphereToDisk 1 pneg)).1 0 = -1
      rw [show r (sphereToDisk 1 pneg) = pneg from hri pneg]
      simp [pneg]
    have hfpos : f (sphereToDisk 1 ppos) = 1 := by
      change (r (sphereToDisk 1 ppos)).1 0 = 1
      rw [show r (sphereToDisk 1 ppos) = ppos from hri ppos]
      simp [ppos]
    have hz : (0 : ℝ) ∈ Set.range f := by
      apply intermediate_value_univ (sphereToDisk 1 pneg) (sphereToDisk 1 ppos) hf
      rw [hfneg, hfpos]
      norm_num
    obtain ⟨x, hx⟩ := hz
    have hvec : (r x).1 = 0 := by
      ext i
      fin_cases i
      exact hx
    have hs := (r x).2
    rw [Metric.mem_sphere, hvec, dist_self] at hs
    norm_num at hs
  · let i : C(Sphere (n + 1), Disk (n + 1) 1) :=
      ⟨sphereToDisk (n + 1), continuous_sphereToDisk (n + 1)⟩
    let rc : C(Disk (n + 1) 1, Sphere (n + 1)) := ⟨r, hr⟩
    have hsplit : rc.comp i = ContinuousMap.id (Sphere (n + 1)) := by
      apply ContinuousMap.ext
      intro s
      exact hri s
    have hsphere :
        ¬ IsZero (H n (Sphere (n + 1))) := by
      intro h
      have hz : IsZero (ModuleCat.of ℤ ℤ) :=
        h.of_iso
          (ConstructionTargets.SphereHomology.sphereModuleTopHomologyIsoInt n
            (Nat.pos_of_ne_zero hn)).symm
      have hid : 𝟙 (ModuleCat.of ℤ ℤ) = 0 := (IsZero.iff_id_eq_zero _).mp hz
      have hone := ConcreteCategory.congr_hom hid (1 : ℤ)
      norm_num at hone
    have hdiskGroup : IsZero
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).obj (TopCat.of (Disk (n + 1) 1))) := by
      letI : ContractibleSpace (Disk (n + 1) 1) :=
        Metric.contractibleSpace_closedBall (by norm_num)
      exact ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
        (Disk (n + 1) 1) n hn
    have hdisk : IsZero
        (H n (Disk (n + 1) 1)) :=
      ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
        _ _ hdiskGroup
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)
    have hi : F.map (TopCat.ofHom i) = 0 := hdisk.eq_of_tgt _ _
    apply hsphere
    rw [IsZero.iff_id_eq_zero]
    have hsplit' :
        F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom rc) = 𝟙 _ := by
      rw [← F.map_comp]
      have hTop : TopCat.ofHom i ≫ TopCat.ofHom rc = 𝟙 (TopCat.of (Sphere (n + 1))) := by
        change TopCat.ofHom (rc.comp i) = TopCat.ofHom (ContinuousMap.id _)
        exact congrArg TopCat.ofHom hsplit
      rw [hTop, F.map_id]
    rw [← hsplit', hi, zero_comp]

/-- **LIBRARY (B2b).** Brouwer's fixed-point theorem for the closed unit disk,
from no retraction (B2a, taken as `hNR`) by the ray construction. -/
private noncomputable def largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d
    {n : ℕ} (g : Disk n 1 → Disk n 1) (x : Disk n 1) : E n := x.1 - (g x).1

private noncomputable def largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_A
    {n : ℕ} (g : Disk n 1 → Disk n 1) (x : Disk n 1) : ℝ :=
  ‖largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d g x‖ ^ 2

private noncomputable def largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_B
    {n : ℕ} (g : Disk n 1 → Disk n 1) (x : Disk n 1) : ℝ :=
  @inner ℝ (E n) _ x.1 (largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d g x)

private noncomputable def largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C
    {n : ℕ} (x : Disk n 1) : ℝ := 1 - ‖x.1‖ ^ 2

private noncomputable def largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_t
    {n : ℕ} (g : Disk n 1 → Disk n 1) (x : Disk n 1) : ℝ :=
  let A := largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_A g x
  let B := largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_B g x
  let C := largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C x
  (-B + Real.sqrt (B ^ 2 + A * C)) / A

theorem largeInterior_isOpen_aux_euclidean_aux_brouwer (n : ℕ)
    (hNR : ∀ m : ℕ, ¬ ∃ r : Disk (m + 1) 1 → Sphere (m + 1),
      Continuous r ∧ ∀ s, r (sphereToDisk (m + 1) s) = s)
    {g : Disk n 1 → Disk n 1} (hg : Continuous g) : ∃ x, g x = x := by
  by_contra hfix
  push_neg at hfix
  cases n with
  | zero =>
      have hx : (⟨0, by simp [Disk]⟩ : Disk 0 1) = g ⟨0, by simp [Disk]⟩ := by
        apply Subtype.ext
        ext i
        exact Fin.elim0 i
      exact hfix _ hx.symm
  | succ m =>
      apply hNR m
      let d : Disk (m + 1) 1 → E (m + 1) :=
        largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d g
      let A : Disk (m + 1) 1 → ℝ :=
        largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_A g
      let B : Disk (m + 1) 1 → ℝ :=
        largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_B g
      let C : Disk (m + 1) 1 → ℝ :=
        largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C
      let t : Disk (m + 1) 1 → ℝ :=
        largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_t g
      have hd : Continuous d := by
        exact continuous_subtype_val.sub
          (continuous_subtype_val.comp hg)
      have hA : Continuous A := by
        exact (continuous_norm.comp hd).pow 2
      have hB : Continuous B := by
        exact continuous_inner.comp
          (continuous_subtype_val.prodMk hd)
      have hC : Continuous C := by
        exact continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2)
      have hApos (x : Disk (m + 1) 1) : 0 < A x := by
        rw [show A x = ‖d x‖ ^ 2 by rfl]
        exact sq_pos_of_pos (norm_pos_iff.mpr (by
          intro hd0
          apply hfix x
          apply Subtype.ext
          change (g x).1 = x.1
          dsimp [d, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d] at hd0
          exact sub_eq_zero.mp hd0 |>.symm))
      have hCnonneg (x : Disk (m + 1) 1) : 0 ≤ C x := by
        dsimp [C, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C]
        have hx : ‖x.1‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
        nlinarith [norm_nonneg x.1]
      have hdisc (x : Disk (m + 1) 1) : 0 ≤ B x ^ 2 + A x * C x :=
        add_nonneg (sq_nonneg _) (mul_nonneg (hApos x).le (hCnonneg x))
      have ht : Continuous t := by
        change Continuous (fun x =>
          (-B x + Real.sqrt (B x ^ 2 + A x * C x)) / A x)
        exact (hB.neg.add (Real.continuous_sqrt.comp
          ((hB.pow 2).add (hA.mul hC)))).div hA (fun x => ne_of_gt (hApos x))
      have hquad (x : Disk (m + 1) 1) :
          A x * (t x) ^ 2 + 2 * B x * t x = C x := by
        have hs := Real.sq_sqrt (hdisc x)
        have hAn : A x ≠ 0 := ne_of_gt (hApos x)
        change A x * ((-B x + Real.sqrt (B x ^ 2 + A x * C x)) / A x) ^ 2 +
          2 * B x * ((-B x + Real.sqrt (B x ^ 2 + A x * C x)) / A x) = C x
        rw [div_pow]
        field_simp [hAn]
        nlinarith [hs]
      have hrnorm (x : Disk (m + 1) 1) : ‖x.1 + t x • d x‖ = 1 := by
        have hi : @inner ℝ (E (m + 1)) _ (d x) (d x) = A x := by
          simp [A, d, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_A,
            real_inner_self_eq_norm_sq]
        have hib : @inner ℝ (E (m + 1)) _ x.1 (d x) = B x := rfl
        have hxnorm : ‖x.1‖ ^ 2 = 1 - C x := by
          simp [C, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C]
        have hs : ‖x.1 + t x • d x‖ ^ 2 = 1 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_add_left, inner_add_right, real_inner_smul_left,
            inner_smul_right, hi, hib, real_inner_comm]
          rw [real_inner_self_eq_norm_sq, hxnorm]
          nlinarith [hquad x]
        nlinarith [norm_nonneg (x.1 + t x • d x)]
      let r : Disk (m + 1) 1 → Sphere (m + 1) := fun x =>
        ⟨x.1 + t x • d x, by
          rw [Metric.mem_sphere, dist_zero_right, hrnorm]⟩
      refine ⟨r, ?_, ?_⟩
      · apply Continuous.subtype_mk
        exact continuous_subtype_val.add (ht.smul hd)
      · intro s
        apply Subtype.ext
        change (sphereToDisk (m + 1) s).1 +
            t (sphereToDisk (m + 1) s) • d (sphereToDisk (m + 1) s) = s.1
        have hC0 : C (sphereToDisk (m + 1) s) = 0 := by
          dsimp [C, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_C]
          have hs : ‖s.1‖ = 1 := by
            simpa [Metric.mem_sphere, dist_zero_right] using s.2
          change 1 - ‖s.1‖ ^ 2 = 0
          rw [hs]
          norm_num
        have hBnonneg : 0 ≤ B (sphereToDisk (m + 1) s) := by
          dsimp [B, d, largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_B,
            largeInterior_isOpen_aux_euclidean_aux_brouwer_aux_d]
          have hs : ‖s.1‖ = 1 := by
            simpa [Metric.mem_sphere, dist_zero_right] using s.2
          have hg' : ‖(g (sphereToDisk (m + 1) s)).1‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using
              (g (sphereToDisk (m + 1) s)).2
          simp only [sphereToDisk]
          rw [inner_sub_right, real_inner_self_eq_norm_sq, hs]
          exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa [hs] using hg'))
        have ht0 : t (sphereToDisk (m + 1) s) = 0 := by
          change (-B (sphereToDisk (m + 1) s) +
            Real.sqrt (B (sphereToDisk (m + 1) s) ^ 2 +
              A (sphereToDisk (m + 1) s) * C (sphereToDisk (m + 1) s))) /
                A (sphereToDisk (m + 1) s) = 0
          rw [hC0, mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg hBnonneg]
          simp
        rw [ht0]
        simp [sphereToDisk]

/-- **LIBRARY (B2c).** A continuous injection of the closed unit disk into
`E n` sends the centre to an interior point of its image (Tao's argument:
Tietze-extend the inverse and apply Brouwer, B2b, taken as `hB`). -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_stability
    (n : ℕ)
    (hB : ∀ {g : Disk n 1 → Disk n 1}, Continuous g → ∃ x, g x = x)
    {f : Disk n 1 → E n} (hf : Continuous f)
    {Gtilde : E n → E n} (hGtilde : Continuous Gtilde)
    (hclose : ∀ x : Disk n 1, ‖x.1 - Gtilde (f x)‖ ≤ 1) :
    ∃ y ∈ Set.range f, Gtilde y = 0 := by
  let g : Disk n 1 → Disk n 1 := fun x =>
    ⟨x.1 - Gtilde (f x), by
      simpa [Metric.mem_closedBall, dist_zero_right] using hclose x⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (hGtilde.comp (hf.comp continuous_id))
  obtain ⟨x, hx⟩ := hB hg
  refine ⟨f x, ⟨x, rfl⟩, ?_⟩
  have hxval : x.1 - Gtilde (f x) = x.1 := congrArg Subtype.val hx
  exact sub_eq_self.mp hxval

/-- Tietze step of B2c: a continuous injection of the compact disk is a closed
embedding, so its inverse on the image extends to a continuous self-map of `E n`. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_tietze
    (n : ℕ) {f : Disk n 1 → E n} (hf : Continuous f) (hinj : Function.Injective f) :
    ∃ Gtilde : E n → E n, Continuous Gtilde ∧ ∀ x : Disk n 1, Gtilde (f x) = x.1 := by
  let v : C(Disk n 1, E n) := ⟨fun x ↦ x.1, continuous_subtype_val⟩
  obtain ⟨G, hG⟩ := v.exists_extension (hf.isClosedEmbedding hinj)
  refine ⟨G, G.continuous, fun x ↦ ?_⟩
  exact DFunLike.congr_fun hG x

/-- Perturbation, step 1: a point outside `range f` arbitrarily close to `f 0`. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_nearby_complement
    (n : ℕ) {f : Disk n 1 → E n}
    (hnot : f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∉ interior (Set.range f))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : E n, dist c (f ⟨0, Metric.mem_closedBall_self zero_le_one⟩) < ε ∧
      c ∉ Set.range f := by
  by_contra h
  push_neg at h
  apply hnot
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [Metric.ball_mem_nhds
    (f ⟨0, Metric.mem_closedBall_self zero_le_one⟩) hε] with c hc
  exact h c (by simpa [dist_comm] using hc)

/-- Perturbation, radial push: `Φ y = c + max (ε / ‖y - c‖) 1 • (y - c)` fixes points at
distance `≥ ε` from `c` and sends the rest of `{c}ᶜ` onto `sphere c ε`. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_push
    (n : ℕ) (c : E n) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : E n → E n, ContinuousOn Φ {c}ᶜ ∧ (∀ y, ε ≤ ‖y - c‖ → Φ y = y) ∧
      ∀ y, y ≠ c → ‖y - c‖ < ε → Φ y ∈ Metric.sphere c ε := by
  let Φ : E n → E n := fun y ↦
    c + max (ε / ‖y - c‖) 1 • (y - c)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro y hy
    have hyc : y ≠ c := by simpa using hy
    have hyn : ‖y - c‖ ≠ 0 := by
      simpa [norm_eq_zero, sub_eq_zero] using hyc
    have hn : ContinuousAt (fun z : E n ↦ ‖z - c‖) y :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt
    have hq : ContinuousAt (fun z : E n ↦ ε / ‖z - c‖) y :=
      continuousAt_const.div hn hyn
    exact (continuousAt_const.add
      ((hq.max continuousAt_const).smul
        (continuous_id.sub continuous_const).continuousAt)).continuousWithinAt
  · intro y hy
    have hyn : 0 < ‖y - c‖ := lt_of_lt_of_le hε hy
    have hdiv : ε / ‖y - c‖ ≤ 1 := (div_le_one hyn).2 hy
    dsimp [Φ]
    rw [max_eq_right hdiv, one_smul, add_sub_cancel]
  · intro y hyc hy
    have hyn : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyc)
    have hdiv : 1 ≤ ε / ‖y - c‖ := (le_div_iff₀ hyn).2 (by simpa using hy.le)
    rw [Metric.mem_sphere, dist_eq_norm]
    dsimp [Φ]
    rw [add_sub_cancel_left, max_eq_left hdiv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hε hyn), div_mul_cancel₀ ε (ne_of_gt hyn)]

/-- Perturbation, approximation: a continuous self-map of `E n` is uniformly within `η` of a
`C¹` map on any compact set (mollify with a `ContDiffBump`, or Stone–Weierstrass). -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_smooth_approx
    (n : ℕ) {G : E n → E n} (hG : Continuous G)
    {T : Set (E n)} (hT : IsCompact T) {η : ℝ} (hη : 0 < η) :
    ∃ P : E n → E n, ContDiff ℝ 1 P ∧ ∀ y ∈ T, ‖P y - G y‖ < η := by
  let g : C(E n, E n) := ⟨G, hG⟩
  have hg := ContinuousMap.dense_setOf_contDiff (E := E n) (F := E n) g
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity
      (Filter.HasBasis.compactConvergenceUniformity (α := E n)
        (β := E n) Metric.uniformity_basis_dist))] at hg
  simp only [Prod.forall, mem_setOf_eq, and_imp] at hg
  obtain ⟨P, hP, hPT⟩ := hg T η hT hη
  exact ⟨P, hP.of_le (by norm_num), fun y hy ↦ by simpa [dist_eq_norm] using hPT y hy⟩

/-- Perturbation, avoidance: for `0 < n` the `C¹` image of `sphere c ε` is Haar-null
(`Measure.addHaar_sphere`, `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`),
so some `v` with `‖v‖ < η` is not a value of `P` on the sphere. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_avoid_sphere
    (n : ℕ) (hn : 0 < n) {P : E n → E n} (hP : ContDiff ℝ 1 P)
    (c : E n) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ v : E n, ‖v‖ < η ∧ ∀ y ∈ Metric.sphere c ε, P y ≠ v := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have himage : MeasureTheory.volume (P '' Metric.sphere c ε) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      MeasureTheory.volume
      hP.differentiable_one.differentiableOn
      (MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume c ε)
  have hball : 0 < MeasureTheory.volume (Metric.ball (0 : E n) η) :=
    Metric.measure_ball_pos MeasureTheory.volume 0 hη
  have hnsub : ¬ Metric.ball (0 : E n) η ⊆ P '' Metric.sphere c ε := by
    intro hsub
    have hle : MeasureTheory.volume (Metric.ball (0 : E n) η) ≤
        MeasureTheory.volume (P '' Metric.sphere c ε) :=
      MeasureTheory.measure_mono hsub
    rw [himage] at hle
    exact (not_lt_of_ge hle) hball
  obtain ⟨v, hv, hnv⟩ := Set.not_subset.mp hnsub
  refine ⟨v, ?_, ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm] using hv
  · intro y hy heq
    exact hnv ⟨y, hy, heq⟩

/-- A continuous map with no zero on a compact set is bounded away from zero there. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_lower_bound
    (n : ℕ) {G : E n → E n} (hG : Continuous G)
    {S : Set (E n)} (hS : IsCompact S) (h0 : ∀ y ∈ S, G y ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ y ∈ S, m ≤ ‖G y‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hG.norm.continuousOn
    exact ⟨‖G y₀‖, norm_pos_iff.mpr (h0 y₀ hy₀), fun y hy => hmin hy⟩

/-- Perturbation step of B2c (Tao's argument).  If `f 0` is not interior to the
image, pick `c ∉ range f` within `ε` of `f 0`; push the part of the image inside
`ball c ε` radially onto `sphere c ε`, and replace `Gtilde` by a `C¹` approximation
`P` that has no zero on `range f \ ball c ε` (where `Gtilde` is bounded away from 0)
and none on `sphere c ε` (its image of that null set is null, by
`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`;
subtract a small constant outside it).  `K = P ∘ push ∘ f` is then zero-free and
within `1` of the identity. -/
theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb
    (n : ℕ) (hn : 0 < n)
    {f : Disk n 1 → E n} (hf : Continuous f) (hinj : Function.Injective f)
    {Gtilde : E n → E n} (hGtilde : Continuous Gtilde)
    (hGf : ∀ x : Disk n 1, Gtilde (f x) = x.1)
    (hnot : f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∉ interior (Set.range f)) :
    ∃ K : Disk n 1 → E n, Continuous K ∧ (∀ x, K x ≠ 0) ∧ ∀ x, ‖x.1 - K x‖ ≤ 1 := by
  set x₀ : Disk n 1 := ⟨0, Metric.mem_closedBall_self zero_le_one⟩ with hx₀
  set y₀ := f x₀ with hy₀
  have hG0 : Gtilde y₀ = 0 := hGf x₀
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuous_iff.mp hGtilde y₀ (1 / 4) (by norm_num)
  set ε := δ / 3 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨c, hcy, hc⟩ := largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_nearby_complement n hnot hε
  have hfc : ∀ x, f x ≠ c := fun x h => hc ⟨x, h⟩
  -- `Gtilde` is within `1/4` of `0` on `closedBall c ε`.
  have hnear : ∀ y, ‖y - c‖ ≤ ε → ‖Gtilde y‖ < 1 / 4 := by
    intro y hy
    have h := hδG y (by
      calc dist y y₀ ≤ dist y c + dist c y₀ := dist_triangle _ _ _
        _ < δ := by rw [dist_eq_norm]; linarith)
    simpa [hG0, dist_eq_norm] using h
  obtain ⟨Φ, hΦc, hΦfar, hΦnear⟩ := largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_push n c hε
  set S : Set (E n) := Set.range f ∩ {y | ε ≤ ‖y - c‖} with hSdef
  have hS : IsCompact S :=
    (isCompact_range hf).inter_right
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hS0 : ∀ y ∈ S, Gtilde y ≠ 0 := by
    rintro y ⟨⟨x, rfl⟩, hy⟩ h
    rw [hGf] at h
    have hx : x = x₀ := Subtype.ext h
    subst hx
    have : ‖y₀ - c‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact hcy
    exact absurd hy (not_le.mpr this)
  obtain ⟨m, hm, hmG⟩ := largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_lower_bound n hGtilde hS hS0
  set η := min m (1 / 4) with hηdef
  have hη : 0 < η := lt_min hm (by norm_num)
  obtain ⟨Q, hQ, hQG⟩ := largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_smooth_approx n hGtilde
    (hS.union (isCompact_sphere c ε)) (half_pos hη)
  obtain ⟨v, hv, hQv⟩ := largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb_aux_avoid_sphere n hn hQ c hε (half_pos hη)
  have hΦf : Continuous fun x => Φ (f x) :=
    hΦc.comp_continuous hf (fun x => hfc x)
  -- Where the pushed image lands.
  have hland : ∀ x, (ε ≤ ‖f x - c‖ ∧ Φ (f x) = f x ∧ Φ (f x) ∈ S) ∨
      (‖f x - c‖ < ε ∧ Φ (f x) ∈ Metric.sphere c ε) := by
    intro x
    by_cases h : ε ≤ ‖f x - c‖
    · exact Or.inl ⟨h, hΦfar _ h, by rw [hΦfar _ h]; exact ⟨⟨x, rfl⟩, h⟩⟩
    · exact Or.inr ⟨not_le.mp h, hΦnear _ (hfc x) (not_le.mp h)⟩
  refine ⟨fun x => Q (Φ (f x)) - v, (hQ.continuous.comp hΦf).sub continuous_const,
    ?_, ?_⟩
  · intro x hK
    have hKv : Q (Φ (f x)) = v := sub_eq_zero.mp hK
    rcases hland x with ⟨_, _, hS'⟩ | ⟨_, hsph⟩
    · have h1 := hQG _ (Or.inl hS')
      have h2 := hmG _ hS'
      rw [hKv] at h1
      have : ‖Gtilde (Φ (f x))‖ ≤ ‖v - Gtilde (Φ (f x))‖ + ‖v‖ := by
        calc ‖Gtilde (Φ (f x))‖ = ‖v - (v - Gtilde (Φ (f x)))‖ := by abel_nf
          _ ≤ ‖v‖ + ‖v - Gtilde (Φ (f x))‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      have : η ≤ m := min_le_left _ _
      linarith
    · exact hQv _ hsph hKv
  · intro x
    have hx : x.1 = Gtilde (f x) := (hGf x).symm
    have hmem : Φ (f x) ∈ S ∪ Metric.sphere c ε := by
      rcases hland x with ⟨_, _, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have hQ1 := hQG _ hmem
    have hη4 : η ≤ 1 / 4 := min_le_right _ _
    have hdiff : ‖Gtilde (f x) - Gtilde (Φ (f x))‖ ≤ 1 / 2 := by
      rcases hland x with ⟨_, hΦ, _⟩ | ⟨hlt, hsph⟩
      · rw [hΦ, sub_self, norm_zero]; norm_num
      · have ha := hnear (f x) hlt.le
        have hb := hnear (Φ (f x)) (by
          rw [Metric.mem_sphere, dist_eq_norm] at hsph; exact hsph.le)
        calc ‖Gtilde (f x) - Gtilde (Φ (f x))‖
            ≤ ‖Gtilde (f x)‖ + ‖Gtilde (Φ (f x))‖ := norm_sub_le _ _
          _ ≤ 1 / 2 := by linarith
    rw [hx]
    calc ‖Gtilde (f x) - (Q (Φ (f x)) - v)‖
        = ‖(Gtilde (f x) - Gtilde (Φ (f x))) + (Gtilde (Φ (f x)) - Q (Φ (f x))) + v‖ := by
          congr 1; abel
      _ ≤ ‖Gtilde (f x) - Gtilde (Φ (f x))‖ + ‖Gtilde (Φ (f x)) - Q (Φ (f x))‖ + ‖v‖ :=
          norm_add₃_le
      _ ≤ 1 := by
          have := norm_sub_rev (Gtilde (Φ (f x))) (Q (Φ (f x)))
          linarith

theorem largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive
    (n : ℕ) (hn : 0 < n)
    (hB : ∀ {g : Disk n 1 → Disk n 1}, Continuous g → ∃ x, g x = x)
    {f : Disk n 1 → E n} (hf : Continuous f) (hinj : Function.Injective f) :
    f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∈ interior (Set.range f) := by
  by_contra hnot
  obtain ⟨Gtilde, hGtilde, hGf⟩ :=
    largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_tietze n hf hinj
  obtain ⟨K, hK, hK0, hKc⟩ :=
    largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive_aux_perturb
      n hn hf hinj hGtilde hGf hnot
  obtain ⟨y, ⟨x, rfl⟩, hy⟩ :=
    largeInterior_isOpen_aux_euclidean_aux_interior_aux_stability n hB hK continuous_id
      (fun x => by simpa using hKc x)
  exact hK0 x hy

theorem largeInterior_isOpen_aux_euclidean_aux_interior (n : ℕ)
    (hB : ∀ {g : Disk n 1 → Disk n 1}, Continuous g → ∃ x, g x = x)
    {f : Disk n 1 → E n} (hf : Continuous f) (hinj : Function.Injective f) :
    f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∈ interior (Set.range f) := by
  by_cases hn : n = 0
  · subst n
    have hrange : Set.range f = Set.univ :=
      (Set.range_nonempty f).eq_univ
    rw [hrange, interior_univ]
    exact Set.mem_univ _
  · exact largeInterior_isOpen_aux_euclidean_aux_interior_aux_positive
      n (Nat.pos_of_ne_zero hn) hB hf hinj

/-- **LIBRARY (B2d).** Euclidean invariance of domain, from B2c (taken as `hI`) by rescaling
closed balls inside `U`. -/
theorem largeInterior_isOpen_aux_euclidean_aux_open (n : ℕ)
    (hI : ∀ {f : Disk n 1 → E n}, Continuous f → Function.Injective f →
      f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∈ interior (Set.range f))
    {U : Set (E n)} (hU : IsOpen U) {g : U → E n} (hg : Continuous g)
    (hinj : Function.Injective g) : IsOpenMap g := by
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨x, hxV, rfl⟩
  have hW : IsOpen ((Subtype.val : U → E n) '' V) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap V hV
  have hxW : x.1 ∈ (Subtype.val : U → E n) '' V := ⟨x, hxV, rfl⟩
  obtain ⟨r, hr, hrsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  let q : Disk n 1 → U := fun y => ⟨x.1 + r • y.1, by
    rcases hrsub (show x.1 + r • y.1 ∈ Metric.closedBall x.1 r by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (by
        have hy := y.2
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        exact hy)) with ⟨w, hw, heq⟩
    simpa only [heq] using w.2⟩
  let f : Disk n 1 → E n := fun y => g (q y)
  have hf : Continuous f := by
    apply hg.comp
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_const.smul continuous_subtype_val)
  have hfinj : Function.Injective f := by
    intro a b hab
    have huv : x.1 + r • a.1 = x.1 + r • b.1 :=
      congrArg Subtype.val (hinj hab)
    apply Subtype.ext
    have hrs : r • a.1 = r • b.1 := add_left_cancel huv
    have := congrArg (fun z : E n => r⁻¹ • z) hrs
    simpa [hr.ne'] using this
  have hcenter := hI hf hfinj
  have hfrange : Set.range f ⊆ g '' V := by
    rintro _ ⟨y, rfl⟩
    refine ⟨q y, ?_, rfl⟩
    rcases hrsub (show x.1 + r • y.1 ∈ Metric.closedBall x.1 r by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (by
        have hy := y.2
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        exact hy)) with ⟨w, hw, heq⟩
    have hwq : w = q y := by
      apply Subtype.ext
      exact heq
    exact hwq ▸ hw
  have hq0 : q ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = x := by
    apply Subtype.ext
    simp [q]
  have hcenter' : g x ∈ interior (Set.range f) := by
    simpa only [f, hq0] using hcenter
  have hmem : g x ∈ interior (g '' V) :=
    interior_mono hfrange hcenter'
  exact Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset

/-- **LIBRARY (B2e).** Reduction of manifold invariance of domain to the
Euclidean case through charts (the model `I d` has no boundary, so chart
targets are open in `E d`). -/
theorem largeInterior_isOpen_aux_euclidean_aux_chart
    (d : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace (E d) X]
    [IsManifold (I d) (⊤ : ℕ∞) X]
    (hE : ∀ {U : Set (E d)}, IsOpen U → ∀ {g : U → E d}, Continuous g →
      Function.Injective g → IsOpenMap g)
    {f : LargeInterior (n := d) → X} (hf : Continuous f)
    (hinj : Function.Injective f) : IsOpenMap f := by
  let q : LargeInterior (n := d) → E d := fun x => x.1.1
  have hq : IsOpenEmbedding q := by
    exact Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp
      largeInteriorHomeomorphBall.isOpenEmbedding
  intro s hs
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨x, hx, rfl⟩
  let c := chartAt (E d) (f x)
  let A : Set (LargeInterior (n := d)) := s ∩ f ⁻¹' c.source
  have hA : IsOpen A := hs.inter (c.open_source.preimage hf)
  have hxA : x ∈ A := ⟨hx, mem_chart_source (E d) (f x)⟩
  let U : Set (E d) := q '' A
  have hU : IsOpen U := hq.isOpenMap A hA
  let e : A ≃ₜ U :=
    (Equiv.Set.image q A hq.injective).toHomeomorphOfIsInducing
      ((hq.restrict (fun z (hz : z ∈ A) =>
        show q z ∈ U from ⟨z, hz, rfl⟩) hA).isInducing)
  let g : U → E d := fun z => c (f (e.symm z).1)
  have hg : Continuous g := by
    apply c.continuousOn.comp_continuous
      (hf.comp (continuous_subtype_val.comp e.symm.continuous))
    intro z
    exact (e.symm z).2.2
  have hginj : Function.Injective g := by
    intro z w hzw
    have hc : f (e.symm z).1 = f (e.symm w).1 :=
      c.injOn (e.symm z).2.2 (e.symm w).2.2 hzw
    exact e.symm.injective (Subtype.ext (hinj hc))
  have hopen_g : IsOpenMap g := hE hU hg hginj
  let T : Set (E d) := g '' (e '' {z : A | z.1 ∈ s})
  have heall : e '' {z : A | z.1 ∈ s} = Set.univ := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨e.symm z, (e.symm z).2.1, e.apply_symm_apply z⟩
  have hT : IsOpen T := hopen_g _ (by rw [heall]; exact isOpen_univ)
  have hTtarget : T ⊆ c.target := by
    rintro z ⟨u, hu, rfl⟩
    exact c.map_source (e.symm u).2.2
  refine ⟨c.symm '' T, ?_, c.isOpen_image_symm_of_subset_target hT hTtarget, ?_⟩
  · rintro z ⟨u, huT, huz⟩
    obtain ⟨v, hv, rfl⟩ := huT
    refine ⟨(e.symm v).1, (e.symm v).2.1, ?_⟩
    rw [← huz]
    change f (e.symm v).1 = c.symm (c (f (e.symm v).1))
    exact (c.left_inv (e.symm v).2.2).symm
  · refine ⟨g (e ⟨x, hxA⟩), ?_, ?_⟩
    · refine ⟨e ⟨x, hxA⟩, ?_, rfl⟩
      rw [heall]
      trivial
    · change c.symm (c (f (e.symm (e ⟨x, hxA⟩)).1)) = f x
      rw [e.symm_apply_apply]
      exact c.left_inv (mem_chart_source (E d) (f x))

/-- **LIBRARY (B2).** Invariance of domain for the interior of a collared ball. -/
theorem largeInterior_isOpen_aux_euclidean
    (d : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace (E d) X]
    [IsManifold (I d) (⊤ : ℕ∞) X]
    {f : LargeInterior (n := d) → X} (hf : Continuous f)
    (hinj : Function.Injective f) : IsOpenMap f :=
  largeInterior_isOpen_aux_euclidean_aux_chart d X
    (fun hU _ hg hinj => largeInterior_isOpen_aux_euclidean_aux_open d
      (fun hf' hinj' => largeInterior_isOpen_aux_euclidean_aux_interior d
        (fun hg' => largeInterior_isOpen_aux_euclidean_aux_brouwer d
          largeInterior_isOpen_aux_euclidean_aux_noRetraction hg') hf' hinj')
      hU hg hinj)
    hf hinj

theorem largeInterior_isOpen (n : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M) :
    IsOpen c.radialTwo := by
  apply c.largeInterior_isOpen_of_isOpenMap
  exact largeInterior_isOpen_aux_euclidean n M
    c.largeInteriorMap_isEmbedding.continuous
    c.largeInteriorMap_isEmbedding.injective

/-- **LIBRARY (B3).** Removing the open ball of a collar does not disconnect
a connected manifold of dimension at least two. -/
lemma punctured_pathConnected_aux_first_entry
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {O K : Set X} (hO : IsOpen O) (hK : IsClosed K) (hOK : O ⊆ K)
    {x k : X} (hx : x ∉ O) (hk : k ∈ K) :
    ∃ z ∈ K \ O, JoinedIn Oᶜ x z := by
  classical
  by_cases hxK : x ∈ K
  · exact ⟨x, ⟨hxK, hx⟩, JoinedIn.refl hx⟩
  let γ : Path x k := PathConnectedSpace.somePath x k
  let S : Set ℝ := {t | t ∈ Set.Icc 0 1 ∧ γ.extend t ∈ K}
  have hS_closed : IsClosed S :=
    isClosed_Icc.inter (hK.preimage γ.continuous_extend)
  have hS_ne : S.Nonempty := by
    refine ⟨1, ⟨Set.right_mem_Icc.2 zero_le_one, ?_⟩⟩
    simpa [γ] using hk
  have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀S : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_nonneg : 0 ≤ t₀ := ht₀S.1.1
  have ht₀_le_one : t₀ ≤ 1 := ht₀S.1.2
  have ht₀_pos : 0 < t₀ := by
    refine lt_of_le_of_ne ht₀_nonneg (Ne.symm ?_)
    intro ht
    apply hxK
    have : γ.extend 0 ∈ K := by simpa [ht] using ht₀S.2
    simpa [γ] using this
  have hleast : ∀ s ∈ S, t₀ ≤ s := (isGLB_csInf hS_ne hS_bdd).1
  have ht₀_notO : γ.extend t₀ ∉ O := by
    intro htO
    have hopen : IsOpen (γ.extend ⁻¹' O) := hO.preimage γ.continuous_extend
    rcases Metric.isOpen_iff.1 hopen t₀ htO with ⟨ε, hε, hball⟩
    let s := t₀ - min (t₀ / 2) (ε / 2)
    have hmin_pos : 0 < min (t₀ / 2) (ε / 2) :=
      lt_min (half_pos ht₀_pos) (half_pos hε)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      have := min_le_left (t₀ / 2) (ε / 2)
      linarith
    have hslt : s < t₀ := by simp [s, hmin_pos]
    have hs1 : s ≤ 1 := hslt.le.trans ht₀_le_one
    have hsO : γ.extend s ∈ O := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [s]
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (le_of_lt hmin_pos)]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    exact (not_lt_of_ge (hleast s ⟨⟨hs0, hs1⟩, hOK hsO⟩)) hslt
  refine ⟨γ.extend t₀, ⟨ht₀S.2, ht₀_notO⟩, ?_⟩
  refine ⟨(γ.truncateOfLE ht₀_nonneg).cast (by simp [γ]) rfl, ?_⟩
  intro u
  change γ.extend (min (max (u : ℝ) 0) t₀) ∈ Oᶜ
  intro huO
  let s := min (max (u : ℝ) 0) t₀
  have hs0 : 0 ≤ s := by simp [s, ht₀_nonneg]
  have hst : s ≤ t₀ := min_le_right _ _
  have hs1 : s ≤ 1 := hst.trans ht₀_le_one
  by_cases hst' : s = t₀
  · exact ht₀_notO (by simpa [s, hst'] using huO)
  · have hslt : s < t₀ := lt_of_le_of_ne hst hst'
    exact (not_lt_of_ge
      (hleast s ⟨⟨hs0, hs1⟩, hOK (by simpa [s] using huO)⟩)) hslt

theorem punctured_pathConnected (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [PathConnectedSpace M]
    [ChartedSpace (E n) M] [IsManifold (I n) (⊤ : ℕ∞) M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    PathConnectedSpace c.Punctured := by
  classical
  let O : Set M := c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1}
  have hO : IsOpen O := by
    let S₁ : Set (Disk n 2) := {x | dist x.1 0 < 1}
    let S₂ : Set (Disk n 2) := {x | dist x.1 0 < 2}
    have hS₁ : IsOpen S₁ := radialRegion_isOpen 1
    obtain ⟨W, hW, hWpre⟩ := c.largeEmbedding.isInducing.isOpen_iff.mp hS₁
    have himage : c.largeMap '' S₁ = W ∩ c.largeMap '' S₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxW : c.largeMap x ∈ W := by
          have : x ∈ c.largeMap ⁻¹' W := hWpre.symm ▸ hx
          exact this
        exact ⟨hxW, x, by dsimp [S₁, S₂] at hx ⊢; linarith, rfl⟩
      · rintro ⟨hzW, x, hx₂, rfl⟩
        refine ⟨x, ?_, rfl⟩
        have : x ∈ c.largeMap ⁻¹' W := hzW
        exact hWpre ▸ this
    have hunit : O = c.radialUnit := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨unitToLarge n y, hy, c.largeMap_unitToLarge y⟩
      · rintro ⟨x, hx, rfl⟩
        let y : Disk n 1 := ⟨x.1, by
          rw [Metric.mem_closedBall]
          exact le_of_lt hx⟩
        refine ⟨y, hx, ?_⟩
        have hxy : unitToLarge n y = x := Subtype.ext rfl
        rw [← hxy]
        exact (c.largeMap_unitToLarge y).symm
    rw [hunit]
    change IsOpen (c.largeMap '' S₁)
    rw [himage]
    exact hW.inter hopen
  have hK : IsClosed (Set.range c.smallMap) :=
    (isCompact_range c.smallEmbedding.continuous).isClosed
  have hOK : O ⊆ Set.range c.smallMap := Set.image_subset_range _ _
  let b : Sphere n → M := fun s ↦ (c.boundaryMap s).1
  have hb : Continuous b := c.continuous_boundaryMap.subtype_val
  haveI : PathConnectedSpace (Sphere n) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        simpa using (show 1 < n by omega)) 0 (by norm_num))
  have hS : IsPathConnected (Set.range b) := isPathConnected_range hb
  have hSO : Set.range b ⊆ Oᶜ := by
    rintro _ ⟨s, rfl⟩
    exact (c.boundaryMap s).2
  have hKO : Set.range c.smallMap \ O ⊆ Set.range b := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    have hy1 : ¬ dist y.1 0 < 1 := fun h ↦ hy ⟨y, h, rfl⟩
    have hy2 : dist y.1 0 ≤ 1 := by
      exact Metric.mem_closedBall.mp y.2
    have hs : y.1 ∈ Sphere n := by
      simpa [Metric.mem_sphere] using le_antisymm hy2 (not_lt.mp hy1)
    exact ⟨⟨y.1, hs⟩, rfl⟩
  have hP : IsPathConnected Oᶜ := by
    obtain ⟨s0, hs0⟩ := hS.nonempty
    refine ⟨s0, hSO hs0, fun {x} hx ↦ ?_⟩
    obtain ⟨z, hz, hxz⟩ :=
      punctured_pathConnected_aux_first_entry hO hK hOK hx
        (Set.mem_range_self (f := c.smallMap) ⟨0, by simp⟩)
    exact (hxz.trans ((hS.joinedIn _ (hKO hz) _ hs0).mono hSO)).symm
  exact isPathConnected_iff_pathConnectedSpace.mp hP

/-- **LIBRARY (B4a).** A punctured closed manifold has no top homology. -/
noncomputable def punctured_topHomology_zero_aux_inclusion (n : ℕ) (M : Type)
    [TopologicalSpace M] (c : BallCollar n M) :
    H n c.Punctured ⟶ H n M :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- The complement of the radius-two collar is closed and lies in the interior
of the punctured manifold: the excision hypothesis for the pair
`(M, Punctured)`.  (Banked by lemma-3, job 579.) -/
lemma punctured_topHomology_zero_aux_mono_aux_excision_set
    {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    IsClosed c.radialTwoᶜ ∧ c.radialTwoᶜ ⊆
      interior (Set.range (fun x : c.Punctured ↦ x.1)) := by
  refine ⟨hopen.isClosed_compl, ?_⟩
  have hcompact : IsCompact (Set.range c.smallMap) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image c.smallEmbedding.continuous
  have hrangeOpen : IsOpen (Set.range c.smallMap)ᶜ := hcompact.isClosed.isOpen_compl
  have hrangeSub : (Set.range c.smallMap)ᶜ ⊆
      Set.range (fun x : c.Punctured ↦ x.1) := by
    intro z hz
    refine ⟨⟨z, ?_⟩, rfl⟩
    rintro ⟨y, hy, heq⟩
    exact hz ⟨y, heq⟩
  intro z hz
  apply interior_maximal hrangeSub hrangeOpen
  intro hzrange
  rcases hzrange with ⟨y, rfl⟩
  apply hz
  refine ⟨unitToLarge n y, ?_, c.largeMap_unitToLarge y⟩
  change dist y.1 0 < 2
  have hy : dist y.1 0 ≤ 1 := Metric.mem_closedBall.mp y.2
  linarith

/-- The closed annulus `1 ≤ ‖x‖` inside the open radius-two Euclidean ball. -/
def punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus
    (n : ℕ) : Set (Metric.ball (0 : E n) 2) :=
  {x | 1 ≤ dist x.1 0}

/-- LEAF. A homeomorphism of pairs carries vanishing relative homology. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_pair_iso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (hAB : e '' A = B) (k : ℕ)
    (hB : IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      B).homology k)) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      A).homology k) := by
  have hpair : ∀ x, x ∈ A ↔ e x ∈ B := by
    intro x
    constructor
    · intro hx
      rw [← hAB]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hAB] at hx
      obtain ⟨y, hy, hye⟩ := hx
      have hyx : y = x := e.injective hye
      exact hyx ▸ hy
  exact hB.of_iso
    (ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularHomologyIsoOfHomeomorphPair
      e A B hpair k)

/-- LEAF. `largeMap` carries the excised pair onto the Euclidean
(radius-two ball, annulus) pair. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_chart
    (n : ℕ) (M : Type) [TopologicalSpace M] (c : BallCollar n M) :
    ∃ e : ↥(c.radialTwoᶜᶜ) ≃ₜ Metric.ball (0 : E n) 2,
      e '' ConstructionTargets.SingularExcision.excisedSubspace
          (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ c.radialTwoᶜ =
        punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n := by
  let er : LargeInterior (n := n) ≃ₜ ↥c.radialTwo :=
    (c.largeInteriorMap_isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr c.range_largeInteriorMap)
  let e : ↥(c.radialTwoᶜᶜ) ≃ₜ Metric.ball (0 : E n) 2 :=
    (Homeomorph.setCongr (compl_compl c.radialTwo)).trans
      (er.symm.trans (largeInteriorHomeomorphBall (n := n)))
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 1 ≤ dist _ 0
    by_contra hlt
    have hlt' : dist ((e z : Metric.ball (0 : E n) 2) : E n) 0 < 1 :=
      lt_of_not_ge hlt
    apply hz
    let y : Disk n 1 := ⟨(e z).1, Metric.mem_closedBall.mpr hlt'.le⟩
    refine ⟨y, hlt', ?_⟩
    let z' : ↥c.radialTwo := (Homeomorph.setCongr (compl_compl c.radialTwo)) z
    let w : LargeInterior (n := n) := er.symm z'
    have hw : er w = z' := er.apply_symm_apply z'
    have hez : c.largeMap ⟨(e z).1, Metric.mem_closedBall.mpr (e z).2.le⟩ = z.1 := by
      change c.largeMap w.1 = z.1
      simpa [er, z'] using congrArg Subtype.val hw
    change c.smallMap y = z.1
    rw [← c.largeMap_unitToLarge y]
    convert hez using 1
  · intro hx
    change 1 ≤ dist x.1 0 at hx
    let z : ↥(c.radialTwoᶜᶜ) :=
      ⟨c.largeMap ⟨x.1, Metric.mem_closedBall.mpr x.2.le⟩, by
        simp only [compl_compl]
        exact ⟨⟨x.1, Metric.mem_closedBall.mpr x.2.le⟩, x.2, rfl⟩⟩
    refine ⟨z, ?_, ?_⟩
    · change z.1 ∈ (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
      rintro ⟨y, hy, heq⟩
      have heq' : unitToLarge n y = ⟨x.1, Metric.mem_closedBall.mpr x.2.le⟩ :=
        c.largeEmbedding.injective ((c.largeMap_unitToLarge y).trans heq)
      have hxy : y.1 = x.1 := congrArg Subtype.val heq'
      exact (not_lt_of_ge hx) (by simpa [hxy] using hy)
    · apply Subtype.ext
      let w : LargeInterior (n := n) :=
        ⟨⟨x.1, Metric.mem_closedBall.mpr x.2.le⟩, x.2⟩
      let z' : ↥c.radialTwo := (Homeomorph.setCongr (compl_compl c.radialTwo)) z
      have hz' : z' = er w := by
        apply Subtype.ext
        rfl
      change (er.symm z').1.1 = x.1
      rw [hz']
      simp [w]

/-- LEAF. Radial projection is a homotopy equivalence from the annulus to the
unit sphere. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_hequiv
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n)
      (Sphere n)) := by
  let A := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n
  let f : A → Sphere n := fun x ↦
    ⟨(‖(x.1.1 : E n)‖)⁻¹ • (x.1.1 : E n), by
      have hx : 1 ≤ ‖(x.1.1 : E n)‖ := by
        simpa [A,
          punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus,
          dist_zero_right] using x.2
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
      exact ne_of_gt (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hx)⟩
  let g : Sphere n → A := fun x ↦
    ⟨⟨(x : E n), by
        rw [Metric.mem_ball, dist_zero_right]
        simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩, by
      change 1 ≤ dist (x : E n) 0
      simpa [Metric.mem_sphere] using x.2.le⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp
      (continuous_subtype_val.comp continuous_subtype_val)).inv₀ (fun x ↦ by
        have hx : 1 ≤ ‖(x.1.1 : E n)‖ := by
          simpa [A,
            punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus,
            dist_zero_right] using x.2
        exact ne_of_gt (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hx))).smul
      (continuous_subtype_val.comp continuous_subtype_val)
  have hg : Continuous g := by
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨{
    toFun := ⟨f, hf⟩
    invFun := ⟨g, hg⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · let gf : C(A, A) := (⟨g, hg⟩ : C(Sphere n, A)).comp ⟨f, hf⟩
    have H : ContinuousMap.Homotopy (ContinuousMap.id A) gf := by
      refine {
        toFun := fun z ↦
          ⟨⟨((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖(z.2.1.1 : E n)‖)⁻¹) •
              (z.2.1.1 : E n), ?_⟩, ?_⟩
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
      · have hr : 1 ≤ ‖(z.2.1.1 : E n)‖ := by
          simpa [A,
            punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus,
            dist_zero_right] using z.2.2
        have hr2 : ‖(z.2.1.1 : E n)‖ < 2 := by
          simpa only [Metric.mem_ball, dist_zero_right] using z.2.1.2
        have ht0 : 0 ≤ (z.1 : ℝ) := z.1.2.1
        have ht1 : (z.1 : ℝ) ≤ 1 := z.1.2.2
        have hr0 : 0 < ‖(z.2.1.1 : E n)‖ := lt_of_lt_of_le (by norm_num) hr
        have hinv : 0 ≤ (‖(z.2.1.1 : E n)‖)⁻¹ := inv_nonneg.2 hr0.le
        have ha : 0 ≤ (1 - (z.1 : ℝ)) +
            (z.1 : ℝ) * (‖(z.2.1.1 : E n)‖)⁻¹ := by nlinarith
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ha]
        field_simp
        nlinarith
      · change 1 ≤ dist (((1 - (z.1 : ℝ)) +
            (z.1 : ℝ) * (‖(z.2.1.1 : E n)‖)⁻¹) • (z.2.1.1 : E n)) 0
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
        have hr : 1 ≤ ‖(z.2.1.1 : E n)‖ := by
          simpa [A,
            punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus,
            dist_zero_right] using z.2.2
        have ht0 : 0 ≤ (z.1 : ℝ) := z.1.2.1
        have ht1 : (z.1 : ℝ) ≤ 1 := z.1.2.2
        have hr0 : 0 < ‖(z.2.1.1 : E n)‖ := lt_of_lt_of_le (by norm_num) hr
        have hinv : 0 ≤ (‖(z.2.1.1 : E n)‖)⁻¹ := inv_nonneg.2 hr0.le
        have ha : 0 ≤ (1 - (z.1 : ℝ)) +
            (z.1 : ℝ) * (‖(z.2.1.1 : E n)‖)⁻¹ := by nlinarith
        rw [abs_of_nonneg ha]
        field_simp
        nlinarith
      · apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        have hr : Continuous (fun z : unitInterval × A ↦ ‖(z.2.1.1 : E n)‖) :=
          continuous_norm.comp
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
        have hi : Continuous (fun z : unitInterval × A ↦
            (‖(z.2.1.1 : E n)‖)⁻¹) :=
          hr.inv₀ (fun z ↦ by
            have hz : 1 ≤ ‖(z.2.1.1 : E n)‖ := by
              simpa [A,
                punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus,
                dist_zero_right] using z.2.2
            exact ne_of_gt (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hz))
        have hs : Continuous (fun z : unitInterval × A ↦
            (1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖(z.2.1.1 : E n)‖)⁻¹) := by
          fun_prop
        exact hs.smul
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
      · intro x
        apply Subtype.ext
        apply Subtype.ext
        simp
      · intro x
        apply Subtype.ext
        apply Subtype.ext
        simp [gf, f, g, inv_smul_smul₀]
    exact ⟨H.symm⟩
  · have hcomp : (⟨f, hf⟩ : C(A, Sphere n)).comp
        (⟨g, hg⟩ : C(Sphere n, A)) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      have hx : ‖(x : E n)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using x.2
      simp [f, g, hx]
    rw [hcomp]

lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus_homology
    (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of
      ↥(punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n))).homology n) := by
  obtain ⟨e⟩ := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_hequiv n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hS : IsZero (ConstructionTargets.SphereHomology.GroupHomology m (m + 1)) :=
    ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt m (m + 1) (by omega)
  exact hS.of_iso
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv e (m + 1))

lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_model
    (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n)).homology
        (n + 1)) := by
  let A := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n
  haveI : ContractibleSpace (Metric.ball (0 : E n) 2) :=
    (convex_ball (0 : E n) 2).contractibleSpace ⟨0, by simp⟩
  have hX : IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of (Metric.ball (0 : E n) 2))).homology (n + 1)) :=
    ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      _ (n + 1) (by omega)
  have hA := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus_homology
    n hn
  have hex := ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative A n
  exact hex.isZero_X₂ (hX.eq_of_src _ _) (hA.eq_of_tgt _ _)

/-- The excised pair: removing `Z = c.radialTwoᶜ` from
`(M, M minus the small open ball)` leaves (open radius-two ball, ball minus
the open unit ball), whose degree-`(n + 1)` relative homology vanishes.
Sketch: carry the pair by `largeMap` to the Euclidean radius-two ball and
annulus; the pair's long exact sequence
(`SingularHomologyConcrete.singularPairHomology_exact_*`) with the ball
contractible gives `H_{n+1} ≅ H̃_n` of a space homotopy equivalent to
`Sphere n` (an `(n-1)`-sphere), zero since `n ≥ 2`. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.SingularExcision.excisedSubspace
          (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
          c.radialTwoᶜ)).homology (n + 1)) := by
  obtain ⟨e, he⟩ := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_chart n M c
  exact punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_pair_iso e _ _ he
    (n + 1) (punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_model n (by omega))

/-- Excision step (proved, lemma-2 job 2128): the relative group of
`(M, M minus the small open ball)` is that of the excised pair. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_of_excised
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo)
    (hlocal : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.SingularExcision.excisedSubspace
          (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
          c.radialTwoᶜ)).homology (n + 1))) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology (n + 1)) := by
  letI : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
        c.radialTwoᶜ) (n + 1)) := by
    rcases punctured_topHomology_zero_aux_mono_aux_excision_set c hopen with
      ⟨hclosed, hsub⟩
    have hrange : Set.range (fun x : c.Punctured ↦ x.1) =
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange] at hsub
    exact ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
      _ _ hclosed hsub n
  exact hlocal.of_iso (asIso (HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeExcisionMap
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
      c.radialTwoᶜ) (n + 1))).symm

/-- LEAF. The relative group of `(M, Punctured)` one above top degree
vanishes.  Sketch: excise `Z = c.radialTwoᶜ`
(`SingularExcision.relativeExcisionMap_homologyMap_isIso_succ`, hypotheses
from `_aux_excision_set`), reducing to the pair (open radius-two ball, ball
minus the open unit ball), carried by `largeMap` (an embedding); that pair's
long exact sequence (`SingularHomologyConcrete.singularPairHomology_exact_*`)
with the ball contractible gives `H_{n+1} ≅ H̃_n` of a space homotopy
equivalent to `Sphere n` (an `(n-1)`-sphere), which is zero since `n ≥ 2`. -/
lemma punctured_topHomology_zero_aux_mono_aux_relative_zero (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology (n + 1)) := by
  exact punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_of_excised n M c hopen
    (punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local n hn M c hopen)

/-- LEAF. If the relative group of `(M, Punctured)` in degree `n + 1`
vanishes, the degree-`n` inclusion map is injective.  Sketch: exactness of
the pair sequence at `H_n(Punctured)`
(`SingularHomologyConcrete.singularPairHomology_exact_subspace`), then
transport from the concrete `AddCommGrpCat` homology to `H` (module-valued
`singularHomologyFunctor`) with the `IntegralSingularHomologyComparison` /
`T00A01MayerVietorisAdapters` isos.  `↥(c.smallMap '' _)ᶜ` is `c.Punctured`
by definition. -/
lemma punctured_topHomology_zero_aux_mono_aux_of_relative_zero (n : ℕ)
    (M : Type) [TopologicalSpace M] (c : BallCollar n M)
    (hrel : IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology (n + 1))) :
    Mono (punctured_topHomology_zero_aux_inclusion n M c) := by
  let A : Set M := (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
  let i : TopCat.of A ⟶ TopCat.of M :=
    ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A
  letI hg : Mono (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) n) :=
    (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_subspace
      A n).mono_g (hrel.eq_of_src _ _)
  let F := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
  let eA := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of A) n
  let eM := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of M) n
  letI : IsIso eA.hom := eA.isIso_hom
  letI : IsIso eM.hom := eM.isIso_hom
  letI : Mono eA.hom := inferInstance
  letI : Mono eM.hom := inferInstance
  letI hcomp : Mono (eA.hom ≫ HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) n) :=
    ⟨fun u v huv ↦ by
      apply (cancel_mono eA.hom).1
      apply hg.right_cancellation
      simpa only [Category.assoc] using huv⟩
  have hnat : F.map (punctured_topHomology_zero_aux_inclusion n M c) ≫ eM.hom =
      eA.hom ≫ HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) n := by
    exact ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
      i n
  haveI : Mono (F.map (punctured_topHomology_zero_aux_inclusion n M c) ≫ eM.hom) :=
    hnat ▸ hcomp
  haveI : Mono (F.map (punctured_topHomology_zero_aux_inclusion n M c)) :=
    mono_of_mono_fac (f := eM.hom)
      (h := F.map (punctured_topHomology_zero_aux_inclusion n M c) ≫ eM.hom) rfl
  exact F.mono_of_mono_map
    (show Mono (F.map (punctured_topHomology_zero_aux_inclusion n M c)) from
      inferInstance)

/-- The top-homology map of the puncture inclusion is injective.  This is the
relative-homology/excision input: the relative group immediately above top
degree vanishes. -/
theorem punctured_topHomology_zero_aux_mono (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    Mono (punctured_topHomology_zero_aux_inclusion n M c) := by
  exact punctured_topHomology_zero_aux_mono_aux_of_relative_zero n M c
    (punctured_topHomology_zero_aux_mono_aux_relative_zero n hn M c hopen)

/-- The puncture inclusion misses the collar center.  (Banked by lemma-1,
job 588.) -/
theorem punctured_topHomology_zero_aux_map_eq_zero_aux_avoids_center
    (n : ℕ) (M : Type) [TopologicalSpace M] (c : BallCollar n M) :
    Set.MapsTo (fun z : c.Punctured ↦ z.1) Set.univ
      (LocalHomologyNeighborhoodExcision.deletedPoint
        (c.smallMap (0 : Disk n 1))) := by
  intro z _ hz
  apply z.2
  refine ⟨0, ?_, hz.symm⟩
  change dist (0 : E n) 0 < 1
  simp

/-- LEAF (split by claude-14 from `_localization_mono` after lemma-1's PARTIAL,
job 2134, 2026-10-22): the localized global generator has infinite order in
`H_n(M, M - x)`.  This is the nonvanishing of the fundamental class at a point
(Hatcher 3.26); `_localization_mono` follows from it because `H_n M` is
generated by `groupGlobalGenerator`.  Route: by
`localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator` the
localized generator is `r • ambientLocalGenerator x`, and
`ambientLocalGenerator_zsmul_injective` reduces the claim to `r ≠ 0`; a
generator localizing to zero at one point localizes to zero everywhere (local
constancy along the connected `M`), and then compactness forces it to vanish
in `H_n M`, contradicting `H_n M ≅ ℤ`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_of_coefficient
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (x : M) (q : ℤ)
    (hq : q • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
      ManifoldFundamentalClass.localizationMap x (k + 2)
        (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e))
    (hq0 : q ≠ 0) :
    Function.Injective (fun r : ℤ ↦ r •
      ManifoldFundamentalClass.localizationMap x (k + 2)
        (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e)) := by
  intro r s hrs
  rw [← hq] at hrs
  change r • (q • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) =
    s • (q • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) at hrs
  rw [smul_smul, smul_smul] at hrs
  have hrsq : r * q = s * q :=
    ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective k x hrs
  exact (mul_right_cancel₀ hq0 hrsq)

/-- The local degree of the global generator at `y`: its image in
`H_(k+2)(M, M - y)`, read as an integer through `ambientLocalNormalization`.
(Split by claude-14 from `_coefficient_ne_zero` after lemma-2's PARTIAL, job
2299, 2026-10-22, following t00A01's dimension-3
`..._fundamental_aux_coefficient_is_sign_aux_degree`.) -/
noncomputable def punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (y : M) : ℤ :=
  (ManifoldFundamentalClass.ambientLocalNormalization k y).hom.hom
    (ManifoldFundamentalClass.localizationMap y (k + 2)
      (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e))

/-- The coefficient `q` of `hq` is the local degree at `x`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (x : M) (q : ℤ)
    (hq : q • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
      ManifoldFundamentalClass.localizationMap x (k + 2)
        (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e)) :
    q = punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e x := by
  have h := congrArg
    (ManifoldFundamentalClass.ambientLocalNormalization k x).hom.hom hq
  rw [map_zsmul, ManifoldFundamentalClass.ambientLocalNormalization_generator] at h
  change q * (1 : ℤ) = _ at h
  rw [mul_one] at h
  exact h

/-- LEAF (claude-14, 2026-10-22): the absolute local degree is locally
constant.  Template: t00A01's sorry-free dimension-3
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant`
in `problems/t00A01/lean/Main.lean` (via its `_aux_eventually_sign`: on a
chart ball around `x`, `H(M, M - ball) → H(M, M - y)` is an isomorphism for
every `y` in the ball, and two normalizations of one group as `ℤ` differ by
`±1`).  Generalize from `Fin 3` / `k := 1` to `k + 2`.  Do not reduce this to
`_localization_mono` or `_coefficient_ne_zero`: both are assembled from it. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_natAbs_eq
    (a b : ℤ) (h : a = b ∨ a = -b) : a.natAbs = b.natAbs := by
  rcases h with h | h
  · exact congrArg Int.natAbs h
  · rw [h, Int.natAbs_neg]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_units
    {G : AddCommGrpCat} (f g : G ≅ AddCommGrpCat.of ℤ) (a : G) :
    f.hom.hom a = g.hom.hom a ∨ f.hom.hom a = -g.hom.hom a := by
  let u : AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ := g.symm ≪≫ f
  have hmul : ∀ (h : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (n : ℤ),
      h.hom n = n * h.hom 1 := fun h n => by
    have h' := h.hom.map_zsmul 1 n
    simpa [smul_eq_mul] using h'
  have h1 : u.inv.hom (u.hom.hom 1) = 1 :=
    ConcreteCategory.congr_hom u.hom_inv_id 1
  rw [hmul u.inv] at h1
  have hu : IsUnit (u.hom.hom 1) :=
    ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hf : f.hom.hom a = u.hom.hom (g.hom.hom a) := by
    have ha : g.inv.hom (g.hom.hom a) = a :=
      ConcreteCategory.congr_hom g.hom_inv_id a
    change f.hom.hom a = f.hom.hom (g.inv.hom (g.hom.hom a))
    rw [ha]
  rw [hf, hmul u.hom]
  rcases Int.isUnit_iff.1 hu with h | h
  · left
    rw [h, mul_one]
  · right
    rw [h, mul_neg_one]

/-- PROVED: the identity of `M` sends `M ∖ K` into `M ∖ z` when `z ∈ K`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
    {M : Type} [TopologicalSpace M] (K : Set M) (z : M) (hz : z ∈ K) :
    Set.MapsTo (ContinuousMap.id M) Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) :=
  fun y hy hyz => hy (by
    have hyz' : y = z := hyz
    exact hyz' ▸ hz)

/-- PROVED: for `z ∈ K`, localization at `z` factors through `H_n(M, M ∖ K)`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor
    {M : Type} [TopologicalSpace M] (K : Set M) (z : M) (hz : z ∈ K) (n : ℕ) :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap z n =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ) n ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
              K z hz)) n := by
  have h := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality Kᶜ
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) (ContinuousMap.id M)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
      K z hz)
  have hid : (TopCat.ofHom (ContinuousMap.id M) : TopCat.of M ⟶ TopCat.of M) = 𝟙 _ := rfl
  have hab : ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap
      (ContinuousMap.id M) = 𝟙 _ := by
    simp [ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap, hid]
  have h' : ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap (ContinuousMap.id M) ≫
      ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) =
    ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ ≫
      ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          K z hz) := h
  rw [hab, Category.id_comp] at h'
  show HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)) n = _
  rw [h', HomologicalComplex.homologyMap_comp]


/-- PROVED (lemma-3, job invoke-1792647491039-2327-805dce26): Hatcher 3.27's
assembly.  Given joint injectivity of the localizations (`hinj`, leaf
`_aux_injective`), global divisibility (`hdivide`, leaf `_aux_divide`) and the
locally constant absolute degree (`_locallyConstant`), some point has local
degree `±1`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_assembly
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ)
    (hinj : ∀ z : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2),
      (∀ y : M, ManifoldFundamentalClass.localizationMap y (k + 2) z = 0) → z = 0)
    (hdivide : ∀ (z : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2))
      (m : ℤ), m ≠ 0 →
      (∀ y : M,
        ((ManifoldFundamentalClass.ambientLocalNormalization k y).hom.hom
          (ManifoldFundamentalClass.localizationMap y (k + 2) z)).natAbs = m.natAbs) →
      ∃ μ : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2),
        ∀ y : M, m • ManifoldFundamentalClass.localizationMap y (k + 2) μ =
          ManifoldFundamentalClass.localizationMap y (k + 2) z)
    (hloc : IsLocallyConstant (fun y : M ↦
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
        k M e y).natAbs)) :
    ∃ y : M, (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
      k M e y).natAbs = 1 := by
  set g := ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e with hgdef
  let φ : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2) →+ ℤ :=
    e.hom.hom.toAddMonoidHom.comp
      (IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).inv.hom
  have hφg : φ g = 1 := by
    change e.hom.hom
      ((IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).inv.hom
        ((IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).hom.hom
          (e.inv.hom 1))) = 1
    have hc := ConcreteCategory.congr_hom
      (IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).hom_inv_id
      (e.inv.hom 1)
    change
      (IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).inv.hom
        ((IntegralSingularHomologyComparison.singularHomologyComparison (TopCat.of M) (k + 2)).hom.hom
          (e.inv.hom 1)) = e.inv.hom 1 at hc
    rw [hc]
    exact ConcreteCategory.congr_hom e.inv_hom_id (1 : ℤ)
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, map_zero] at hφg
    exact zero_ne_one hφg
  obtain ⟨x, hx⟩ : ∃ x : M,
      ManifoldFundamentalClass.localizationMap x (k + 2) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg0 (hinj g h)
  set d := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
    k M e x with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hx
    apply (ConcreteCategory.bijective_of_isIso
      (ManifoldFundamentalClass.ambientLocalNormalization k x).hom).1
    rw [map_zero]
    exact h0
  have hall : ∀ y : M,
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
        k M e y).natAbs = d.natAbs := fun y =>
    hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ y) (Set.mem_univ x)
  obtain ⟨μ, hμ⟩ := hdivide g d hd0 hall
  have hgμ : d • μ - g = 0 := by
    apply hinj
    intro y
    rw [map_sub, map_zsmul, hμ y, sub_self]
  have h1 : d * φ μ = 1 := by
    rw [← hφg, ← smul_eq_mul, ← map_zsmul, sub_eq_zero.mp hgμ]
  exact ⟨x, by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> simp [← hd, h]⟩

/-- `A` is good for `M` (Hatcher Lemma 3.27, integer coefficients):
`H_i(M, M ∖ A)` vanishes above degree `k + 2`, and a class of `H_(k+2)(M, M ∖ A)` whose
image in `H_(k+2)(M, M ∖ y)` vanishes for every `y ∈ A` is zero.  Ported from t00A01's dimension-3
`_aux_good` (claude-14, 2026-10-22). -/
def punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good (k : ℕ) (M : Type) [TopologicalSpace M] (A : Set M) : Prop :=
  (∀ i : ℕ, k + 2 < i → Subsingleton
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i)) ∧
    ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology (k + 2),
      (∀ (y : M) (hy : y ∈ A),
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2) c = 0) →
      c = 0

/-- PROVED (lemma-1, banked from its `_aux_convex` PARTIAL, 2026-10-20): the
empty set is good (last line fixed by claude-14). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_empty
    (k : ℕ) (M : Type) [TopologicalSpace M] :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M ∅ := by
  constructor
  · intro i hi
    have hz :=
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero M i
    simpa using (AddCommGrpCat.isZero_iff_subsingleton.mp hz)
  · intro c hc
    have hz :=
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero M (k + 2)
    have hz' : IsZero
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (∅ : Set M)ᶜ).homology (k + 2)) := by
      simpa using hz
    exact @Subsingleton.elim _ (AddCommGrpCat.isZero_iff_subsingleton.mp hz') c 0

/-- PROVED (ported verbatim from t00A01 by claude-14, 2026-10-22): `H_n(M) → H_n(M, ∅)` is an isomorphism (the subcomplex of
chains in the empty set is zero).  `T02A06SphereShift`'s
`singularPairProjection_isIso_of_subspace_isZero` is one route. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_chains
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↑((Set.univ : Set M)ᶜ))).X n) := by
  letI : IsEmpty ↑((Set.univ : Set M)ᶜ) :=
    ⟨fun x ↦ by simpa using x.2⟩
  letI : IsEmpty (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n) :=
    ⟨fun σ ↦ by
      let p : SimplexCategory.toTop.obj (SimplexCategory.mk n) :=
        Classical.choice inferInstance
      exact isEmptyElim (σ.down.hom p)⟩
  letI := Classical.decEq
    (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n)
  have h : IsZero (AddCommGrpCat.of
      (DirectSum (ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of ↑((Set.univ : Set M)ᶜ)) n)
        (fun _ ↦ ℤ))) := by
    apply AddCommGrpCat.isZero_of_subsingleton
  exact h.of_iso (ConstructionTargets.SingularSubdivision.addCommGrpCoproductIsoDirectSum
    (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n))

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_homology
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↑((Set.univ : Set M)ᶜ))).homology n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ShortComplex.exact_of_isZero_X₂ _
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_chains M n)

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) n) := by
  cases n with
  | zero =>
      letI : Mono (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
            (Set.univ : Set M)ᶜ) 0) :=
        (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_absolute
          ((Set.univ : Set M)ᶜ) 0).mono_g
          ((punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_homology M 0).eq_of_src _ _)
      letI : Epi (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
            (Set.univ : Set M)ᶜ) 0) := by
        letI : Epi
            ((ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
              ((Set.univ : Set M)ᶜ)).f 0) := by
          dsimp [ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection]
          exact Functor.map_epi
            (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 0)
            (cokernel.π
              (ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι
                ((Set.univ : Set M)ᶜ)))
        apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
        intro j hj
        simp at hj
      exact isIso_of_mono_of_epi _
  | succ q =>
      exact ConstructionTargets.T02A06SphereShift.singularPairProjection_isIso_of_subspace_isZero
        ((Set.univ : Set M)ᶜ) q
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_homology M (q + 1))
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ_aux_homology M q)

/-- PROVED (lemma-1, banked from its `_aux_union` PARTIAL, 2026-10-22; t00A01 port):
complement identities for the Mayer--Vietoris step. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ ⊆ Aᶜ := by
  intro x hx hxa
  exact hx (Or.inl hxa)

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ ⊆ Bᶜ := by
  intro x hx hxb
  exact hx (Or.inr hxb)

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_inter
    {M : Type} (A B : Set M) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, not_or]

/-- LIBRARY LEAF (Hatcher 3.27, relative Mayer--Vietoris, joint injectivity):
for closed `A`, `B`, if `H_{n+1}(M, M ∖ (A ∩ B))` vanishes then a class of
`H_n(M, M ∖ (A ∪ B))` whose images in `H_n(M, M ∖ A)` and `H_n(M, M ∖ B)` both
vanish is zero.  Split from `_aux_union` after lemma-2's PARTIAL (2026-10-20).
Route (lemma-2's diagnosis): `CoefficientSubcomplexRelativeHomologySequence`
for the subcomplexes `P = range (M ∖ A)`, `Q = range (M ∖ B)` of the singular
simplicial set of `M` is exact at the intersection term
`H_{n+1}(S, P ∪ Q) → H_n(S, P ∩ Q) → H_n(S, P) ⊕ H_n(S, Q)`.  Transport it
to the literal relative chains: `P ∩ Q` is `range ((A ∪ B)ᶜ)`
(`CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap`),
`P`, `Q` are `range Aᶜ`, `range Bᶜ` (`rangeRelativeCokernelMap`); `P ∪ Q` is
the `{Aᶜ, Bᶜ}`-small chains of `(A ∩ B)ᶜ`, whose relative homology agrees with
`H_{n+1}(M, M ∖ (A ∩ B))` because `Aᶜ`, `Bᶜ` are open (small chains, as in
`CoefficientCompactComplementUnionComparison`, plus the five lemma).  Check that
the transported piece maps are `relativeSingularMap` of the identity, and pass
from `ModuleCat ℤ` to the `AddCommGrpCat` complexes here.
Ingredients already in this file (lemma-1's BLOCKED-ON, job 192, named a module
`IntegralRelativeSingularHomologyComparison` that does not exist; 2026-10-20):
exactness is `_aux_divide_aux_union_aux_glue_aux_exact_degree` (with `S = Aᶜ`,
`T = Bᶜ`); the `ModuleCat ℤ` → `AddCommGrpCat` relative comparison is
`ManifoldFundamentalClass.integralRelativeHomologyComparison`; the piece maps are
identified with `relativeSingularMap` by `_aux_divide_aux_union_aux_glue_aux_sq_inter`;
`h` reaches the union term through `CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso`
(`Aᶜ`, `Bᶜ` open).  `Aᶜ ∩ Bᶜ` vs `(A ∪ B)ᶜ`: generalise to sets equal to them and `subst`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_comparison
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n).hom =
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport A n).hom := by
  have ht :
      (ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport A).hom =
        𝟙 _ := by
    apply (cancel_epi (cokernel.π
      ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)))).1
    rw [ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport_projection]
    rfl
  have hc :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison A).hom =
        (ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport A).hom := by
    unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison
    unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport
    dsimp
    rw [ht]
    exact Category.assoc _ _ _
  unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison
  unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
  dsimp
  rw [hc]
/-- LIBRARY LEAF (split by claude-14 from `_union_aux_joint` after lemma-1's PARTIAL,
job 202, 2026-10-21): the vanishing hypothesis moved to the subcomplex model.  For
closed `A`, `B` in `M`, if `H_{n+1}(M, (A ∩ B)ᶜ)` is trivial, so is degree `n + 1`
homology of `C(M) / C(P ⊔ Q)`, where `P`, `Q` are the singular simplices landing in
`Aᶜ`, `Bᶜ`.  Route: `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ` (`Set.compl_inter`);
`integralRelativeHomologyComparison` identifies the production group with
`forgetIntModules` of `H(relativeChains ℤ (Aᶜ ∪ Bᶜ))`;
`CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ Aᶜ Bᶜ`
(both open) identifies that with `H(cokernel (unionGeneratedAmbientInclusion ℤ Aᶜ Bᶜ))`,
whose cokernel is the one of `unionAmbient ℤ P Q` (same `chains`, same `(P ⊔ Q).ι`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_union_vanish
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (n : ℕ) (h : Subsingleton ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∩ B)ᶜ).homology (n + 1))) :
    Subsingleton ((cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.unionAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ))).homology (n + 1)) := by
  have hopenA : IsOpen Aᶜ := hA.isOpen_compl
  have hopenB : IsOpen Bᶜ := hB.isOpen_compl
  have hrel : Subsingleton
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (Aᶜ ∪ Bᶜ)).homology (n + 1)) := by
    simpa only [Set.compl_inter] using h
  constructor
  intro x y
  let e := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso
        ℤ Aᶜ Bᶜ hopenA hopenB (n + 1)) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison
      (Aᶜ ∪ Bᶜ) (n + 1)
  have hm : e.hom x = e.hom y :=
    @Subsingleton.elim _ hrel _ _
  have hxy := congrArg (fun z => e.inv z) hm
  simpa only [Iso.hom_inv_id_apply] using hxy

/-- LIBRARY LEAF (split by claude-14 from `_union_aux_joint` after lemma-1's PARTIAL,
job 202, 2026-10-21): the conclusion moved to the subcomplex model.  If, in degree `n`,
a class of `C(M) / C(P ⊓ Q)` that dies in both `C(M) / C(P)` and `C(M) / C(Q)` is zero,
then a class of `H_n(M, (A ∪ B)ᶜ)` that dies in both `H_n(M, Aᶜ)` and `H_n(M, Bᶜ)` is
zero.  Route: `Φ` = `intersectionRelativeIso ℤ Aᶜ Bᶜ n` (after `Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ`)
followed by `integralRelativeHomologyComparison (A ∪ B)ᶜ n` (equal to the
`WithTransport` form by `_aux_comparison`) is a bijection onto the production group;
take `c' = Φ⁻¹ c`.  The left square `Φ_A ∘ H(intersectionToLeftRelative) =
H(relativeSingularMap (A ∪ B)ᶜ Aᶜ id _) ∘ Φ` (with `Φ_A` from `rangeRelativeIso ℤ Aᶜ`)
and its right analogue turn `hcA`, `hcB` into the two hypotheses of `hinj`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport_aux_sq
    (M : Type) [TopologicalSpace M] (S T : Set M) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap (ConstructionTargets.SingularExcision.relativeSingularMap
        (S ∩ T) S (ContinuousMap.id M) (fun _ hx => hx.1)) n ∧
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap (ConstructionTargets.SingularExcision.relativeSingularMap
        (S ∩ T) T (ContinuousMap.id M) (fun _ hx => hx.2)) n := by
  have hl :
      ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S =
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T ≫
        ConstructionTargets.CoefficientRadialPair.pairMap ℤ (S ∩ T) S (ContinuousMap.id M) (fun _ hx => hx.1) := by
    apply (cancel_epi (cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
      (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)))).1
    rw [← Category.assoc, ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToLeftRelative_projection]
    have hs : cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S =
        cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ S) := cokernel.π_desc _ _ _
    rw [hs]
    have hi : cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T =
        cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∩ T)) :=
      (cokernel.π_desc _ _ _).trans (Category.id_comp _)
    rw [← Category.assoc, hi]
    have h := ConstructionTargets.CoefficientRadialPair.projection ℤ (S ∩ T) S (ContinuousMap.id M) (fun _ hx => hx.1)
    rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at h
    exact h.symm
  have hr :
      ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T =
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T ≫
        ConstructionTargets.CoefficientRadialPair.pairMap ℤ (S ∩ T) T (ContinuousMap.id M) (fun _ hx => hx.2) := by
    apply (cancel_epi (cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
      (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)))).1
    rw [← Category.assoc, ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToRightRelative_projection]
    have hs : cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T =
        cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ T) := cokernel.π_desc _ _ _
    rw [hs]
    have hi : cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange S) (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T =
        cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∩ T)) :=
      (cokernel.π_desc _ _ _).trans (Category.id_comp _)
    rw [← Category.assoc, hi]
    have h := ConstructionTargets.CoefficientRadialPair.projection ℤ (S ∩ T) T (ContinuousMap.id M) (fun _ hx => hx.2)
    rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at h
    exact h.symm
  have hl' := congrArg (fun f => ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
    (HomologicalComplex.homologyMap f n)) hl
  have hr' := congrArg (fun f => ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
    (HomologicalComplex.homologyMap f n)) hr
  simp only [HomologicalComplex.homologyMap_comp, Functor.map_comp] at hl' hr'
  have hS : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S) n := rfl
  have hT : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T) n := rfl
  have hI : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T) n := rfl
  constructor
  · rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_comparison S n,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_comparison (S ∩ T) n]
    rw [hS, hI, ← Category.assoc, hl', Category.assoc]
    rw [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality]
    rw [← Category.assoc]
  · rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_comparison T n,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_comparison (S ∩ T) n]
    rw [hT, hI, ← Category.assoc]
    refine (congrArg (fun q => q ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport T n).hom) hr').trans ?_
    rw [Category.assoc]
    rw [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality]
    rw [← Category.assoc]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport_aux_inter
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ)
    (hinj : ∀ c' : (cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ))).homology n,
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n c' = 0 →
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n c' = 0 →
      c' = 0)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (Aᶜ ∩ Bᶜ)).homology n)
    (hcA : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Aᶜ (ContinuousMap.id M)
        (fun _ hx => hx.1)) n c = 0)
    (hcB : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Bᶜ (ContinuousMap.id M)
        (fun _ hx => hx.2)) n c = 0) :
    c = 0 := by
  let Φ := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ Aᶜ Bᶜ n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (Aᶜ ∩ Bᶜ) n
  let ΦA := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ Aᶜ n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison Aᶜ n
  let ΦB := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ Bᶜ n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison Bᶜ n
  have v := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport_aux_sq M Aᶜ Bᶜ n
  let c0 : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (Aᶜ ∩ Bᶜ)).homology n := c
  let d := Φ.inv c0
  have hdA : HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n d = 0 := by
    have hz : ΦA.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n d) = 0 := by
      have q := ConcreteCategory.congr_hom v.1 d
      dsimp [d] at q
      change _ = ConcreteCategory.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Aᶜ
          (ContinuousMap.id M) (fun _ hx => hx.1)) n) (Φ.hom (Φ.inv c0)) at q
      have hi : Φ.hom (Φ.inv c0) = c0 := by simpa using Iso.hom_inv_id_apply Φ c0
      have q' := q.trans (congrArg (fun z => ConcreteCategory.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Aᶜ
          (ContinuousMap.id M) (fun _ hx => hx.1)) n) z) hi)
      exact q'.trans (by dsimp [c0]; exact hcA)
    have hz' := congrArg ΦA.inv hz
    simpa using hz'
  have hdB : HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n d = 0 := by
    have hz : ΦB.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ
          (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n d) = 0 := by
      have q := ConcreteCategory.congr_hom v.2 d
      dsimp [d] at q
      change _ = ConcreteCategory.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Bᶜ
          (ContinuousMap.id M) (fun _ hx => hx.2)) n) (Φ.hom (Φ.inv c0)) at q
      have hi : Φ.hom (Φ.inv c0) = c0 := by simpa using Iso.hom_inv_id_apply Φ c0
      have q' := q.trans (congrArg (fun z => ConcreteCategory.hom (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (Aᶜ ∩ Bᶜ) Bᶜ
          (ContinuousMap.id M) (fun _ hx => hx.2)) n) z) hi)
      exact q'.trans (by dsimp [c0]; exact hcB)
    have hz' := congrArg ΦB.inv hz
    simpa using hz'
  have hd := hinj d hdA hdB
  have hc0 := congrArg Φ.hom hd
  have hc0' : c0 = 0 := by simpa [d] using hc0
  dsimp [c0] at hc0'
  exact hc0'

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ)
    (hinj : ∀ c' : (cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ))).homology n,
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n c' = 0 →
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n c' = 0 →
      c' = 0)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology n)
    (hcA : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) n c = 0)
    (hcB : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) n c = 0) :
    c = 0 := by
  have key : ∀ (Z : Set M) (hZ : Z = Aᶜ ∩ Bᶜ) (hA : Z ⊆ Aᶜ) (hB : Z ⊆ Bᶜ)
      (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Z).homology n),
      HomologicalComplex.homologyMap (ConstructionTargets.SingularExcision.relativeSingularMap Z Aᶜ
        (ContinuousMap.id M) (fun _ hx => hA hx)) n c = 0 →
      HomologicalComplex.homologyMap (ConstructionTargets.SingularExcision.relativeSingularMap Z Bᶜ
        (ContinuousMap.id M) (fun _ hx => hB hx)) n c = 0 → c = 0 := by
    intro Z hZ hA hB c hcA hcB
    subst hZ
    exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport_aux_inter M A B n hinj c hcA hcB
  exact key _ (Set.compl_union A B) _ _ c hcA hcB

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (n : ℕ) (h : Subsingleton ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∩ B)ᶜ).homology (n + 1)))
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology n)
    (hcA : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) n c = 0)
    (hcB : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) n c = 0) :
    c = 0 := by
  refine punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_transport M A B n ?_ c hcA hcB
  intro c' hl hr
  haveI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint_aux_union_vanish M A B hA hB n h
  have hex := (ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence.exact_union_connecting_intersection_pieces
    ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ) n)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have key : ∀ y : (cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)) ⊞ cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ))).homology n,
      HomologicalComplex.homologyMap (biprod.fst : cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)) ⊞ cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) ⟶ _) n y = 0 →
      HomologicalComplex.homologyMap (biprod.snd : cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)) ⊞ cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) ⟶ _) n y = 0 → y = 0 := by
    intro y h1 h2
    have ht := congrArg (fun φ : cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)) ⊞ cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) ⟶
        cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)) ⊞ cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) =>
        HomologicalComplex.homologyMap φ n y)
      (biprod.total (X := cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ))) (Y := cokernel (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ))))
    simp only at ht
    rw [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_add,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at ht
    simpa [h1, h2] using ht.symm
  have hp : HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ) (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n c' = 0 := by
    apply key
    · rw [← CategoryTheory.comp_apply, ← HomologicalComplex.homologyMap_comp]
      simpa [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative] using hl
    · rw [← CategoryTheory.comp_apply, ← HomologicalComplex.homologyMap_comp]
      simpa [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative] using hr
  obtain ⟨d, hd⟩ := hex c' hp
  rw [← hd, Subsingleton.elim d 0, map_zero]

/-- PROVED (claude-14, 2026-10-22, ported from t00A01 after lemma-1's PARTIAL
on `_union`, which banked the `_aux_compl_*` identities; split by claude-14, after lemma-3's PARTIAL on
`_exists_unit_aux_injective`; Hatcher 3.27, Mayer--Vietoris step): if closed
`A`, `B` and `A ∩ B` are good, so is `A ∪ B`.  Template: t00A01's sorry-free
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union`
with its `_aux_joint` and `_aux_compl_*` pieces.  No manifold structure is
used; the only dimension in the template is the degree, so replace `3` by
`k + 2` and `4` by `k + 3`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union
    (k : ℕ) (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (gA : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M A)
    (gB : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M B)
    (gAB : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M (A ∩ B)) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M (A ∪ B) := by
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · have key : ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology i, c = 0 := fun c =>
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint M A B hA hB i (gAB.1 (i + 1) (by omega)) c
        (@Subsingleton.elim _ (gA.1 i hi) _ _) (@Subsingleton.elim _ (gB.1 i hi) _ _)
    exact ⟨fun c d => (key c).trans (key d).symm⟩
  · refine punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint M A B hA hB (k + 2) (gAB.1 (k + 3) (by omega)) c ?_ ?_
    · refine gA.2 _ fun y hy => ?_
      have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
        (A ∪ B)ᶜ Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M) (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy)) (k + 2)
      have := congrArg (fun f => f c) e
      simp only [ConcreteCategory.comp_apply] at this
      rw [this]; exact hc y (Or.inl hy)
    · refine gB.2 _ fun y hy => ?_
      have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
        (A ∪ B)ᶜ Bᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M) (ContinuousMap.id M)
        (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy)) (k + 2)
      have := congrArg (fun f => f c) e
      simp only [ConcreteCategory.comp_apply] at this
      rw [this]; exact hc y (Or.inr hy)

/-- PROVED (lemma-1, banked from its `_aux_convex` PARTIAL, job 2363, 2026-10-22):
in a `(k+2)`-manifold, `H_i(M, M ∖ y) = 0` for `i > k + 2`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_point
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (y : M) (i : ℕ) (hi : k + 2 < i) :
    Subsingleton ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology i) := by
  open ConstructionTargets.SingularHomologyConcrete
    ConstructionTargets.SingularExcision
    ConstructionTargets.LocalHomologyNeighborhoodExcision
    ConstructionTargets.T02A06HemisphereExcision
    ConstructionTargets.T02A06DiskRadialComparison
    ConstructionTargets.SphereHomology
    ConstructionTargets.ChartPairRelativeHomologyTransport
    ConstructionTargets.HigherChartLocalGenerator in
  have hmodel : Limits.IsZero ((RelativeSingularChains (P k)).homology i) := by
    have hamb : Limits.IsZero
        ((SingularChains (TopCat.of (D k))).homology i) := by
      letI : ContractibleSpace (D k) := Metric.contractibleSpace_ball (by norm_num)
      exact contractibleHigherHomology_isZero _ i (by omega)
    have hpunct : Limits.IsZero
        ((SingularChains (TopCat.of (P k))).homology (i - 1)) := by
      exact (sphereHomology_isZero_of_gt (k + 1) (i - 1) (by omega)).of_iso
        (singularHomologyIsoOfHomotopyEquiv
          (sphereHomotopyEquivPuncturedOpenDisk (k + 2)) (i - 1)).symm
    have hi' : i - 1 + 1 = i := by omega
    rw [← hi'] at hamb
    have hz := (singularPairHomology_exact_relative (P k) (i - 1)).isZero_X₂
      (hamb.eq_of_src _ _) (hpunct.eq_of_tgt _ _)
    simpa [hi'] using hz
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (P k) (deletedPoint y)
      (ambientChartMap (k := k) y) (ambientChartMap_mapsTo (k := k) y)) i
  have hf : IsIso f := by
    letI := relativeSingularMap_homeomorphPair_isIso (modelChart (k := k) y) (P k)
      (neighborhoodDeletedPoint (chartNeighborhood (k := k) y) y)
      (modelChart_deletedPoint_iff (k := k) y) i
    have hn : IsIso (HomologicalComplex.homologyMap
        (relativeSingularMap
          (neighborhoodDeletedPoint (chartNeighborhood (k := k) y) y)
          (deletedPoint y) (neighborhoodInclusion (chartNeighborhood (k := k) y))
          (neighborhoodInclusion_mapsTo (chartNeighborhood (k := k) y) y)) i) := by
      have hn' := ConstructionTargets.ManifoldFundamentalClass.neighborhoodInclusion_Hsucc_isIso
        (chartNeighborhood (k := k) y) y (chartNeighborhood_open (k := k) y)
        (mem_chartNeighborhood (k := k) y) (i - 1)
      rw [show i - 1 + 1 = i by omega] at hn'
      exact hn'
    letI := hn
    change IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (P k) (deletedPoint y)
        (ambientChartMap (k := k) y) (ambientChartMap_mapsTo (k := k) y)) i)
    rw [ambientChartMap_chain_eq (k := k), HomologicalComplex.homologyMap_comp]
    infer_instance
  letI := hf
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hmodel.of_iso (asIso f).symm)

/-- LEAF (split by claude-14 from `_aux_convex` after lemma-1's PARTIAL, job 2363,
2026-10-22): the convex model in `ℝ^(k+2)`.  For compact convex `K` and `u ∈ K`,
the identity induces an isomorphism `H_(n+1)(ℝⁿ, ℝⁿ ∖ K) → H_(n+1)(ℝⁿ, ℝⁿ ∖ u)`.
Template: t00A01's sorry-free `apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model` (with its helpers
`_aux_model_aux_hequiv`, `_aux_model_aux_bounding_ball`, `_aux_model_aux_sub`):
radial deformation shows `ℝⁿ ∖ K ↪ ℝⁿ ∖ u` is a homotopy equivalence, then the
five lemma (`relativeSingularMap_homologyMap_isIso`).  Generalize `Fin 3` to
`k + 2`; nothing in that route uses the dimension. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_hequiv
    (k : ℕ) (K : Set (E (k + 2))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) :
    ∃ e : ContinuousMap.HomotopyEquiv (Kᶜ : Set (E (k + 2)))
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u),
      ∀ x, ((e.toFun x : E (k + 2))) = (x : E (k + 2)) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 1 u
  let j : C((Kᶜ : Set (E (k + 2))),
      ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u) :=
    { toFun := fun x => ⟨x.1, by
        intro hx
        apply x.2
        have : x.1 = u := by
          simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint] using hx
        simpa [this] using hu⟩
      continuous_toFun := by fun_prop }
  let ρ : C(ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
      (Kᶜ : Set (E (k + 2)))) :=
    { toFun := fun x => ⟨u + (1 + R / ‖x.1 - u‖) • (x.1 - u), by
        intro hxK
        have hxne : x.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
            hxu]))
        have hn : 0 < ‖x.1 - u‖ := norm_pos_iff.mpr hxne
        have ha : 0 ≤ 1 + R / ‖x.1 - u‖ := by positivity
        have hdist : dist (u + (1 + R / ‖x.1 - u‖) • (x.1 - u)) u =
            ‖x.1 - u‖ + R := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ha]
          field_simp
        have hb := hKR hxK
        rw [Metric.mem_ball, hdist] at hb
        linarith⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hv : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            x.1 - u) := continuous_subtype_val.sub continuous_const
        have hn : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            ‖x.1 - u‖) := continuous_norm.comp hv
        have hn0 : ∀ x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
            ‖x.1 - u‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
              intro hxu
              exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
                hxu])))
        exact continuous_const.add
          ((continuous_const.add (continuous_const.div hn hn0)).smul hv) }
  let Hout : ContinuousMap.Homotopy (j.comp ρ) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro heq
        have hxne : tx.2.1 ≠ u := by
          intro hx
          exact tx.2.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint, hx])
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr hxne
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        have hcoef : 0 < (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ) := by
          have ht0 := tx.1.2.1
          have ht1 := tx.1.2.2
          have : 0 < R := lt_trans (by norm_num) hR
          have hq : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        apply hvne
        have hzero : ((1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) +
            (tx.1 : ℝ)) • (tx.2.1 - u) = 0 := by
          calc
            _ = (1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
                (tx.1 : ℝ) • tx.2.1 - u := by dsimp [j, ρ]; module
            _ = 0 := sub_eq_zero.mpr heq
        exact (smul_eq_zero.mp hzero).resolve_left hcoef.ne'⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [j, ρ]
      map_one_left := by intro x; apply Subtype.ext; simp }
  let Hin : ContinuousMap.Homotopy (ρ.comp j) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro hz
        have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
        have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact tx.2.2 (by simpa [hxu] using hu))
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        let c : ℝ := (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ)
        have hc : 1 ≤ c := by
          dsimp [c]
          have hRp : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
        have hzform : (1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1 = u + c • (tx.2.1 - u) := by
          dsimp [c, ρ, j]
          module
        have hp : tx.2.1 = (1 - c⁻¹) • u + c⁻¹ •
            ((1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1) := by
          rw [hzform]
          rw [smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
          module
        have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
        have hc_sub : 0 ≤ 1 - c⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hc0).2 hc)
        have hmem := hconv hu hz hc_sub hc_inv (by ring)
        exact tx.2.2 (hp.symm ▸ hmem)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [ρ, j]
      map_one_left := by intro x; apply Subtype.ext; simp }
  refine ⟨{ toFun := j, invFun := ρ, left_inv := ⟨Hin⟩, right_inv := ⟨Hout⟩ }, ?_⟩
  intro x
  rfl

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub
    (k : ℕ) (K : Set (E (k + 2))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (ConstructionTargets.SingularExcision.subspaceMap Kᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
          (ContinuousMap.id (E (k + 2)))
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu))) i) := by
  obtain ⟨e, he⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_hequiv k K hK hconv u hu
  have hmap : ConstructionTargets.SingularExcision.subspaceMap Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
      (ContinuousMap.id (E (k + 2)))
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu) = TopCat.ofHom e.toFun := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (he x).symm
  change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
    (AddCommGrpCat.of ℤ)).map _)
  rw [hmap, ← ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom e i]
  infer_instance

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model
    (k : ℕ) (K : Set (E (k + 2))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u) (ContinuousMap.id (E (k + 2)))
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu)) (n + 1)) := by
  have hamb : ∀ j, IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ContinuousMap.id (E (k + 2))))) j) := by
    intro j
    change IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of (E (k + 2))))) j)
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    infer_instance
  apply ConstructionTargets.SingularExcision.relativeSingularMap_homologyMap_isIso
  · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub k K hK hconv u hu (n + 1)
  · exact hamb (n + 1)
  · intro j _
    exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub k K hK hconv u hu j
  · intro j _
    exact hamb j

/-- LEAF (split by claude-14 from `_aux_convex` after lemma-1's PARTIAL, job 2363,
2026-10-22): the chart reduction.  For compact `K` in the chart source of
`e = chartAt x` and `z ∈ K`, if `H_i(ℝⁿ, ℝⁿ ∖ e '' K) → H_i(ℝⁿ, ℝⁿ ∖ e z)` is an
isomorphism, so is `H_i(M, M ∖ K) → H_i(M, M ∖ z)`.  Template: t00A01's sorry-free
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_reduce` (with `_aux_isIso_aux_restrict` (excision of
the complement of an open `U ⊇ K`), `_aux_isIso_aux_homeo`, `_aux_isIso_aux_excision`,
`_aux_isIso_aux_chart`).  Generalize `Fin 3` to `k + 2`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_excision
    {X : Type} [TopologicalSpace X] (K U : Set X)
    (hU : IsOpen U) (hKU : Uᶜ ⊆ interior Kᶜ) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap Kᶜ Uᶜ) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
    Kᶜ Uᶜ hU.isClosed_compl hKU n

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_chart
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A B
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e)
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
          e A B hAB)) i) := by
  exact ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    e A B hAB i

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): localization can be computed in an open subspace.  For open
`U ⊆ X` and closed `B ⊆ A ⊆ U`, the identity `H_i(X, X ∖ A) → H_i(X, X ∖ B)` is an
isomorphism iff the identity `H_i(U, U ∖ A) → H_i(U, U ∖ B)` is.  Route: the inclusion
`U ↪ X` gives a commuting square (`relativeSingularMap_comp`, both composites are the
inclusion); its two vertical maps are excisions of `X ∖ U` (`_aux_excision`, after the
identification `U ≃ₜ (Uᶜ)ᶜ` as in `neighborhoodInclusion_chain_eq`), so both are
isomorphisms for `i > 0`, and two-out-of-three gives the iff. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_pair
    {X : Type} [TopologicalSpace X] (U K : Set X) (u : U) :
    u ∈ {v : U | v.1 ∉ K} ↔
      ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U u ∈
        ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ := by
  rfl

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_chain
    {X : Type} [TopologicalSpace X] (U K : Set X) :
    ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ K} Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
        (fun _ h => h) =
      ConstructionTargets.SingularExcision.relativeSingularMap
          {u : U | u.1 ∉ K}
          (ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ)
          (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U))
          (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
            _ _ _
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_pair U K)) ≫
        ConstructionTargets.SingularExcision.relativeExcisionMap Kᶜ Uᶜ := by
  let e := ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U)
  have he := ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U)
    {u : U | u.1 ∉ K} (ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_pair U K)
  have hf := ConstructionTargets.SingularExcision.excisionInclusion_mapsTo Kᶜ Uᶜ
  have hcomp : (ConstructionTargets.SingularExcision.excisionInclusion Uᶜ).comp e =
      ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U := by
    ext u
    rfl
  have h := ConstructionTargets.SingularExcision.relativeSingularMap_comp
    {u : U | u.1 ∉ K}
    (ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ) Kᶜ
    e (ConstructionTargets.SingularExcision.excisionInclusion Uᶜ) he hf (hf.comp he)
  simpa only [hcomp] using h.symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_inclusion
    {X : Type} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ K} Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
        (fun _ h => h)) i) := by
  have hZ : Uᶜ ⊆ interior Kᶜ := by
    rw [hK.isOpen_compl.interior_eq]
    intro x hx hxK
    exact hx (hKU hxK)
  letI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_excision
    K U hU hZ i hi
  letI := ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U)
    {u : U | u.1 ∉ K} (ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_pair U K) i
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_chain,
    HomologicalComplex.homologyMap_comp]
  infer_instance

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
    {X : Type} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAU : A ⊆ U) (hBA : B ⊆ A)
    (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
        (ContinuousMap.id X) (fun _ hx hb => hx (hBA hb))) i) ↔
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ A} {u : U | u.1 ∉ B}
        (ContinuousMap.id U) (fun _ hx hb => hx (hBA hb))) i) := by
  let jA := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U
  let jB := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U
  let fU := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ A} {u : U | u.1 ∉ B} (ContinuousMap.id U)
    (fun _ hx hb => hx (hBA hb))
  let fX := ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
    (ContinuousMap.id X) (fun _ hx hb => hx (hBA hb))
  let vA := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ A} Aᶜ jA (fun _ h => h)
  let vB := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ B} Bᶜ jB (fun _ h => h)
  have hsquare : HomologicalComplex.homologyMap fU i ≫
        HomologicalComplex.homologyMap vB i =
      HomologicalComplex.homologyMap vA i ≫
        HomologicalComplex.homologyMap fX i := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    dsimp [fU, fX, vA, vB, jA, jB]
    have hleft := ConstructionTargets.SingularExcision.relativeSingularMap_comp
      {u : U | u.1 ∉ A} {u : U | u.1 ∉ B} Bᶜ
      (ContinuousMap.id U)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
      (fun _ hx hb => hx (hBA hb)) (fun _ h => h)
      (fun _ hx hb => hx (hBA hb))
    have hright := ConstructionTargets.SingularExcision.relativeSingularMap_comp
      {u : U | u.1 ∉ A} Aᶜ Bᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
      (ContinuousMap.id X) (fun _ h => h) (fun _ hx hb => hx (hBA hb))
      (fun _ hx hb => hx (hBA hb))
    rw [hleft, hright]
    rfl
  letI : IsIso (HomologicalComplex.homologyMap vA i) :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_inclusion
      U hU A hA hAU i hi
  letI : IsIso (HomologicalComplex.homologyMap vB i) :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_inclusion
      U hU B hB (hBA.trans hAU) i hi
  constructor
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fX i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap fU i ≫
        HomologicalComplex.homologyMap vB i) := by
      rw [hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap fU i)
      (HomologicalComplex.homologyMap vB i)
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fU i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap vA i ≫
        HomologicalComplex.homologyMap fX i) := by
      rw [← hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap vA i)
      (HomologicalComplex.homologyMap fX i)

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): localization is invariant under homeomorphism.  If
`e : X ≃ₜ Y` carries `A` to `A'` and `B` to `B'`, the identity
`H_i(X, A) → H_i(X, B)` is an isomorphism iff `H_i(Y, A') → H_i(Y, B')` is.
Route: the square with horizontal maps the pair homeomorphisms
(`_aux_chart`, isomorphisms in every degree) commutes by `relativeSingularMap_comp`
(both composites are `e`); two-out-of-three. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (A B : Set X) (A' B' : Set Y)
    (hA : ∀ x, x ∈ A ↔ e x ∈ A') (hB : ∀ x, x ∈ B ↔ e x ∈ B')
    (hAB : Set.MapsTo (ContinuousMap.id X) A B)
    (hAB' : Set.MapsTo (ContinuousMap.id Y) A' B') (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A B
        (ContinuousMap.id X) hAB) i) ↔
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A' B'
        (ContinuousMap.id Y) hAB') i) := by
  let e' := ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e
  let fX := ConstructionTargets.SingularExcision.relativeSingularMap A B
    (ContinuousMap.id X) hAB
  let fY := ConstructionTargets.SingularExcision.relativeSingularMap A' B'
    (ContinuousMap.id Y) hAB'
  let uA := ConstructionTargets.SingularExcision.relativeSingularMap A A' e'
    (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
      e A A' hA)
  let uB := ConstructionTargets.SingularExcision.relativeSingularMap B B' e'
    (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
      e B B' hB)
  have heAB : Set.MapsTo e' A B' := fun x hx =>
    (hB x).1 (hAB hx)
  have hsquare : HomologicalComplex.homologyMap fX i ≫
        HomologicalComplex.homologyMap uB i =
      HomologicalComplex.homologyMap uA i ≫
        HomologicalComplex.homologyMap fY i := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    dsimp [fX, fY, uA, uB, e']
    rw [ConstructionTargets.SingularExcision.relativeSingularMap_comp
        A B B' (ContinuousMap.id X) e' hAB
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
          e B B' hB) heAB,
      ConstructionTargets.SingularExcision.relativeSingularMap_comp
        A A' B' e' (ContinuousMap.id Y)
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
          e A A' hA) hAB' heAB]
    rfl
  letI : IsIso (HomologicalComplex.homologyMap uA i) :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_chart
      e A A' hA i
  letI : IsIso (HomologicalComplex.homologyMap uB i) :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_chart
      e B B' hB i
  constructor
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fX i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap uA i ≫
        HomologicalComplex.homologyMap fY i) := by
      rw [← hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap uA i)
      (HomologicalComplex.homologyMap fY i)
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fY i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap fX i ≫
        HomologicalComplex.homologyMap uB i) := by
      rw [hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap fX i)
      (HomologicalComplex.homologyMap uB i)

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): the chart reduction shared by `_inj_aux_isIso` and
`_ball_aux_reduce`.  For compact `K` in the chart source of `e = chartAt x` and
`z ∈ K`, if `H_i(ℝ³, ℝ³ ∖ e '' K) → H_i(ℝ³, ℝ³ ∖ e z)` is an isomorphism, so is
`H_i(M, M ∖ K) → H_i(M, M ∖ z)`.  Route: `_aux_restrict` with `U = e.source`
(`K` compact in a Hausdorff space, hence closed; points are closed); `_aux_homeo`
along `e.toHomeomorphSourceTarget`, whose membership conditions are
`u ∈ K ↔ e u ∈ e '' K` (`e` injective on the source) and `u = z ↔ e u = e z`;
`_aux_restrict` again in `ℝ³` with `U = e.target` (`e '' K` compact). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (K : Set M) (hK : IsCompact K)
    (hsub : K ⊆ (chartAt (E (k + 2)) x).source)
    (z : M) (hz : z ∈ K) (i : ℕ) (hi : 0 < i)
    (hmodel : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        ((chartAt (E (k + 2)) x) '' K)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
          ((chartAt (E (k + 2)) x) z))
        (ContinuousMap.id (E (k + 2)))
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo ((chartAt (E (k + 2)) x) '' K) ((chartAt (E (k + 2)) x) z)
          (Set.mem_image_of_mem _ hz))) i)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K z hz)) i) := by
  let e := chartAt (E (k + 2)) x
  have hzsub : z ∈ e.source := hsub hz
  have hKclosed : IsClosed K := hK.isClosed
  have himgCompact : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.continuousOn.mono hsub)
  have himgClosed : IsClosed (e '' K) := himgCompact.isClosed
  have htarget : e '' K ⊆ e.target := by
    rintro _ ⟨w, hw, rfl⟩
    exact e.map_source (hsub hw)
  have hmodelTarget : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : e.target | u.1 ∉ e '' K}
        {u : e.target | u.1 ∉ ({e z} : Set (E (k + 2)))}
        (ContinuousMap.id e.target) (fun u hu huz => hu (by
          have heq : u.1 = e z := by simpa using huz
          rw [heq]
          exact Set.mem_image_of_mem e hz))) i) := by
    exact (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
      e.target e.open_target (e '' K) ({e z} : Set (E (k + 2)))
      himgClosed isClosed_singleton htarget (by
        intro a ha
        rcases ha with rfl
        exact Set.mem_image_of_mem e hz) i hi).mp hmodel
  have hsource : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : e.source | u.1 ∉ K} {u : e.source | u.1 ∉ ({z} : Set M)}
        (ContinuousMap.id e.source) (fun u hu huz => hu (by
          have heq : u.1 = z := by simpa using huz
          rw [heq]
          exact hz))) i) := by
    exact (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
      e.toHomeomorphSourceTarget
      {u : e.source | u.1 ∉ K} {u : e.source | u.1 ∉ ({z} : Set M)}
      {u : e.target | u.1 ∉ e '' K}
      {u : e.target | u.1 ∉ ({e z} : Set (E (k + 2)))}
      (by
        intro u
        constructor
        · intro hu himg
          obtain ⟨w, hw, hew⟩ := himg
          have hwu : w = u.1 := e.injOn (hsub hw) u.property hew
          exact hu (hwu ▸ hw)
        · intro hu hw
          exact hu ⟨u, hw, rfl⟩)
      (by
        intro u
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        apply not_congr
        constructor
        · exact congrArg e
        · exact e.injOn u.property hzsub)
      (fun u hu huz => hu (by
        have heq : u.1 = z := by simpa using huz
        rw [heq]
        exact hz))
      (fun u hu huz => hu (by
        have heq : u.1 = e z := by simpa using huz
        rw [heq]
        exact Set.mem_image_of_mem e hz)) i).mpr hmodelTarget
  exact (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
    e.source e.open_source K ({z} : Set M) hKclosed isClosed_singleton hsub
    (by
      intro a ha
      have heq : a = z := by simpa using ha
      rw [heq]
      exact hz) i hi).mpr hsource

/-- PROVED (claude-14, 2026-10-22, from lemma-1's PARTIAL, job 2390-1331c110): around each `x`
there is a set `K` (a closed chart ball) such that for every `z` near `x`, `z ∈ K` and
`H_{k+2}(M, M ∖ K) → H_{k+2}(M, M ∖ z)` is an isomorphism.  `_aux_model` and `_aux_reduce`
specialise `_exists_unit_aux_injective_aux_convex_aux_inj_aux_model` / `_aux_reduce` to a
closed ball; the block (with `_eventually_sign`, `_locallyConstant`) sits after them for that
reason (moved from before `_exists_unit_aux_assembly`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model
    (k : ℕ) (c u : E (k + 2)) (r : ℝ) (hu : dist u c < r) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (Metric.closedBall c r)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
        (ContinuousMap.id (E (k + 2)))
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          (Metric.closedBall c r) u (Metric.mem_closedBall.2 hu.le))) (k + 2)) := by
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model k
    (Metric.closedBall c r) (isCompact_closedBall c r) (convex_closedBall c r) u
    (Metric.mem_closedBall.2 hu.le) (k + 1)

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_reduce
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M] (x : M) (r : ℝ)
    (hr : Metric.closedBall (chartAt (E (k + 2)) x x) r ⊆
      (chartAt (E (k + 2)) x).target)
    (z : M) (hz : z ∈ (chartAt (E (k + 2)) x).source)
    (hzr : dist (chartAt (E (k + 2)) x z) (chartAt (E (k + 2)) x x) < r) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap ((chartAt (E (k + 2)) x).source ∩
          chartAt (E (k + 2)) x ⁻¹' Metric.closedBall (chartAt (E (k + 2)) x x) r)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          ((chartAt (E (k + 2)) x).source ∩
          chartAt (E (k + 2)) x ⁻¹' Metric.closedBall (chartAt (E (k + 2)) x x) r) z
          ⟨hz, Metric.mem_closedBall.2 hzr.le⟩)) (k + 2)) := by
  set e := chartAt (E (k + 2)) x
  have hK : IsCompact (e.source ∩ e ⁻¹' Metric.closedBall (e x) r) := by
    rw [← e.symm_image_eq_source_inter_preimage hr]
    exact (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hr)
  have hKeq : e '' (e.source ∩ e ⁻¹' Metric.closedBall (e x) r) = Metric.closedBall (e x) r := by
    rw [← e.symm_image_eq_source_inter_preimage hr]
    exact e.toPartialEquiv.image_symm_image_of_subset_target hr
  have key : ∀ (S : Set (E (k + 2))) (_ : S = Metric.closedBall (e x) r) (hzS : e z ∈ S),
      IsIso (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Sᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (e z))
          (ContinuousMap.id (E (k + 2)))
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo S (e z) hzS)) (k + 2)) := by
    rintro S rfl hzS
    exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model k (e x) (e z) r hzr
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce k M x _ hK
    Set.inter_subset_left z ⟨hz, Metric.mem_closedBall.2 hzr.le⟩ (k + 2) (by omega)
    (key _ hKeq (Set.mem_image_of_mem _ ⟨hz, Metric.mem_closedBall.2 hzr.le⟩))

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M] (x : M) :
    ∃ K : Set M, ∀ᶠ z in nhds x, ∃ hz : z ∈ K,
      IsIso (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
          (ContinuousMap.id M)
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
            K z hz)) (k + 2)) := by
  set e := chartAt (E (k + 2)) x
  obtain ⟨r, hr0, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (e.open_target.mem_nhds (mem_chart_target (E (k + 2)) x))
  refine ⟨e.source ∩ e ⁻¹' Metric.closedBall (e x) r, ?_⟩
  have hev : ∀ᶠ z in nhds x, z ∈ e.source ∩ e ⁻¹' Metric.ball (e x) r :=
    (e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source (E (k + 2)) x, Metric.mem_ball_self hr0⟩
  filter_upwards [hev] with z hz
  exact ⟨⟨hz.1, Metric.ball_subset_closedBall hz.2⟩,
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_reduce
      k M x r hr z hz.1 hz.2⟩

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (x : M) :
    ∀ᶠ y in nhds x,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e y =
        punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e x ∨
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e y =
        -punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e x := by
  obtain ⟨K, hK⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball k M x
  obtain ⟨hxK, hxI⟩ := hK.self_of_nhds
  let c := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ) (k + 2)
    (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e)
  have key : ∀ (w : M) (hw : w ∈ K) [IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint w)
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          K w hw)) (k + 2))],
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e w =
        (asIso (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint w)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
              K w hw)) (k + 2)) ≪≫
          ManifoldFundamentalClass.ambientLocalNormalization k w).hom.hom c := by
    intro w hw _
    unfold punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
    rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor
      K w hw (k + 2)]
    rfl
  refine hK.mono fun z hz => ?_
  obtain ⟨hzK, hzI⟩ := hz
  rw [key z hzK, key x hxK]
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_units _ _ c

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) :
    IsLocallyConstant (fun y : M ↦ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e y).natAbs) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  exact
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign
      k M e x).mono fun y hy =>
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_natAbs_eq _ _ hy

/-- PROVED from `_aux_inj_aux_model`, `_aux_inj_aux_reduce` (claude-14, 2026-10-22):
for compact `A` in one chart with convex chart image and `y ∈ A`, the
localization `H_i(M, M ∖ A) → H_i(M, M ∖ y)` is injective for `i > 0`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : Convex ℝ ((chartAt (E (k + 2)) x) '' A))
    (y : M) (hy : y ∈ A) (i : ℕ) (hi : 0 < i) (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i)
    (hc : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y) (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i c = 0) :
    c = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  letI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce k M x A hA hsub y hy (n + 1) hi
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model k _ (hA.image_of_continuousOn
        ((chartAt (E (k + 2)) x).continuousOn.mono hsub)) hconv _ (Set.mem_image_of_mem _ hy) n)
  exact (AddCommGrpCat.mono_iff_injective (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y) (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (n + 1))).1 inferInstance
    (hc.trans (map_zero _).symm)

/-- PROVED from `_aux_convex_aux_point`, `_aux_convex_aux_inj` (claude-14, 2026-10-22); was LEAF (split by claude-14, after lemma-1's BLOCKED-ON on
`_aux_inChart`, job 2352; Hatcher 3.27, step 1): a compact `A` inside one chart
whose chart image is convex is good.  Template: t00A01's sorry-free
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex`
(through `_aux_convex_aux_point` and `_aux_convex_aux_inj`, with its
`_aux_inj_aux_model` (radial deformation `ℝⁿ ∖ K ≃ₕ ℝⁿ ∖ u`) and `_aux_inj_aux_isIso`
(excision + chart transport) helpers).  Generalize `Fin 3` to `k + 2`; the model
computation `H_i(ℝⁿ, ℝⁿ ∖ y) = 0` for `i > n` (t00A01 uses `HigherModelLocalHomology`
at `ℝ³`) is the part that changes.  The empty case is `_aux_convex_aux_empty`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : Convex ℝ ((chartAt (E (k + 2)) x) '' A)) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_empty k M
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · have key : ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i, c = 0 := fun c =>
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj k M x A hA hsub hconv y hy i (by omega) c
        (@Subsingleton.elim _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_point k M y i hi) _ _)
    exact ⟨fun c d => (key c).trans (key d).symm⟩
  · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj k M x A hA hsub hconv y hy (k + 2) (by omega) c (hc y hy)

/-- LEAF (split by claude-14, 2026-10-22, after lemma-3's PARTIAL on
`_exists_unit_aux_injective`; Hatcher 3.27, steps 1-3): every compact subset of
one chart source is good.  Template: t00A01's sorry-free
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_inChart`
(through `_aux_inChart_aux_{lift,cover,finite}` and `_aux_convex`).  CCSH's
`_aux_convex` is the leaf above (claude-14, 2026-10-22): use it as the convex
base case.  Generalize `Fin 3` to `k + 2`. -/
/- PROVED (claude-14, split of lemma-3's PARTIAL, 2026-10-21): localization
maps between relative homologies of `M` compose. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp
    (k : ℕ)
    (M : Type) [TopologicalSpace M] (S T U : Set M)
    (h1 : Set.MapsTo (ContinuousMap.id M) S T) (h2 : Set.MapsTo (ContinuousMap.id M) T U)
    (h3 : Set.MapsTo (ContinuousMap.id M) S U) (i : ℕ)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains S).homology i) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap T U (ContinuousMap.id M) h2) i
        (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap S T (ContinuousMap.id M) h1) i c) =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap S U (ContinuousMap.id M) h3) i c := by
  have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
    S T U (ContinuousMap.id M) (ContinuousMap.id M) h1 h2 h3 i
  have := congrArg (fun f => f c) e
  simp only [ConcreteCategory.comp_apply] at this
  exact this

/- PROVED (lemma-3, PARTIAL on `_aux_inChart_aux_lift`, 2026-10-21): a finite
family of compact-domain maps into `M ∖ A` misses every `K` inside some open
`V ⊇ A`.  `V` is the complement of the union of their ranges, which is
compact, hence closed (`T2Space`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_support
    (k : ℕ)
    (M P : Type) [TopologicalSpace M] [T2Space M] [TopologicalSpace P] [CompactSpace P]
    (A : Set M) (s : Finset C(P, M))
    (hs : ∀ f ∈ s, Set.range f ⊆ Aᶜ) :
    ∃ V : Set M, IsOpen V ∧ A ⊆ V ∧
      ∀ (K : Set M), K ⊆ V → ∀ f ∈ s, Set.range f ⊆ Kᶜ := by
  classical
  let S : Set M := ⋃ f ∈ s, Set.range f
  have hSc : IsClosed S := by
    apply isClosed_biUnion_finset
    intro f hf
    exact (isCompact_range f.continuous).isClosed
  refine ⟨Sᶜ, hSc.isOpen_compl, ?_, ?_⟩
  · intro a ha hS
    rcases Set.mem_iUnion.mp hS with ⟨f, hf⟩
    rcases Set.mem_iUnion.mp hf with ⟨hfs, haf⟩
    exact (hs f hfs haf) ha
  · intro K hK f hfs y hy hKy
    exact (hK hKy) (Set.mem_iUnion_of_mem f (Set.mem_iUnion_of_mem hfs hy))

/- LIBRARY LEAF (chain level; claude-14's split of lemma-3's PARTIAL on
`_aux_inChart_aux_lift`, 2026-10-21): every class of `H_i(M, M ∖ A)` is the
class of a relative cycle `y` that is the image of an absolute chain `z`, and
the boundary of `z` lies in the subcomplex generated by simplices of `M ∖ A`.
Route: `homologyπ` is epi, hence surjective in `AddCommGrpCat`; `iCycles y`
lifts along the degreewise-surjective `cokernel.π`; `π (∂z) = d (iCycles y) = 0`,
and the kernel of `cokernel.π` in degree `i - 1` is the range of `ι`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep_aux_homology
    (k : ℕ)
    (M : Type) [TopologicalSpace M] (A : Set M) (i : ℕ)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i) :
    ∃ y, (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homologyπ i y = c := by
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance c

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep_aux_projection
    (k : ℕ)
    (M : Type) [TopologicalSpace M] (A : Set M) (i : ℕ)
    (y : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).cycles i) :
    ∃ z, (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ).f i z =
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).iCycles i y := by
  let Q := ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ
  letI : Epi Q := by
    change Epi (cokernel.π
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Aᶜ))
    dsimp only [cokernel.π]
    infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance _

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep
    (k : ℕ)
    (M : Type) [TopologicalSpace M] (A : Set M) (i : ℕ)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i) :
    ∃ (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).X i)
      (y : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).cycles i),
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homologyπ i y = c ∧
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).iCycles i y =
        (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ).f i z ∧
      (ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).d i (i - 1) z ∈
        Set.range ((ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Aᶜ).f (i - 1)) := by
  open ConstructionTargets.SingularHomologyConcrete in
  obtain ⟨y, hy⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep_aux_homology k M A i c
  obtain ⟨z, hz⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep_aux_projection k M A i y
  refine ⟨z, y, hy, hz.symm, ?_⟩
  have hzero : (relativeSingularProjection Aᶜ).f (i - 1)
      ((SingularChains (TopCat.of M)).d i (i - 1) z) = 0 := by
    have h1 := congrArg (fun g => g z) (congrArg ConcreteCategory.hom
      ((relativeSingularProjection Aᶜ).comm i (i - 1)))
    simp only [ConcreteCategory.comp_apply] at h1
    rw [← h1, hz]
    have h2 := congrArg (fun g => g y) (congrArg ConcreteCategory.hom
      ((RelativeSingularChains Aᶜ).iCycles_d i (i - 1)))
    simpa only [ConcreteCategory.comp_apply] using h2
  have hex := (HomologicalComplex.exact_iff_degreewise_exact _).mp
    (singularPairShortComplex_shortExact Aᶜ).exact (i - 1)
  obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).mp hex _ hzero
  refine ⟨(factorThruImage (singularSubspaceMap Aᶜ)).f (i - 1) w, ?_⟩
  rw [← hw]
  change ((factorThruImage (singularSubspaceMap Aᶜ)).f (i - 1) ≫
    (relativeSingularSubcomplex.ι Aᶜ).f (i - 1)) w = (singularSubspaceMap Aᶜ).f (i - 1) w
  rw [← HomologicalComplex.comp_f]
  simp only [relativeSingularSubcomplex.ι, image.fac]

/- LIBRARY LEAF (chain level; claude-14's split of lemma-3's PARTIAL on
`_aux_inChart_aux_lift`, 2026-10-21): a chain generated by simplices of
`M ∖ A` is generated by simplices of `M ∖ K` for every `K` between `A` and
some open `V ⊇ A`.  Route: `relativeSingularSubcomplex Aᶜ` is the image of
`singularSubspaceMap Aᶜ`, so the chain is the image of a finite ℤ-combination
of singular simplices of the subspace `Aᶜ`; compose them with the inclusion to
get a `Finset` of maps from the compact topological simplex into `M` with
ranges in `Aᶜ`, and apply `_aux_lift_aux_support`.  For `K ⊆ V` each of those
simplices factors through `Kᶜ`, so the chain is in the image of
`singularSubspaceMap Kᶜ`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_finite_aux_chain
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] (A : Set M) (j : ℕ)
    (c : (ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↥(Aᶜ))).X j) :
    ∃ V : Set M, IsOpen V ∧ A ⊆ V ∧ ∀ (K : Set M), A ⊆ K → K ⊆ V →
      ∃ d : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of ↥(Kᶜ))).X j,
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Kᶜ).f j d =
          (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ).f j c := by
  classical
  let a := ConstructionTargets.SingularSubdivision.productionChainFinsupp j c
  let F : ConstructionTargets.SingularSubdivision.SingularSimplex (TopCat.of ↥(Aᶜ)) j →
      C(stdSimplex ℝ (Fin (j + 1)), M) := fun s ↦
    (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion Aᶜ).hom.comp
      (ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex j s)
  obtain ⟨V, hVo, hAV, hV⟩ :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_support k
      M (stdSimplex ℝ (Fin (j + 1))) A (a.support.image F) (by
        intro f hf
        rcases Finset.mem_image.mp hf with ⟨s, hs, rfl⟩
        intro y hy
        rcases hy with ⟨t, rfl⟩
        exact (ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex j s t).2)
  refine ⟨V, hVo, hAV, ?_⟩
  intro K hAK hKV
  have hsK : ∀ s ∈ a.support, Set.range (F s) ⊆ Kᶜ := by
    intro s hs
    exact hV K hKV (F s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  let lift (s : ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↥(Aᶜ)) j) (hs : s ∈ a.support) :
      C(stdSimplex ℝ (Fin (j + 1)), ↥(Kᶜ)) :=
    ⟨fun t ↦ ⟨F s t, hsK s hs ⟨t, rfl⟩⟩,
      (F s).continuous.subtype_mk _⟩
  let d : (ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↥(Kᶜ))).X j :=
    ∑ s : a.support,
      (ConstructionTargets.SingularSubdivision.singularGenerator (TopCat.of ↥(Kᶜ)) j
        (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of ↥(Kᶜ)) j (lift s s.property))) (a s)
  refine ⟨d, ?_⟩
  simp only [d, map_sum]
  have hgen : ∀ s : a.support,
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Kᶜ).f j
          ((ConstructionTargets.SingularSubdivision.singularGenerator (TopCat.of ↥(Kᶜ)) j
            (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
              (TopCat.of ↥(Kᶜ)) j
              (lift s s.property))) (a s)) =
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ).f j
          ((ConstructionTargets.SingularSubdivision.singularGenerator (TopCat.of ↥(Aᶜ)) j s) (a s)) := by
    intro s
    have hK := congrArg (fun q ↦ q (a s))
      (ConstructionTargets.SingularSubdivision.singularGenerator_singularPostcomposition j
        (lift s s.property)
        (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion Kᶜ).hom)
    have hA := congrArg (fun q ↦ q (a s))
      (ConstructionTargets.SingularSubdivision.singularGenerator_singularPostcomposition j
        (ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex j s)
        (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion Aᶜ).hom)
    exact hK.trans hA.symm
  simp_rw [hgen]
  have he := congrArg (fun f ↦ f (1 : ℤ))
    (ConstructionTargets.SingularSubdivision.finiteProductionChainRealize_productionChainFinsupp
      j c)
  simp only [ConstructionTargets.SingularSubdivision.finiteProductionChainRealize,
    Finsupp.sum, a, AddCommGrpCat.asHom, map_sum] at he
  have he' : (∑ s ∈ a.support,
      (ConstructionTargets.SingularSubdivision.singularGenerator
        (TopCat.of ↥(Aᶜ)) j s) (a s)) = c := by
    have happ : ((∑ s ∈ a.support, (a s) •
        ConstructionTargets.SingularSubdivision.singularGenerator
          (TopCat.of ↥(Aᶜ)) j s) :
        AddCommGrpCat.of ℤ ⟶
          (ConstructionTargets.SingularHomologyConcrete.SingularChains
            (TopCat.of ↥(Aᶜ))).X j) (1 : ℤ) =
      ∑ s ∈ a.support,
        (ConstructionTargets.SingularSubdivision.singularGenerator
          (TopCat.of ↥(Aᶜ)) j s) (a s) := by
      induction a.support using Finset.induction_on with
      | empty => simp
      | @insert s S hs ih =>
          simp only [Finset.sum_insert, hs, not_false_eq_true]
          change (a s) •
              (ConstructionTargets.SingularSubdivision.singularGenerator
                (TopCat.of ↥(Aᶜ)) j s) (1 : ℤ) +
              (∑ t ∈ S, (a t) •
                ConstructionTargets.SingularSubdivision.singularGenerator
                  (TopCat.of ↥(Aᶜ)) j t) (1 : ℤ) =
            (ConstructionTargets.SingularSubdivision.singularGenerator
              (TopCat.of ↥(Aᶜ)) j s) (a s) +
              ∑ t ∈ S, (ConstructionTargets.SingularSubdivision.singularGenerator
                (TopCat.of ↥(Aᶜ)) j t) (a t)
          rw [ih]
          congr 1
          rw [← map_zsmul]
          simp
    calc
      _ = (∑ s ∈ a.support, (a s) •
          ConstructionTargets.SingularSubdivision.singularGenerator
            (TopCat.of ↥(Aᶜ)) j s) (1 : ℤ) := happ.symm
      _ = c := by simpa [a, AddCommGrpCat.asHom] using he
  rw [← map_sum]
  apply congrArg
    (fun z ↦ (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ).f j z)
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_attach a.support (fun s ↦
      (ConstructionTargets.SingularSubdivision.singularGenerator
        (TopCat.of ↥(Aᶜ)) j s) (a s))).trans he'
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_finite
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] (A : Set M) (j : ℕ)
    (x : (ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).X j)
    (hx : x ∈ Set.range
      ((ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Aᶜ).f j)) :
    ∃ V : Set M, IsOpen V ∧ A ⊆ V ∧ ∀ (K : Set M), A ⊆ K → K ⊆ V →
      x ∈ Set.range
        ((ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Kᶜ).f j) := by
  rcases hx with ⟨q, rfl⟩
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective
    ((CategoryTheory.Limits.factorThruImage
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ)).f j)).mp
      inferInstance q
  obtain ⟨V, hVo, hAV, hV⟩ :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_finite_aux_chain k
      M A j c
  refine ⟨V, hVo, hAV, ?_⟩
  intro K hAK hKV
  obtain ⟨d, hd⟩ := hV K hAK hKV
  refine ⟨(CategoryTheory.Limits.factorThruImage
    (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Kᶜ)).f j d, ?_⟩
  dsimp [ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι]
  have eK := congrArg (fun f => f d) (congrArg (fun f => f.f j)
    (CategoryTheory.Limits.image.fac
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Kᶜ)))
  have eA := congrArg (fun f => f c) (congrArg (fun f => f.f j)
    (CategoryTheory.Limits.image.fac
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ)))
  simpa only [ConcreteCategory.comp_apply] using
    eK.trans (hd.trans (eA.symm.trans (congrArg
      (fun z => (CategoryTheory.Limits.image.ι
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap Aᶜ)).f j z) hc)))

/- LIBRARY LEAF (chain level; claude-14's split of lemma-3's PARTIAL on
`_aux_inChart_aux_lift`, 2026-10-21): if `K ⊇ A` and the boundary of the
absolute chain `z` is generated by simplices of `M ∖ K`, then `π_{Kᶜ} z` is a
relative cycle, and its class maps to the class of `y` (where
`iCycles y = π_{Aᶜ} z`).  Route: `π_{Kᶜ}(∂z) = 0` because `π ∘ ι = 0`; so
`d (π_{Kᶜ} z) = 0` and `π_{Kᶜ} z` lifts to a cycle `y'`.  By
`relativeSingularMap_projection_naturality` (with `absoluteMap id = 𝟙`), the
relative map sends `π_{Kᶜ} z` to `π_{Aᶜ} z`, so it sends `y'` to `y`
(`iCycles` is mono), and `homologyπ` is natural. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_nat
    (k : ℕ)
    (M : Type) [TopologicalSpace M] (A K : Set M) (hAK : A ⊆ K) (i : ℕ)
    (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).X i)
    (y : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).cycles i)
    (hy : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).iCycles i y =
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ).f i z)
    (hz : (ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).d i (i - 1) z ∈
      Set.range ((ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Kᶜ).f (i - 1))) :
    ∃ d : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Kᶜ).homology i,
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ Aᶜ (ContinuousMap.id M)
          (fun y hy => Set.compl_subset_compl.mpr hAK hy)) i d =
        (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homologyπ i y := by
  let CK := ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Kᶜ
  let CA := ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ
  let pK := ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ
  let F := ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ Aᶜ
    (ContinuousMap.id M) (fun y hy => Set.compl_subset_compl.mpr hAK hy)
  have hpd : pK.f (i - 1)
      ((ConstructionTargets.SingularHomologyConcrete.SingularChains (TopCat.of M)).d i (i - 1) z) = 0 := by
    obtain ⟨w, hw⟩ := hz
    rw [← hw]
    change (pK.f (i - 1))
      ((ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Kᶜ).f
        (i - 1) w) = 0
    rw [← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f (i - 1))
        (cokernel.condition
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι Kᶜ))) w
  have hcycle : CK.d i (i - 1) (pK.f i z) = 0 := by
    have hc := ConcreteCategory.congr_hom (pK.comm i (i - 1)) z
    simpa only [ConcreteCategory.comp_apply, hpd] using hc
  let xhom : AddCommGrpCat.of ℤ ⟶ CK.X i :=
    AddCommGrpCat.ofHom (zmultiplesHom _ (pK.f i z))
  have xhomd : xhom ≫ CK.d i (i - 1) = 0 := by
    apply ConcreteCategory.hom_ext
    intro n
    change CK.d i (i - 1) (n • pK.f i z) = 0
    rw [map_zsmul, hcycle, smul_zero]
  have hnext : (ComplexShape.down ℕ).next i = i - 1 := by
    cases i with
    | zero => exact ChainComplex.next_nat_zero
    | succ i => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        ChainComplex.next_nat_succ i
  let yhom : AddCommGrpCat.of ℤ ⟶ CK.cycles i :=
    CK.liftCycles xhom (i - 1) hnext xhomd
  let yK : CK.cycles i := yhom (1 : ℤ)
  have hyKi : CK.iCycles i yK = pK.f i z := by
    have hc := ConcreteCategory.congr_hom
      (CK.liftCycles_i xhom (i - 1) hnext xhomd) (1 : ℤ)
    change CK.iCycles i yK = xhom (1 : ℤ) at hc
    rw [hc]
    change (1 : ℤ) • pK.f i z = pK.f i z
    exact one_zsmul _
  refine ⟨CK.homologyπ i yK, ?_⟩
  have hyK : HomologicalComplex.cyclesMap F i yK = y := by
    apply (AddCommGrpCat.mono_iff_injective (CA.iCycles i)).mp inferInstance
    have hci := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i F i) yK
    simp only [ConcreteCategory.comp_apply] at hci
    rw [hci, hyKi, hy]
    have hn := ConcreteCategory.congr_hom
      (congrArg (fun f => f.f i)
        (ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
          Kᶜ Aᶜ (ContinuousMap.id M)
            (fun y hy => Set.compl_subset_compl.mpr hAK hy))) z
    have hid :
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (ContinuousMap.id M))).f i z = z := by
      change (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M))).f i z = z
      have he := congrArg (fun q => q.f i)
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map_id (TopCat.of M))
      exact ConcreteCategory.congr_hom he z
    change (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ).f i
      ((((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (ContinuousMap.id M))).f i z) =
      F.f i (pK.f i z) at hn
    rw [hid] at hn
    exact hn.symm
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality F i) yK
  simpa only [ConcreteCategory.comp_apply, hyK] using hn

/- LIBRARY LEAF (Hatcher p. 237, chain level; split from `_aux_inChart`
after lemma-3's PARTIAL, 2026-10-21): a class of `H_i(M, M ∖ A)` lifts to
`H_i(M, M ∖ K)` for every `K` between `A` and some open `V ⊇ A`.  Route: pick
a relative cycle `z` representing the class (a chain of `M` whose boundary is
a chain of `M ∖ A`).  The boundary is a finite sum of singular simplices, each
with compact image in `M ∖ A`; their union `S` is compact, hence closed
(`T2Space`).  Take `V = Sᶜ`.  For `A ⊆ K ⊆ V`, every simplex of `∂z` lies in
`M ∖ K`, so `z` is a relative cycle of `(M, M ∖ K)`, and its class maps to the
given one.  Nothing about charts or dimension is used.  (`_divide_aux_inChart`
needs the same lift.) -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] (A : Set M) (i : ℕ)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i) :
    ∃ V : Set M, IsOpen V ∧ A ⊆ V ∧ ∀ (K : Set M) (hAK : A ⊆ K), K ⊆ V →
      ∃ d : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Kᶜ).homology i,
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ Aᶜ (ContinuousMap.id M)
            (fun y hy => Set.compl_subset_compl.mpr hAK hy)) i d = c := by
  obtain ⟨z, y, hyc, hyz, hdz⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_rep k M A i c
  obtain ⟨V, hV, hAV, hK⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_finite k M A (i - 1) _ hdz
  refine ⟨V, hV, hAV, fun K hAK hKV => ?_⟩
  obtain ⟨d, hd⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift_aux_nat k M A K hAK i z y hyz (hK K hAK hKV)
  exact ⟨d, hd.trans hyc⟩

/- LIBRARY LEAF (point-set; split from `_aux_inChart` after lemma-3's
PARTIAL, 2026-10-21): a compact `A` in one chart source, inside an open `V`,
is covered by finitely many compact sets `K a` (`a ∈ s`), each inside the
chart source and `V`, with convex chart image, and each meeting `A`.  Route:
for `a ∈ A` choose `r > 0` with the closed ball about `chart a` of radius `r`
inside `chart.target ∩ chart.symm ⁻¹' (source ∩ V)` (open, contains
`chart a`); let `K a = chart.symm '' closedBall (chart a) r`.  It is compact
(`chart.symm` is continuous on the target), its chart image is the closed
ball (`chart (chart.symm p) = p` on the target), and it is a neighbourhood of
`a` (it contains `source ∩ chart ⁻¹' ball (chart a) r`).
`IsCompact.elim_nhds_subcover` gives the finite `s ⊆ A`.  For `a ∉ A` take
`K a = ∅`.  (`_divide_aux_inChart` needs the same cover.) -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_cover_aux_radius
    (k : ℕ)
    (M : Type) [TopologicalSpace M]
    [ChartedSpace (E (k + 2)) M]
    (x a : M) (ha : a ∈ (chartAt (E (k + 2)) x).source)
    (V : Set M) (hV : IsOpen V) (haV : a ∈ V) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((chartAt (E (k + 2)) x) a) r ⊆
        (chartAt (E (k + 2)) x).target ∩
          (chartAt (E (k + 2)) x).symm ⁻¹'
            ((chartAt (E (k + 2)) x).source ∩ V) := by
  let e := chartAt (E (k + 2)) x
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' (e.source ∩ V)) :=
    e.isOpen_inter_preimage_symm (e.open_source.inter hV)
  have hea : e a ∈ e.target ∩ e.symm ⁻¹' (e.source ∩ V) := by
    refine ⟨e.mapsTo ha, ?_⟩
    simpa [e.left_inv ha] using And.intro ha haV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW (e a) hea
  refine ⟨ε / 2, half_pos hε, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_cover
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (V : Set M) (hV : IsOpen V) (hAV : A ⊆ V) :
    ∃ (s : Finset M) (K : M → Set M),
      (∀ a, IsCompact (K a)) ∧ (∀ a, K a ⊆ (chartAt (E (k + 2)) x).source) ∧
      (∀ a, Convex ℝ ((chartAt (E (k + 2)) x) '' K a)) ∧ (∀ a, K a ⊆ V) ∧
      (∀ a ∈ s, (K a ∩ A).Nonempty) ∧ A ⊆ ⋃ a ∈ s, K a := by
  classical
  let e := chartAt (E (k + 2)) x
  have hex : ∀ a : M, ∃ r : ℝ, a ∈ A → 0 < r ∧
      Metric.closedBall (e a) r ⊆ e.target ∩ e.symm ⁻¹' (e.source ∩ V) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨r, hr, hball⟩ :=
        punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_cover_aux_radius k
          M x a (hsub ha) V hV (hAV ha)
      exact ⟨r, fun _ => ⟨hr, hball⟩⟩
    · exact ⟨1, fun h => (ha h).elim⟩
  choose r hr using hex
  let K : M → Set M := fun a => if a ∈ A then e.symm '' Metric.closedBall (e a) (r a) else ∅
  have hnhds : ∀ a ∈ A, K a ∈ nhds a := by
    intro a ha
    rw [show K a = e.source ∩ e ⁻¹' Metric.closedBall (e a) (r a) by
      simp only [K, if_pos ha]
      exact e.symm_image_eq_source_inter_preimage (fun z hz => (hr a ha).2 hz |>.1)]
    exact Filter.inter_mem (e.open_source.mem_nhds (hsub ha))
      (e.continuousAt (hsub ha) (Metric.closedBall_mem_nhds _ (hr a ha).1))
  obtain ⟨s, hsA, hcov⟩ := hA.elim_nhds_subcover K hnhds
  refine ⟨s, K, ?_, ?_, ?_, ?_, ?_, hcov⟩
  · intro a
    by_cases ha : a ∈ A
    · simp only [K, if_pos ha]
      exact (isCompact_closedBall _ _).image_of_continuousOn
        (e.continuousOn_symm.mono (fun z hz => (hr a ha).2 hz |>.1))
    · simp [K, ha]
  · intro a
    by_cases ha : a ∈ A
    · simp only [K, if_pos ha]
      rintro z ⟨y, hy, rfl⟩
      exact e.symm_mapsTo ((hr a ha).2 hy).1
    · simp [K, ha]
  · intro a
    by_cases ha : a ∈ A
    · simp only [K, if_pos ha]
      change Convex ℝ (e '' (e.symm '' Metric.closedBall (e a) (r a)))
      rw [show (e : M → E (k + 2)) =
        (e.toPartialEquiv : M → E (k + 2)) from rfl]
      rw [show (e.symm : E (k + 2) → M) =
        (e.toPartialEquiv.symm : E (k + 2) → M) from rfl]
      have heq := e.toPartialEquiv.image_symm_image_of_subset_target
        (fun z hz => (hr a ha).2 hz |>.1)
      exact Eq.mpr (congrArg (Convex ℝ) heq) (convex_closedBall _ _)
    · simp only [K, if_neg ha, Set.image_empty]
      exact convex_empty
  · intro a
    by_cases ha : a ∈ A
    · simp only [K, if_pos ha]
      rintro z ⟨y, hy, rfl⟩
      exact ((hr a ha).2 hy).2.2
    · simp [K, ha]
  · intro a has
    have ha := hsA a has
    refine ⟨a, ?_, ha⟩
    simp only [K, if_pos ha]
    refine ⟨e a, Metric.mem_closedBall_self (le_of_lt (hr a ha).1), ?_⟩
    exact e.left_inv (hsub ha)

/- LIBRARY LEAF (Hatcher 3.27, step 2; split from `_aux_inChart` after
lemma-3's PARTIAL, 2026-10-21): a finite union of compact sets in one chart
source, each with convex chart image, is good.  Route: `Finset.induction_on`
over `s`, generalized over the family.  The empty union is
`_aux_convex_aux_empty`.  For `insert a s`: the union is `K a ∪ L` with
`L = ⋃ j ∈ s, K j`; `K a` is good by `_aux_convex`, `L` by induction, and
`K a ∩ L = ⋃ j ∈ s, (K a ∩ K j)` by induction applied to the family
`fun j => K a ∩ K j` (compact; its chart image is `chart '' K a ∩ chart '' K j`
because the chart is injective on the source, `Set.InjOn.image_inter`, hence
convex).  Conclude with `_aux_union` (compact sets are closed in a T2 space;
`Finset.isCompact_biUnion`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_finite
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) {ι : Type} (K : ι → Set M) (hK : ∀ j, IsCompact (K j))
    (hsub : ∀ j, K j ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : ∀ j, Convex ℝ ((chartAt (E (k + 2)) x) '' K j))
    (s : Finset ι) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M (⋃ j ∈ s, K j) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
      simpa using
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_empty k M)
  | @insert a s ha ih =>
      have gKa :=
        punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex k
          M x (K a) (hK a) (hsub a) (hconv a)
      have gL := ih K hK hsub hconv
      have hKi : ∀ j, IsCompact (K a ∩ K j) := fun j => (hK a).inter (hK j)
      have hKis : ∀ j, K a ∩ K j ⊆
          (chartAt (E (k + 2)) x).source := fun j =>
        (Set.inter_subset_left.trans (hsub a))
      have hKic : ∀ j, Convex ℝ
          ((chartAt (E (k + 2)) x) '' (K a ∩ K j)) := by
        intro j
        rw [(chartAt (E (k + 2)) x).injOn.image_inter
          (hsub a) (hsub j)]
        exact (hconv a).inter (hconv j)
      have gI := ih (fun j => K a ∩ K j) hKi hKis hKic
      have hLcompact : IsCompact (⋃ j ∈ s, K j) :=
        s.isCompact_biUnion (fun j _ => hK j)
      have hIeq : K a ∩ (⋃ j ∈ s, K j) = ⋃ j ∈ s, (K a ∩ K j) := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        aesop
      have hUeq : (⋃ j ∈ insert a s, K j) = K a ∪ (⋃ j ∈ s, K j) := by
        ext y
        simp [ha]
      rw [hUeq]
      apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union k
        M (K a) (⋃ j ∈ s, K j) (hK a).isClosed hLcompact.isClosed gKa gL
      rw [hIeq]
      exact gI

/- PROVED from `_aux_inChart_aux_lift`, `_aux_inChart_aux_cover`,
`_aux_inChart_aux_finite`, `_aux_convex_aux_inj` (Hatcher 3.27, step 3;
claude-14's split of lemma-3's PARTIAL, 2026-10-21): every compact subset of
one chart source is good.  A class `c` of `H_i(M|A)` (`i ≥ 3`) lifts to `d` in
`H_i(M|L)`, `L` a finite union of convex chart balls meeting `A`.  For
`i > 3`, `d = 0` since `L` is good.  For `i = 3` and `y ∈ K a ⊆ L`, with
`b ∈ K a ∩ A`: the image of `d` in `H₃(M|K a)` maps to the image of `c` at `b`,
which is `0`, so it is `0` (`_aux_convex_aux_inj`), so `d` vanishes at `y`;
hence `d = 0` and `c = 0`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M A := by
  have key : ∀ (i : ℕ) (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i),
      k + 2 ≤ i → (∀ (hi : i = k + 2) (y : M) (hy : y ∈ A),
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i c = 0) → c = 0 := by
    intro i c hi3 hc
    obtain ⟨V, hV, hAV, hlift⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift k M A i c
    obtain ⟨s, K, hKc, hKs, hKconv, hKV, hKA, hcov⟩ :=
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_cover k M x A hA hsub V hV hAV
    have gL := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_finite k M x K hKc hKs hKconv s
    obtain ⟨d, rfl⟩ := hlift (⋃ a ∈ s, K a) hcov (Set.iUnion₂_subset fun a _ => hKV a)
    suffices hd : d = 0 by rw [hd, map_zero]
    rcases hi3.lt_or_eq with hlt | rfl
    · exact @Subsingleton.elim _ (gL.1 i hlt) d 0
    refine gL.2 d fun y hy => ?_
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨b, hbK, hbA⟩ := hKA a ha
    have hKL : K a ⊆ ⋃ a ∈ s, K a := Set.subset_biUnion_of_mem ha
    have hLK : Set.MapsTo (ContinuousMap.id M) (⋃ a ∈ s, K a)ᶜ (K a)ᶜ :=
      fun z hz => Set.compl_subset_compl.mpr hKL hz
    have hdK : HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap _ _ (ContinuousMap.id M) hLK) (k + 2) d = 0 := by
      refine punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj k M x (K a) (hKc a) (hKs a) (hKconv a) b hbK (k + 2) (by omega) _ ?_
      rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hLK _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ b (hKL hbK)),
        ← punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ Aᶜ _ (fun z hz => Set.compl_subset_compl.mpr hcov hz) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A b hbA)]
      exact hc rfl b hbA
    rw [← punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hLK (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (K a) y hya), hdK, map_zero]
  refine ⟨fun i hi => ⟨fun c d => (key i c hi.le (fun h => absurd h (by omega))).trans (key i d hi.le (fun h => absurd h (by omega))).symm⟩,
    fun c hc => key (k + 2) c le_rfl fun _ => hc⟩

/-- PROVED from `_aux_union`, `_aux_inChart` and `_aux_convex_aux_empty` (Hatcher 3.27,
step 4; ported from t00A01 by claude-14, 2026-10-22): every compact `A ⊆ M` is good.
Route: cover `A` by finitely many compact `K_j`, each inside a chart source
(closed chart balls; `M` is locally compact).  Write `A = A₁ ∪ ⋯ ∪ A_m` with
`A_j = A ∩ K_j` and induct on `m` using `_aux_union`: `A_m` and
`(A₁ ∪ ⋯ ∪ A_{m-1}) ∩ A_m` are compact subsets of the chart source of `K_m`,
so both are good by `_aux_inChart`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_compact
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (A : Set M) (hA : IsCompact A) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M A := by
  classical
  letI := ChartedSpace.locallyCompactSpace (E (k + 2)) M
  choose K hK using fun x : M =>
    (isCompact_isClosed_basis_nhds x).mem_iff.mp
      (chart_source_mem_nhds (E (k + 2)) x)
  have hKn (x : M) : K x ∈ nhds x := (hK x).1.1
  have hKc (x : M) : IsCompact (K x) := (hK x).1.2.1
  have hKcl (x : M) : IsClosed (K x) := (hK x).1.2.2
  have hKs (x : M) : K x ⊆ (chartAt (E (k + 2)) x).source :=
    (hK x).2
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : M => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => Set.mem_iUnion.mpr
      ⟨x, mem_interior_iff_mem_nhds.mpr (hKn x)⟩)
  have hfinite : ∀ t : Finset M,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M
        (⋃ x ∈ t, A ∩ K x) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_empty k M)
    | @insert x t hxt ih =>
        rw [Finset.set_biUnion_insert]
        apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union
        · exact (hA.inter_right (hKcl x)).isClosed
        · exact isClosed_biUnion_finset fun y _ => (hA.inter_right (hKcl y)).isClosed
        · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart
            k M x (A ∩ K x) (hA.inter_right (hKcl x))
            (fun _ hz => hKs x hz.2)
        · exact ih
        · apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart
          · exact (hA.inter_right (hKcl x)).inter_right
              (t.finite_toSet.isCompact_biUnion fun y _ => hA.inter_right (hKcl y)).isClosed
          · intro _ hz
            exact hKs x hz.1.2
  have hEq : (⋃ x ∈ s, A ∩ K x) = A := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun x _ => inter_subset_left
    · intro x hx
      obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion₂.mpr ⟨y, hyS, hx, interior_subset hxy⟩
  rw [← hEq]
  exact hfinite s


/-- PROVED from `_aux_compact` with `A = M`, `_aux_univ` and `_aux_factor`
(claude-14, 2026-10-22, ported from t00A01).  Was a LEAF split by claude-14 from lemma-3's PARTIAL on
`_exists_unit`: Hatcher Lemma 3.27(b) with `A = M`.  A class of `H_(k+2)(M)`
whose image in every `H_(k+2)(M, M ∖ y)` vanishes is zero.  Template: t00A01's
sorry-free dimension-3 `apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective` (through its `_aux_compact` with
`A = M`, `_aux_univ`, `_aux_factor`); generalize `Fin 3` to `k + 2`.  Second
countability is not an instance here: derive it from compactness and the
charts if the template needs it.  Do not go through `localizationMap x (k + 2)`
being an iso (that is downstream of this lemma). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (z : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2))
    (hz : ∀ y : M, ManifoldFundamentalClass.localizationMap y (k + 2) z = 0) :
    z = 0 := by
  set f := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      (Set.univ : Set M)ᶜ) (k + 2)
  haveI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ M (k + 2)
  have hc : f z = 0 := by
    refine (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_compact k M Set.univ isCompact_univ).2 _ fun y hy => ?_
    rw [← ConcreteCategory.comp_apply, ← punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y hy (k + 2)]
    exact hz y
  calc z = inv f (f z) := by
        rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    _ = 0 := by rw [hc, map_zero]

section exists_unit_aux_divide

/-- PROVED (lemma-2, banked from its `_aux_divide` PARTIAL, 2026-10-20): at
each point the local image of `z` is `m` times a signed normalized local
generator. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_local
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology (k + 2)) (m : ℤ)
    (hz : ∀ y : M,
      ((ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization k y).hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y (k + 2) z)).natAbs =
        m.natAbs) :
    ∀ y : M, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      m • (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization k y).inv.hom e =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y (k + 2) z := by
  intro y
  let N := ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization k y
  have hsign : N.hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y (k + 2) z) = m ∨
      N.hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y (k + 2) z) = -m :=
    Int.natAbs_eq_natAbs_iff.mp (hz y)
  rcases hsign with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso N.hom).1
    have hinv : N.hom.hom (N.inv.hom (1 : ℤ)) = 1 :=
      ConcreteCategory.congr_hom N.inv_hom_id 1
    rw [map_zsmul, hinv, hpos]
    simp
  · refine ⟨-1, Or.inr rfl, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso N.hom).1
    have hinv : N.hom.hom (N.inv.hom (-1 : ℤ)) = -1 :=
      ConcreteCategory.congr_hom N.inv_hom_id (-1)
    rw [map_zsmul, hinv, hneg]
    simp

/-- `A` admits division by `m` (existence half of Hatcher Lemma 3.27, integer
coefficients): a class of `H_(k+2)(M, M ∖ A)` whose image in `H_(k+2)(M, M ∖ y)` is
divisible by `m` at every `y ∈ A` has the same local images as `m • μ` for one
class `μ` of `H_(k+2)(M, M ∖ A)`.  Split from `_aux_divide` after lemma-2's PARTIAL
(2026-10-20).  Stated without a section of the orientation cover: the
divisibility hypothesis replaces it. -/
def punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good (k : ℕ) (M : Type) [TopologicalSpace M] (m : ℤ) (A : Set M) : Prop :=
  ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology (k + 2),
    (∀ (y : M) (hy : y ∈ A), ∃ g, m • g =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2) c) →
      ∃ μ : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology (k + 2),
        ∀ (y : M) (hy : y ∈ A), m •
          HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2) μ =
          HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2) c

/-- PROVED (lemma-3, banked from its `_aux_divide_aux_union` PARTIAL,
2026-10-20): restrict `c` to `A` and to `B` and divide there. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_restrict
    (k : ℕ) (M : Type) [TopologicalSpace M] (m : ℤ) (A B : Set M)
    (gA : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m A)
    (gB : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m B)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (A ∪ B)ᶜ).homology (k + 2))
    (hc : ∀ (y : M) (hy : y ∈ A ∪ B), ∃ g, m • g =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
          (ContinuousMap.id M)
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y hy)) (k + 2) c) :
    (∃ μA : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology (k + 2),
      ∀ (y : M) (hy : y ∈ A), m •
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2) μA =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2)
          (HomologicalComplex.homologyMap
            (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ
              (ContinuousMap.id M)
              (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) (k + 2) c)) ∧
    (∃ μB : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Bᶜ).homology (k + 2),
      ∀ (y : M) (hy : y ∈ B), m •
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)) (k + 2) μB =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)) (k + 2)
          (HomologicalComplex.homologyMap
            (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ
              (ContinuousMap.id M)
              (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) (k + 2) c)) := by
  constructor
  · apply gA
    intro y hy
    obtain ⟨g, hg⟩ := hc y (Or.inl hy)
    refine ⟨g, ?_⟩
    have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy)) (k + 2)
    exact hg.trans (by
      simpa only [ConcreteCategory.comp_apply] using
        (congrArg (fun f => f c) e).symm)
  · apply gB
    intro y hy
    obtain ⟨g, hg⟩ := hc y (Or.inr hy)
    refine ⟨g, ?_⟩
    have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Bᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy)) (k + 2)
    exact hg.trans (by
      simpa only [ConcreteCategory.comp_apply] using
        (congrArg (fun f => f c) e).symm)

/-- LIBRARY LEAF: `H_(k+2)(M, M ∖ y)` is torsion-free.  Split from `_aux_union` after
lemma-3's PARTIAL (2026-10-20).  Route: `ambientLocalNormalization k y` is an
isomorphism onto `ℤ` (see `_aux_divide_aux_local`); apply its `hom`, use
`map_zsmul`, cancel `m ≠ 0` in `ℤ`, and pull back by injectivity. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_torsion
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (y : M) (m : ℤ) (hm : m ≠ 0)
    (x : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology (k + 2)) (h : m • x = 0) : x = 0 := by
  let e := ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization k y
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have he : m • e.hom.hom x = 0 := by
    rw [← map_zsmul, h, map_zero]
  simpa using (eq_zero_or_eq_zero_of_smul_eq_zero he).resolve_left hm

/-- PROVED (lemma-3, banked from its `_aux_glue` PARTIAL, job 187, 2026-10-20):
middle exactness of the coefficient-subcomplex relative Mayer--Vietoris sequence for
the subspaces `Aᶜ`, `Bᶜ`.  `_aux_glue` still has to transport it to the literal
relative chains (`relativeSingularMap`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_exact
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) (n + 1))
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.piecesToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) (n + 1))
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.relative_arrows_zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact
    ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence.exact_intersection_pieces_union
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ) n

/-- PROVED (lemma-3, banked from its third `_aux_glue` PARTIAL, job 189, 2026-10-20):
`_aux_glue_aux_exact` at every degree `n`, `0` included, from `homology_exact₂` of the
degreewise short exact sequence. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_exact_degree
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n)
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.piecesToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.relative_arrows_zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact
    (ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact.shortComplex_shortExact
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)).homology_exact₂ n

/-- LIBRARY LEAF (split by claude-14 from `_aux_glue` after lemma-3's third PARTIAL,
job 189, 2026-10-20): naturality of the comparison isomorphisms for the intersection
arrows.  Write `Φ_S` for `forget (rangeRelativeIso ℤ S n).hom ≫
integralRelativeHomologyComparison S n` (range-subcomplex relative homology →
literal `H_n(M, S)`), and `Φ_∩` for the same through `intersectionRelativeIso`.
Then `intersectionToLeftRelative` / `…ToRightRelative` become the
`relativeSingularMap`s `(M, S ∩ T) → (M, S)` / `(M, S ∩ T) → (M, T)`.  Route: every
map is a `cokernel.map` of chain maps induced by inclusions; check the square on
chains after `cokernel.π` (epi), using `ambientSubspaceRangeChainsIso_hom_comp_subspaceMap`,
`integralRelativeChainsComparison`'s definition and
`coefficientRelativeProjection_mapHomologyIso_naturality` for the forgetful step. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_comparison
    (M : Type) [TopologicalSpace M] (A : Set M) (n : ℕ) :
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n).hom =
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport A n).hom := by
  have ht :
      (ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport A).hom =
        𝟙 _ := by
    apply (cancel_epi (cokernel.π
      ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)))).1
    rw [ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport_projection]
    rfl
  have hc :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison A).hom =
        (ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport A).hom := by
    unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison
    unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport
    dsimp
    rw [ht]
    exact Category.assoc _ _ _
  unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison
  unfold ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
  dsimp
  rw [hc]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_left_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
        ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ (S ∩ T) S (ContinuousMap.id M)
        (fun _ hx => hx.1) := by
  apply (cancel_epi (cokernel.π
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange T)))).1
  rw [← Category.assoc,
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToLeftRelative_projection]
  have hrange :
      cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ S) := by
    exact cokernel.π_desc _ _ _
  rw [hrange]
  have hinter :
      cokernel.π
          (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
            (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∩ T)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  rw [← Category.assoc, hinter]
  have hproj := ConstructionTargets.CoefficientRadialPair.projection ℤ (S ∩ T) S
    (ContinuousMap.id M) (fun _ hx => hx.1)
  rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at hproj
  exact hproj.symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_right_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
        ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ (S ∩ T) T (ContinuousMap.id M)
        (fun _ hx => hx.2) := by
  apply (cancel_epi (cokernel.π
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange T)))).1
  rw [← Category.assoc,
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToRightRelative_projection]
  have hrange :
      cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ T) := by
    exact cokernel.π_desc _ _ _
  rw [hrange]
  have hinter :
      cokernel.π
          (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient ℤ
            (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∩ T)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  rw [← Category.assoc, hinter]
  have hproj := ConstructionTargets.CoefficientRadialPair.projection ℤ (S ∩ T) T
    (ContinuousMap.id M) (fun _ hx => hx.2)
  rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at hproj
  exact hproj.symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter
    (M : Type) [TopologicalSpace M] (S T : Set M) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (S ∩ T) S (ContinuousMap.id M)
          (fun _ hx => hx.1)) n ∧
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (S ∩ T) T (ContinuousMap.id M)
          (fun _ hx => hx.2)) n := by
  have hleft := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_left_chain M S T)
  have hleft' := congrArg
    (fun f => ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map f) hleft
  simp only [HomologicalComplex.homologyMap_comp, Functor.map_comp] at hleft'
  have hright := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_right_chain M S T)
  have hright' := congrArg
    (fun f => ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map f) hright
  simp only [HomologicalComplex.homologyMap_comp, Functor.map_comp] at hright'
  have hS :
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S) n := rfl
  have hT :
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T) n := rfl
  have hI :
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap ℤ S T) n := rfl
  constructor
  · rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_comparison M S n,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_comparison M (S ∩ T) n]
    rw [hS, hI]
    rw [← Category.assoc]
    rw [hleft']
    rw [Category.assoc]
    rw [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality]
    rw [← Category.assoc]
  · rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_comparison M T n,
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter_aux_comparison M (S ∩ T) n]
    rw [hT, hI]
    rw [← Category.assoc]
    refine (congrArg (fun q => q ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport T n).hom)
        hright').trans ?_
    rw [Category.assoc]
    rw [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality]
    rw [← Category.assoc]

/-- LIBRARY LEAF (split by claude-14 from `_aux_glue` after lemma-3's third PARTIAL,
job 189, 2026-10-20): the same naturality for the union arrows, with
`relativeComparisonIso ℤ S T hS hT n` (generated union `P S ⊔ P T` → literal `S ∪ T`,
needs `S`, `T` open) on the target.  `leftToUnionRelative` / `rightToUnionRelative`
become the `relativeSingularMap`s `(M, S) → (M, S ∪ T)` / `(M, T) → (M, S ∪ T)`.  Route as
for `_aux_sq_inter`; `relativeComparisonIso_hom` unfolds the target iso to a
`cokernel.map`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_transport
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport A).hom = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).1
  simp [ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport]
  exact (Category.comp_id _).symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n =
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport A n := by
  have hc : ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison A =
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport A := by
    ext1
    simp [ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison,
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport, punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_transport]
    exact (Category.id_comp _).symm
  simp only [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison,
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport, hc]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_left_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion ℤ S T)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∪ T))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction ℤ S T)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square ℤ S T) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ S (S ∪ T)
        (ContinuousMap.id M) (fun _ hx => Or.inl hx) := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap ℤ (ContinuousMap.id M) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains ℤ).map
      (TopCat.toSSet.map (𝟙 (TopCat.of M))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_right_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion ℤ S T)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∪ T))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction ℤ S T)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square ℤ S T) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ T (S ∪ T)
        (ContinuousMap.id M) (fun _ hx => Or.inr hx) := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap ℤ (ContinuousMap.id M) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains ℤ).map
      (TopCat.toSSet.map (𝟙 (TopCat.of M))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (f : C(X, X)) (hf : Set.MapsTo f A B) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap ℤ A B f hf) n) ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison B n).hom =
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap A B f hf) n := by
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq, punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq]
  exact ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality A B f hf n

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union
    (M : Type) [TopologicalSpace M] (S T : Set M) (hS : IsOpen S) (hT : IsOpen T) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ S T hS hT n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∪ T) n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap S (S ∪ T) (ContinuousMap.id M)
          (fun _ hx => Or.inl hx)) n ∧
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ S T hS hT n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∪ T) n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap T (S ∪ T) (ContinuousMap.id M)
          (fun _ hx => Or.inr hx)) n := by
  constructor
  · rw [ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso_hom]
    rw [← Category.assoc, ← Functor.map_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_left_chain]
    erw [HomologicalComplex.homologyMap_comp]
    erw [Functor.map_comp]
    have h := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality S (S ∪ T) (ContinuousMap.id M)
      (fun _ hx => Or.inl hx) n
    exact (congrArg (fun q =>
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S) n) ≫ q)
      h).trans (Category.assoc _ _ _).symm
  · rw [ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso_hom]
    rw [← Category.assoc, ← Functor.map_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_right_chain]
    erw [HomologicalComplex.homologyMap_comp]
    erw [Functor.map_comp]
    have h := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality T (S ∪ T) (ContinuousMap.id M)
      (fun _ hx => Or.inr hx) n
    exact (congrArg (fun q =>
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T) n) ≫ q)
      h).trans (Category.assoc _ _ _).symm

open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
  ConstructionTargets.SingularExcision in

/-- PROVED (claude-14, after lemma-3's fourth `_aux_glue` PARTIAL, job 201, 2026-10-21):
the existence half of relative Mayer--Vietoris in the subcomplex model.  Classes of
`C(M)/C(P)` and `C(M)/C(Q)` with equal images in `C(M)/C(P ⊔ Q)` come from one class of
`C(M)/C(P ⊓ Q)`; from `homology_exact₂` of the degreewise short exact sequence. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_model
    (M : Type) [TopologicalSpace M] (S T : Set M) (n : ℕ)
    (y₁ : (cokernel (leftAmbient ℤ (ambientSubspaceRange S))).homology n)
    (y₂ : (cokernel (rightAmbient ℤ (ambientSubspaceRange T))).homology n)
    (h : HomologicalComplex.homologyMap
        (leftToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n y₁ =
      HomologicalComplex.homologyMap
        (rightToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n y₂) :
    ∃ x, HomologicalComplex.homologyMap
        (intersectionToLeftRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n x = y₁ ∧
      HomologicalComplex.homologyMap
        (intersectionToRightRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n x = y₂ := by
  have hex : (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (intersectionToPiecesRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n)
      (HomologicalComplex.homologyMap
        (piecesToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.relative_arrows_zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
    (ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact.shortComplex_shortExact
      ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)).homology_exact₂ n
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have e₁ : HomologicalComplex.homologyMap (biprod.inl : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (piecesToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n =
      HomologicalComplex.homologyMap (leftToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n := by
    rw [← HomologicalComplex.homologyMap_comp, piecesToUnionRelative, biprod.inl_desc]
  have e₂ : HomologicalComplex.homologyMap (biprod.inr : cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (piecesToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n =
      -HomologicalComplex.homologyMap (rightToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n := by
    rw [← HomologicalComplex.homologyMap_comp, piecesToUnionRelative, biprod.inr_desc,
      HomologicalComplex.homologyMap_neg]
  have f₁ : HomologicalComplex.homologyMap (intersectionToPiecesRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n ≫ HomologicalComplex.homologyMap (biprod.fst : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S))) n =
      HomologicalComplex.homologyMap (intersectionToLeftRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n := by
    rw [← HomologicalComplex.homologyMap_comp, intersectionToPiecesRelative, biprod.lift_fst]
  have f₂ : HomologicalComplex.homologyMap (intersectionToPiecesRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n ≫ HomologicalComplex.homologyMap (biprod.snd : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n =
      HomologicalComplex.homologyMap (intersectionToRightRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n := by
    rw [← HomologicalComplex.homologyMap_comp, intersectionToPiecesRelative, biprod.lift_snd]
  have g₁ : HomologicalComplex.homologyMap (biprod.inl : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (biprod.fst : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S))) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  have g₂ : HomologicalComplex.homologyMap (biprod.inr : cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (biprod.fst : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S))) n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inr_fst, HomologicalComplex.homologyMap_zero]
  have g₃ : HomologicalComplex.homologyMap (biprod.inl : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (biprod.snd : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inl_snd, HomologicalComplex.homologyMap_zero]
  have g₄ : HomologicalComplex.homologyMap (biprod.inr : cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n ≫ HomologicalComplex.homologyMap (biprod.snd : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inr_snd, HomologicalComplex.homologyMap_id]
  obtain ⟨x, hx⟩ := hex (HomologicalComplex.homologyMap (biprod.inl : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n y₁ + HomologicalComplex.homologyMap (biprod.inr : cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n y₂) (by
    change HomologicalComplex.homologyMap (piecesToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n (HomologicalComplex.homologyMap (biprod.inl : cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n y₁ + HomologicalComplex.homologyMap (biprod.inr : cokernel (rightAmbient ℤ (ambientSubspaceRange T)) ⟶ cokernel (leftAmbient ℤ (ambientSubspaceRange S)) ⊞ cokernel (rightAmbient ℤ (ambientSubspaceRange T))) n y₂) = 0
    rw [map_add, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, e₁, e₂, h]
    simp)
  change HomologicalComplex.homologyMap (intersectionToPiecesRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n x = _ at hx
  refine ⟨x, ?_, ?_⟩
  · rw [← f₁, CategoryTheory.comp_apply, hx, map_add, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, g₁, g₂]
    simp
  · rw [← f₂, CategoryTheory.comp_apply, hx, map_add, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, g₃, g₄]
    simp

open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
  ConstructionTargets.SingularExcision ConstructionTargets.IntegralSingularHomologyComparison in

/-- PROVED (claude-14, after lemma-3's fourth `_aux_glue` PARTIAL, job 201, 2026-10-21):
`_aux_model` carried to the literal relative chains, for open `S`, `T` and any sets
`Z = S ∩ T`, `W = S ∪ T` (so that `_aux_glue` can take `Z = (A ∪ B)ᶜ`, `W = (A ∩ B)ᶜ`
without casts: `subst`, then the `MapsTo` proofs agree by proof irrelevance).  Pull
`μS`, `μT` back along the comparison isomorphisms, move `h` to the model by
`_aux_sq_union` (the union comparison is injective), lift by `_aux_model`, and push the
lift forward by `_aux_sq_inter`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_transport
    (M : Type) [TopologicalSpace M] (S T Z W : Set M) (hS : IsOpen S) (hT : IsOpen T)
    (hZ : Z = S ∩ T) (hW : W = S ∪ T) (n : ℕ)
    (hSW : Set.MapsTo (ContinuousMap.id M) S W) (hTW : Set.MapsTo (ContinuousMap.id M) T W)
    (hZS : Set.MapsTo (ContinuousMap.id M) Z S) (hZT : Set.MapsTo (ContinuousMap.id M) Z T)
    (μS : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains S).homology n)
    (μT : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains T).homology n)
    (h : HomologicalComplex.homologyMap (relativeSingularMap S W (ContinuousMap.id M) hSW) n μS =
      HomologicalComplex.homologyMap (relativeSingularMap T W (ContinuousMap.id M) hTW) n μT) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Z).homology n,
      HomologicalComplex.homologyMap (relativeSingularMap Z S (ContinuousMap.id M) hZS) n μ = μS ∧
      HomologicalComplex.homologyMap (relativeSingularMap Z T (ContinuousMap.id M) hZT) n μ = μT := by
  subst hZ hW
  let ΦS := forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n
  let ΦT := forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n
  let Φi := forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n
  let Ψ := forgetIntModules.mapIso
      (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ S T hS hT n) ≪≫
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∪ T) n
  obtain ⟨u₁, u₂⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union M S T hS hT n
  obtain ⟨v₁, v₂⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter M S T n
  have hl : Ψ.hom (forgetIntModules.map (HomologicalComplex.homologyMap (leftToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n) (ΦS.inv μS)) =
      HomologicalComplex.homologyMap (relativeSingularMap S (S ∪ T) (ContinuousMap.id M) hSW) n μS := by
    have := ConcreteCategory.congr_hom u₁ (ΦS.inv μS)
    change _ = HomologicalComplex.homologyMap (relativeSingularMap S (S ∪ T) (ContinuousMap.id M) hSW) n (ΦS.hom (ΦS.inv μS)) at this
    rwa [Iso.inv_hom_id_apply] at this
  have hr : Ψ.hom (forgetIntModules.map (HomologicalComplex.homologyMap (rightToUnionRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n) (ΦT.inv μT)) =
      HomologicalComplex.homologyMap (relativeSingularMap T (S ∪ T) (ContinuousMap.id M) hTW) n μT := by
    have := ConcreteCategory.congr_hom u₂ (ΦT.inv μT)
    change _ = HomologicalComplex.homologyMap (relativeSingularMap T (S ∪ T) (ContinuousMap.id M) hTW) n (ΦT.hom (ΦT.inv μT)) at this
    rwa [Iso.inv_hom_id_apply] at this
  have hm := congrArg Ψ.inv (hl.trans (h.trans hr.symm))
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at hm
  obtain ⟨x, hx₁, hx₂⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_model M S T n (ΦS.inv μS) (ΦT.inv μT) hm
  refine ⟨Φi.hom x, ?_, ?_⟩
  · have := ConcreteCategory.congr_hom v₁ x
    change ΦS.hom (forgetIntModules.map (HomologicalComplex.homologyMap (intersectionToLeftRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n) x) =
      HomologicalComplex.homologyMap (relativeSingularMap (S ∩ T) S (ContinuousMap.id M) hZS) n (Φi.hom x) at this
    rw [← this]
    change ΦS.hom (HomologicalComplex.homologyMap (intersectionToLeftRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n x) = μS
    rw [hx₁, Iso.inv_hom_id_apply]
  · have := ConcreteCategory.congr_hom v₂ x
    change ΦT.hom (forgetIntModules.map (HomologicalComplex.homologyMap (intersectionToRightRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n) x) =
      HomologicalComplex.homologyMap (relativeSingularMap (S ∩ T) T (ContinuousMap.id M) hZT) n (Φi.hom x) at this
    rw [← this]
    change ΦT.hom (HomologicalComplex.homologyMap (intersectionToRightRelative ℤ (ambientSubspaceRange S) (ambientSubspaceRange T)) n x) = μT
    rw [hx₂, Iso.inv_hom_id_apply]

/-- PROVED (claude-14 from `_aux_transport`, 2026-10-21; Hatcher 3.27, relative Mayer--Vietoris, existence half): for
closed `A`, `B`, classes of `H_n(M, M ∖ A)` and `H_n(M, M ∖ B)` with the same
image in `H_n(M, M ∖ (A ∩ B))` come from one class of `H_n(M, M ∖ (A ∪ B))`.
Split from `_aux_union` after lemma-3's PARTIAL (2026-10-20).  Route: exactness
of the same relative Mayer--Vietoris sequence as `_aux_injective_aux_union_aux_joint`,
at the middle term `H_n(S, P ∩ Q) → H_n(S, P) ⊕ H_n(S, Q) → H_n(S, P ∪ Q)`
(`CoefficientSubcomplexRelativeHomologySequence`; transport to the literal
relative chains with `CoefficientSubcomplexRelativeLiteralComparison` and
`CoefficientCompactComplementUnionToRelative`).  The sign convention of the
difference map does not matter here: equality of the two images is the kernel
condition.  ASSEMBLY (claude-14's split after lemma-3's third PARTIAL, job 189):
apply `_aux_glue_aux_exact_degree` and transport through `_aux_glue_aux_sq_inter`,
`_aux_glue_aux_sq_union` with `S = Aᶜ`, `T = Bᶜ` (open by `hA.isOpen_compl`,
`hB.isOpen_compl`).  The squares are stated for `S ∩ T`, `S ∪ T`, while this lemma has
`(A ∪ B)ᶜ`, `(A ∩ B)ᶜ`: first prove the version for arbitrary sets `Z`, `W` with
`Z = Aᶜ ∩ Bᶜ`, `W = Aᶜ ∪ Bᶜ` and arbitrary `MapsTo` proofs, `subst`, then specialise
(`Set.compl_union`, `Set.compl_inter`).  The middle term is the homology of the
biproduct complex `cokernel (leftAmbient) ⊞ cokernel (rightAmbient)`; take its two
components with `biprod.fst`/`biprod.snd` (both commute with `homologyMap`). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (n : ℕ) (μA : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology n) (μB : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Bᶜ).homology n)
    (h : HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (A ∩ B)ᶜ (ContinuousMap.id M) (fun x hx hab => hx hab.1)) n μA =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ (A ∩ B)ᶜ (ContinuousMap.id M) (fun x hx hab => hx hab.2)) n μB) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology n,
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ (ContinuousMap.id M)
          (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) n μ = μA ∧
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ (ContinuousMap.id M)
          (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) n μ = μB := by
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_transport M Aᶜ Bᶜ (A ∪ B)ᶜ (A ∩ B)ᶜ hA.isOpen_compl hB.isOpen_compl
    (Set.compl_union A B) (Set.compl_inter A B) n _ _ _ _ μA μB h

/-- ASSEMBLY from `_aux_union_aux_restrict`, `_aux_torsion`, `_aux_glue` and
`gAB.2` (Hatcher 3.27(a), Mayer--Vietoris step): if closed `A`, `B`
admit division by `m ≠ 0` and `A ∩ B` is good in the sense of
`_aux_injective_aux_good`, then `A ∪ B` admits division by `m`.  Route:
restrict `c` to `H_(k+2)(M|A)`, `H_(k+2)(M|B)` (the local maps compose,
`relativeSingularMap_comp`) and divide there: `μ_A`, `μ_B`.  On `A ∩ B` the
difference `d` of their restrictions has `m • r_y d = 0`, so `r_y d = 0`
(`H_(k+2)(M|y) ≅ ℤ` by `ambientLocalNormalization k y`, torsion-free), so `d = 0`
by `gAB.2`.  Exactness of the relative Mayer--Vietoris sequence at
`H_(k+2)(M|A) ⊕ H_(k+2)(M|B)` (`CoefficientSubcomplexRelativeMayerVietoris*`) lifts
`(μ_A, μ_B)` to `μ ∈ H_(k+2)(M|A ∪ B)`, whose local images are those of `μ_A`
on `A` and of `μ_B` on `B`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (m : ℤ) (hm : m ≠ 0) (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (gA : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m A) (gB : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m B)
    (gAB : punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_good k M (A ∩ B)) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m (A ∪ B) := by
  intro c hc
  obtain ⟨⟨μA, hμA⟩, ⟨μB, hμB⟩⟩ :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_restrict
      k M m A B gA gB c hc
  let rA := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (A ∩ B)ᶜ
      (ContinuousMap.id M) (fun x hx hab => hx hab.1)) (k + 2)
  let rB := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ (A ∩ B)ᶜ
      (ContinuousMap.id M) (fun x hx hab => hx hab.2)) (k + 2)
  have hr : rA μA = rB μB := by
    apply sub_eq_zero.mp
    apply gAB.2 (rA μA - rB μB)
    intro y hy
    apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_torsion k M y m hm
    rw [map_sub, smul_sub]
    have hcompA := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      Aᶜ (A ∩ B)ᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx hab => hx hab.1)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∩ B) y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy.1) (k + 2)
    have hcompB := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      Bᶜ (A ∩ B)ᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx hab => hx hab.2)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∩ B) y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy.2) (k + 2)
    have eA := congrArg (fun f => f μA) hcompA
    have eB := congrArg (fun f => f μB) hcompB
    simp [rA, rB, ConcreteCategory.comp_apply] at eA eB
    rw [eA, eB, hμA y hy.1, hμB y hy.2]
    have ucompA := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Aᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy.1)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy.1)) (k + 2)
    have ucompB := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Bᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy.2)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy.2)) (k + 2)
    have euA := congrArg (fun f => f c) ucompA
    have euB := congrArg (fun f => f c) ucompB
    exact sub_eq_zero.mpr (by
      simpa only [ConcreteCategory.comp_apply] using euA.trans euB.symm)
  obtain ⟨μ, hμA', hμB'⟩ :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue
      M A B hA hB (k + 2) μA μB hr
  refine ⟨μ, ?_⟩
  intro y hy
  rcases hy with hy | hy
  · have hcomp := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Aᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy)) (k + 2)
    have eμ := congrArg (fun f => f μ) hcomp
    have ec := congrArg (fun f => f c) hcomp
    simp [ConcreteCategory.comp_apply] at eμ ec
    rw [← eμ, hμA', hμA y hy, ec]
  · have hcomp := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Bᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy)) (k + 2)
    have eμ := congrArg (fun f => f μ) hcomp
    have ec := congrArg (fun f => f c) hcomp
    simp [ConcreteCategory.comp_apply] at eμ ec
    rw [← eμ, hμB', hμB y hy, ec]

/-- LEAF (split by claude-14, 2026-10-22, after lemma-2's PARTIAL on `_divide`;
Hatcher 3.27(a), step 3): every compact subset of one chart source admits division
by `m ≠ 0`.  Template: t00A01's sorry-free
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_inChart`
(through `_aux_inChart_aux_finite`, `_aux_convex` and the `_aux_injective_aux_inChart_aux_{lift,cover,comp}`
and `_aux_injective_aux_convex_aux_inj_aux_isIso` helpers).  Those helpers are the
machinery of CCSH's `_aux_injective_aux_inChart` (a separate leaf); reuse them once
it lands.  Generalize `Fin 3` to `k + 2`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_isIso
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : Convex ℝ ((chartAt (E (k + 2)) x) '' A))
    (y : M) (hy : y ∈ A) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce k M x A hA hsub y hy (n + 1) hi
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model k _ (hA.image_of_continuousOn
      ((chartAt (E (k + 2)) x).continuousOn.mono hsub)) hconv _ (Set.mem_image_of_mem _ hy) n)

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_convex
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : Convex ℝ ((chartAt (E (k + 2)) x) '' A)) (m : ℤ) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m A := by
  intro c hc
  rcases A.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact ⟨0, by simp⟩
  obtain ⟨g, hg⟩ := hc y hy
  let f := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) (k + 2)
  letI : IsIso f := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_isIso k M x A hA hsub hconv y hy (k + 2) (by omega)
  obtain ⟨μ, hμ⟩ := (ConcreteCategory.bijective_of_isIso f).2 g
  refine ⟨μ, fun z hz => ?_⟩
  have heq : m • μ = c := by
    apply (ConcreteCategory.bijective_of_isIso f).1
    change f (m • μ) = f c
    rw [map_zsmul, hμ, hg]
  rw [← map_zsmul, heq]

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_finite
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) {ι : Type} (K : ι → Set M) (hK : ∀ j, IsCompact (K j))
    (hsub : ∀ j, K j ⊆ (chartAt (E (k + 2)) x).source)
    (hconv : ∀ j, Convex ℝ ((chartAt (E (k + 2)) x) '' K j))
    (m : ℤ) (hm : m ≠ 0) (s : Finset ι) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m (⋃ j ∈ s, K j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_convex k M x ∅ isCompact_empty (Set.empty_subset _)
      (by rw [Set.image_empty]; exact convex_empty) m
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union k M m hm _ _ (hK a).isClosed
      (s.isCompact_biUnion fun j _ => hK j).isClosed
    · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_convex k M x (K a) (hK a) (hsub a) (hconv a) m
    · exact ih
    · rw [Set.inter_iUnion₂]
      exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_finite k M x (fun j => K a ∩ K j)
        (fun j => (hK a).inter (hK j)) (fun j y hy => hsub a hy.1)
        (fun j => by
          rw [(chartAt (E (k + 2)) x).injOn.image_inter (hsub a) (hsub j)]
          exact (hconv a).inter (hconv j)) s

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (E (k + 2)) x).source)
    (m : ℤ) (hm : m ≠ 0) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m A := by
  intro c hc
  obtain ⟨V, hV, hAV, hlift⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_lift k M A (k + 2) c
  obtain ⟨s, K, hKc, hKs, hKconv, hKV, hKA, hcov⟩ :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_cover k M x A hA hsub V hV hAV
  have gL := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_finite k M x K hKc hKs hKconv m hm s
  have hAL : Set.MapsTo (ContinuousMap.id M) (⋃ a ∈ s, K a)ᶜ Aᶜ :=
    fun z hz => Set.compl_subset_compl.mpr hcov hz
  obtain ⟨d, hd⟩ := hlift (⋃ a ∈ s, K a) hcov (Set.iUnion₂_subset fun a _ => hKV a)
  obtain ⟨μL, hμL⟩ := gL d (by
    intro y hy
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨b, hbK, hbA⟩ := hKA a ha
    have hKL : K a ⊆ ⋃ a ∈ s, K a := Set.subset_biUnion_of_mem ha
    have hLK : Set.MapsTo (ContinuousMap.id M) (⋃ a ∈ s, K a)ᶜ (K a)ᶜ :=
      fun z hz => Set.compl_subset_compl.mpr hKL hz
    let fb := HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (K a)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint b)
        (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (K a) b hbK)) (k + 2)
    letI : IsIso fb := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart_aux_isIso k M x (K a) (hKc a) (hKs a) (hKconv a) b hbK (k + 2) (by omega)
    obtain ⟨g, hg⟩ := hc b hbA
    have hfb : fb (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap _ _ (ContinuousMap.id M) hLK) (k + 2) d) =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint b)
            (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A b hbA)) (k + 2) c := by
      rw [← hd]
      simp only [fb]
      rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hLK _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ b (hKL hbK)),
        punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hAL _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ b (hKL hbK))]
    have hdK : m • inv fb g = HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap _ _ (ContinuousMap.id M) hLK) (k + 2) d := by
      apply (ConcreteCategory.bijective_of_isIso fb).1
      rw [map_zsmul, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
        ConcreteCategory.id_apply, hg, hfb]
    refine ⟨HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (K a)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M) (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (K a) y hya)) (k + 2) (inv fb g), ?_⟩
    rw [← map_zsmul, hdK, punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hLK _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ y hy)])
  refine ⟨HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap _ _ (ContinuousMap.id M) hAL) (k + 2) μL,
    fun y hy => ?_⟩
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hAL _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ y (hcov hy)), hμL y (hcov hy), ← hd,
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart_aux_comp k M _ _ _ hAL _ (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo _ y (hcov hy))]

/-- LIBRARY LEAF (Hatcher 3.27(a), step 4): every compact `A ⊆ M` admits
division by `m ≠ 0`.  Route: the same finite chart cover and induction as
`_aux_injective_aux_compact`, with `_aux_union`, `_aux_inChart` and
`_aux_injective_aux_inChart` (for the intersections, which are compact
subsets of the last chart source). -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_compact
    (k : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (E (k + 2)) M]
    (A : Set M) (hA : IsCompact A) (m : ℤ) (hm : m ≠ 0) :
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good k M m A := by
  classical
  let U : M → Set M := fun x => (chartAt (E (k + 2)) x).source
  have hUopen : ∀ x, IsOpen (U x) := fun x => (chartAt (E (k + 2)) x).open_source
  have hAcov : A ⊆ ⋃ x, U x := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨y, mem_chart_source (E (k + 2)) y⟩
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U hUopen hAcov
  obtain ⟨K, hKcompact, hKsub, hAK⟩ := hA.finite_compact_cover s U
    (fun x _ => hUopen x) hs
  have key : ∀ (t : Finset M),
      punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_good
        k M m (⋃ x ∈ t, K x) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
        intro c hc
        exact ⟨0, fun y hy => (hy.elim)⟩
    | @insert x t hxt ih =>
        rw [Finset.set_biUnion_insert]
        have hLt : IsCompact (⋃ y ∈ t, K y) :=
          t.isCompact_biUnion (fun y _ => hKcompact y)
        apply punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union
          k M m hm (K x) (⋃ y ∈ t, K y) (hKcompact x).isClosed hLt.isClosed
        · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_inChart
            k M x (K x) (hKcompact x) (hKsub x) m hm
        · exact ih
        · exact punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_inChart
            k M x (K x ∩ ⋃ y ∈ t, K y) ((hKcompact x).inter hLt)
              (Set.inter_subset_left.trans (hKsub x))
  rw [hAK]
  exact key s

end exists_unit_aux_divide

/-- PROVED from `_aux_local`, `_aux_compact` with `A = M`, `_aux_univ` and `_aux_factor`
(claude-14, 2026-10-22, ported from t00A01 after lemma-2's PARTIAL; was a LEAF split
from lemma-3's PARTIAL on `_exists_unit`): Hatcher Lemma 3.27(a) with `A = M`.  If the local degree of
`z` has absolute value `|m| ≠ 0` at every point, then `z`'s local images are
all divisible by `m` through ONE global class.  Template: t00A01's sorry-free
dimension-3 `apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide` (through its `_aux_local`, `_aux_compact`,
`_aux_univ`, `_aux_factor`); generalize `Fin 3` / `k := 1` to `k + 2`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (z : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2))
    (m : ℤ) (hm : m ≠ 0)
    (hz : ∀ y : M,
      ((ManifoldFundamentalClass.ambientLocalNormalization k y).hom.hom
        (ManifoldFundamentalClass.localizationMap y (k + 2) z)).natAbs = m.natAbs) :
    ∃ μ : (SingularHomologyConcrete.SingularChains (TopCat.of M)).homology (k + 2),
      ∀ y : M, m • ManifoldFundamentalClass.localizationMap y (k + 2) μ =
        ManifoldFundamentalClass.localizationMap y (k + 2) z := by
  haveI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_univ M (k + 2)
  obtain ⟨μ', hμ'⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_compact k M Set.univ isCompact_univ m hm
    (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) (k + 2) z) fun y hy => by
    obtain ⟨e, -, he⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_local k M z m hz y
    refine ⟨_, he.trans ?_⟩
    rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y hy (k + 2), ConcreteCategory.comp_apply]
  refine ⟨inv (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) (k + 2)) μ', fun y => ?_⟩
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y (Set.mem_univ y) (k + 2), ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (inv _), IsIso.inv_hom_id,
    ConcreteCategory.id_apply]
  exact hμ' y (Set.mem_univ y)

/-- ASSEMBLED (claude-14, 2026-10-22) from `_aux_assembly`, `_aux_injective`,
`_aux_divide` and `_locallyConstant`.  Some point has local degree `±1`.  Template:
t00A01's sorry-free dimension-3
`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit`
(Hatcher 3.27 for compact `M`, through its `_aux_injective` and
`_aux_divide`).  Generalize from `Fin 3` / `k := 1` to `k + 2`.  Do not reduce
this to `_localization_mono` or `_coefficient_ne_zero`: both are assembled
from it. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) :
    ∃ y : M, (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e y).natAbs = 1 :=
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_assembly k M e
    (fun z hz => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective k M z hz)
    (fun z m hm hz => punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide k M z m hm hz)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant k M e)

/-- The localization coefficient of the global generator is nonzero: its
absolute value is the absolute local degree, which is locally constant, so
constant on connected `M`, and `1` somewhere. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (x : M) (q : ℤ)
    (hq : q • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
      ManifoldFundamentalClass.localizationMap x (k + 2)
        (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 2) e)) :
    q ≠ 0 := by
  obtain ⟨y, hy⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit k M e
  have hxy := (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant k M e).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec k e x q hq]
  intro h0
  rw [h0] at hxy
  simp at hxy
  omega

lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective
    (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M]
    (e : H n M ≅ ModuleCat.of ℤ ℤ) (x : M) :
    Function.Injective (fun r : ℤ ↦ r •
      ManifoldFundamentalClass.localizationMap x n
        (ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) n e)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
    refine ⟨n - 2, ?_⟩
    omega
  obtain ⟨q, hq⟩ :=
    ManifoldFundamentalClass.localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
      k e x
  exact
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_of_coefficient
      k e x q hq
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero
          k M e x q hq)

/-- LEAF (local fundamental class). On a closed connected `n`-manifold whose
top integral homology is `ℤ`, localizing at a point is injective in degree
`n`: `H_n M → H_n(M, M - x)`.  Sketch (Hatcher 3.26): `ManifoldFundamentalClass`
has the ingredients: `localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator`
writes the localized global generator as `r • ambientLocalGenerator x`,
`ambientLocalGenerator_zsmul_injective` makes `r ↦ r • _` injective, so it
remains to show `r ≠ 0` (a generator localizing to zero would make `H_n M`
vanish, by local constancy of the localized class along the connected `M`
and compactness).  Group-homology form, to match `localizationMap`. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono
    (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M]
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ)) (x : M) :
    Mono (ManifoldFundamentalClass.localizationMap x n) := by
  rcases htop with ⟨e⟩
  apply CategoryTheory.ConcreteCategory.mono_of_injective
  intro a b hab
  obtain ⟨r, rfl⟩ :=
    ManifoldFundamentalClass.groupGlobalGenerator_generates
      (TopCat.of M) n e a
  obtain ⟨s, rfl⟩ :=
    ManifoldFundamentalClass.groupGlobalGenerator_generates
      (TopCat.of M) n e b
  simp only [map_zsmul] at hab
  have hrs : r = s :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective
      n hn M e x hab
  rw [hrs]

/-- LEAF. The puncture inclusion followed by localization at the collar
center is zero: it factors through the self-relative homology of
`(M - x, M - x)`, which vanishes
(`SingularHomologyConcrete.selfRelativeSingularHomology_isZero`), using
`_aux_avoids_center` and `relativeSingularMap` naturality. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_localize_zero
    (n : ℕ) (M : Type) [TopologicalSpace M] (c : BallCollar n M) :
    HomologicalComplex.homologyMap
        (ManifoldFundamentalClass.absoluteSingularMap
          ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩) n ≫
      ManifoldFundamentalClass.localizationMap (c.smallMap (0 : Disk n 1)) n = 0 := by
  let f : C(c.Punctured, M) :=
    ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩
  let x : M := c.smallMap (0 : Disk n 1)
  have hf : Set.MapsTo f Set.univ
      (LocalHomologyNeighborhoodExcision.deletedPoint x) :=
    punctured_topHomology_zero_aux_map_eq_zero_aux_avoids_center n M c
  have hnaturality := ManifoldFundamentalClass.absoluteSingularMap_relativeProjection_naturality
    (Set.univ : Set c.Punctured)
    (LocalHomologyNeighborhoodExcision.deletedPoint x) f hf
  have hhom := congrArg (fun q => HomologicalComplex.homologyMap q n) hnaturality
  simp only [HomologicalComplex.homologyMap_comp] at hhom
  change HomologicalComplex.homologyMap
      (ManifoldFundamentalClass.absoluteSingularMap f) n ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
            (LocalHomologyNeighborhoodExcision.deletedPoint x)) n = 0
  rw [hhom]
  rw [(ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero
    c.Punctured n).eq_of_tgt
      (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
          (Set.univ : Set c.Punctured)) n) 0,
    zero_comp]

/-- LEAF (representation transport). If the puncture inclusion is zero on
concrete `AddCommGrpCat` singular homology, it is zero on `H` (module-valued
`singularHomologyFunctor`).  Sketch: the comparison isos of
`IntegralSingularHomologyComparison` are natural in the space. -/
lemma punctured_topHomology_zero_aux_map_eq_zero_aux_of_group_zero
    (n : ℕ) (M : Type) [TopologicalSpace M] (c : BallCollar n M)
    (h0 : HomologicalComplex.homologyMap
        (ManifoldFundamentalClass.absoluteSingularMap
          ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩) n = 0) :
    punctured_topHomology_zero_aux_inclusion n M c = 0 := by
  unfold punctured_topHomology_zero_aux_inclusion
  apply ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_injective
  apply (cancel_mono
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of M) n).hom).1
  rw [CategoryTheory.Functor.map_zero, zero_comp]
  calc
    _ = (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of c.Punctured) n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom
              ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩) :=
      ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
          (TopCat.ofHom
            ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩) n
    _ = 0 := by
      rw [show ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom
              ⟨fun z : c.Punctured ↦ z.1, continuous_subtype_val⟩) = 0 from h0,
        comp_zero]

/-- A top-dimensional cycle supported away from a nonempty collared ball has
zero image in the top homology of the connected closed manifold.  This is the
local-fundamental-class input. -/
theorem punctured_topHomology_zero_aux_map_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) :
    punctured_topHomology_zero_aux_inclusion n M c = 0 := by
  letI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono
    n hn M htop (c.smallMap (0 : Disk n 1))
  apply punctured_topHomology_zero_aux_map_eq_zero_aux_of_group_zero n M c
  rw [← cancel_mono (ManifoldFundamentalClass.localizationMap
    (c.smallMap (0 : Disk n 1)) n), zero_comp]
  exact punctured_topHomology_zero_aux_map_eq_zero_aux_localize_zero n M c

theorem punctured_topHomology_zero_aux_of_mono_eq_zero
    {X Y : ModuleCat ℤ} (f : X ⟶ Y) [Mono f] (hf : f = 0) : IsZero X := by
  exact IsZero.of_mono_eq_zero f hf

theorem punctured_topHomology_zero (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) : IsZero (H n c.Punctured) := by
  letI := punctured_topHomology_zero_aux_mono n hn M c hopen
  exact punctured_topHomology_zero_aux_of_mono_eq_zero
    (punctured_topHomology_zero_aux_inclusion n M c)
    (punctured_topHomology_zero_aux_map_eq_zero n hn M c htop hopen)

/-- **LIBRARY (B4b).** The local fundamental class makes the boundary sphere
null in top-minus-one homology of the punctured manifold. -/
lemma boundary_homology_zero_aux_connecting_factorization
    (n m : ℕ) (hnm : n = m + 1) (hm : 1 ≤ m) (M : Type) [TopologicalSpace M]
    (c : BallCollar n M) :
    let A : Set M :=
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
    ∃ j : (ConstructionTargets.SingularHomologyConcrete.SingularChains
          (TopCat.of (Sphere n))).homology m ⟶
        (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology (m + 1),
      j ≫ ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A m =
        HomologicalComplex.homologyMap
          (ManifoldFundamentalClass.absoluteSingularMap
            ⟨c.boundaryMap, c.continuous_boundaryMap⟩) m := by
  let A : Set M :=
    (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
  let B : Set (Disk n 1) := {y | dist y.1 0 < 1}ᶜ
  let f : C(Disk n 1, M) := ⟨c.smallMap, c.smallEmbedding.continuous⟩
  have hf : Set.MapsTo f B A := by
    intro x hx
    simp only [A, B, Set.mem_compl_iff, Set.mem_image]
    rintro ⟨y, hy, hxy⟩
    have hxeq : x = y := c.smallEmbedding.injective hxy.symm
    subst y
    exact hx hy
  have hg (s : Sphere n) : sphereToDisk n s ∈ B := by
    simp only [B, Set.mem_compl_iff, Set.mem_setOf_eq]
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    simpa [sphereToDisk, hs]
  let g : C(Sphere n, B) :=
    ⟨fun s => ⟨sphereToDisk n s, hg s⟩,
      (continuous_sphereToDisk n).subtype_mk (fun s => hg s)⟩
  letI : ContractibleSpace (Disk n 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let e := ConstructionTargets.T02A06DiskPairShift.singularPairConnectingIsoOfAbsoluteIsZero
    B m
      (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
        (TopCat.of (Disk n 1)) (m + 1) (by omega))
      (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
        (TopCat.of (Disk n 1)) m (by omega))
  let gs := HomologicalComplex.homologyMap
    (ManifoldFundamentalClass.absoluteSingularMap g) m
  let bs := HomologicalComplex.homologyMap
    (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map
        (ConstructionTargets.SingularExcision.subspaceMap B A f hf)) m
  let rf := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap B A f hf) (m + 1)
  refine ⟨gs ≫ e.inv ≫ rf, ?_⟩
  change (gs ≫ e.inv ≫ rf) ≫
      ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A m = _
  rw [Category.assoc, Category.assoc]
  rw [← ConstructionTargets.RelativeSingularConnectingNaturality.singularPairConnecting_naturality
    B A f hf m]
  have he : e.inv ≫
      ConstructionTargets.SingularHomologyConcrete.singularPairConnecting B m = 𝟙 _ :=
    e.inv_hom_id
  have hc : gs ≫ e.inv ≫
      ConstructionTargets.SingularHomologyConcrete.singularPairConnecting B m ≫ bs =
      gs ≫ bs := by
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun k => gs ≫ k ≫ bs) he
  rw [hc]
  change HomologicalComplex.homologyMap
      (ManifoldFundamentalClass.absoluteSingularMap g) m ≫
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (ConstructionTargets.SingularExcision.subspaceMap B A f hf)) m = _
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom g) ≫
      ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
          (ConstructionTargets.SingularExcision.subspaceMap B A f hf) = _
  rw [← Functor.map_comp]
  apply congrArg (fun k : TopCat.of (Sphere n) ⟶ TopCat.of A =>
    ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map k)
  ext s
  rfl

/-- PROVED (claude-14, 2026-10-22), for `_projection_epi`: on a closed connected
`(k + 2)`-manifold with top homology `ℤ`, the global generator localizes to
`±` the local generator at every point (absolute local degree `1` everywhere),
from `_exists_unit` and `_locallyConstant` as in `_coefficient_ne_zero`. This is
blueprint node B4 (`closedManifold_topClass_localGenerator`). -/
lemma boundary_homology_zero_aux_projection_epi_aux_degree_unit
    (k : ℕ)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E (k + 2)) M]
    [IsManifold (I (k + 2)) (⊤ : ℕ∞) M]
    (e : H (k + 2) M ≅ ModuleCat.of ℤ ℤ) (x : M) :
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree k M e x).natAbs = 1 := by
  obtain ⟨y, hy⟩ := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit k M e
  have hxy := (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant k M e).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
  exact hxy.trans hy

/-- Banked by lemma-3 (job invoke-1792656253896-2423-095fe60f, PARTIAL). -/
lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_sets
    {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    let K := c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1}
    IsOpen c.radialTwo ∧ IsClosed (Set.range c.smallMap) ∧
      K ⊆ c.radialTwo ∧ c.smallMap 0 ∈ K := by
  dsimp only
  refine ⟨hopen, ?_, ?_, ?_⟩
  · exact (isCompact_range c.smallEmbedding.continuous).isClosed
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨unitToLarge n y, ?_, c.largeMap_unitToLarge y⟩
    change dist y.1 0 < 2
    have hy' : dist y.1 0 ≤ 1 := Metric.mem_closedBall.mp y.2
    linarith
  · exact ⟨0, by simp, rfl⟩

/-- Copies of the convex model (`_convex_aux_inj_aux_model` and helpers) with
`IsCompact K` weakened to `Bornology.IsBounded K` (the proof only used
boundedness), and of the excision restriction (`_reduce_aux_restrict`) with
closedness of `A`, `B` replaced by `Uᶜ ⊆ interior Aᶜ`, `Uᶜ ⊆ interior Bᶜ` (the
only use of closedness).  Made by claude-14 for `_localization`, whose set `U`
is open, after lemma-3's PARTIAL (job invoke-1792656253896-2423-095fe60f). -/
lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_model_aux_hequiv
    (k : ℕ) (K : Set (E (k + 2))) (hK : Bornology.IsBounded K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) :
    ∃ e : ContinuousMap.HomotopyEquiv (Kᶜ : Set (E (k + 2)))
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u),
      ∀ x, ((e.toFun x : E (k + 2))) = (x : E (k + 2)) := by
  obtain ⟨R, hR, hKR⟩ := hK.subset_ball_lt 1 u
  let j : C((Kᶜ : Set (E (k + 2))),
      ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u) :=
    { toFun := fun x => ⟨x.1, by
        intro hx
        apply x.2
        have : x.1 = u := by
          simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint] using hx
        simpa [this] using hu⟩
      continuous_toFun := by fun_prop }
  let ρ : C(ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
      (Kᶜ : Set (E (k + 2)))) :=
    { toFun := fun x => ⟨u + (1 + R / ‖x.1 - u‖) • (x.1 - u), by
        intro hxK
        have hxne : x.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
            hxu]))
        have hn : 0 < ‖x.1 - u‖ := norm_pos_iff.mpr hxne
        have ha : 0 ≤ 1 + R / ‖x.1 - u‖ := by positivity
        have hdist : dist (u + (1 + R / ‖x.1 - u‖) • (x.1 - u)) u =
            ‖x.1 - u‖ + R := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ha]
          field_simp
        have hb := hKR hxK
        rw [Metric.mem_ball, hdist] at hb
        linarith⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hv : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            x.1 - u) := continuous_subtype_val.sub continuous_const
        have hn : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            ‖x.1 - u‖) := continuous_norm.comp hv
        have hn0 : ∀ x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
            ‖x.1 - u‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
              intro hxu
              exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
                hxu])))
        exact continuous_const.add
          ((continuous_const.add (continuous_const.div hn hn0)).smul hv) }
  let Hout : ContinuousMap.Homotopy (j.comp ρ) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro heq
        have hxne : tx.2.1 ≠ u := by
          intro hx
          exact tx.2.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint, hx])
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr hxne
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        have hcoef : 0 < (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ) := by
          have ht0 := tx.1.2.1
          have ht1 := tx.1.2.2
          have : 0 < R := lt_trans (by norm_num) hR
          have hq : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        apply hvne
        have hzero : ((1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) +
            (tx.1 : ℝ)) • (tx.2.1 - u) = 0 := by
          calc
            _ = (1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
                (tx.1 : ℝ) • tx.2.1 - u := by dsimp [j, ρ]; module
            _ = 0 := sub_eq_zero.mpr heq
        exact (smul_eq_zero.mp hzero).resolve_left hcoef.ne'⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [j, ρ]
      map_one_left := by intro x; apply Subtype.ext; simp }
  let Hin : ContinuousMap.Homotopy (ρ.comp j) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro hz
        have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
        have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact tx.2.2 (by simpa [hxu] using hu))
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        let c : ℝ := (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ)
        have hc : 1 ≤ c := by
          dsimp [c]
          have hRp : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
        have hzform : (1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1 = u + c • (tx.2.1 - u) := by
          dsimp [c, ρ, j]
          module
        have hp : tx.2.1 = (1 - c⁻¹) • u + c⁻¹ •
            ((1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1) := by
          rw [hzform]
          rw [smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
          module
        have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
        have hc_sub : 0 ≤ 1 - c⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hc0).2 hc)
        have hmem := hconv hu hz hc_sub hc_inv (by ring)
        exact tx.2.2 (hp.symm ▸ hmem)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [ρ, j]
      map_one_left := by intro x; apply Subtype.ext; simp }
  refine ⟨{ toFun := j, invFun := ρ, left_inv := ⟨Hin⟩, right_inv := ⟨Hout⟩ }, ?_⟩
  intro x
  rfl

lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_model_aux_sub
    (k : ℕ) (K : Set (E (k + 2))) (hK : Bornology.IsBounded K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (ConstructionTargets.SingularExcision.subspaceMap Kᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
          (ContinuousMap.id (E (k + 2)))
          (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu))) i) := by
  obtain ⟨e, he⟩ := boundary_homology_zero_aux_projection_epi_aux_localization_aux_model_aux_hequiv k K hK hconv u hu
  have hmap : ConstructionTargets.SingularExcision.subspaceMap Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
      (ContinuousMap.id (E (k + 2)))
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu) = TopCat.ofHom e.toFun := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (he x).symm
  change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
    (AddCommGrpCat.of ℤ)).map _)
  rw [hmap, ← ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom e i]
  infer_instance

lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_model
    (k : ℕ) (K : Set (E (k + 2))) (hK : Bornology.IsBounded K) (hconv : Convex ℝ K)
    (u : E (k + 2)) (hu : u ∈ K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u) (ContinuousMap.id (E (k + 2)))
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu)) (n + 1)) := by
  have hamb : ∀ j, IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ContinuousMap.id (E (k + 2))))) j) := by
    intro j
    change IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of (E (k + 2))))) j)
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    infer_instance
  apply ConstructionTargets.SingularExcision.relativeSingularMap_homologyMap_isIso
  · exact boundary_homology_zero_aux_projection_epi_aux_localization_aux_model_aux_sub k K hK hconv u hu (n + 1)
  · exact hamb (n + 1)
  · intro j _
    exact boundary_homology_zero_aux_projection_epi_aux_localization_aux_model_aux_sub k K hK hconv u hu j
  · intro j _
    exact hamb j

lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict_aux_inclusion
    {X : Type} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (K : Set X) (hZ : Uᶜ ⊆ interior Kᶜ) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ K} Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
        (fun _ h => h)) i) := by
  letI := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_excision
    K U hU hZ i hi
  letI := ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodExcisionHomeomorph U)
    {u : U | u.1 ∉ K} (ConstructionTargets.SingularExcision.excisedSubspace Kᶜ Uᶜ)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_pair U K) i
  rw [punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict_aux_chain,
    HomologicalComplex.homologyMap_comp]
  infer_instance

lemma boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict
    {X : Type} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (A B : Set X) (hA : Uᶜ ⊆ interior Aᶜ) (hB : Uᶜ ⊆ interior Bᶜ) (hBA : B ⊆ A)
    (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
        (ContinuousMap.id X) (fun _ hx hb => hx (hBA hb))) i) ↔
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ A} {u : U | u.1 ∉ B}
        (ContinuousMap.id U) (fun _ hx hb => hx (hBA hb))) i) := by
  let jA := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U
  let jB := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U
  let fU := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ A} {u : U | u.1 ∉ B} (ContinuousMap.id U)
    (fun _ hx hb => hx (hBA hb))
  let fX := ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
    (ContinuousMap.id X) (fun _ hx hb => hx (hBA hb))
  let vA := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ A} Aᶜ jA (fun _ h => h)
  let vB := ConstructionTargets.SingularExcision.relativeSingularMap
    {u : U | u.1 ∉ B} Bᶜ jB (fun _ h => h)
  have hsquare : HomologicalComplex.homologyMap fU i ≫
        HomologicalComplex.homologyMap vB i =
      HomologicalComplex.homologyMap vA i ≫
        HomologicalComplex.homologyMap fX i := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    dsimp [fU, fX, vA, vB, jA, jB]
    have hleft := ConstructionTargets.SingularExcision.relativeSingularMap_comp
      {u : U | u.1 ∉ A} {u : U | u.1 ∉ B} Bᶜ
      (ContinuousMap.id U)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
      (fun _ hx hb => hx (hBA hb)) (fun _ h => h)
      (fun _ hx hb => hx (hBA hb))
    have hright := ConstructionTargets.SingularExcision.relativeSingularMap_comp
      {u : U | u.1 ∉ A} Aᶜ Bᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion U)
      (ContinuousMap.id X) (fun _ h => h) (fun _ hx hb => hx (hBA hb))
      (fun _ hx hb => hx (hBA hb))
    rw [hleft, hright]
    rfl
  letI : IsIso (HomologicalComplex.homologyMap vA i) :=
    boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict_aux_inclusion
      U hU A hA i hi
  letI : IsIso (HomologicalComplex.homologyMap vB i) :=
    boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict_aux_inclusion
      U hU B hB i hi
  constructor
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fX i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap fU i ≫
        HomologicalComplex.homologyMap vB i) := by
      rw [hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap fU i)
      (HomologicalComplex.homologyMap vB i)
  · intro hf
    letI : IsIso (HomologicalComplex.homologyMap fU i) := hf
    haveI : IsIso (HomologicalComplex.homologyMap vA i ≫
        HomologicalComplex.homologyMap fX i) := by
      rw [← hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap vA i)
      (HomologicalComplex.homologyMap fX i)


/-- LEAF (split by claude-14 after lemma-3's BLOCKED-ON, job
invoke-1792655893377-2421-966f0eda, then after lemma-3's PARTIAL, job
invoke-1792656253896-2423-095fe60f, 2026-10-22), for `_projection_epi`: with
`U` the collar's open unit ball and `p = c.smallMap 0` its center, the
localization `H_(m+1)(M, M ∖ U) → H_(m+1)(M, M ∖ p)` is an isomorphism.
`hm : 1 ≤ m` (so `n = k + 2`) is supplied by `_projection_epi`.
Route, all pieces now above:
1. `_aux_restrict` in `M` with the open set `c.radialTwo` (`hopen`); the
   interior conditions follow from `_aux_sets`: `Set.range c.smallMap` is closed,
   contains `U` and `p`, and lies in `c.radialTwo`.
2. `_convex_aux_inj_aux_reduce_aux_homeo` along
   `c.radialTwo ≃ₜ Metric.ball (0 : E n) 2`, built as in
   `punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_chart`
   (`largeInteriorMap_isEmbedding.toHomeomorph`, `range_largeInteriorMap`,
   `largeInteriorHomeomorphBall`).  It sends `U` to `{x | ‖x‖ < 1}` and `p`
   to `0`, using `c.compatible` and injectivity of `c.largeMap`.
3. `_aux_restrict` again in `E n`, with `U = Metric.ball 0 2`, `A = ball 0 1`
   (`closedBall 0 1` is closed and in `ball 0 2`), `B = {0}`.
4. `_aux_model` with `K = Metric.ball 0 1` (bounded, convex), `u = 0`. -/
lemma boundary_homology_zero_aux_projection_epi_aux_localization
    (n m : ℕ) (hnm : n = m + 1) (hm : 1 ≤ m) (M : Type) [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (c.smallMap 0))
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          _ (c.smallMap 0) ⟨0, by simp, rfl⟩)) (m + 1)) := by
  subst hnm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hs := boundary_homology_zero_aux_projection_epi_aux_localization_aux_sets c hopen
  have hclosed : IsClosed (Set.range c.smallMap) := hs.2.1
  have hpK : c.smallMap 0 ∈ c.smallMap '' {y : Disk (k + 1 + 1) 1 | dist y.1 0 < 1} :=
    hs.2.2.2
  have hrange : Set.range c.smallMap ⊆ c.radialTwo := by
    rintro _ ⟨y, rfl⟩
    refine ⟨unitToLarge (k + 1 + 1) y, ?_, c.largeMap_unitToLarge y⟩
    have hy := Metric.mem_closedBall.mp y.2
    change dist y.1 0 < 2
    linarith
  have hM_K : c.radialTwoᶜ ⊆
      interior (c.smallMap '' {y : Disk (k + 1 + 1) 1 | dist y.1 0 < 1})ᶜ := by
    intro x hx
    apply interior_mono (Set.compl_subset_compl.mpr (Set.image_subset_range _ _))
    rw [hclosed.isOpen_compl.interior_eq]
    exact fun h => hx (hrange h)
  have hM_p : c.radialTwoᶜ ⊆ interior ({c.smallMap 0} : Set M)ᶜ := by
    intro x hx
    rw [isClosed_singleton.isOpen_compl.interior_eq]
    rintro rfl
    exact hx (hrange ⟨0, rfl⟩)
  refine (boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict
    c.radialTwo hopen _ {c.smallMap 0} hM_K hM_p (by rintro x rfl; exact hpK)
    (k + 1 + 1) (by omega)).mpr ?_
  let er : LargeInterior (n := k + 1 + 1) ≃ₜ ↥c.radialTwo :=
    (c.largeInteriorMap_isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr c.range_largeInteriorMap)
  let e : ↥c.radialTwo ≃ₜ Metric.ball (0 : E (k + 1 + 1)) 2 :=
    er.symm.trans (largeInteriorHomeomorphBall (n := k + 1 + 1))
  have heval (x : ↥c.radialTwo) :
      c.largeMap ⟨(e x).1, Metric.mem_closedBall.mpr (e x).2.le⟩ = x.1 := by
    change (er (er.symm x)).1 = x.1
    exact congrArg Subtype.val (er.apply_symm_apply x)
  have hA : ∀ x : ↥c.radialTwo,
      x ∈ {u : ↥c.radialTwo | u.1 ∉ c.smallMap '' {y : Disk (k + 1 + 1) 1 | dist y.1 0 < 1}} ↔
      e x ∈ {u : Metric.ball (0 : E (k + 1 + 1)) 2 | u.1 ∉ Metric.ball (0 : E (k + 1 + 1)) 1} := by
    intro x
    change x.1 ∉ _ ↔ (e x).1 ∉ Metric.ball (0 : E (k + 1 + 1)) 1
    apply not_congr
    rw [Metric.mem_ball]
    constructor
    · rintro ⟨y, hy, hyeq⟩
      have hz : unitToLarge (k + 1 + 1) y =
          ⟨(e x).1, Metric.mem_closedBall.mpr (e x).2.le⟩ := by
        apply c.largeEmbedding.injective
        rw [c.largeMap_unitToLarge y, heval x]
        exact hyeq
      have : (y : E (k + 1 + 1)) = (e x).1 := congrArg Subtype.val hz
      rw [← this]
      exact hy
    · intro h
      let y : Disk (k + 1 + 1) 1 := ⟨(e x).1, Metric.mem_closedBall.mpr h.le⟩
      refine ⟨y, h, ?_⟩
      rw [← c.largeMap_unitToLarge y]
      exact heval x
  have hB : ∀ x : ↥c.radialTwo,
      x ∈ {u : ↥c.radialTwo | u.1 ∉ ({c.smallMap 0} : Set M)} ↔
      e x ∈ {u : Metric.ball (0 : E (k + 1 + 1)) 2 | u.1 ∉ ({0} : Set (E (k + 1 + 1)))} := by
    intro x
    change x.1 ∉ ({c.smallMap 0} : Set M) ↔ (e x).1 ∉ ({0} : Set (E (k + 1 + 1)))
    apply not_congr
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hxp
      have hz := c.largeEmbedding.injective (show c.largeMap
          ⟨(e x).1, Metric.mem_closedBall.mpr (e x).2.le⟩ =
          c.largeMap (unitToLarge (k + 1 + 1) (0 : Disk (k + 1 + 1) 1)) by
        rw [heval x, hxp, c.largeMap_unitToLarge])
      exact congrArg Subtype.val hz
    · intro hz
      rw [← heval x, ← c.largeMap_unitToLarge (0 : Disk (k + 1 + 1) 1)]
      congr 1
      exact Subtype.ext hz
  have hAB : Set.MapsTo (ContinuousMap.id ↥c.radialTwo)
      {u : ↥c.radialTwo | u.1 ∉ c.smallMap '' {y : Disk (k + 1 + 1) 1 | dist y.1 0 < 1}}
      {u : ↥c.radialTwo | u.1 ∉ ({c.smallMap 0} : Set M)} := by
    intro x hx hxp
    apply hx
    have : x.1 = c.smallMap 0 := Set.mem_singleton_iff.mp hxp
    rw [this]
    exact hpK
  have hAB' : Set.MapsTo (ContinuousMap.id (Metric.ball (0 : E (k + 1 + 1)) 2))
      {u : Metric.ball (0 : E (k + 1 + 1)) 2 | u.1 ∉ Metric.ball (0 : E (k + 1 + 1)) 1}
      {u : Metric.ball (0 : E (k + 1 + 1)) 2 | u.1 ∉ ({0} : Set (E (k + 1 + 1)))} := by
    intro x hx hx0
    apply hx
    have : x.1 = 0 := Set.mem_singleton_iff.mp hx0
    rw [this]
    exact Metric.mem_ball_self one_pos
  refine (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
    e _ _ _ _ hA hB hAB hAB' (k + 1 + 1)).mpr ?_
  have hEU_A : (Metric.ball (0 : E (k + 1 + 1)) 2)ᶜ ⊆
      interior (Metric.ball (0 : E (k + 1 + 1)) 1)ᶜ := by
    intro x hx
    apply interior_mono (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall)
    rw [Metric.isClosed_closedBall.isOpen_compl.interior_eq]
    intro hx1
    apply hx
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hx1
    linarith
  have hEU_B : (Metric.ball (0 : E (k + 1 + 1)) 2)ᶜ ⊆
      interior ({0} : Set (E (k + 1 + 1)))ᶜ := by
    intro x hx
    rw [isClosed_singleton.isOpen_compl.interior_eq]
    rintro rfl
    exact hx (Metric.mem_ball_self two_pos)
  refine (boundary_homology_zero_aux_projection_epi_aux_localization_aux_restrict
    (Metric.ball (0 : E (k + 1 + 1)) 2) Metric.isOpen_ball
    (Metric.ball (0 : E (k + 1 + 1)) 1) {0} hEU_A hEU_B
    (by rintro x rfl; exact Metric.mem_ball_self one_pos) (k + 1 + 1) (by omega)).mp ?_
  exact boundary_homology_zero_aux_projection_epi_aux_localization_aux_model
    k (Metric.ball 0 1) Metric.isBounded_ball (convex_ball 0 1) 0
    (Metric.mem_ball_self one_pos) (k + 1)

/-- LEAF. `H_(m+1) M → H_(m+1)(M, M ∖ open unit ball)` is onto. `1 ≤ m`
(dimension at least 2) is supplied by `boundary_homology_zero`; the dimension-1
case is not needed. Use `_aux_degree_unit` (the generator localizes to `±` the
local generator at the collar center), then transfer epi back along
`_aux_localization` (an isomorphism `H_(m+1)(M, M ∖ U) → H_(m+1)(M, M ∖ p)`). -/
lemma boundary_homology_zero_aux_projection_epi
    (n m : ℕ) (hnm : n = m + 1) (hm : 1 ≤ m) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) :
    Epi (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        ((c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ)) (m + 1)) := by
  subst n
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let p : M := c.smallMap 0
  let K : Set M := c.smallMap '' {y : Disk (k + 1 + 1) 1 | dist y.1 0 < 1}
  let f := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ) (k + 1 + 1)
  let g := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p)
      (ContinuousMap.id M)
      (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
        K p ⟨0, by simp [K, p], rfl⟩)) (k + 1 + 1)
  letI : IsIso g := boundary_homology_zero_aux_projection_epi_aux_localization
    (k + 1 + 1) (k + 1) rfl (by omega) M c hopen
  obtain ⟨e⟩ := htop
  let z := ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of M) (k + 1 + 1) e
  let d := punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
    k M e p
  have hdabs : d.natAbs = 1 :=
    boundary_homology_zero_aux_projection_epi_aux_degree_unit k M e p
  have hd : d = 1 ∨ d = -1 := by omega
  have hlocal : Function.Surjective (ManifoldFundamentalClass.localizationMap p (k + 1 + 1)) := by
    intro y
    let q : ℤ := (ManifoldFundamentalClass.ambientLocalNormalization k p).hom.hom y
    refine ⟨(q * d) • z, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso
      (ManifoldFundamentalClass.ambientLocalNormalization k p).hom).1
    rw [map_zsmul, map_zsmul]
    change (q * d) • ((ManifoldFundamentalClass.ambientLocalNormalization k p).hom.hom
      (ManifoldFundamentalClass.localizationMap p (k + 1 + 1) z)) = _
    change (q * d) • d = q
    rcases hd with h | h <;> rw [h] <;> simp
  apply ConcreteCategory.epi_of_surjective
  intro y
  obtain ⟨z', hz'⟩ := hlocal (g y)
  refine ⟨z', ?_⟩
  apply (ConcreteCategory.bijective_of_isIso g).1
  rw [← hz']
  change g (f z') = ManifoldFundamentalClass.localizationMap p (k + 1 + 1) z'
  have hchain := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
    Kᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p)
    (ContinuousMap.id M)
    (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
      K p ⟨0, by simp [K, p], rfl⟩)
  change (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M))) ≫
      ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p) =
    ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ ≫
      ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p)
        (ContinuousMap.id M)
        (punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          K p ⟨0, by simp [K, p], rfl⟩) at hchain
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hchain
  have hhom := congrArg (fun q => HomologicalComplex.homologyMap q (k + 1 + 1)) hchain
  have hh := (ConcreteCategory.congr_hom hhom z').symm
  simpa [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply,
    ConstructionTargets.ManifoldFundamentalClass.localizationMap,
    ConcreteCategory.id_apply, f, g] using hh

lemma boundary_homology_zero_aux_transport
    (n m : ℕ) (hnm : n = m + 1) (M : Type) [TopologicalSpace M]
    (c : BallCollar n M)
    (h0 : HomologicalComplex.homologyMap
      (ManifoldFundamentalClass.absoluteSingularMap
        ⟨c.boundaryMap, c.continuous_boundaryMap⟩) m = 0) :
    boundaryHomologyMap c m = 0 := by
  unfold boundaryHomologyMap
  apply ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_injective
  apply (cancel_mono
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of c.Punctured) m).hom).1
  rw [CategoryTheory.Functor.map_zero, zero_comp]
  calc
    _ = (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere n)) m).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat m).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom
              ⟨c.boundaryMap, c.continuous_boundaryMap⟩) :=
      ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
          (TopCat.ofHom
            ⟨c.boundaryMap, c.continuous_boundaryMap⟩) m
    _ = 0 := by
      rw [show ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat m).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom
              ⟨c.boundaryMap, c.continuous_boundaryMap⟩) = 0 from h0,
        comp_zero]

theorem boundary_homology_zero (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) : boundaryHomologyMap c (n - 1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    exact ⟨n - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [hm]
  let A : Set M :=
    (c.smallMap '' {y : Disk (m + 1) 1 | dist y.1 0 < 1})ᶜ
  letI : Epi (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection A)
        (m + 1)) :=
    boundary_homology_zero_aux_projection_epi (m + 1) m rfl (by omega) M c htop hopen
  have hconnecting :
      ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A m = 0 :=
    (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative
      A m).epi_f_iff.mp inferInstance
  obtain ⟨j, hj⟩ :=
    boundary_homology_zero_aux_connecting_factorization (m + 1) m rfl (by omega) M c
  apply boundary_homology_zero_aux_transport (m + 1) m rfl M c
  calc
    _ = j ≫ ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A m :=
      hj.symm
    _ = 0 := by rw [hconnecting, comp_zero]

/-- **LIBRARY (B5).** Integral homology of a collared puncture. -/
lemma punctured_homology_aux_H0 {n : ℕ} {M : Type} [TopologicalSpace M]
    (c : BallCollar n M) [PathConnectedSpace c.Punctured] :
    Nonempty (H 0 c.Punctured ≅ ModuleCat.of ℤ ℤ) := by
  let p : c.Punctured := Classical.choice inferInstance
  let q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class p
  letI : Epi q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi p
  letI : Mono q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_mono p
  letI : IsIso q := isIso_of_mono_of_epi q
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of c.Punctured) 0 (ModuleCat.of ℤ ℤ) (asIso q).symm⟩

noncomputable def punctured_homology_aux_middle_aux_inclusion
    {n k : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M) :
    H k c.Punctured ⟶ H k M :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- Excision for the collared open ball: below the manifold dimension, the
puncture inclusion induces an isomorphism on integral singular homology. -/
lemma punctured_homology_aux_middle_aux_inclusion_isIso_aux_pair
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hk1 : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology
        (k + 1)))
    (hk : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology k)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) := by
  open ConstructionTargets.SingularHomologyConcrete in
    exact ConstructionTargets.T00A01MayerVietorisAdapters.isIso_middle_of_two_exact_of_isZero_ends
      (singularPairConnecting A k)
      (HomologicalComplex.homologyMap (singularSubspaceMap A) k)
      (HomologicalComplex.homologyMap (relativeSingularProjection A) k)
      ((singularPairShortComplex_shortExact A).δ_comp (k + 1) k rfl)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap
          ((singularPairShortComplex A).f ≫ (singularPairShortComplex A).g) k = 0
        rw [(singularPairShortComplex A).zero,
          HomologicalComplex.homologyMap_zero])
      (singularPairHomology_exact_subspace A k)
      (singularPairHomology_exact_absolute A k) hk1 hk

lemma punctured_homology_aux_middle_aux_inclusion_isIso_aux_model
    (n j : ℕ) (hn : 2 ≤ n) (hj0 : 0 < j) (hjn : j < n) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n)).homology
        j) := by
  let A := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n
  letI : ContractibleSpace (Metric.ball (0 : E n) 2) :=
    (convex_ball (0 : E n) 2).contractibleSpace ⟨0, by simp⟩
  have hX : IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of (Metric.ball (0 : E n) 2))).homology j) :=
    ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      _ j (by omega)
  by_cases hj : j = 1
  · subst j
    have hmono : Mono (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) 0) := by
      letI : PathConnectedSpace (Metric.ball (0 : E n) 2) := inferInstance
      letI : PathConnectedSpace (Sphere n) := isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere (by
          rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
          exact_mod_cast (by omega : 1 < n)) 0 (by norm_num))
      letI : PathConnectedSpace A := by
        obtain ⟨e⟩ := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_hequiv
          n (by omega)
        refine ⟨⟨e.symm (PathConnectedSpace.nonempty (X := Sphere n)).some⟩, ?_⟩
        intro x y
        let middle : Path (e.symm (e x)) (e.symm (e y)) :=
          (PathConnectedSpace.somePath (e x) (e y)).map e.symm.continuous
        exact ⟨(e.left_inv.some.evalAt x).symm.trans
          (middle.trans (e.left_inv.some.evalAt y))⟩
      exact ConstructionTargets.T02A06SphereH0.pathConnectedSubspace_homologyMap_mono_zero A
    have hex := ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative A 0
    have hc : ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A 0 = 0 := by
      apply (cancel_mono (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) 0)).1
      rw [zero_comp]
      exact (ConstructionTargets.SingularHomologyConcrete.singularPairShortComplex_shortExact A).δ_comp 1 0 rfl
    exact hex.isZero_X₂ (hX.eq_of_src _ _) hc
  · have hjm : 0 < j - 1 := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨e⟩ := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_hequiv
      (m + 1) (by omega)
    have hA : IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of ↑A)).homology (j - 1)) :=
      (ConstructionTargets.SphereHomology.spherePositiveHomology_isZero_of_lt
        m (j - 1) hjm (by omega)).of_iso
          (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
            e (j - 1))
    have hj' : j - 1 + 1 = j := by omega
    rw [← hj'] at hX
    have hz := (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative
      A (j - 1)).isZero_X₂ (hX.eq_of_src _ _) (hA.eq_of_tgt _ _)
    simpa only [hj'] using hz

lemma punctured_homology_aux_middle_aux_inclusion_isIso_aux_relative_zero
    (n : ℕ) (hn : 2 ≤ n) (M : Type) [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < n) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology j) := by
  have hlocal : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.SingularExcision.excisedSubspace
          (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
          c.radialTwoᶜ)).homology j) := by
    obtain ⟨e, he⟩ :=
      punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_chart n M c
    exact punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_pair_iso
      e _ _ he j
      (punctured_homology_aux_middle_aux_inclusion_isIso_aux_model n j hn hj0 hjn)
  have hj' : j - 1 + 1 = j := by omega
  letI : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ c.radialTwoᶜ) j) := by
    rcases punctured_topHomology_zero_aux_mono_aux_excision_set c hopen with ⟨hclosed, hsub⟩
    have hrange : Set.range (fun x : c.Punctured ↦ x.1) =
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange] at hsub
    have hi := ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
      _ _ hclosed hsub (j - 1)
    rw [hj'] at hi
    exact hi
  exact hlocal.of_iso (asIso (HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeExcisionMap
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ c.radialTwoᶜ) j)).symm

lemma punctured_homology_aux_middle_aux_inclusion_isIso_aux_transport
    {n k : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (hgroup : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ) k)) :
    IsIso (punctured_homology_aux_middle_aux_inclusion (k := k) c) := by
  let A : Set M := (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
  let i : TopCat.of A ⟶ TopCat.of M :=
    ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A
  let F := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
  let eA := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of A) k
  let eM := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of M) k
  letI : IsIso eA.hom := eA.isIso_hom
  letI : IsIso eM.hom := eM.isIso_hom
  have hg : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) := by
    dsimp [A]; exact hgroup
  have hnat : F.map (punctured_homology_aux_middle_aux_inclusion (k := k) c) ≫ eM.hom =
      eA.hom ≫ HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality i k
  haveI hright : IsIso (eA.hom ≫ HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) :=
    IsIso.comp_isIso' eA.isIso_hom hg
  haveI : IsIso (F.map (punctured_homology_aux_middle_aux_inclusion (k := k) c) ≫ eM.hom) :=
    hnat ▸ hright
  haveI : IsIso (F.map (punctured_homology_aux_middle_aux_inclusion (k := k) c)) :=
    IsIso.of_isIso_comp_right _ eM.hom
  exact isIso_of_reflects_iso _ F

lemma punctured_homology_aux_middle_aux_inclusion_isIso_aux_top_adjacent
    (n m : ℕ) (hnm : n = m + 1) (hm1 : 1 ≤ m) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo)
    (hm : IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology m)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ) m) := by
  subst hnm
  let A : Set M := (c.smallMap '' {y : Disk (m + 1) 1 | dist y.1 0 < 1})ᶜ
  letI : Epi (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection A) (m + 1)) :=
    boundary_homology_zero_aux_projection_epi (m + 1) m rfl hm1 M c htop hopen
  have hnzero : ConstructionTargets.SingularHomologyConcrete.singularPairConnecting A m = 0 := by
    rw [← cancel_epi (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection A) (m + 1)),
      comp_zero]
    exact (ConstructionTargets.SingularHomologyConcrete.singularPairShortComplex_shortExact A).comp_δ
      (m + 1) m rfl
  letI : Mono (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) m) :=
    (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_subspace A m).mono_g hnzero
  letI : Epi (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) m) :=
    (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_absolute A m).epi_f
      (hm.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma punctured_homology_aux_middle_aux_inclusion_isIso
    (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    IsIso (punctured_homology_aux_middle_aux_inclusion (k := k) c) := by
  have hk := punctured_homology_aux_middle_aux_inclusion_isIso_aux_relative_zero
    n hn M c hopen k hk0 hkn
  apply punctured_homology_aux_middle_aux_inclusion_isIso_aux_transport c
  by_cases htopdeg : k + 1 = n
  · exact punctured_homology_aux_middle_aux_inclusion_isIso_aux_top_adjacent
      n k htopdeg.symm hk0 M c htop hopen hk
  · have hk1 := punctured_homology_aux_middle_aux_inclusion_isIso_aux_relative_zero
      n hn M c hopen (k + 1) (by omega) (by omega)
    exact punctured_homology_aux_middle_aux_inclusion_isIso_aux_pair
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ k hk1 hk

lemma punctured_homology_aux_middle (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    ∀ k, 0 < k → k < n → Nonempty (H k c.Punctured ≅ H k M) := by
  intro k hk0 hkn
  letI : IsIso (punctured_homology_aux_middle_aux_inclusion (k := k) c) :=
    punctured_homology_aux_middle_aux_inclusion_isIso
      n hn M c htop hopen hpath k hk0 hkn
  exact ⟨asIso (punctured_homology_aux_middle_aux_inclusion (k := k) c)⟩

noncomputable def punctured_homology_aux_above_aux_inclusion
    {n k : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M) :
    H k c.Punctured ⟶ H k M :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

lemma punctured_homology_aux_above_aux_inclusion_isIso_aux_pair
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hk1 : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology
        (k + 1)))
    (hk : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology k)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) := by
  open ConstructionTargets.SingularHomologyConcrete in
    exact ConstructionTargets.T00A01MayerVietorisAdapters.isIso_middle_of_two_exact_of_isZero_ends
      (singularPairConnecting A k)
      (HomologicalComplex.homologyMap (singularSubspaceMap A) k)
      (HomologicalComplex.homologyMap (relativeSingularProjection A) k)
      ((singularPairShortComplex_shortExact A).δ_comp (k + 1) k rfl)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap
          ((singularPairShortComplex A).f ≫ (singularPairShortComplex A).g) k = 0
        rw [(singularPairShortComplex A).zero,
          HomologicalComplex.homologyMap_zero])
      (singularPairHomology_exact_subspace A k)
      (singularPairHomology_exact_absolute A k) hk1 hk

/-- The excised ball/annulus pair has no relative homology above dimension
`n`.  This is the geometric input needed in two adjacent degrees. -/
lemma punctured_homology_aux_above_aux_inclusion_isIso_aux_relative_zero_aux_model
    (n j : ℕ) (hn : 1 ≤ n) (hnj : n < j) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n)).homology
        j) := by
  let A := punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_annulus n
  haveI : ContractibleSpace (Metric.ball (0 : E n) 2) :=
    (convex_ball (0 : E n) 2).contractibleSpace ⟨0, by simp⟩
  have hX : IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of (Metric.ball (0 : E n) 2))).homology j) :=
    ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      _ j (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ :=
    punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_hequiv
      (m + 1) (by omega)
  have hA : IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↑A)).homology (j - 1)) :=
    (ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt
      m (j - 1) (by omega)).of_iso
        (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          e (j - 1))
  have hex :=
    ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_relative
      A (j - 1)
  have hj : j - 1 + 1 = j := by omega
  rw [← hj] at hX
  have hz := hex.isZero_X₂ (hX.eq_of_src _ _) (hA.eq_of_tgt _ _)
  simpa only [hj] using hz

lemma punctured_homology_aux_above_aux_inclusion_isIso_aux_relative_zero
    (n : ℕ) (hn : 2 ≤ n) (M : Type) [TopologicalSpace M] [T2Space M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo)
    (j : ℕ) (hnj : n < j) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ).homology j) := by
  have hlocal : IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.SingularExcision.excisedSubspace
          (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
          c.radialTwoᶜ)).homology j) := by
    obtain ⟨e, he⟩ :=
      punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_chart n M c
    exact
      punctured_topHomology_zero_aux_mono_aux_relative_zero_aux_local_aux_pair_iso
        e _ _ he j
        (punctured_homology_aux_above_aux_inclusion_isIso_aux_relative_zero_aux_model
          n j (by omega) hnj)
  have hj : j - 1 + 1 = j := by omega
  letI : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
        c.radialTwoᶜ) j) := by
    rcases punctured_topHomology_zero_aux_mono_aux_excision_set c hopen with
      ⟨hclosed, hsub⟩
    have hrange : Set.range (fun x : c.Punctured ↦ x.1) =
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange] at hsub
    have hi :=
      ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
        _ _ hclosed hsub (j - 1)
    rw [hj] at hi
    exact hi
  exact hlocal.of_iso (asIso (HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeExcisionMap
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
      c.radialTwoᶜ) j)).symm

/-- Naturality of the integral comparison transports the concrete inclusion
isomorphism to the `ModuleCat ℤ` singular-homology functor. -/
lemma punctured_homology_aux_above_aux_inclusion_isIso_aux_transport
    {n k : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (hgroup : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap
        (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ) k)) :
    IsIso (punctured_homology_aux_above_aux_inclusion (k := k) c) := by
  let A : Set M := (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ
  let i : TopCat.of A ⟶ TopCat.of M :=
    ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A
  let F := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
  let eA := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of A) k
  let eM := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of M) k
  letI : IsIso eA.hom := eA.isIso_hom
  letI : IsIso eM.hom := eM.isIso_hom
  have hg : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) := by
    dsimp [A]
    exact hgroup
  have hnat : F.map (punctured_homology_aux_above_aux_inclusion (k := k) c) ≫ eM.hom =
      eA.hom ≫ HomologicalComplex.homologyMap
        (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k := by
    exact ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
      i k
  haveI hright : IsIso (eA.hom ≫ HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) k) :=
    IsIso.comp_isIso' eA.isIso_hom hg
  haveI : IsIso (F.map (punctured_homology_aux_above_aux_inclusion (k := k) c) ≫
      eM.hom) := hnat ▸ hright
  haveI : IsIso (F.map (punctured_homology_aux_above_aux_inclusion (k := k) c)) :=
    IsIso.of_isIso_comp_right _ eM.hom
  exact isIso_of_reflects_iso
    (punctured_homology_aux_above_aux_inclusion (k := k) c) F

/-- Collar excision in degrees strictly above the manifold dimension: removing
the collared open ball does not change integral homology in these degrees. -/
lemma punctured_homology_aux_above_aux_inclusion_isIso
    (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (k : ℕ) (hnk : n < k) :
    IsIso (punctured_homology_aux_above_aux_inclusion (k := k) c) := by
  have hk := punctured_homology_aux_above_aux_inclusion_isIso_aux_relative_zero
    n hn M c hopen k hnk
  have hk1 := punctured_homology_aux_above_aux_inclusion_isIso_aux_relative_zero
    n hn M c hopen (k + 1) (lt_trans hnk (Nat.lt_succ_self k))
  exact punctured_homology_aux_above_aux_inclusion_isIso_aux_transport c
    (punctured_homology_aux_above_aux_inclusion_isIso_aux_pair
      (c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1})ᶜ k hk1 hk)

lemma punctured_homology_aux_above (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (habove : ∀ k, n < k → IsZero (H k M))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (htopzero : IsZero (H n c.Punctured)) :
    ∀ k, n ≤ k → IsZero (H k c.Punctured) := by
  intro k hnk
  rcases hnk.eq_or_lt with rfl | hnk
  · exact htopzero
  · letI : IsIso (punctured_homology_aux_above_aux_inclusion (k := k) c) :=
      punctured_homology_aux_above_aux_inclusion_isIso
        n hn M c hopen hpath k hnk
    exact IsZero.of_iso (habove k hnk) (asIso
      (punctured_homology_aux_above_aux_inclusion (k := k) c))

theorem punctured_homology (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (habove : ∀ k, n < k → IsZero (H k M))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (htopzero : IsZero (H n c.Punctured)) :
    Nonempty (H 0 c.Punctured ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k, 0 < k → k < n → Nonempty (H k c.Punctured ≅ H k M)) ∧
      (∀ k, n ≤ k → IsZero (H k c.Punctured)) := by
  letI : PathConnectedSpace c.Punctured := hpath
  exact ⟨punctured_homology_aux_H0 c,
    punctured_homology_aux_middle n hn M c htop hopen hpath,
    punctured_homology_aux_above n hn M c habove hopen hpath htopzero⟩

/-- **LIBRARY (B6).** The fundamental group is unchanged by puncturing a
three-manifold along a collared ball. -/
lemma punctured_fundamentalGroup_three_aux_of_hequiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (e : ContinuousMap.HomotopyEquiv X Y)
    (p : Path (e.toFun x) y) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) := by
  exact ⟨((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p)⟩

noncomputable def punctured_fundamentalGroup_three_aux_coprod_trivial
    (G H : Type) [Group G] [Group H] [Subsingleton H] :
    Monoid.Coprod G H ≃* G where
  toFun := Monoid.Coprod.lift (MonoidHom.id G) 1
  invFun := Monoid.Coprod.inl
  left_inv x := by
    have h : (Monoid.Coprod.inl : G →* Monoid.Coprod G H).comp
        (Monoid.Coprod.lift (MonoidHom.id G) 1) = MonoidHom.id _ := by
      apply Monoid.Coprod.hom_ext
      · ext g; simp
      · ext h; simp [Subsingleton.elim h 1]
    exact DFunLike.congr_fun h x
  right_inv g := by simp
  map_mul' := map_mul _

lemma punctured_fundamentalGroup_three_aux_subsingleton
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (FundamentalGroup X x) :=
  ⟨fun a b => by
    unfold FundamentalGroup at a b ⊢
    exact Subsingleton.elim (α := Path.Homotopic.Quotient x x) a b⟩

def punctured_fundamentalGroup_three_aux_cover_aux_inner
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) : Set M :=
  c.largeMap '' {x : Disk 3 2 | dist x.1 0 ≤ 1 / 2}

def punctured_fundamentalGroup_three_aux_cover_aux_U
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) : Set M :=
  (punctured_fundamentalGroup_three_aux_cover_aux_inner c)ᶜ

def punctured_fundamentalGroup_three_aux_cover_aux_V
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) : Set M :=
  c.radialTwo

lemma punctured_fundamentalGroup_three_aux_cover_aux_U_open
    {M : Type} [TopologicalSpace M] [T2Space M] (c : BallCollar 3 M) :
    IsOpen (punctured_fundamentalGroup_three_aux_cover_aux_U c) := by
  haveI : CompactSpace (Disk 3 2) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hK : IsCompact {x : Disk 3 2 | dist x.1 0 ≤ 1 / 2} :=
    (isClosed_le (continuous_subtype_val.dist continuous_const)
      continuous_const).isCompact
  exact (hK.image c.largeEmbedding.continuous).isClosed.isOpen_compl

lemma punctured_fundamentalGroup_three_aux_cover_aux_union
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) :
    punctured_fundamentalGroup_three_aux_cover_aux_U c ∪
      punctured_fundamentalGroup_three_aux_cover_aux_V c = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  by_cases hx : x ∈ punctured_fundamentalGroup_three_aux_cover_aux_inner c
  · right
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    change dist y.1 0 < 2
    exact lt_of_le_of_lt (show dist y.1 0 ≤ 1 / 2 from hy) (by norm_num)
  · exact Or.inl hx

lemma punctured_fundamentalGroup_three_aux_cover_aux_boundary_mem
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) (s : Sphere 3) :
    (c.boundaryMap s).1 ∈ punctured_fundamentalGroup_three_aux_cover_aux_U c ∩
      punctured_fundamentalGroup_three_aux_cover_aux_V c := by
  have hs : dist s.1 0 = 1 := by
    simpa [Metric.mem_sphere, dist_comm] using s.2
  constructor
  · rintro ⟨y, hy, heq⟩
    have heq' : c.largeMap y = c.largeMap
        (unitToLarge 3 (sphereToDisk 3 s)) := by
      rw [c.largeMap_unitToLarge]
      exact heq
    have hy' : y = unitToLarge 3 (sphereToDisk 3 s) :=
      c.largeEmbedding.injective heq'
    subst y
    change dist s.1 0 ≤ 1 / 2 at hy
    rw [hs] at hy
    norm_num at hy
  · refine ⟨unitToLarge 3 (sphereToDisk 3 s), ?_, ?_⟩
    · change dist s.1 0 < 2
      rw [hs]
      norm_num
    · exact c.largeMap_unitToLarge (sphereToDisk 3 s)

lemma punctured_fundamentalGroup_three_aux_cover_aux_U_pathConnected_aux_annulus :
    IsPathConnected {x : Disk 3 2 | 1 / 2 < dist x.1 0} := by
  let S : Set (E 3 × ℝ) := Metric.sphere 0 1 ×ˢ Set.Ioc (1 / 2) 2
  have hsphere : IsPathConnected (Metric.sphere (0 : E 3) 1) := by
    apply isPathConnected_sphere
    · norm_num [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    · norm_num
  have hinter : IsPathConnected (Set.Ioc (1 / 2 : ℝ) 2) := by
    exact (convex_Ioc _ _).isPathConnected (by norm_num)
  haveI : PathConnectedSpace (Metric.sphere (0 : E 3) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsphere
  haveI : PathConnectedSpace (Set.Ioc (1 / 2 : ℝ) 2) :=
    isPathConnected_iff_pathConnectedSpace.mp hinter
  let f : (Metric.sphere (0 : E 3) 1) × (Set.Ioc (1 / 2 : ℝ) 2) → Disk 3 2 :=
    fun p ↦ ⟨p.2.1 • p.1.1, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num) p.2.2.1.le)]
      have hs : ‖p.1.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
      rw [hs, mul_one]
      exact p.2.2.2⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)
  have himage : Set.range f = {x : Disk 3 2 | 1 / 2 < dist x.1 0} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      change 1 / 2 < dist (p.2.1 • p.1.1) 0
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num) p.2.2.1.le)]
      have hs : ‖p.1.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
      simpa [hs] using p.2.2.1
    · intro hx
      have hrpos : 0 < ‖x.1‖ :=
        lt_trans (show (0 : ℝ) < 1 / 2 by norm_num) (by simpa [dist_zero_right] using hx)
      let u : Metric.sphere (0 : E 3) 1 := ⟨(‖x.1‖⁻¹) • x.1, by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hrpos.ne']⟩
      let r : Set.Ioc (1 / 2 : ℝ) 2 := ⟨‖x.1‖, by
        constructor
        · simpa [dist_zero_right] using hx
        · simpa only [Metric.mem_closedBall, dist_zero_right] using x.2⟩
      refine ⟨(u, r), Subtype.ext ?_⟩
      dsimp [f, u, r]
      rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  rw [← himage]
  letI : PathConnectedSpace
      ((Metric.sphere (0 : E 3) 1) × (Set.Ioc (1 / 2 : ℝ) 2)) :=
    { nonempty := Nonempty.map2 (fun x y ↦ (x, y))
        hsphere.nonempty.to_subtype hinter.nonempty.to_subtype
      joined := fun x y ↦
        ⟨(PathConnectedSpace.somePath x.1 y.1).prod
          (PathConnectedSpace.somePath x.2 y.2)⟩ }
  exact isPathConnected_range hf

lemma punctured_fundamentalGroup_three_aux_cover_aux_U_pathConnected
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E 3) M]
    [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    PathConnectedSpace (punctured_fundamentalGroup_three_aux_cover_aux_U c) := by
  let P : Set M := Set.range ((↑) : c.Punctured → M)
  let A : Set M := c.largeMap '' {x : Disk 3 2 | 1 / 2 < dist x.1 0}
  have hP : IsPathConnected P := by
    exact isPathConnected_range continuous_subtype_val
  have hA : IsPathConnected A := by
    exact punctured_fundamentalGroup_three_aux_cover_aux_U_pathConnected_aux_annulus.image
      c.largeEmbedding.continuous
  have hPA : (P ∩ A).Nonempty := by
    refine ⟨(c.boundaryMap s).1, ⟨⟨c.boundaryMap s, rfl⟩, ?_⟩⟩
    refine ⟨unitToLarge 3 (sphereToDisk 3 s), ?_,
      c.largeMap_unitToLarge (sphereToDisk 3 s)⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change 1 / 2 < dist s.1 0
    rw [hs]
    norm_num
  have heq : P ∪ A = punctured_fundamentalGroup_three_aux_cover_aux_U c := by
    ext x
    constructor
    · rintro (hxP | hxA)
      · rcases hxP with ⟨z, rfl⟩
        intro hz
        rcases hz with ⟨y, hy, heq⟩
        apply z.2
        let w : Disk 3 1 := ⟨y.1, by
          rw [Metric.mem_closedBall]
          exact le_trans hy (by norm_num)⟩
        refine ⟨w, ?_, ?_⟩
        · change dist y.1 0 < 1
          exact lt_of_le_of_lt hy (by norm_num)
        · have hyw : unitToLarge 3 w = y := Subtype.ext rfl
          rw [← heq, ← hyw]
          exact (c.largeMap_unitToLarge w).symm
      · rcases hxA with ⟨y, hy, rfl⟩
        intro hz
        rcases hz with ⟨z, hz, heq⟩
        have : z = y := c.largeEmbedding.injective heq
        subst z
        change dist y.1 0 ≤ 1 / 2 at hz
        change 1 / 2 < dist y.1 0 at hy
        exact (not_lt_of_ge hz) hy
    · intro hx
      by_cases hunit : x ∈ c.radialUnit
      · right
        rcases hunit with ⟨y, hy, rfl⟩
        refine ⟨y, ?_, rfl⟩
        by_contra hhalf
        apply hx
        refine ⟨y, ?_, rfl⟩
        change ¬ 1 / 2 < dist y.1 0 at hhalf
        exact le_of_not_gt hhalf
      · left
        refine ⟨⟨x, ?_⟩, rfl⟩
        rintro ⟨y, hy, rfl⟩
        apply hunit
        exact ⟨unitToLarge 3 y, hy, c.largeMap_unitToLarge y⟩
  rw [← isPathConnected_iff_pathConnectedSpace, ← heq]
  exact hP.union hA hPA

lemma punctured_fundamentalGroup_three_aux_cover_aux_V_simplyConnected
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E 3) M]
    [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    SimplyConnectedSpace (punctured_fundamentalGroup_three_aux_cover_aux_V c) := by
  letI : ContractibleSpace (Metric.ball (0 : E 3) 2) :=
    Metric.contractibleSpace_ball (by norm_num)
  letI : ContractibleSpace (LargeInterior (n := 3)) :=
    (largeInteriorHomeomorphBall (n := 3)).contractibleSpace
  let e : LargeInterior (n := 3) ≃ₜ
      punctured_fundamentalGroup_three_aux_cover_aux_V c :=
    c.largeInteriorMap_isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr c.range_largeInteriorMap)
  letI : ContractibleSpace
      (punctured_fundamentalGroup_three_aux_cover_aux_V c) :=
    e.symm.contractibleSpace
  exact SimplyConnectedSpace.ofContractible _

section punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_sphere
open Set

variable {X : Type*} [TopologicalSpace X]

open scoped unitInterval

/-- Select one of two sets without putting the selection proof into the type of
points or paths. -/
def punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart (U V : Set X) (side : Bool) : Set X :=
  if side then U else V

/-- Two paths with the same endpoints that remain in a simply connected set
are homotopic in the ambient space. -/
theorem IsSimplyConnected.punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_pathsHomotopic_of_mem {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    Path.Homotopic p q := by
  let xs : s := ⟨x, p.source ▸ hp 0⟩
  let ys : s := ⟨y, p.target ▸ hp 1⟩
  let ps : Path xs ys :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let qs : Path xs ys :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have hsub : Path.Homotopic ps qs := by
    letI : SimplyConnectedSpace s := hs
    exact SimplyConnectedSpace.paths_homotopic ps qs
  simpa [ps, qs] using hsub.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))

/-- A vertex lying in two incident charts can be connected to a fixed overlap
point by a path lying in the intersection of those charts.  The chart-label
case split is confined to the proof of this existential; its result has a
uniform, non-dependent type. -/
theorem exists_path_mem_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_inter {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c x : X} (hc : c ∈ U ∩ V)
    (i j : Bool) (hxi : x ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V i) (hxj : x ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V j) :
    ∃ p : Path x c, ∀ t, p t ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V i ∩ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V j := by
  cases i <;> cases j
  · have hxV : x ∈ V := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxi
    have h := hV.isPathConnected.joinedIn x hxV c hc.2
    exact ⟨h.somePath, fun t ↦ by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using
      (⟨h.somePath_mem t, h.somePath_mem t⟩ : h.somePath t ∈ V ∩ V)⟩
  · have hxV : x ∈ V := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxi
    have hxU : x ∈ U := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxj
    have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩
    have h := hUV.joinedIn x hxUV c hc
    exact ⟨h.somePath, fun t ↦ by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, and_comm] using h.somePath_mem t⟩
  · have hxU : x ∈ U := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxi
    have hxV : x ∈ V := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxj
    have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩
    have h := hUV.joinedIn x hxUV c hc
    exact ⟨h.somePath, fun t ↦ by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using h.somePath_mem t⟩
  · have hxU : x ∈ U := by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using hxi
    have h := hU.isPathConnected.joinedIn x hxU c hc.1
    exact ⟨h.somePath, fun t ↦ by simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart] using
      (⟨h.somePath_mem t, h.somePath_mem t⟩ : h.somePath t ∈ U ∩ U)⟩

/-- Uniformly choose the interior-vertex connectors after proving their
existence.  Neither the connector type nor its range certificate branches on
the adjacent chart labels. -/
theorem exists_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_connectors {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c : X} (hc : c ∈ U ∩ V)
    (vertex : ℕ → X) (side : ℕ → Bool)
    (hleft : ∀ k, vertex (k + 1) ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k))
    (hright : ∀ k, vertex (k + 1) ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side (k + 1))) :
    ∃ conn : ∀ k, Path (vertex (k + 1)) c,
      ∀ k t, conn k t ∈
        punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) ∩ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side (k + 1)) := by
  choose conn hconn using fun k ↦
    exists_path_mem_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_inter hU hV hUV hc
      (side k) (side (k + 1)) (hleft k) (hright k)
  exact ⟨conn, hconn⟩

/-- Connector edges telescope after passing to path-homotopy classes. -/
theorem Path.Homotopic.punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_concat_connector_telescope {n : ℕ}
    (point : Fin (n + 1) → X) (c : X)
    (conn : (k : Fin (n + 1)) → Path (point k) c) :
    Path.Homotopic
      (Path.concat point fun k ↦
        (conn k.castSucc).trans (conn k.succ).symm)
      ((conn 0).trans (conn (Fin.last n)).symm) := by
  induction n with
  | zero =>
      simpa [Path.concat_zero] using
        (⟨Path.Homotopy.reflTransSymm (conn 0)⟩ :
          Path.Homotopic (Path.refl _) ((conn 0).trans (conn 0).symm))
  | succ n ih =>
      rw [Path.concat_succ]
      simp_rw [Fin.succ_castSucc]
      refine (Path.Homotopic.hcomp
        (ih (point ∘ Fin.castSucc) (fun k ↦ conn k.castSucc))
        (Path.Homotopic.refl _)).trans ?_
      let a := conn 0
      let b := conn (Fin.last n).castSucc
      let d := conn (Fin.last (n + 1))
      have hinner : Path.Homotopic (b.symm.trans (b.trans d.symm)) d.symm :=
        (Path.Homotopic.trans_assoc b.symm b d.symm).symm.trans <|
          (Path.Homotopic.hcomp (Path.Homotopic.symm_trans b)
            (Path.Homotopic.refl d.symm)).trans
              (Path.Homotopic.refl_trans d.symm)
      exact (Path.Homotopic.trans_assoc a b.symm (b.trans d.symm)).trans <|
        Path.Homotopic.hcomp (Path.Homotopic.refl a) hinner

/-- Choose all connectors for a positive-length cyclic subdivision at once.
The endpoint identification is part of the existential result, so no
chart-dependent path type escapes the construction. -/
theorem exists_cyclic_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_connectors {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c : X} (hc : c ∈ U ∩ V)
    {n : ℕ} (point : Fin (n + 2) → X) (side : Fin (n + 1) → Bool)
    (hpiece : ∀ k, point k.castSucc ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) ∧
      point k.succ ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k))
    (hcycle : point 0 = point (Fin.last (n + 1))) :
    ∃ conn : (k : Fin (n + 2)) → Path (point k) c,
      (∀ k t, conn k.castSucc t ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) ∧
        conn k.succ t ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k)) ∧
      Path.Homotopic (conn 0)
        ((conn (Fin.last (n + 1))).cast hcycle rfl) := by
  have hxFirst : point 0 ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side 0) := (hpiece 0).1
  have hxLast : point 0 ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side (Fin.last n)) := by
    rw [hcycle]
    exact (hpiece (Fin.last n)).2
  obtain ⟨boundary, hboundary⟩ :=
    exists_path_mem_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_inter hU hV hUV hc
      (side 0) (side (Fin.last n)) hxFirst hxLast
  have hinter : ∀ k : Fin n, ∃ p : Path (point k.succ.castSucc) c,
      ∀ t, p t ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k.castSucc) ∩
        punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k.succ) := by
    intro k
    apply exists_path_mem_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_inter hU hV hUV hc
    · simpa only [Fin.succ_castSucc] using (hpiece k.castSucc).2
    · exact (hpiece k.succ).1
  choose interior hinter_mem using hinter
  let boundaryLast : Path (point (Fin.last (n + 1))) c :=
    boundary.cast hcycle.symm rfl
  let conn : (k : Fin (n + 2)) → Path (point k) c :=
    Fin.cases boundary fun i ↦
      Fin.lastCases boundaryLast (fun k ↦ interior k) i
  have conn_last : conn (Fin.last n).succ = boundaryLast := by
    simp only [conn, Fin.cases_succ, Fin.lastCases_last]
  refine ⟨conn, ?_, ?_⟩
  · intro k t
    constructor
    · refine Fin.cases ?_ (fun j ↦ ?_) k
      · simpa [conn] using (hboundary t).1
      · rw [← Fin.succ_castSucc]
        simpa [conn] using (hinter_mem j t).2
    · refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · rw [conn_last]
        simpa [boundaryLast, Path.cast_coe] using (hboundary t).2
      · rw [Fin.succ_castSucc]
        simpa [conn] using (hinter_mem j t).1
  · have hzero : conn 0 = boundary := by rfl
    have hlast : (conn (Fin.last (n + 1))).cast hcycle rfl = boundary := by
      apply Path.ext
      simpa only [← Fin.succ_last, conn_last, boundaryLast, Path.cast_coe]
    rw [hzero, hlast]

/-- Finite, positive-length wrapper around Mathlib's `ℕ`-indexed subdivision
of the unit interval.  Cover labels are chosen before restricting the
subdivision to `Fin`, avoiding dependent reindexing. -/
theorem punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_exists_fin_Icc_subset_open_cover_unitInterval {ι : Type*}
    {cover : ι → Set unitInterval} (hopen : ∀ i, IsOpen (cover i))
    (hcover : (Set.univ : Set unitInterval) ⊆ ⋃ i, cover i) :
    ∃ n : ℕ, ∃ t : Fin (n + 2) → unitInterval,
      ∃ side : Fin (n + 1) → ι,
        t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
          Monotone t ∧ ∀ k, Set.Icc (t k.castSucc) (t k.succ) ⊆ cover (side k) := by
  obtain ⟨u, hu0, humono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  choose label hlabel using hsub
  refine ⟨m, fun k ↦ u k.val, fun k ↦ label k.val, ?_, ?_, ?_, ?_⟩
  · exact hu0
  · exact hm (m + 1) (Nat.le_succ m)
  · intro i j hij
    exact humono (by exact_mod_cast hij)
  · intro k
    simpa only [Fin.val_castSucc, Fin.val_succ] using hlabel k.val

/-- A space covered by two open simply connected sets with path-connected
overlap is simply connected. -/
theorem punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_simplyConnectedSpace_of_union_eq_univ {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : SimplyConnectedSpace X := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · rw [pathConnectedSpace_iff_univ, ← hcover]
    exact hU.isPathConnected.union hV.isPathConnected hUV.nonempty
  · intro x p
    obtain ⟨c, hc⟩ := hUV.nonempty
    let cover : Bool → Set unitInterval := fun b ↦
      if b then p ⁻¹' U else p ⁻¹' V
    have cover_open : ∀ b, IsOpen (cover b) := by
      intro b
      cases b <;> simp [cover, hUopen, hVopen, IsOpen.preimage p.continuous]
    have cover_all : (Set.univ : Set unitInterval) ⊆ ⋃ b, cover b := by
      intro t _
      have hpt : p t ∈ U ∪ V := by rw [hcover]; trivial
      rcases hpt with htU | htV
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [cover] using htU⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [cover] using htV⟩
    obtain ⟨n, t, side, ht0, ht1, htmono, hsub⟩ :=
      punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_exists_fin_Icc_subset_open_cover_unitInterval cover_open cover_all
    let point : Fin (n + 2) → X := fun k ↦ p (t k)
    have hpiece : ∀ k, point k.castSucc ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) ∧
        point k.succ ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) := by
      intro k
      have hle : t k.castSucc ≤ t k.succ := htmono k.castSucc_le_succ
      have hl := hsub k ⟨le_rfl, hle⟩
      have hr := hsub k ⟨hle, le_rfl⟩
      cases hside : side k <;>
        simp [cover, hside] at hl hr <;>
        simpa [point, punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using And.intro hl hr
    have hcycle : point 0 = point (Fin.last (n + 1)) := by
      simp only [point, ht0, ht1, p.source, p.target]
    obtain ⟨conn, hconn, hconnCycle⟩ :=
      exists_cyclic_punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart_connectors hU hV hUV hc point side hpiece hcycle
    let piece : (k : Fin (n + 1)) →
        Path (point k.castSucc) (point k.succ) := fun k ↦
      p.subpath (t k.castSucc) (t k.succ)
    have piece_mem (k : Fin (n + 1)) (s : unitInterval) :
        piece k s ∈ punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) := by
      have hs : piece k s ∈ Set.range (piece k) := Set.mem_range_self s
      simp only [piece] at hs
      rw [Path.range_subpath_of_le p _ _ (htmono k.castSucc_le_succ)] at hs
      rcases hs with ⟨r, hr, hrs⟩
      have hm := hsub k hr
      rw [← hrs]
      cases hside : side k <;> simpa [cover, punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using hm
    have replacement_mem (k : Fin (n + 1)) (s : unitInterval) :
        ((conn k.castSucc).trans (conn k.succ).symm) s ∈
          punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart U V (side k) := by
      rw [Path.trans_apply]
      split_ifs
      · exact (hconn k _).1
      · exact (hconn k _).2
    have hreplace (k : Fin (n + 1)) : Path.Homotopic (piece k)
        ((conn k.castSucc).trans (conn k.succ).symm) := by
      cases hside : side k
      · apply IsSimplyConnected.punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_pathsHomotopic_of_mem hV
        · intro s; simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using piece_mem k s
        · intro s; simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using replacement_mem k s
      · apply IsSimplyConnected.punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_pathsHomotopic_of_mem hU
        · intro s; simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using piece_mem k s
        · intro s; simpa [punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_twoChart, hside] using replacement_mem k s
    have hconcat := Path.Homotopic.concat_hcomp point piece
      (fun k ↦ (conn k.castSucc).trans (conn k.succ).symm) hreplace
    have htelescope := Path.Homotopic.punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_concat_connector_telescope point c conn
    have hparts := Path.Homotopic.concat_subpath p t
    have hx0 : point 0 = x := by simp [point, ht0, p.source]
    have hxlast : point (Fin.last (n + 1)) = x := by simp [point, ht1, p.target]
    let pCast : Path (point 0) (point (Fin.last (n + 1))) :=
      p.cast hx0 hxlast
    have hparts' : Path.Homotopic (Path.concat point piece) pCast := by
      have hend : p.subpath (t 0) (t (Fin.last (n + 1))) = pCast := by
        ext s
        simp [Path.subpath, ht0, ht1, pCast, Path.cast_coe]
      simpa [point, piece] using hparts.trans (hend ▸ Path.Homotopic.refl pCast)
    let cycleRefl : Path (point 0) (point (Fin.last (n + 1))) :=
      (Path.refl (point 0)).cast rfl hcycle.symm
    have htail : Path.Homotopic
        ((conn 0).trans (conn (Fin.last (n + 1))).symm) cycleRefl := by
      let last := conn (Fin.last (n + 1))
      have hcastTrans : (last.cast hcycle rfl).trans last.symm =
          (last.trans last.symm).cast hcycle rfl := by
        apply Path.ext
        simp [Path.trans_apply, Path.cast_coe]
      have hcastRefl : (Path.refl (point (Fin.last (n + 1)))).cast hcycle rfl =
          cycleRefl := by
        apply Path.ext
        exact funext fun _ ↦ hcycle.symm
      refine (Path.Homotopic.hcomp hconnCycle (Path.Homotopic.refl last.symm)).trans ?_
      rw [hcastTrans]
      exact (Path.Homotopic.pathCast (Path.Homotopic.trans_symm last) hcycle rfl).trans <|
        hcastRefl ▸ Path.Homotopic.refl cycleRefl
    have hall := hparts'.symm.trans (hconcat.trans (htelescope.trans htail))
    have hall' := Path.Homotopic.pathCast hall hx0.symm hxlast.symm
    have hpCast : pCast.cast hx0.symm hxlast.symm = p := by
      apply Path.ext
      simp [pCast, Path.cast_coe]
    have hrefl : cycleRefl.cast hx0.symm hxlast.symm = Path.refl x := by
      apply Path.ext
      exact funext fun _ ↦ hx0
    rw [hpCast, hrefl] at hall'
    exact hall'

/-- A unit sphere is simply connected once the orthogonal complement of one
unit pole has real rank greater than one. -/
theorem punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_simplyConnectedSpace_sphere_of_pole
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1)
    (hrank : 1 < Module.rank ℝ (ℝ ∙ v)ᗮ) :
    SimplyConnectedSpace (Metric.sphere (0 : E) 1) := by
  let north : Metric.sphere (0 : E) 1 := ⟨v, by simpa [mem_sphere_zero_iff_norm]⟩
  let south : Metric.sphere (0 : E) 1 := -north
  let eN := stereographic hv
  let eS := stereographic (show ‖-v‖ = 1 by simpa using hv)
  have hsouth : eN south = 0 := by simpa [north, south, eN] using stereographic_apply_neg north
  have hnorth : eS north = 0 := by simpa [north, south, eS] using stereographic_neg_apply north
  have hNsimple : IsSimplyConnected eN.source := by
    let e := eN.toHomeomorphSourceTarget
    let et : eN.target ≃ₜ (ℝ ∙ v)ᗮ :=
      (Homeomorph.setCongr (by simp [eN])).trans (Homeomorph.Set.univ _)
    letI : SimplyConnectedSpace eN.target :=
      et.toHomotopyEquiv.simplyConnectedSpace
    exact e.toHomotopyEquiv.simplyConnectedSpace
  have hSsimple : IsSimplyConnected eS.source := by
    let e := eS.toHomeomorphSourceTarget
    let et : eS.target ≃ₜ (ℝ ∙ (-v))ᗮ :=
      (Homeomorph.setCongr (by simp [eS])).trans (Homeomorph.Set.univ _)
    letI : SimplyConnectedSpace eS.target :=
      et.toHomotopyEquiv.simplyConnectedSpace
    exact e.toHomotopyEquiv.simplyConnectedSpace
  have hopenN : IsOpen eN.source := eN.open_source
  have hopenS : IsOpen eS.source := eS.open_source
  have hns : north ≠ south := by
    intro h
    have hvneg : v = -v := congrArg Subtype.val h
    have hv0 : v = 0 := by
      have htwo : (2 : ℝ) • v = 0 := by
        calc
          (2 : ℝ) • v = v + v := two_smul ℝ v
          _ = -v + v := congrArg (fun z ↦ z + v) hvneg
          _ = 0 := neg_add_cancel v
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [hv0, norm_zero] at hv
    norm_num at hv
  have hcover : eN.source ∪ eS.source = Set.univ := by
    change (stereographic hv).source ∪
      (stereographic (show ‖-v‖ = 1 by simpa using hv)).source = Set.univ
    rw [stereographic_source, stereographic_source]
    ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    by_cases hx : x = north
    · exact Or.inr fun hxs ↦ hns (hx.symm.trans hxs)
    · exact Or.inl hx
  have hoverlap : IsPathConnected (eN.source ∩ eS.source) := by
    have hpunct : IsPathConnected ({0}ᶜ : Set (ℝ ∙ v)ᗮ) :=
      isPathConnected_compl_singleton_of_one_lt_rank hrank 0
    have himage := hpunct.image'
      (eN.symm.continuousOn.mono (by intro; simp [eN]))
    have hset : eN.symm '' ({0}ᶜ : Set (ℝ ∙ v)ᗮ) = eN.source ∩ eS.source := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨eN.symm.map_source (by simp [eN]), ?_⟩
        simp only [eS, stereographic_source, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        intro h
        apply hy
        calc
          y = eN (eN.symm y) := (eN.right_inv (by simp [eN])).symm
          _ = eN south := congrArg eN h
          _ = 0 := hsouth
      · rintro ⟨hxN, hxS⟩
        refine ⟨eN x, ?_, eN.left_inv hxN⟩
        intro hz
        apply hxS
        have hsouthN : south ∈ eN.source := by simpa [eN] using hns.symm
        calc
          x = eN.symm (eN x) := (eN.left_inv hxN).symm
          _ = eN.symm 0 := congrArg eN.symm hz
          _ = eN.symm (eN south) := congrArg eN.symm hsouth.symm
          _ = south := eN.left_inv hsouthN
    rw [← hset]
    exact himage
  exact punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_simplyConnectedSpace_of_union_eq_univ hopenN hopenS hcover
    hNsimple hSsimple hoverlap

end punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_sphere

/-- The open radial shell `1/2 < ‖x‖ < 2` in `E 3`; the collar carries it onto `U ∩ V`. -/
def punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell : Set (E 3) :=
  {x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2}

/-- `U ∩ V` is the `largeMap`-image of the shell `1/2 < ‖x‖ < 2` of `Disk 3 2`, and
`largeMap` is an embedding, so `U ∩ V` is homeomorphic to the shell. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_homeomorph
    {M : Type} [TopologicalSpace M] (c : BallCollar 3 M) :
    Nonempty ((punctured_fundamentalGroup_three_aux_cover_aux_U c ∩
        punctured_fundamentalGroup_three_aux_cover_aux_V c : Set M) ≃ₜ
      punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell) := by
  let S : Set (Disk 3 2) := {x | 1 / 2 < ‖x.1‖ ∧ ‖x.1‖ < 2}
  let g₀ : punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell →
      Disk 3 2 := fun x ↦ ⟨x.1, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.2.2.le⟩
  have hg₀ : Topology.IsEmbedding g₀ :=
    Topology.IsEmbedding.subtypeVal.codRestrict _ _
  let g : punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell → S :=
    fun x ↦ ⟨g₀ x, by
      change 1 / 2 < ‖x.1‖ ∧ ‖x.1‖ < 2
      exact x.2⟩
  have hg : Topology.IsEmbedding g := hg₀.codRestrict _ _
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    refine ⟨⟨x.1, by simpa [S,
      punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell] using hx⟩, ?_⟩
    apply Subtype.ext
    rfl
  let e₀ := hg.toHomeomorphOfSurjective hgsurj
  have himage : c.largeMap '' S =
      punctured_fundamentalGroup_three_aux_cover_aux_U c ∩
        punctured_fundamentalGroup_three_aux_cover_aux_V c := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 1 / 2 < ‖x.1‖ ∧ ‖x.1‖ < 2 at hx
      refine ⟨?_, ⟨x, ?_, rfl⟩⟩
      · rintro ⟨z, hz, heq⟩
        have hzx : z = x := c.largeEmbedding.injective heq
        subst z
        exact (not_le_of_gt hx.1) (by simpa only [dist_zero_right] using hz)
      · change dist x.1 0 < 2
        simpa only [dist_zero_right] using hx.2
    · rintro ⟨hyU, ⟨x, hx, rfl⟩⟩
      change dist x.1 0 < 2 at hx
      refine ⟨x, ⟨?_, by simpa only [dist_zero_right] using hx⟩, rfl⟩
      by_contra hhalf
      apply hyU
      exact ⟨x, by simpa only [dist_zero_right] using le_of_not_gt hhalf, rfl⟩
  exact ⟨(e₀.trans ((c.largeEmbedding.homeomorphImage S).trans
    (Homeomorph.setCongr himage))).symm⟩

/-- Radial projection `x ↦ x / ‖x‖` is a homotopy equivalence from the shell to the
unit sphere (inverse: inclusion; homotopy: straight-line rescaling of the radius). -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell_hequiv :
    Nonempty (ContinuousMap.HomotopyEquiv
      punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell
      (Metric.sphere (0 : E 3) 1)) := by
  let S := punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell
  let f : S → Metric.sphere (0 : E 3) 1 := fun x ↦
    ⟨(‖(x : E 3)‖)⁻¹ • (x : E 3), by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
      exact ne_of_gt (lt_trans (by norm_num) x.2.1)⟩
  let g : Metric.sphere (0 : E 3) 1 → S := fun x ↦
    ⟨(x : E 3), by
      have hx : ‖(x : E 3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using x.2
      change 1 / 2 < ‖(x : E 3)‖ ∧ ‖(x : E 3)‖ < 2
      simpa [hx] using (show (1 / 2 : ℝ) < 1 ∧ (1 : ℝ) < 2 by norm_num)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp continuous_subtype_val).inv₀ (fun x ↦
      ne_of_gt (lt_trans (by norm_num) x.2.1))).smul continuous_subtype_val
  have hg : Continuous g := by
    exact continuous_subtype_val.subtype_mk _
  refine ⟨{
    toFun := ⟨f, hf⟩
    invFun := ⟨g, hg⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · let gf : C(S, S) := (⟨g, hg⟩ : C(Metric.sphere (0 : E 3) 1, S)).comp ⟨f, hf⟩
    have H : ContinuousMap.Homotopy (ContinuousMap.id S) gf := by
      refine {
      toFun := fun z ↦ ⟨((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖(z.2 : E 3)‖)⁻¹) •
        (z.2 : E 3), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
      · have hr : 1 / 2 < ‖(z.2 : E 3)‖ := z.2.2.1
        have hr2 : ‖(z.2 : E 3)‖ < 2 := z.2.2.2
        have ht0 : 0 ≤ (z.1 : ℝ) := z.1.2.1
        have ht1 : (z.1 : ℝ) ≤ 1 := z.1.2.2
        have hr0 : 0 < ‖(z.2 : E 3)‖ := lt_trans (by norm_num) hr
        have hinv : 0 ≤ (‖(z.2 : E 3)‖)⁻¹ := inv_nonneg.2 hr0.le
        have ha : 0 ≤ (1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖(z.2 : E 3)‖)⁻¹ := by nlinarith
        change 1 / 2 < ‖((1 - (z.1 : ℝ) + (z.1 : ℝ) * ‖(z.2 : E 3)‖⁻¹) •
          (z.2 : E 3))‖ ∧ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
        constructor <;> field_simp <;> nlinarith
      · apply Continuous.subtype_mk
        have hn : Continuous (fun z : unitInterval × S ↦ ‖(z.2 : E 3)‖) :=
          continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
        have hi : Continuous (fun z : unitInterval × S ↦ (‖(z.2 : E 3)‖)⁻¹) :=
          hn.inv₀ (fun z ↦ ne_of_gt (lt_trans (by norm_num) z.2.2.1))
        have hs : Continuous (fun z : unitInterval × S ↦
            (1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖(z.2 : E 3)‖)⁻¹) := by
          fun_prop
        exact hs.smul (continuous_subtype_val.comp continuous_snd)
      · intro x
        apply Subtype.ext
        simp
      · intro x
        apply Subtype.ext
        simp [gf, f, g, inv_smul_smul₀]
    exact ⟨H.symm⟩
  · have hcomp : (⟨f, hf⟩ : C(S, Metric.sphere (0 : E 3) 1)).comp
        (⟨g, hg⟩ : C(Metric.sphere (0 : E 3) 1, S)) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      have hx : ‖(x : E 3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using x.2
      simp [f, g, hx]
    rw [hcomp]

/-- The unit sphere in `E 3` is simply connected. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_sphere :
    SimplyConnectedSpace (Metric.sphere (0 : E 3) 1) := by
  have hv : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3)‖ = 1 := by simp
  have hv0 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E 3) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  haveI : Fact (Module.finrank ℝ (E 3) = 2 + 1) := ⟨by simp⟩
  have hfin := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 2) hv0
  refine punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_simplyConnectedSpace_sphere_of_pole _ hv ?_
  rw [← Module.finrank_eq_rank, hfin]
  norm_num

lemma punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E 3) M]
    [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    SimplyConnectedSpace
      (punctured_fundamentalGroup_three_aux_cover_aux_U c ∩ punctured_fundamentalGroup_three_aux_cover_aux_V c : Set M) := by
  obtain ⟨h⟩ := punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_homeomorph c
  obtain ⟨e⟩ := punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell_hequiv
  haveI := punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_sphere
  haveI : SimplyConnectedSpace
      punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected_aux_shell :=
    e.simplyConnectedSpace
  exact h.toHomotopyEquiv.simplyConnectedSpace

abbrev punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 :=
  Disk 3 1

abbrev punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 :=
  Disk 3 2

def punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 →
      punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 :=
  unitToLarge 3

abbrev punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_punctured
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) :=
  {x : M // x ∉ φ '' {y | dist y.1 0 < 1}}

def punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner
    {M : Type} [TopologicalSpace M]
    (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) :
    Set M :=
  Φ '' {x | dist x.1 0 ≤ 1 / 2}

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) :
    φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 | dist x.1 0 < 1} =
      Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 1} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge x, ?_, ?_⟩
    · exact hx
    · exact congrFun hΦφ x
  · rintro ⟨x, hx, rfl⟩
    have hxclosed : dist x.1 0 ≤ 1 := le_of_lt hx
    let y : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 :=
      ⟨x.1, by simpa [Metric.mem_closedBall, dist_comm] using hxclosed⟩
    refine ⟨y, ?_, ?_⟩
    · exact hx
    · have hu : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge y = x := Subtype.ext rfl
      simpa [Function.comp_apply, hu] using (congrFun hΦφ y).symm

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inner_subset
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ ⊆
      φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 | dist x.1 0 < 1} := by
  rw [punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image
    φ Φ hΦφ]
  rintro z ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  change dist x.1 0 ≤ 1 / 2 at hx
  show dist x.1 0 < 1
  exact lt_of_le_of_lt hx (by norm_num)

def punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inclusion
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_punctured φ →
      ↥(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ :=
  fun x ↦ ⟨x.1, fun hx ↦ x.2
    (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inner_subset
      φ Φ hΦφ hx)⟩

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inclusion_continuous
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) :
    Continuous
      (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inclusion
        φ Φ hΦφ) := by
  exact Continuous.subtype_mk continuous_subtype_val _

/-- The radial collar homotopy on `M`: a point `Φ x` with `‖x‖ < 1` moves along
the segment from `x` to `x / ‖x‖`; every other point stays put. At `t = 1` it is
the radial retraction of `M \ Φ(closedBall 0 (1/2))` onto the punctured manifold. -/
noncomputable def punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
    {M : Type} (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (t : unitInterval) (z : M) : M := by
  classical
  exact if h : ∃ x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3, Φ x = z ∧ dist x.1 0 < 1 then
    (if hv : (1 - (t : ℝ)) • h.choose.1 + (t : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 then
      Φ ⟨_, hv⟩ else z)
  else z

/-- LEAF: the collar homotopy is continuous on `I × U`, where
`U = M \ Φ(closedBall 0 (1/2))`. Glue two pieces. On the open set
`Φ(ball 0 2) ∩ U` it is `Φ ∘ G ∘ Φ⁻¹` (transport through the embedding `Φ`),
where `G t x` is `(1-t)•x + t•(x/‖x‖)` for `‖x‖ < 1` and `x` for `‖x‖ ≥ 1`;
`G` is continuous on `1/2 < ‖x‖ < 2` because the two formulas agree at
`‖x‖ = 1`. On the closed set `M \ Φ(ball 0 1)` (closed because `Φ(ball 0 1)`
is open: `Φ` restricted to the open set `Φ(ball 0 2)` is an open embedding) it
is the identity. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_open
    {M : Type} [TopologicalSpace M]
    (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2})) :
    IsOpen (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 1}) := by
  let s : Set punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 := {x | dist x.1 0 < 1}
  let u : Set punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 := {x | dist x.1 0 < 2}
  have hs : IsOpen s := by
    have hd : Continuous (fun x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 => dist x.1 0) :=
      continuous_subtype_val.dist (continuous_const : Continuous (fun _ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 =>
        (0 : EuclideanSpace ℝ (Fin 3))))
    exact isOpen_lt hd continuous_const
  obtain ⟨v, hv, hvpre⟩ := hΦ.isInducing.isOpen_iff.mp hs
  have hsu : s ⊆ u := by
    intro x hx
    change dist x.1 0 < 1 at hx
    change dist x.1 0 < 2
    linarith
  have himage : Φ '' s = v ∩ Φ '' u := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hvx : Φ x ∈ v := by
        have : x ∈ Φ ⁻¹' v := by simpa [hvpre] using hx
        exact this
      exact ⟨hvx, ⟨x, hsu hx, rfl⟩⟩
    · rintro ⟨hzv, x, hxu, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have : x ∈ Φ ⁻¹' v := hzv
      simpa [hvpre] using this
  rw [himage]
  exact hv.inter hΦo

/-- `Φ` of a closed sub-ball `{‖x‖ ≤ r}` is closed in `M`: the sub-ball is
compact, and `M` is Hausdorff. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (hΦ : Continuous Φ) (r : ℝ) :
    IsClosed (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 ≤ r}) := by
  haveI : CompactSpace punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : IsClosed {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 ≤ r} :=
    isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const
  exact (hc.isCompact.image hΦ).isClosed

/-- Off `Φ(ball 0 1)` the collar homotopy is the identity. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_eq_self
    {M : Type} (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (t : unitInterval) (z : M)
    (hz : z ∉ Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 1}) :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ t z = z := by
  unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
  rw [dif_neg]
  rintro ⟨x, hx, hx1⟩
  exact hz ⟨x, hx1, hx⟩

/-- LEAF: the radial deformation of Euclidean space, `x ↦ (1-t)•x + t•(x/‖x‖)`
for `‖x‖ < 1` and `x ↦ x` otherwise, is jointly continuous away from the
radius-one-half ball. Use `ContinuousOn.if`: each formula is continuous on
`‖x‖ > 1/2` (the first because `‖x‖ ≠ 0`), and on the frontier `‖x‖ = 1` of
`{‖x‖ < 1}` the two formulas agree. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_radial :
    ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
        if ‖p.2‖ < 1 then (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2) else p.2)
      (univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}) := by
  let s : Set (unitInterval × EuclideanSpace ℝ (Fin 3)) :=
    univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}
  let f : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun p ↦ (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2)
  let g : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun p ↦ p.2
  have ht : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ p.2) :=
    continuous_snd
  have hn : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖) :=
    continuous_norm.comp hx
  have hne : ∀ p ∈ s, ‖p.2‖ ≠ 0 := by
    intro p hp
    have hp' : 1 / 2 < ‖p.2‖ := hp.2
    positivity
  have hinv : ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖⁻¹) s :=
    hn.continuousOn.inv₀ hne
  have hf : ContinuousOn f s := by
    exact ((continuous_const.sub ht).continuousOn.smul hx.continuousOn).add
      (ht.continuousOn.smul (hinv.smul hx.continuousOn))
  have hg : ContinuousOn g s := hx.continuousOn
  have hboundary : ∀ p ∈ s ∩ frontier
      {p : unitInterval × EuclideanSpace ℝ (Fin 3) | ‖p.2‖ < 1}, f p = g p := by
    intro p hp
    have heq : ‖p.2‖ = 1 :=
      (frontier_lt_subset_eq hn continuous_const) hp.2
    simp only [f, g, heq, inv_one, one_smul]
    rw [← add_smul, sub_add_cancel, one_smul]
  exact ContinuousOn.if hboundary
    (hf.mono inter_subset_left) (hg.mono inter_subset_left)

/-- LEAF: the collar homotopy is continuous on `I × (Φ(ball 0 2) \ Φ(closedBall 0 (1/2)))`.
There `Φ` restricted to `{‖x‖ < 2}` is a homeomorphism onto the open set
`Φ(ball 0 2)` (`hΦ` is an embedding), and for `z = Φ x` the homotopy is
`Φ (G t x)` with `G` the radial map of
`punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_radial`
(the `closedBall 0 2` test in the definition always holds: for `‖x‖ < 1` the
moving point has norm `(1-t)‖x‖ + t ≤ 1`). Transport the continuity of `G`
through the homeomorphism. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball_aux_radial :
    ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
        if ‖p.2‖ < 1 then (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2) else p.2)
      (univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}) := by
  let s : Set (unitInterval × EuclideanSpace ℝ (Fin 3)) :=
    univ ×ˢ {x | 1 / 2 < ‖x‖}
  let P : unitInterval × EuclideanSpace ℝ (Fin 3) → Prop := fun p ↦ ‖p.2‖ < 1
  apply ContinuousOn.if (p := P)
  · intro p hp
    have hpcl : p ∈ closure {q | P q} := frontier_subset_closure hp.2
    have hnle : ¬ ‖p.2‖ < 1 := by
      have hc : p ∈ closure {q | ¬ P q} := by
        apply frontier_subset_closure
        have : p ∈ frontier ({q | P q}ᶜ) := by simpa only [frontier_compl] using hp.2
        simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using this
      have hsub : closure {q | ¬ P q} ⊆ {q | 1 ≤ ‖q.2‖} :=
        closure_minimal (by intro q hq; exact le_of_not_gt hq)
          (isClosed_le continuous_const (continuous_norm.comp continuous_snd))
      exact not_lt_of_ge (hsub hc)
    have hle : ‖p.2‖ ≤ 1 := by
      simpa [P] using (show p ∈ {q | ‖q.2‖ ≤ 1} from
        closure_minimal (by intro q hq; change ‖q.2‖ < 1 at hq; exact le_of_lt hq)
          (isClosed_le (continuous_norm.comp continuous_snd) continuous_const) hpcl)
    have heq : ‖p.2‖ = 1 := le_antisymm hle (le_of_not_gt hnle)
    rw [heq, inv_one, one_smul, ← add_smul]
    norm_num
  · have hnorm : ContinuousOn (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖⁻¹)
        (s ∩ closure {q | P q}) := by
      apply (continuous_norm.comp continuous_snd).continuousOn.inv₀
      intro p hp hzero
      have hp' : 1 / 2 < ‖p.2‖ := by simpa [s] using hp.1.2
      have : (0 : ℝ) < ‖p.2‖ := lt_of_lt_of_le (by norm_num) (le_of_lt hp')
      exact (ne_of_gt this) hzero
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      continuous_snd).continuousOn.add
        ((continuous_subtype_val.comp continuous_fst).continuousOn.smul
          (hnorm.smul continuous_snd.continuousOn)))
  · exact continuous_snd.continuousOn

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball
    {M : Type} [TopologicalSpace M]
    (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2} ∩
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ)) := by
  let S : Set (unitInterval × M) := univ ×ˢ
    (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2} ∩
      (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ)
  let inv : S → punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 := fun p ↦
    hΦ.toHomeomorph.symm ⟨p.1.2, by
      rcases p.2.2.1 with ⟨x, hx, hxp⟩
      exact ⟨x, hxp⟩⟩
  have hinv : Continuous inv := by
    let rangeMap : S → Set.range Φ := fun p ↦ ⟨p.1.2, by
      rcases p.2.2.1 with ⟨x, hx, hxp⟩
      exact ⟨x, hxp⟩⟩
    have hrange : Continuous rangeMap :=
      Continuous.subtype_mk ((continuous_snd : Continuous (fun p : unitInterval × M ↦ p.2)).comp
        continuous_subtype_val) _
    exact hΦ.toHomeomorph.symm.continuous.comp hrange
  have hinv_eq (p : S) : Φ (inv p) = p.1.2 := by
    exact congrArg Subtype.val (hΦ.toHomeomorph.apply_symm_apply _)
  have hinv_lt (p : S) : dist (inv p).1 0 < 2 := by
    rcases p.2.2.1 with ⟨x, hx, hxp⟩
    have : inv p = x := hΦ.injective (by rw [hinv_eq p, hxp])
    simpa [this] using hx
  have hinv_half (p : S) : 1 / 2 < ‖(inv p).1‖ := by
    by_contra hn
    apply p.2.2.2
    refine ⟨inv p, ?_, hinv_eq p⟩
    change dist (inv p).1 0 ≤ 1 / 2
    simpa [dist_eq_norm] using le_of_not_gt hn
  let Q : S → unitInterval × EuclideanSpace ℝ (Fin 3) := fun p ↦ (p.1.1, (inv p).1)
  have hQ : Continuous Q := by
    dsimp [Q]
    fun_prop
  have hmaps : MapsTo Q univ (univ ×ˢ {x | 1 / 2 < ‖x‖}) := by
    intro p hp
    exact ⟨trivial, hinv_half p⟩
  have hrad : Continuous (fun p : S ↦
      if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
        ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2) := by
    rw [← continuousOn_univ]
    exact punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball_aux_radial.comp
      hQ.continuousOn hmaps
  let R : S → punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 := fun p ↦ ⟨
    if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
      ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2, by
    change dist _ 0 ≤ 2
    rw [dist_zero_right]
    by_cases hlt : ‖(Q p).2‖ < 1
    · rw [if_pos hlt]
      have hnpos : 0 < ‖(Q p).2‖ := by
        have := hinv_half p
        simpa [Q] using lt_trans (by norm_num : (0 : ℝ) < 1 / 2) this
      have hn : ‖(Q p).2‖ ≠ 0 := ne_of_gt hnpos
      have ht0 : 0 ≤ ((Q p).1 : ℝ) := (Q p).1.2.1
      have ht1 : ((Q p).1 : ℝ) ≤ 1 := (Q p).1.2.2
      calc
        ‖(1 - ((Q p).1 : ℝ)) • (Q p).2 +
            ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2)‖ ≤
            ‖(1 - ((Q p).1 : ℝ)) • (Q p).2‖ +
              ‖((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2)‖ := norm_add_le _ _
        _ = (1 - ((Q p).1 : ℝ)) * ‖(Q p).2‖ + ((Q p).1 : ℝ) := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
          simp [abs_inv, abs_of_nonneg (norm_nonneg (Q p).2), hn]
        _ ≤ 2 := by nlinarith [norm_nonneg (Q p).2]
    · rw [if_neg hlt]
      exact le_of_lt (by simpa [Q, dist_eq_norm] using hinv_lt p)⟩
  have hR : Continuous R := by
    apply Continuous.subtype_mk hrad
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.congr (hΦ.continuous.comp hR)
  intro p
  symm
  change punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ p.1.1 p.1.2 = _
  rw [← hinv_eq p]
  unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
  by_cases hlt : ‖(inv p).1‖ < 1
  · have hex : ∃ x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3, Φ x = Φ (inv p) ∧ dist x.1 0 < 1 :=
      ⟨inv p, rfl, by simpa [dist_eq_norm] using hlt⟩
    rw [dif_pos hex]
    have hchoose : hex.choose = inv p := hΦ.injective hex.choose_spec.1
    simp only [hchoose, Q, hlt, if_pos]
    have hv : (1 - (p.1.1 : ℝ)) • (hex.choose).1 +
        (p.1.1 : ℝ) • (‖(hex.choose).1‖⁻¹ • (hex.choose).1) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
      rw [hchoose]
      simpa [R, Q, hlt] using (R p).2
    rw [dif_pos hv]
    apply congrArg Φ
    apply Subtype.ext
    simp [R, Q, hlt]
  · have hnone : ¬ ∃ x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3,
        Φ x = Φ (inv p) ∧ dist x.1 0 < 1 := by
      rintro ⟨x, hx, hx1⟩
      have hxeq : x = inv p := hΦ.injective hx
      apply hlt
      simpa [hxeq, dist_eq_norm] using hx1
    rw [dif_neg hnone]
    simp [R, Q, hlt]

/-- The collar homotopy is continuous on `I × U`, `U = M \ Φ(closedBall 0 (1/2))`:
near a point of `Φ(ball 0 2)` use the `_aux_ball` leaf on that open set; any other
point lies in the open set `M \ Φ(closedBall 0 1)`, where the homotopy is the
identity. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ) := by
  intro p hp
  have hU : IsOpen (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ :=
    (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
      Φ hΦ.continuous (1 / 2)).isOpen_compl
  by_cases hb : p.2 ∈ Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2}
  · have hA : IsOpen (univ ×ˢ (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2} ∩
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ) : Set (unitInterval × M)) :=
      isOpen_univ.prod (hΦo.inter hU)
    exact ((punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball
      Φ hΦ hΦo).continuousAt (hA.mem_nhds ⟨trivial, hb, hp.2⟩)).continuousWithinAt
  · have hB : IsOpen (univ ×ˢ (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) :=
      isOpen_univ.prod
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
          Φ hΦ.continuous 1).isOpen_compl
    have hpB : p ∈ (univ ×ˢ (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) := by
      refine ⟨trivial, ?_⟩
      rintro ⟨x, hx, hxp⟩
      refine hb ⟨x, ?_, hxp⟩
      change dist x.1 0 ≤ 1 at hx
      change dist x.1 0 < 2
      linarith
    have heq : (fun q : unitInterval × M ↦
        punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ q.1 q.2)
          =ᶠ[nhds p] Prod.snd := by
      filter_upwards [hB.mem_nhds hpB] with q hq
      apply punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn_aux_eq_self
      rintro ⟨x, hx, hxq⟩
      refine hq.2 ⟨x, ?_, hxq⟩
      change dist x.1 0 < 1 at hx
      change dist x.1 0 ≤ 1
      exact le_of_lt hx
    exact (continuous_snd.continuousAt.congr heq.symm).continuousWithinAt

/-- LEAF: the collar homotopy keeps `U = M \ Φ(closedBall 0 (1/2))` inside `U`,
and at time `1` lands in the punctured manifold. For `z = Φ x ∈ U` with
`‖x‖ < 1` one has `‖x‖ > 1/2`, and the moving point has norm
`(1-t)‖x‖ + t ∈ (1/2, 1]`, equal to `1` at `t = 1`; injectivity of `Φ` and
`φ '' {‖y‖ < 1} = Φ '' {‖x‖ < 1}`
(`punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image`) finish. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_mapsTo
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦ : Function.Injective Φ) (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) :
    (∀ t : unitInterval,
      MapsTo (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ t)
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ) ∧
    MapsTo (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ 1)
      (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ
      {z | z ∉ φ '' {y : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 | dist y.1 0 < 1}} := by
  classical
  have radial_bounds (t : unitInterval) (x : EuclideanSpace ℝ (Fin 3))
      (hx : 1 / 2 < ‖x‖) (hx1 : ‖x‖ < 1) :
      1 / 2 < ‖(1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x)‖ ∧
        ‖(1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x)‖ ≤ 1 := by
    have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have heq :
        (1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x) =
          ((1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹) • x := by
      rw [add_smul, mul_smul]
    rw [heq, norm_smul, Real.norm_eq_abs]
    have hi0 : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
    have hc0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹ :=
      add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0 hi0)
    rw [abs_of_nonneg hc0]
    have hcalc :
        ((1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹) * ‖x‖ =
          (1 - (t : ℝ)) * ‖x‖ + (t : ℝ) := by
      field_simp
    rw [hcalc]
    constructor <;> nlinarith
  constructor
  · intro t z hz
    unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · rintro ⟨y, hy, heq⟩
      have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      have hx1 : ‖h.choose.1‖ < 1 := by
        simpa [dist_eq_norm] using h.choose_spec.2
      have hb := (radial_bounds t h.choose.1 hxhalf hx1).1
      have hy' : ‖y.1‖ ≤ 1 / 2 := by
        simpa [dist_eq_norm] using hy
      have hxy : y.1 =
          (1 - (t : ℝ)) • h.choose.1 +
            (t : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) := by
        exact congrArg Subtype.val (hΦ heq)
      rw [hxy] at hy'
      linarith
    · exact hz
    · exact hz
  · intro z hz
    unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      have hx1 : ‖h.choose.1‖ < 1 := by
        simpa [dist_eq_norm] using h.choose_spec.2
      rw [punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image
          φ Φ hΦφ]
      rintro ⟨y, hy, heq⟩
      have hxy : y.1 =
            (1 - (1 : ℝ)) • h.choose.1 +
              (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) := by
          exact congrArg Subtype.val (hΦ heq)
      have hnorm : ‖(1 - (1 : ℝ)) • h.choose.1 +
              (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1)‖ = 1 := by
        rw [show (1 : ℝ) - 1 = 0 by norm_num, zero_smul, zero_add, one_smul,
          norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h.choose.1))]
        exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hxhalf))
      have hy' : ‖y.1‖ < 1 := by simpa [dist_eq_norm] using hy
      rw [hxy, hnorm] at hy'
      exact (lt_irrefl 1 hy')
    · have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      exfalso
      apply hv
      change ‖(1 - (1 : ℝ)) • h.choose.1 +
            (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) - 0‖ ≤ 2
      rw [show (1 : ℝ) - 1 = 0 by norm_num, zero_smul, zero_add, one_smul,
        sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h.choose.1))]
      rw [inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hxhalf))]
      norm_num
    · rw [punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image
          φ Φ hΦφ]
      rintro ⟨x, hx, hxz⟩
      exact h ⟨x, hxz, hx⟩

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_zero
    {M : Type} (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M) (z : M) :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ 0 z = z := by
  classical
  unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
  split_ifs with h hv
  · have hx := h.choose_spec.1
    convert hx using 2
    apply Subtype.ext
    simp
  · rfl
  · rfl

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_one
    {M : Type} [TopologicalSpace M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ) (z : M)
    (hz : z ∉ φ '' {y : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 | dist y.1 0 < 1}) :
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ 1 z = z := by
  classical
  unfold punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H
  rw [dif_neg]
  rintro ⟨x, hxz, hx⟩
  rw [punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_image
    φ Φ hΦφ] at hz
  exact hz ⟨x, hx, hxz⟩

/-- The punctured manifold is a deformation retract of the slightly
enlarged punctured part `M \ Φ(closedBall 0 (1/2))`, by pushing the shell
`1/2 < ‖x‖ < 1` radially out to the unit sphere inside the collar. -/
lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv
    {M : Type} [TopologicalSpace M] [T2Space M]
    (φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_Disk3 → M) (Φ : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 → M)
    (hΦ : Topology.IsEmbedding Φ) (hΦφ : Φ ∘ punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_unitToLarge = φ)
    (hΦo : IsOpen (Φ '' {x : punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty (ContinuousMap.HomotopyEquiv (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_punctured φ)
      ↥(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ) := by
  obtain ⟨hmap, hmap1⟩ :=
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_mapsTo
      φ Φ hΦ.injective hΦφ
  have hcont :=
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_continuousOn
      Φ hΦ hΦo
  have hHc : Continuous (fun p : unitInterval ×
      ↥(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ ↦
      punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1) :=
    hcont.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨mem_univ _, p.2.2⟩)
  let i : C(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_punctured φ,
      ↥(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ) :=
    ⟨punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inclusion φ Φ hΦφ,
      punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_inclusion_continuous
        φ Φ hΦφ⟩
  let r : C(↥(punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_inner Φ)ᶜ,
      punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_punctured φ) :=
    ⟨fun z ↦ ⟨punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ 1 z.1,
      hmap1 z.2⟩,
      (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let F : ContinuousMap.Homotopy (ContinuousMap.id _) (i.comp r) :=
    { toFun := fun p ↦
        ⟨punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1,
          hmap p.1 p.2.2⟩
      continuous_toFun := hHc.subtype_mk _
      map_zero_left := fun z ↦ Subtype.ext
        (punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_zero Φ z.1)
      map_one_left := fun z ↦ rfl }
  have hri : r.comp i = ContinuousMap.id _ := by
    ext z
    exact punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv_aux_H_one
      φ Φ hΦφ z.1 z.2
  exact ⟨{ toFun := i, invFun := r
           left_inv := by rw [hri]
           right_inv := ⟨F.symm⟩ }⟩

/-- LEAF: the open shell `Φ(1/2 < ‖x‖ < 2)` is homeomorphic to a Euclidean
shell, hence homotopy equivalent to `S²`, hence simply connected
(`ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected`). -/

lemma punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E 3) M]
    [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    ∃ e : ContinuousMap.HomotopyEquiv c.Punctured (punctured_fundamentalGroup_three_aux_cover_aux_U c),
      Joined (e.toFun (c.boundaryMap s))
        ⟨c.boundaryMap s, (punctured_fundamentalGroup_three_aux_cover_aux_boundary_mem c s).1⟩ := by
  obtain ⟨e⟩ :=
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv_aux_enlarged_hequiv
      c.smallMap c.largeMap c.largeEmbedding c.compatible hopen
  letI : PathConnectedSpace (punctured_fundamentalGroup_three_aux_cover_aux_U c) :=
    punctured_fundamentalGroup_three_aux_cover_aux_U_pathConnected M c s hopen hpath
  exact ⟨e, PathConnectedSpace.joined _ _⟩

lemma punctured_fundamentalGroup_three_aux_cover_aux_geometry
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E 3) M]
    [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    PathConnectedSpace (punctured_fundamentalGroup_three_aux_cover_aux_U c) ∧
      SimplyConnectedSpace (punctured_fundamentalGroup_three_aux_cover_aux_V c) ∧
      SimplyConnectedSpace
        (punctured_fundamentalGroup_three_aux_cover_aux_U c ∩
          punctured_fundamentalGroup_three_aux_cover_aux_V c : Set M) ∧
      ∃ e : ContinuousMap.HomotopyEquiv c.Punctured
          (punctured_fundamentalGroup_three_aux_cover_aux_U c),
        Joined (e.toFun (c.boundaryMap s))
          ⟨c.boundaryMap s,
            (punctured_fundamentalGroup_three_aux_cover_aux_boundary_mem c s).1⟩ := by
  exact ⟨punctured_fundamentalGroup_three_aux_cover_aux_U_pathConnected M c s hopen hpath,
    punctured_fundamentalGroup_three_aux_cover_aux_V_simplyConnected M c s hopen hpath,
    punctured_fundamentalGroup_three_aux_cover_aux_inter_simplyConnected M c s hopen hpath,
    punctured_fundamentalGroup_three_aux_cover_aux_homotopyEquiv M c s hopen hpath⟩

lemma punctured_fundamentalGroup_three_aux_cover (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace (E 3) M] [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    ∃ (U V : Set M) (hU : IsOpen U) (hV : IsOpen V),
      U ∪ V = Set.univ ∧
      ∃ (hu : (c.boundaryMap s).1 ∈ U) (hv : (c.boundaryMap s).1 ∈ V),
        PathConnectedSpace U ∧ SimplyConnectedSpace V ∧
        SimplyConnectedSpace (U ∩ V : Set M) ∧
        ∃ e : ContinuousMap.HomotopyEquiv c.Punctured U,
          Joined (e.toFun (c.boundaryMap s)) ⟨c.boundaryMap s, hu⟩ := by
  let U := punctured_fundamentalGroup_three_aux_cover_aux_U c
  let V := punctured_fundamentalGroup_three_aux_cover_aux_V c
  have hU : IsOpen U := punctured_fundamentalGroup_three_aux_cover_aux_U_open c
  have hV : IsOpen V := hopen
  have hcover : U ∪ V = Set.univ :=
    punctured_fundamentalGroup_three_aux_cover_aux_union c
  have hb := punctured_fundamentalGroup_three_aux_cover_aux_boundary_mem c s
  obtain ⟨hpcU, hscV, hscUV, e, he⟩ :=
    punctured_fundamentalGroup_three_aux_cover_aux_geometry
      M c s hopen hpath
  exact ⟨U, V, hU, hV, hcover, hb.1, hb.2, hpcU, hscV, hscUV, e, he⟩

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_groupEquivalence_apply
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)]
    (z : FundamentalGroup X w.1) :
    TwoOpenFreeProductMapping.groupEquivalence hU hV hcover w z =
      (TwoOpenFreeProductMapping.sourceEquivalence hU hV hcover w).functor.map z := by
  have h1 : ∀ (h : (TwoOpenFreeProductMapping.sourceEquivalence hU hV hcover w).functor.obj
      (FundamentalGroupoid.mk w.val) = SingleObj.star _), eqToHom h = 𝟙 _ := fun h => rfl
  unfold TwoOpenFreeProductMapping.groupEquivalence
  erw [MulEquiv.trans_apply, MulEquiv.trans_apply, Iso.conj_apply, eqToIso.hom, eqToIso.inv,
    h1, Category.id_comp, Category.comp_id]
  rfl

/-- Component of the counit of `Equivalence.trans` into a functor category. -/
private lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_trans_counit_app {A B S T : Type*} [Category A] [Category B] [Category S] [Category T]
    (e : A ≌ B) (f : B ≌ (S ⥤ T)) (Y : S ⥤ T) (s : S) :
    ((e.trans f).counitIso.hom.app Y).app s =
      (f.functor.map (e.counitIso.hom.app (f.inverse.obj Y))).app s ≫ (f.counitIso.hom.app Y).app s := by
  simp

/-- Free-product side: the counit of `freeProductPointSpanEquivalence ⋯ representationSingleObjEquivalence`
at the identity functor has identity component at the single object. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_freeProduct
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).counitIso.hom.app
        (Functor.id (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))).app
      (SingleObj.star (Monoid.Coprod (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))) = 𝟙 _ := by
  rfl

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_left
    {X : Type} [TopologicalSpace X] (U V : Set X) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (TwoOpenPointSpanComparison.leftEquivalence U V w).counitIso.hom.app
      (SingleObj.star (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base)) = 𝟙 _ := by
  change ((ConnectedGroupoidSingleObjEquivalence.connectorSingleObjEquivalence
    (TwoOpenLegCompatibleConnectorSystems.leftConnectors w)).counitIso.hom.app _) = _
  change ((TwoOpenLegCompatibleConnectorSystems.leftConnectors w).connector
    (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base).hom = _
  rw [TwoOpenLegCompatibleConnectorSystems.leftConnectors_connector_base]
  rfl

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_right
    {X : Type} [TopologicalSpace X] (U V : Set X) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (TwoOpenPointSpanComparison.rightEquivalence U V w).counitIso.hom.app
      (SingleObj.star (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)) = 𝟙 _ := by
  change ((ConnectedGroupoidSingleObjEquivalence.connectorSingleObjEquivalence
    (TwoOpenLegCompatibleConnectorSystems.rightConnectors w)).counitIso.hom.app _) = _
  change ((TwoOpenLegCompatibleConnectorSystems.rightConnectors w).connector
    (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base).hom = _
  rw [TwoOpenLegCompatibleConnectorSystems.rightConnectors_connector_base]
  rfl

/-- Component of the counit of a threefold `Equivalence.trans`. -/
private lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_trans3 {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ≌ B) (S : B ≌ C) (Cmp : C ≌ D) (Y : D) :
    ((P.trans S).trans Cmp).counitIso.hom.app Y =
      Cmp.functor.map (S.functor.map (P.counitIso.hom.app (S.inverse.obj (Cmp.inverse.obj Y))) ≫
        S.counitIso.hom.app (Cmp.inverse.obj Y)) ≫ Cmp.counitIso.hom.app Y := by
  simp
/-- Point-span comparison factor of the span counit: the counit of
`TwoOpenPointSpanComparison.comparison` at the inverse image of the identity, sent through the
free-product equivalence, has identity component at the single object.  Route: the comparison is
`pseudoCoconeEquivalenceOfSpanEquivalences` built from `leftEquivalence`/`rightEquivalence`, whose
counit components at the base objects are identities (`_aux_span_aux_left`, `_aux_span_aux_right`,
banked by job 2367), and `pointComparison`, whose components are `Iso.refl`.
Split from `punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span` after job 2367. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_comparison
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).functor.map
      ((TwoOpenPointSpanComparison.comparison U V w (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).counitIso.hom.app
        (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).inverse.obj
          (Functor.id (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))))).app
      (SingleObj.star (Monoid.Coprod (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))) = 𝟙 _ := by
  change (((TwoOpenPointSpanComparison.leftEquivalence U V w).congrLeft).counitIso.hom.app _).app _ = _
  have h := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_left U V w
  simp only [Equivalence.congrLeft] at *
  simp [h]
  erw [CategoryTheory.Functor.map_id]
  rfl
/-- Descent factor of the span counit: the counit of the pseudopushout (descent)
equivalence, transported through `pseudoSpanEquivalence`, the point-span comparison and the
free-product equivalence, has identity component at the single object.  This is where job 2367
stopped: unfolding reaches the descent counit composed with `invFunIdAssoc`, and the remaining
normalisation is through `TwoOpenPseudoCoconeStrictification.twoOpenDescentPseudoCoconeEquivalence`.
Split from `punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span` after job 2367. -/
private lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_descent_aux_eqToHom
    (G : Type) [Group G] {a b : SingleObj G} (h : a = b) :
    (eqToHom h : a ⟶ b) = (1 : G) := by
  subst b
  rfl

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_descent
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).functor.map
      ((TwoOpenPointSpanComparison.comparison U V w (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).functor.map
        ((TwoOpenFreeProductMapping.pseudoSpanEquivalence (U := U) (V := V) (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).functor.map
          ((TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence
            (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) hU hV hcover).counitIso.hom.app
            ((TwoOpenFreeProductMapping.pseudoSpanEquivalence (U := U) (V := V) (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).inverse.obj
              ((TwoOpenPointSpanComparison.comparison U V w (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).inverse.obj
                (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).inverse.obj
          (Functor.id (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))))))))).app
      (SingleObj.star (Monoid.Coprod (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))) = 𝟙 _ := by
  dsimp [TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence,
    TwoOpenPseudoCoconeStrictification.twoOpenDescentPseudoCoconeEquivalence,
    TwoOpenDescentCategory.twoOpenDescentEquivalence,
    TwoOpenDescentCategory.descentReconstructionIso,
    TwoOpenDescentCategory.descentReconstructionAppIso,
    TwoOpenDescentCategory.descentReconstructionHom,
    TwoOpenDescentRestriction.pieceRestrictionIso,
    TwoOpenDescentRestriction.restrictionAppIso,
    TwoOpenFundamentalGroupoidSpan.descentToPseudoCoconeFunctor,
    TwoOpenFundamentalGroupoidSpan.descentPseudoCoconeMap,
    CategoryTheory.Equivalence.mk,
    TwoOpenFreeProductMapping.pseudoSpanEquivalence,
    TwoOpenFreeProductMapping.pseudoToSpanFunctor,
    TwoOpenFreeProductMapping.pseudoToSpanMap,
    TwoOpenPointSpanComparison.comparison,
    GenericSpanPseudoCoconeTransport.pseudoCoconeEquivalenceOfSpanEquivalences,
    GenericSpanPseudoCoconeTransport.transportFunctor,
    GenericSpanPseudoCoconeTransport.transportMap,
    FreeProductPointSpanRepresentations.toRepresentationFunctor,
    FreeProductPointSpanRepresentations.toRepresentationMap,
    FreeProductRepresentationSingleObjEquivalence.representationToFunctor,
    FreeProductRepresentationSingleObjEquivalence.representationToFunctorMap,
    FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence,
    TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationNatIso,
    TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationIso,
    TwoOpenPseudoCoconeStrictification.pseudoCoconeStrictificationInv,
    TwoOpenFundamentalGroupoidSpan.pieceStrictificationIso,
    TwoOpenFundamentalGroupoidSpan.strictifiedObjectIso,
    TwoOpenFundamentalGroupoidSpan.pseudoPieceFunctor]
  rfl

/-- Span side: the counit of the first three factors of `mapping` (descent/pseudopushout,
`TwoOpenFreeProductMapping.pseudoSpanEquivalence`, point-span comparison), at the free-product inverse image of the
identity, is sent by the free-product functor to an identity component at the single object.
Split from `punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity` after job 2328. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).functor.map
      ((((TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence
            (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) hU hV hcover).trans
          (TwoOpenFreeProductMapping.pseudoSpanEquivalence (U := U) (V := V) (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))).trans
          (TwoOpenPointSpanComparison.comparison U V w (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))).counitIso.hom.app
        (((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
        (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
          (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))).inverse.obj
          (Functor.id (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))))).app
      (SingleObj.star (Monoid.Coprod (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base) (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))) = 𝟙 _ := by
  have hc := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_comparison U V w
  have hd := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_descent U V hU hV hcover w
  rw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span_aux_trans3]
  erw [Functor.map_comp, Functor.map_comp, NatTrans.comp_app, NatTrans.comp_app]
  erw [hd, hc]
  simp
  rfl

/-- The counit of the five-step mapping equivalence, at the inverse image of the
identity, has identity component at the single object.  Route: the counit of
`Equivalence.trans` is built from the counits of the factors; `pseudoSpanEquivalence`
has `Iso.refl` counit, so the components to compute come from the descent
equivalence, the point-span comparison and the two free-product equivalences
(named in `TwoOpenFreeProductMappingCompositeCounitIdentity.compositeCounitComponent`).
Split from `punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left` after job 2282. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    (TwoOpenFreeProductMappingInverseIdentityLegCoordinates.inverseIdentityCounit
        hU hV hcover w).hom.app
      (SingleObj.star (Monoid.Coprod
        (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base)
        (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base))) = 𝟙 _ := by
  have h1 := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_freeProduct U V w
  have h2 := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_span U V hU hV hcover w
  rw [TwoOpenFreeProductMappingInverseIdentityLegCoordinates.inverseIdentityCounit, Iso.app_hom]
  erw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_counit_identity_aux_trans_counit_app, h2, h1, Category.comp_id]
  rfl

/-- Descent seam (split after job 2537): on a morphism included from the `U` piece, the
two-open descent functor is that piece's functor conjugated by the datum's object
equalities.  This is `pieceRestrictionIso` naturality. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_descent
    {X : Type} [TopologicalSpace X] {U V : Set X} {C : Type} [Category C]
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)
    {a z : FundamentalGroupoid (FundamentalGroupoidTwoOpenDescent.CoverPiece U V true)}
    (f : a ⟶ z) :
    (TwoOpenDescentFunctor.twoOpenDescentFunctor hU hV hcover D).map
        ((FundamentalGroupoid.map (TwoOpenDescentRestriction.coverPieceInclusion true)).map f) =
      eqToHom (D.obj_eq true a).symm ≫ (D.functor true).map f ≫
        eqToHom (D.obj_eq true z) := by
  change (TwoOpenDescentRestriction.restrictedAmbientFunctor hU hV hcover D true).map f = _
  exact (NatIso.naturality_1
    (TwoOpenDescentRestriction.pieceRestrictionIso hU hV hcover D true) f).symm

/-- Strictification seam (split after job 2537): the strictified `U`-piece functor is the
pseudococone's left leg conjugated by `strictifiedObjectIso` (an `eqToIso` on `U`). -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_strict
    {X : Type} [TopologicalSpace X] {U V : Set X} {C : Type} [Category C]
    (hcover : U ∪ V = Set.univ)
    (P : TwoOpenFundamentalGroupoidSpan.PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    {a z : FundamentalGroupoid (FundamentalGroupoidTwoOpenDescent.CoverPiece U V true)}
    (f : a ⟶ z) :
    ((TwoOpenPseudoCoconeStrictification.strictifiedDescentDatum hcover P).functor true).map f =
      (TwoOpenFundamentalGroupoidSpan.strictifiedObjectIso hcover P true a).inv ≫
        P.left.map f ≫
        (TwoOpenFundamentalGroupoidSpan.strictifiedObjectIso hcover P true z).hom := rfl

/-- The pseudococone that `mapping.inverse` produces from `𝟭` before the descent layer. -/
def punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_pseudo
    {X : Type} [TopologicalSpace X] {U V : Set X}
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
    (w : (U ∩ V : Set X)) :
    TwoOpenFundamentalGroupoidSpan.PseudoFunctorCocone (X := X) (U := U) (V := V)
      (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w) :=
  (((TwoOpenFreeProductMapping.pseudoSpanEquivalence (U := U) (V := V)
      (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)).trans
    (TwoOpenPointSpanComparison.comparison U V w
      (GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w))).trans
    ((FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence
        (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)
        (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base)
        (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)).trans
      (FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence
        (C := GenericTargetNaturalSourceReconstructionLegCoordinates.FreeProductTarget w)
        (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base)
        (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)))).inverse.obj (𝟭 _)

/-- `inverseIdentityFunctor` is the descent functor of the strictified `_aux_pseudo`. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_unfold
    {X : Type} [TopologicalSpace X] {U V : Set X}
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X)) :
    TwoOpenFreeProductMappingInverseIdentityLegCoordinates.inverseIdentityFunctor
        hU hV hcover w =
      TwoOpenDescentFunctor.twoOpenDescentFunctor hU hV hcover
        (TwoOpenPseudoCoconeStrictification.strictifiedDescentDatum hcover
          (punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_pseudo w)) := rfl

/-- Remaining leaf (split after job 2537).  The left leg of `_aux_pseudo` sends `g` to
`inl g`.  The descent and strictification layers are already removed (`_aux_descent`,
`_aux_strict`, `_aux_unfold`); what is left is, from the inside out,
`representationSingleObjEquivalence.inverse.obj 𝟭`, `fromRepresentationFunctor`,
`TwoOpenPointSpanComparison.comparison.inverse`, `pseudoSpanEquivalence.inverse` (identity
on legs).  The comparison inverse should make the left leg
`(leftEquivalence U V w).functor ⋙ _`, i.e. `connectorSingleObjEquivalence (leftConnectors w)`
at the base point `w`, followed by `inl`. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_leg
    {X : Type} [TopologicalSpace X] {U V : Set X}
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
    (w : (U ∩ V : Set X)) (g : FundamentalGroup U ⟨w.1, w.2.1⟩) :
    (punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_pseudo (U := U) (V := V) w).left.map
        (show (⟨⟨w.1, w.2.1⟩⟩ : FundamentalGroupoid
            (FundamentalGroupoidTwoOpenDescent.CoverPiece U V true)) ⟶ ⟨⟨w.1, w.2.1⟩⟩ from g) =
      (Monoid.Coprod.inl g : Monoid.Coprod
        (End (TwoOpenLegCompatibleConnectorSystems.leftConnectors w).base)
        (End (TwoOpenLegCompatibleConnectorSystems.rightConnectors w).base)) := by
  sorry

/-- Left leg of the reconstructed source equivalence (re-routed 2026-10-22).  The
previous proof went through `mapping.functor` and its counit, which needed
`_forward_inl_aux_connector`; that connector compares against
`leftEquivalence.inverse`, a `Functor.asEquivalence` inverse built by `Classical.choice`,
and may not hold as stated, so it was removed.  Direct route: `sourceEquivalence.functor`
is `inverseIdentityFunctor = mapping.inverse.obj (𝟭 _)` by `rfl`.  Unfold `mapping.inverse`
on `FundamentalGroup.map (subtype incl) g`: `representationSingleObjEquivalence.inverse`,
then `freeProductPointSpanEquivalence.inverse`, then the comparison inverse
(`reverseTransportFunctor` along `eL.functor = normalFormFunctor`, no choice), then the
descent inverse (`reconstructionFunctor`).  The `U` leg gives the left leg of
`fromRepresentation` at `normalForm g`, and at the base point `normalForm` is `g` up to the
overlap connector at `w`, trivial since `U ∩ V` is simply connected. -/
lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)]
    (g : FundamentalGroup U ⟨w.1, w.2.1⟩) :
    (TwoOpenFreeProductMapping.sourceEquivalence hU hV hcover w).functor.map
        (FundamentalGroup.map
          (⟨((↑) : U → X), continuous_subtype_val⟩ : C(U, X)) ⟨w.1, w.2.1⟩ g) =
      Monoid.Coprod.inl g := by
  change (TwoOpenFreeProductMappingInverseIdentityLegCoordinates.inverseIdentityFunctor
    hU hV hcover w).map _ = _
  rw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_unfold hU hV hcover w]
  have h := punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_descent hU hV hcover
    (TwoOpenPseudoCoconeStrictification.strictifiedDescentDatum hcover (punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_pseudo w))
    (show (⟨⟨w.1, w.2.1⟩⟩ : FundamentalGroupoid
        (FundamentalGroupoidTwoOpenDescent.CoverPiece U V true)) ⟶ ⟨⟨w.1, w.2.1⟩⟩ from g)
  rw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_strict] at h
  refine h.trans ?_
  rw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left_aux_leg]
  rfl

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)]
    (g : FundamentalGroup U ⟨w.1, w.2.1⟩) :
    TwoOpenFreeProductMapping.groupEquivalence hU hV hcover w
        (FundamentalGroup.map
          (⟨((↑) : U → X), continuous_subtype_val⟩ : C(U, X)) ⟨w.1, w.2.1⟩ g) =
      Monoid.Coprod.inl g := by
  rw [punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_groupEquivalence_apply]
  exact punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective_aux_left_aux_sourceFunctor_left
    U V hU hV hcover w g

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    Function.Bijective
      (FundamentalGroup.map
        (⟨((↑) : U → X), continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩) := by
  sorry

lemma punctured_fundamentalGroup_three_aux_van_kampen
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (y : X) [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    Nonempty (FundamentalGroup U ⟨x, hxU⟩ ≃* FundamentalGroup X y) := by
  let i : C(U, X) := ⟨((↑) : U → X), continuous_subtype_val⟩
  have hi : Function.Bijective (FundamentalGroup.map i ⟨x, hxU⟩) :=
    punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective
      U V hU hV hcover x hxU hxV
  exact ⟨(MulEquiv.ofBijective (FundamentalGroup.map i ⟨x, hxU⟩) hi).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y)⟩

theorem punctured_fundamentalGroup_three (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace (E 3) M] [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (m : M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    Nonempty (FundamentalGroup c.Punctured (c.boundaryMap s) ≃*
      FundamentalGroup M m) := by
  obtain ⟨U, V, hU, hV, hcover, hu, hv, hpcU, hscV, hscUV, e, pe⟩ :=
    punctured_fundamentalGroup_three_aux_cover M c s hopen hpath
  letI : PathConnectedSpace U := hpcU
  letI : SimplyConnectedSpace V := hscV
  letI : SimplyConnectedSpace (U ∩ V : Set M) := hscUV
  let u : U := ⟨c.boundaryMap s, hu⟩
  obtain ⟨pe⟩ := pe
  obtain ⟨g₁⟩ := punctured_fundamentalGroup_three_aux_of_hequiv
    (c.boundaryMap s) u e pe
  obtain ⟨g₂⟩ := punctured_fundamentalGroup_three_aux_van_kampen
    U V hU hV hcover (c.boundaryMap s) hu hv m
  exact ⟨g₁.trans g₂⟩

/-- **LIBRARY (B7).** The connected-sum quotient's standard open cover. -/
theorem connectedSum_standardCover_aux_collar_open
    {n : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    IsOpen {x : c.Punctured | x.1 ∈ c.radialTwo} ∧
      ∀ s, c.boundaryMap s ∈ {x : c.Punctured | x.1 ∈ c.radialTwo} := by
  refine ⟨hopen.preimage continuous_subtype_val, fun s ↦ ?_⟩
  refine ⟨unitToLarge n (sphereToDisk n s), ?_, c.largeMap_unitToLarge _⟩
  have hs : dist s.1 0 = 1 := by
    simpa [Metric.mem_sphere, dist_comm] using s.2
  change dist s.1 0 < 2
  linarith

/-- The open thickening of the first piece: all of it, plus the open collar
`radialTwo` of the second piece.  (Reference: the proved dimension-3 analogue
`apm_t00A01_thickLeft` in `holes/labs/blueprints/t00A01/Blueprint.lean`.) -/
def connectedSum_standardCover_aux_thickLeft {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Set.range Sum.inl ∪ Sum.inr '' {x : c₂.Punctured | x.1 ∈ c₂.radialTwo})

/-- The open thickening of the second piece: the open collar of the first
piece, plus all of the second. -/
def connectedSum_standardCover_aux_thickRight {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Sum.inl '' {x : c₁.Punctured | x.1 ∈ c₁.radialTwo} ∪ Set.range Sum.inr)

/-- LEAF. Both thickenings are open and cover the connected sum.  Sketch: each
is saturated for the gluing relation, and its preimage in each summand is
either everything or the open collar (`_aux_collar_open`).  Dimension-3
analogue: `apm_t00A01_collared_standardCover_aux_open`. -/
theorem connectedSum_standardCover_aux_open {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    IsOpen (connectedSum_standardCover_aux_thickLeft c₁ c₂) ∧
      IsOpen (connectedSum_standardCover_aux_thickRight c₁ c₂) ∧
      connectedSum_standardCover_aux_thickLeft c₁ c₂ ∪
        connectedSum_standardCover_aux_thickRight c₁ c₂ = Set.univ := by
  let CA : Set c₁.Punctured := {x | x.1 ∈ c₁.radialTwo}
  let CB : Set c₂.Punctured := {x | x.1 ∈ c₂.radialTwo}
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z ↦ Quotient.mk _ z
  let L : Set (Sum c₁.Punctured c₂.Punctured) :=
    Set.range Sum.inl ∪ Sum.inr '' CB
  let R : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' CA ∪ Set.range Sum.inr
  have hCA : IsOpen CA := hopen₁.preimage continuous_subtype_val
  have hCB : IsOpen CB := hopen₂.preimage continuous_subtype_val
  have hiA : ∀ s, c₁.boundaryMap s ∈ CA := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₁.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hiB : ∀ s, c₂.boundaryMap s ∈ CB := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hL_invariant {x y : Sum c₁.Punctured c₂.Punctured}
      (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) : x ∈ L ↔ y ∈ L := by
    induction hxy with
    | rel x y h =>
        cases h with
        | boundary s =>
            constructor
            · intro _
              exact Or.inr ⟨c₂.boundaryMap s, hiB s, rfl⟩
            · intro _
              exact Or.inl ⟨c₁.boundaryMap s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hR_invariant {x y : Sum c₁.Punctured c₂.Punctured}
      (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) : x ∈ R ↔ y ∈ R := by
    induction hxy with
    | rel x y h =>
        cases h with
        | boundary s =>
            constructor
            · intro _
              exact Or.inr ⟨c₂.boundaryMap s, rfl⟩
            · intro _
              exact Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hpreL : q ⁻¹' (q '' L) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hL_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hpreR : q ⁻¹' (q '' R) = R := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hR_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hopenL : IsOpen L :=
    IsOpen.union isOpen_range_inl (isOpenMap_inr _ hCB)
  have hopenR : IsOpen R :=
    IsOpen.union (isOpenMap_inl _ hCA) isOpen_range_inr
  constructor
  · change IsOpen (q '' L)
    rw [isOpen_coinduced]
    exact hpreL.symm ▸ hopenL
  constructor
  · change IsOpen (q '' R)
    rw [isOpen_coinduced]
    exact hpreR.symm ▸ hopenR
  · apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | _ x =>
        cases x with
        | inl a =>
            left
            exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩
        | inr b =>
            right
            exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, rfl⟩

/-- Points of a collar's punctured manifold whose underlying collar point is
a large-collar point with radius under two: the open collar `1 ≤ ‖y‖ < 2`. -/
abbrev connectedSum_standardCover_aux_collar {n : ℕ} {M : Type}
    [TopologicalSpace M] (c : BallCollar n M) : Set c.Punctured :=
  {x : c.Punctured | x.1 ∈ c.radialTwo}

/-- A large-collar coordinate of a punctured point has norm at least one.
(Proved by lemma-2.) -/
lemma connectedSum_standardCover_aux_left_aux_norm_ge_one
    {n : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (z : c.Punctured) (x : Disk n 2) (hx : c.largeMap x = z.1) :
    1 ≤ ‖x.1‖ := by
  by_contra hn
  have hxlt : ‖x.1‖ < 1 := lt_of_not_ge hn
  apply z.2
  let y : Disk n 1 := ⟨x.1, by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hxlt⟩
  refine ⟨y, ?_, ?_⟩
  · simpa [y, dist_zero_right] using hxlt
  · rw [← hx]
    exact (congrFun c.compatible y).symm

/-- LEAF. The open collar strong-deformation-retracts onto the boundary
sphere, radially.  Sketch: a collar point is `largeMap y` with `1 ≤ ‖y‖ < 2`
(`_aux_left_aux_norm_ge_one`); `y` depends continuously on the point because
`largeMap` is an embedding (`largeEmbedding.toHomeomorph.symm` on its range).
Take `r = y / ‖y‖` and `H (x, t) = largeMap ((1 - t) • y + t • (y / ‖y‖))`;
the radius stays in `[1, ‖y‖]`, so `H` stays in the collar and off the open
unit ball, and points with `‖y‖ = 1` (the boundary sphere) are fixed.  For
`n = 0` the collar is empty.  Proved dimension-3 analogue, to port:
`apm_t00A01_collared_standardCover_aux_left_aux_radial` in
`holes/labs/blueprints/t00A01/Blueprint.lean`. -/
theorem connectedSum_standardCover_aux_radial {n : ℕ} {M : Type}
    [TopologicalSpace M] (c : BallCollar n M) :
    ∃ (r : C(↥(connectedSum_standardCover_aux_collar c), Sphere n))
      (H : C(↥(connectedSum_standardCover_aux_collar c) × unitInterval,
        c.Punctured)),
      (∀ s (h : c.boundaryMap s ∈ connectedSum_standardCover_aux_collar c),
        r ⟨_, h⟩ = s) ∧
      (∀ x, H (x, 0) = x.1) ∧
      (∀ x, H (x, 1) = c.boundaryMap (r x)) ∧
      (∀ p, H p ∈ connectedSum_standardCover_aux_collar c) ∧
      (∀ s (h : c.boundaryMap s ∈ connectedSum_standardCover_aux_collar c) t,
        H (⟨_, h⟩, t) = c.boundaryMap s) := by
  classical
  let C := connectedSum_standardCover_aux_collar c
  let j : C → Set.range c.largeMap := fun x ↦
    ⟨x.1.1, by
      rcases x.2 with ⟨y, hy, hxy⟩
      exact ⟨y, hxy⟩⟩
  let d : C → Disk n 2 := fun x ↦ c.largeEmbedding.toHomeomorph.symm (j x)
  have hj : Continuous j := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have hd : Continuous d := c.largeEmbedding.toHomeomorph.symm.continuous.comp hj
  have hd_image (x : C) : c.largeMap (d x) = x.1.1 := by
    exact congrArg Subtype.val (c.largeEmbedding.toHomeomorph.apply_symm_apply (j x))
  have hd_norm (x : C) : 1 ≤ ‖(d x).1‖ :=
    connectedSum_standardCover_aux_left_aux_norm_ge_one c x.1 (d x) (hd_image x)
  have hd_ne (x : C) : ‖(d x).1‖ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hd_norm x))
  let rv : C → E n := fun x ↦ (‖(d x).1‖)⁻¹ • (d x).1
  have hrv_norm (x : C) : ‖rv x‖ = 1 := by
    simp [rv, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hd_ne x]
  let r : C(C, Sphere n) :=
    ⟨fun x ↦ ⟨rv x, by simpa [Metric.mem_sphere, dist_zero_right] using hrv_norm x⟩, by
      apply Continuous.subtype_mk
      exact ((continuous_norm.comp
        (continuous_subtype_val.comp hd)).inv₀ (fun x ↦ hd_ne x)).smul
          (continuous_subtype_val.comp hd)⟩
  let v : C × unitInterval → E n := fun p ↦
    ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹) • (d p.1).1
  have hv_norm (p : C × unitInterval) :
      ‖v p‖ = (1 - (p.2 : ℝ)) * ‖(d p.1).1‖ + (p.2 : ℝ) := by
    have hn : 0 < ‖(d p.1).1‖ := lt_of_lt_of_le zero_lt_one (hd_norm p.1)
    have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
    have ht1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
    have hinv : 0 < (‖(d p.1).1‖)⁻¹ := inv_pos.mpr hn
    have ha : 0 ≤ (1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹ := by
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹ := mul_nonneg ht0 hinv.le
      linarith
    simp only [v, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg ha]
    field_simp
  have hv_ge (p : C × unitInterval) : 1 ≤ ‖v p‖ := by
    rw [hv_norm]
    nlinarith [hd_norm p.1, p.2.2.1, p.2.2.2]
  have hv_le (p : C × unitInterval) : ‖v p‖ ≤ 2 := by
    rw [hv_norm]
    have hn2 : ‖(d p.1).1‖ ≤ 2 := by
      have hh := (d p.1).2
      change dist (d p.1).1 0 ≤ 2 at hh
      simpa [dist_zero_right] using hh
    nlinarith [p.2.2.1, p.2.2.2]
  let w : C × unitInterval → Disk n 2 := fun p ↦
    ⟨v p, by simpa [Metric.mem_closedBall, dist_zero_right] using hv_le p⟩
  have hw_cont : Continuous w := by
    apply Continuous.subtype_mk
    exact (((continuous_const.sub
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul
          ((continuous_norm.comp
            (continuous_subtype_val.comp (hd.comp continuous_fst))).inv₀
              (fun p ↦ hd_ne p.1)))).smul
        (continuous_subtype_val.comp (hd.comp continuous_fst)))
  have hw_punctured (p : C × unitInterval) :
      c.largeMap (w p) ∉ c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1} := by
    rintro ⟨y, hy, heq⟩
    have heq' : w p = unitToLarge n y := by
      apply c.largeEmbedding.injective
      exact heq.symm.trans (congrFun c.compatible y).symm
    have : ‖v p‖ < 1 := by
      have hv : v p = y.1 := congrArg Subtype.val heq'
      rw [hv]
      simpa [dist_zero_right] using hy
    exact (not_lt_of_ge (hv_ge p)) this
  let H : C(C × unitInterval, c.Punctured) :=
    ⟨fun p ↦ ⟨c.largeMap (w p), hw_punctured p⟩,
      Continuous.subtype_mk (c.largeEmbedding.continuous.comp hw_cont) _⟩
  refine ⟨r, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply Subtype.ext
    change rv ⟨c.boundaryMap s, hs⟩ = s.1
    have hd_eq : d ⟨c.boundaryMap s, hs⟩ = unitToLarge n
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply c.largeEmbedding.injective
      rw [hd_image]
      exact (congrFun c.compatible _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    simp [rv, hd_eq, unitToLarge, hs_norm]
  · intro x
    apply Subtype.ext
    change c.largeMap (w (x, 0)) = x.1.1
    rw [show w (x, 0) = d x by
      apply Subtype.ext
      simp [w, v]]
    exact hd_image x
  · intro x
    apply Subtype.ext
    change c.largeMap (w (x, 1)) = c.smallMap _
    rw [show w (x, 1) = unitToLarge n
        ⟨rv x, by simpa [Metric.mem_closedBall, dist_zero_right] using (hrv_norm x).le⟩ by
      apply Subtype.ext
      change v (x, 1) = rv x
      simp [v, rv]]
    exact congrFun c.compatible _
  · intro p
    change c.largeMap (w p) ∈ c.largeMap '' {y : Disk n 2 | dist y.1 0 < 2}
    refine ⟨w p, ?_, rfl⟩
    have hd_lt : ‖(d p.1).1‖ < 2 := by
      rcases p.1.2 with ⟨y, hy, hyeq⟩
      have : d p.1 = y := c.largeEmbedding.injective ((hd_image p.1).trans hyeq.symm)
      change dist y.1 0 < 2 at hy
      simpa [this, dist_zero_right] using hy
    have hvlt : ‖v p‖ < 2 := by
      rw [hv_norm]
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(d p.1).1‖ - 1) :=
        mul_nonneg p.2.2.1 (sub_nonneg.mpr (hd_norm p.1))
      nlinarith
    simpa [w, dist_zero_right] using hvlt
  · intro s hs t
    apply Subtype.ext
    change c.largeMap (w (⟨_, hs⟩, t)) = c.smallMap _
    have hd_eq : d ⟨c.boundaryMap s, hs⟩ = unitToLarge n
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply c.largeEmbedding.injective
      rw [hd_image]
      exact (congrFun c.compatible _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    rw [show w (⟨_, hs⟩, t) = unitToLarge n
        ⟨s.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hs_norm.le⟩ by
      apply Subtype.ext
      simp [w, v, hd_eq, unitToLarge, hs_norm]]
    exact congrFun c.compatible _

/-- Banked from lemma-2 (round 2 partial). -/
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
    {A B Z : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    (R : Sum A B → Sum A B → Prop)
    (S : Set (Quotient (Relation.EqvGen.setoid R))) (P : Set (Sum A B))
    (hP : IsOpen P)
    (hsat : (fun z : Sum A B ↦ Quotient.mk (Relation.EqvGen.setoid R) z) ⁻¹' S = P)
    (F : unitInterval × ↥S → Z)
    (hF : Continuous fun p : unitInterval × ↥P ↦
      F (p.1, ⟨Quotient.mk (Relation.EqvGen.setoid R) p.2.1,
        (Set.ext_iff.mp hsat p.2.1).mpr p.2.2⟩)) : Continuous F := by
  let q : Sum A B → Quotient (Relation.EqvGen.setoid R) := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hS : IsOpen S := by
    rw [← hq.isOpen_preimage]
    change IsOpen ((fun z : Sum A B ↦ Quotient.mk (Relation.EqvGen.setoid R) z) ⁻¹' S)
    rw [hsat]
    exact hP
  have hqS : Topology.IsQuotientMap (S.restrictPreimage q) :=
    hq.restrictPreimage_isOpen hS
  let e : ↥P ≃ₜ ↥(q ⁻¹' S) := Homeomorph.setCongr hsat.symm
  have he : Topology.IsQuotientMap e := e.isQuotientMap
  have hcomp : S.restrictPreimage q ∘ e = fun x : ↥P ↦
      (⟨Quotient.mk (Relation.EqvGen.setoid R) x.1,
        (Set.ext_iff.mp hsat x.1).mpr x.2⟩ : ↥S) := by
    funext x
    rfl
  apply (hqS.comp he).continuous_lift_prod_right
  simpa only [hcomp] using hF

/-- Banked from lemma-1 (round 2 partial). -/
lemma connectedSum_standardCover_aux_right_aux_quotient_aux_mem
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (C : Set c₁.Punctured) (hiA : ∀ s, c₁.boundaryMap s ∈ C)
    {x y : Sum c₁.Punctured c₂.Punctured}
    (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Sum.inl '' C ∪ Set.range Sum.inr) ↔
      (y ∈ Sum.inl '' C ∪ Set.range Sum.inr) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s =>
          constructor
          · exact fun _ => Or.inr ⟨c₂.boundaryMap s, rfl⟩
          · exact fun _ => Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma connectedSum_standardCover_aux_right_aux_quotient_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiA : ∀ s, c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickRight c₁ c₂ =
      Sum.inl '' connectedSum_standardCover_aux_collar c₁ ∪ Set.range Sum.inr := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_right_aux_quotient_aux_mem
      c₁ c₂ (connectedSum_standardCover_aux_collar c₁) hiA
        (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_right_aux_quotient_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set A) (hC : IsOpen C)
    (F : unitInterval × ↥((@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)) → X)
    (hL : Continuous fun p : unitInterval × ↥C =>
      F (p.1, ⟨Sum.inl p.2.1, Or.inl ⟨p.2.1, p.2.2, rfl⟩⟩))
    (hR : Continuous fun p : unitInterval × B =>
      F (p.1, ⟨Sum.inr p.2, Or.inr ⟨p.2, rfl⟩⟩)) : Continuous F := by
  let P : Set (Sum A B) := (@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)
  let jL : C → P := fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
  let jR : B → P := fun b => ⟨Sum.inr b, Or.inr ⟨b, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inl (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro a a' h; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inr (X := A) (Y := B)) _
    · intro b b' h; exact Sum.inr.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.codRestrict _
  let eL : unitInterval × C → unitInterval × P := fun p => (p.1, jL p.2)
  let eR : unitInterval × B → unitInterval × P := fun p => (p.1, jR p.2)
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
  have hcL : Continuous (F ∘ eL) := by simpa [Function.comp_def, eL, jL, P] using hL
  have hcR : Continuous (F ∘ eR) := by simpa [Function.comp_def, eR, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
    ext ⟨t, z, hz⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · simp [eL, jL, P, ha]
    · simp [eR, jR, P]
  rw [← hcover]
  have hcLi : ContinuousOn F (eL '' Set.univ) :=
    heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (eR '' Set.univ) :=
    heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using heL.isOpen_range)
    (by simpa only [Set.image_univ] using heR.isOpen_range)

/-- The inclusion of the kept summand into the left thickening. -/
def connectedSum_standardCover_aux_left_aux_quotient_aux_incl {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    C(c₁.Punctured, ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂)) :=
  ⟨fun a ↦ ⟨Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a), ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩⟩,
    (continuous_coinduced_rng.comp continuous_inl).subtype_mk _⟩

/-- LEAF. The forward map of the quotient step: a continuous map from the
thickening to the kept summand that is the identity on the kept summand and
`c₁.boundaryMap ∘ r` on the other summand's collar.  Sketch: it is well
defined because glued points `[inl c₁.boundaryMap s] = [inr c₂.boundaryMap s]`
go to `c₁.boundaryMap s` both ways (`hr`).  Continuity: the preimage of the
thickening in the sum is open and saturated, so the restricted quotient map is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`).  Do NOT use a
default point of the sphere or of the target (`EuclideanSpace.single 0 1`
needs `0 : Fin n` and fails for `n = 0`): define the map on the subtype, by
lifting along the restricted quotient map or by choosing a representative in
the saturated preimage (`Classical.choose` of the image membership). -/
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (C : Set c₂.Punctured) (hiB : ∀ s, c₂.boundaryMap s ∈ C)
    {x y : Sum c₁.Punctured c₂.Punctured}
    (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Set.range Sum.inl ∪ Sum.inr '' C) ↔
      (y ∈ Set.range Sum.inl ∪ Sum.inr '' C) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s =>
          constructor
          · exact fun _ => Or.inr ⟨c₂.boundaryMap s, hiB s, rfl⟩
          · exact fun _ => Or.inl ⟨c₁.boundaryMap s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiB : ∀ s, c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickLeft c₁ c₂ =
      Set.range Sum.inl ∪ Sum.inr '' connectedSum_standardCover_aux_collar c₂ := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
      c₁ c₂ (connectedSum_standardCover_aux_collar c₂) hiB
        (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set B) (hC : IsOpen C)
    (F : ↥(Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C) → X)
    (hL : Continuous fun a : A =>
      F ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩)
    (hR : Continuous fun b : C =>
      F ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩) : Continuous F := by
  let P : Set (Sum A B) := Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C
  let jL : A → P := fun a => ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
  let jR : C → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inl (X := A) (Y := B)) _
    · intro a a' h; exact Sum.inl.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inr (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hcL : Continuous (F ∘ jL) := by simpa [Function.comp_def, jL, P] using hL
  have hcR : Continuous (F ∘ jR) := by simpa [Function.comp_def, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range jL ∪ Set.range jR = Set.univ := by
    ext ⟨z, hz⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · simp [jL, P]
    · simp [jR, P, hb]
  rw [← hcover]
  have hcLi : ContinuousOn F (jL '' Set.univ) :=
    hjL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (jR '' Set.univ) :=
    hjR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using hjL.isOpen_range)
    (by simpa only [Set.image_univ] using hjR.isOpen_range)

theorem connectedSum_standardCover_aux_left_aux_quotient_aux_forward {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₂), Sphere n))
    (hr : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂),
      r ⟨_, h⟩ = s) :
    ∃ f : C(↥(connectedSum_standardCover_aux_thickLeft c₁ c₂), c₁.Punctured),
      (∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = a) ∧
      (∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr x.1) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = c₁.boundaryMap (r x)) := by
  classical
  let C := connectedSum_standardCover_aux_collar c₂
  let U := connectedSum_standardCover_aux_thickLeft c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  have hiB (s : Sphere n) : c₂.boundaryMap s ∈ C := by
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Set.range Sum.inl ∪ Sum.inr '' C :=
    connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_preimage c₁ c₂ hiB
  let P : Set (Sum c₁.Punctured c₂.Punctured) := Set.range Sum.inl ∪ Sum.inr '' C
  let e : P ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hpre.symm
  let qP : C(P, U) :=
    ⟨fun z => ⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩,
      Continuous.subtype_mk
        ((continuous_coinduced_rng.comp continuous_subtype_val)) _⟩
  have hU : IsOpen U :=
    (connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂).1
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hqP : Topology.IsQuotientMap qP := by
    have hres := hq.restrictPreimage_isOpen hU
    have he : Topology.IsQuotientMap e := e.isQuotientMap
    exact hres.comp he
  let F : P → c₁.Punctured := fun z => match hz : z.1 with
    | Sum.inl a => a
    | Sum.inr b => c₁.boundaryMap (r ⟨b, by
        rcases z.2 with ⟨a, ha⟩ | ⟨b', hb', heq⟩
        · simp [hz] at ha
        · have hbb : b' = b := Sum.inr.inj (heq.trans hz)
          exact hbb ▸ hb'⟩)
  have hF : Continuous F := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_cont C
      (hopen₂.preimage continuous_subtype_val)
    · simpa [F, P] using (continuous_id : Continuous (id : c₁.Punctured → c₁.Punctured))
    · simpa [F, P] using c₁.continuous_boundaryMap.comp r.continuous
  have hfac : Function.FactorsThrough F qP := by
    intro x y hxy
    have hrel : Relation.EqvGen (GlueRel c₁ c₂) x.1 y.1 :=
      Quotient.exact (congrArg Subtype.val hxy)
    have hrelF {a b : Sum c₁.Punctured c₂.Punctured} (ha : a ∈ P) (hb : b ∈ P)
        (hab : Relation.EqvGen (GlueRel c₁ c₂) a b) :
        F ⟨a, ha⟩ = F ⟨b, hb⟩ := by
      induction hab with
      | rel a b h =>
          cases h with
          | boundary s =>
              change c₁.boundaryMap s = c₁.boundaryMap (r ⟨c₂.boundaryMap s, _⟩)
              rw [hr s]
      | refl => rfl
      | symm a b h ih => exact ih hb ha |>.symm
      | trans a b d hab hbd ihab ihbd =>
          have hm : b ∈ P :=
            (connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
              c₁ c₂ C hiB hab).mp ha
          exact (ihab ha hm).trans (ihbd hm hb)
    exact hrelF x.2 y.2 hrel
  let f : C(U, c₁.Punctured) := hqP.lift ⟨F, hF⟩ hfac
  refine ⟨f, ?_, ?_⟩
  · intro a ha
    let hp : P := ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
    have heq : f (qP hp) = F hp := by
      change (hqP.lift ⟨F, hF⟩ hfac) (qP hp) = F hp
      exact DFunLike.congr_fun (hqP.lift_comp ⟨F, hF⟩ hfac) hp
    simpa [qP, F, P, hp] using heq
  · intro x hx
    let hp : P := ⟨Sum.inr x.1, Or.inr ⟨x.1, x.2, rfl⟩⟩
    have heq : f (qP hp) = F hp := by
      change (hqP.lift ⟨F, hF⟩ hfac) (qP hp) = F hp
      exact DFunLike.congr_fun (hqP.lift_comp ⟨F, hF⟩ hfac) hp
    simpa [qP, F, P, hp] using heq

/-- LEAF. The backward homotopy of the quotient step: inclusion after the
forward map is homotopic to the identity of the thickening.  Sketch: the
homotopy is `[inl a] ↦ [inl a]`, `[inr x] ↦ [inr H (x, t)]`; it is well
defined on glued points by `hHfix`, starts at the identity by `hH0`, and ends
at `incl ∘ f` by `hH1` and `GlueRel.boundary`.  Continuity on
`unitInterval × thickening` via the banked helper
`connectedSum_standardCover_aux_left_aux_quotient_aux_continuous` (quotient
map times the locally compact `unitInterval`). -/
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_mem
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (C : Set c₂.Punctured) (hiB : ∀ s, c₂.boundaryMap s ∈ C)
    {x y : Sum c₁.Punctured c₂.Punctured}
    (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Set.range Sum.inl ∪ Sum.inr '' C) ↔
      (y ∈ Set.range Sum.inl ∪ Sum.inr '' C) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s =>
          constructor
          · exact fun _ => Or.inr ⟨c₂.boundaryMap s, hiB s, rfl⟩
          · exact fun _ => Or.inl ⟨c₁.boundaryMap s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiB : ∀ s, c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickLeft c₁ c₂ =
      Set.range Sum.inl ∪ Sum.inr '' connectedSum_standardCover_aux_collar c₂ := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_mem
      c₁ c₂ _ hiB (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set B) (hC : IsOpen C)
    (F : unitInterval × ↥(Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C) → X)
    (hL : Continuous fun p : unitInterval × A =>
      F (p.1, ⟨Sum.inl p.2, Or.inl ⟨p.2, rfl⟩⟩))
    (hR : Continuous fun p : unitInterval × ↥C =>
      F (p.1, ⟨Sum.inr p.2.1, Or.inr ⟨p.2.1, p.2.2, rfl⟩⟩)) : Continuous F := by
  let P : Set (Sum A B) := Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C
  let jL : A → P := fun a => ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
  let jR : C → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inl (X := A) (Y := B)) _
    · intro a a' h; exact Sum.inl.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inr (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  let eL : unitInterval × A → unitInterval × P := fun p => (p.1, jL p.2)
  let eR : unitInterval × C → unitInterval × P := fun p => (p.1, jR p.2)
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
  have hcL : Continuous (F ∘ eL) := by simpa [Function.comp_def, eL, jL, P] using hL
  have hcR : Continuous (F ∘ eR) := by simpa [Function.comp_def, eR, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
    ext ⟨t, z, hz⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · simp [eL, jL, P]
    · simp [eR, jR, P, hb]
  rw [← hcover]
  have hcLi : ContinuousOn F (eL '' Set.univ) :=
    heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (eR '' Set.univ) :=
    heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using heL.isOpen_range)
    (by simpa only [Set.image_univ] using heR.isOpen_range)

theorem connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₂), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₂) × unitInterval,
      c₂.Punctured))
    (hr : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₂.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₂)
    (hHfix : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) t,
      H (⟨_, h⟩, t) = c₂.boundaryMap s)
    (f : C(↥(connectedSum_standardCover_aux_thickLeft c₁ c₂), c₁.Punctured))
    (hfk : ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = a)
    (hfo : ∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr x.1) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = c₁.boundaryMap (r x)) :
    ContinuousMap.Homotopic ((connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂).comp f)
      (ContinuousMap.id _) := by
  classical
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  let U := connectedSum_standardCover_aux_thickLeft c₁ c₂
  let C := connectedSum_standardCover_aux_collar c₂
  have hiB : ∀ s, c₂.boundaryMap s ∈ C := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Set.range Sum.inl ∪ Sum.inr '' C :=
    connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_preimage
      c₁ c₂ hiB
  have hif (b : c₂.Punctured) (hb : b ∈ C) (t : unitInterval) :
      (if hb' : b ∈ C then H (⟨b, hb'⟩, t) else b) = H (⟨b, hb⟩, t) := by
    rw [dif_pos hb]
  let Kraw : unitInterval × ConnectedSum c₁ c₂ → ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim (fun a => q (.inl a))
      (fun b => q (.inr (if hb : b ∈ C then H (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                dsimp only [Sum.elim_inl, Sum.elim_inr]
                rw [hif _ (hiB s), hHfix s (hiB s) p.1]
                exact Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, by rw [← heq]; simp [Kraw, q]⟩
    · exact ⟨Sum.inr (H (⟨b, hb⟩, p.1)),
        Or.inr ⟨_, hHC (⟨b, hb⟩, p.1), rfl⟩,
          by rw [← heq]; simp only [Kraw, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]⟩⟩
  have hC : IsOpen C := by
    exact IsOpen.preimage continuous_subtype_val hopen₂
  have hP : IsOpen (Set.range (@Sum.inl c₁.Punctured c₂.Punctured) ∪
      (@Sum.inr c₁.Punctured c₂.Punctured) '' C) :=
    (Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpen_range.union
      ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap C hC)
  have hK : Continuous K := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U (Set.range Sum.inl ∪ Sum.inr '' C) hP hpre K
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_cont C hC
    · apply Continuous.subtype_mk
      change Continuous (fun p : unitInterval × c₁.Punctured => q (Sum.inl p.2))
      exact continuous_coinduced_rng.comp (continuous_inl.comp continuous_snd)
    · apply Continuous.subtype_mk
      have heqfun : (fun x : unitInterval × C =>
          (K (x.1, ⟨q (Sum.inr x.2.1),
            (Set.ext_iff.mp hpre (Sum.inr x.2.1)).mpr
              (Or.inr ⟨x.2.1, x.2.2, rfl⟩)⟩)).1) =
          fun x => q (Sum.inr (H (x.2, x.1))) := by
        funext x
        simp only [K, Kraw, q, Quotient.lift_mk, Sum.elim_inr]
        rw [hif x.2.1 x.2.2]
      rw [heqfun]
      exact continuous_coinduced_rng.comp
        (continuous_inr.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst)))
  apply ContinuousMap.Homotopic.symm
  exact ⟨{
    toFun := fun p => K (p.1, p.2)
    continuous_toFun := hK
    map_zero_left := by
      intro x
      rcases x.2 with ⟨z, hz, heq⟩
      apply Subtype.ext
      change Kraw (0, x.1) = x.1
      rw [← heq]
      rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · simp [Kraw, q]
      · rw [show Kraw (0, q (Sum.inr b)) = q (Sum.inr (H (⟨b, hb⟩, 0))) by
          simp only [Kraw, q, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]]
        rw [hH0]
    map_one_left := by
      intro x
      rcases x.2 with ⟨z, hz, heq⟩
      apply Subtype.ext
      change Kraw (1, x.1) =
        ((connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂).comp f x).1
      rw [← heq]
      rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · have ha : q (Sum.inl a) ∈ U := ⟨_, Or.inl ⟨a, rfl⟩, rfl⟩
        have hx : x = ⟨q (Sum.inl a), ha⟩ := Subtype.ext heq.symm
        have fx : f x = a := by rw [hx]; exact hfk a ha
        simp [Kraw, q, fx, connectedSum_standardCover_aux_left_aux_quotient_aux_incl]
      · have hbU : q (Sum.inr b) ∈ U := ⟨_, Or.inr ⟨b, hb, rfl⟩, rfl⟩
        have hx : x = ⟨q (Sum.inr b), hbU⟩ := Subtype.ext heq.symm
        have fx : f x = c₁.boundaryMap (r ⟨b, hb⟩) := by
          rw [hx]
          exact hfo ⟨b, hb⟩ hbU
        rw [show Kraw (1, q (Sum.inr b)) = q (Sum.inr (H (⟨b, hb⟩, 1))) by
          simp only [Kraw, q, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]]
        rw [hH1]
        simp only [ContinuousMap.comp_apply, fx,
          connectedSum_standardCover_aux_left_aux_quotient_aux_incl]
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (GlueRel.boundary (r ⟨b, hb⟩)))).symm }⟩

/-- The inclusion of the kept summand into the right thickening. -/
def connectedSum_standardCover_aux_right_aux_quotient_aux_incl {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    C(c₂.Punctured, ↥(connectedSum_standardCover_aux_thickRight c₁ c₂)) :=
  ⟨fun a ↦ ⟨Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a), ⟨Sum.inr a, Or.inr ⟨a, rfl⟩, rfl⟩⟩,
    (continuous_coinduced_rng.comp continuous_inr).subtype_mk _⟩

/-- LEAF. The forward map of the quotient step: a continuous map from the
thickening to the kept summand that is the identity on the kept summand and
`c₂.boundaryMap ∘ r` on the other summand's collar.  Sketch: it is well
defined because glued points `[inl c₁.boundaryMap s] = [inr c₂.boundaryMap s]`
go to `c₂.boundaryMap s` both ways (`hr`).  Continuity: the preimage of the
thickening in the sum is open and saturated, so the restricted quotient map is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`).  Do NOT use a
default point of the sphere or of the target (`EuclideanSpace.single 0 1`
needs `0 : Fin n` and fails for `n = 0`): define the map on the subtype, by
lifting along the restricted quotient map or by choosing a representative in
the saturated preimage (`Classical.choose` of the image membership). -/
theorem connectedSum_standardCover_aux_right_aux_quotient_aux_forward {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₁), Sphere n))
    (hr : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁),
      r ⟨_, h⟩ = s) :
    ∃ f : C(↥(connectedSum_standardCover_aux_thickRight c₁ c₂), c₂.Punctured),
      (∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = a) ∧
      (∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl x.1) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = c₂.boundaryMap (r x)) := by
  classical
  let C := connectedSum_standardCover_aux_collar c₁
  let U := connectedSum_standardCover_aux_thickRight c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  let P : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' C ∪ Set.range Sum.inr
  have hiA : ∀ s, c₁.boundaryMap s ∈ C :=
    (connectedSum_standardCover_aux_collar_open c₁ hopen₁).2
  have hC : IsOpen C :=
    (connectedSum_standardCover_aux_collar_open c₁ hopen₁).1
  have hpre : q ⁻¹' U = P := by
    simpa [q, U, P, C] using
      connectedSum_standardCover_aux_right_aux_quotient_aux_preimage c₁ c₂ hiA
  have hP : IsOpen P := by
    exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
      (Y := c₂.Punctured)).isOpenMap _ hC).union
      (by simpa only [Set.image_univ] using
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap _ isOpen_univ))
  have inl_mem (a : c₁.Punctured) (ha : Sum.inl a ∈ P) : a ∈ C := by
    rcases ha with h | h
    · rcases h with ⟨a', ha', heq⟩
      exact (Sum.inl.inj heq) ▸ ha'
    · rcases h with ⟨b, h⟩
      cases h
  let k : P → c₂.Punctured := fun z =>
    (match x : z.1 with
      | Sum.inl a => fun hx => c₂.boundaryMap (r ⟨a, inl_mem a (x ▸ hx)⟩)
      | Sum.inr b => fun _ => b) z.2
  have hk_rel {x y : Sum c₁.Punctured c₂.Punctured}
      (hx : x ∈ P) (hy : y ∈ P)
      (he : Relation.EqvGen (GlueRel c₁ c₂) x y) :
      k ⟨x, hx⟩ = k ⟨y, hy⟩ := by
    induction he with
    | rel x y h =>
        cases h with
        | boundary s =>
            change c₂.boundaryMap (r ⟨c₁.boundaryMap s, _⟩) = c₂.boundaryMap s
            rw [hr s]
    | refl => rfl
    | symm x y h ih => exact ih hy hx |>.symm
    | trans x y z hxy hyz ihxy ihyz =>
        have hy' : y ∈ P :=
          (connectedSum_standardCover_aux_right_aux_quotient_aux_mem
            c₁ c₂ C hiA hxy).mp hx
        exact (ihxy hx hy').trans (ihyz hy' hy)
  have hk_eq (z w : P) (hzw : q z.1 = q w.1) : k z = k w := by
    have he : Relation.EqvGen (GlueRel c₁ c₂) z.1 w.1 := Quotient.exact hzw
    exact hk_rel z.2 w.2 he
  let rep : U → P := fun x => ⟨Classical.choose x.2,
    (Classical.choose_spec x.2).1⟩
  let f : U → c₂.Punctured := fun x => k (rep x)
  have hfq (z : P) : f ⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩ = k z := by
    apply hk_eq
    exact (Classical.choose_spec
      ((⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩ : U).2)).2
  have hk : Continuous k := by
    have hprod : Continuous (fun p : unitInterval × P => k p.2) := by
      apply connectedSum_standardCover_aux_right_aux_quotient_aux_cont C hC
      · convert (c₂.continuous_boundaryMap.comp
          (r.continuous.comp continuous_snd)) using 1
      · convert (continuous_snd : Continuous (fun p : unitInterval × c₂.Punctured => p.2)) using 1
    exact hprod.comp ((continuous_const.prodMk continuous_id) :
      Continuous (fun z : P => ((0 : unitInterval), z)))
  have hU : IsOpen U := by
    exact (connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂).2.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : P ≃ₜ q ⁻¹' U := Homeomorph.setCongr hpre.symm
    have heq : f ∘ U.restrictPreimage q = k ∘ e.symm := by
      funext z
      simpa [Function.comp_def, e] using hfq (e.symm z)
    have hc := hk.comp e.symm.continuous
    rw [heq]
    exact hc
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro a h
    have hz : (⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ : P) =
        ⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ := rfl
    simpa [f, k] using hfq (⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ : P)
  · intro x h
    have hx : x.1 ∈ C := x.2
    simpa [f, k] using hfq
      (⟨Sum.inl x.1, Or.inl ⟨x.1, hx, rfl⟩⟩ : P)

/-- LEAF. The backward homotopy of the quotient step: inclusion after the
forward map is homotopic to the identity of the thickening.  Sketch: the
homotopy is `[inr a] ↦ [inr a]`, `[inl x] ↦ [inl H (x, t)]`; it is well
defined on glued points by `hHfix`, starts at the identity by `hH0`, and ends
at `incl ∘ f` by `hH1` and `GlueRel.boundary`.  Continuity on
`unitInterval × thickening` via the banked helper
`connectedSum_standardCover_aux_left_aux_quotient_aux_continuous` (quotient
map times the locally compact `unitInterval`). -/
theorem connectedSum_standardCover_aux_right_aux_quotient_aux_homotopy {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₁), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₁) × unitInterval,
      c₁.Punctured))
    (hr : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₁.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₁)
    (hHfix : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁) t,
      H (⟨_, h⟩, t) = c₁.boundaryMap s)
    (f : C(↥(connectedSum_standardCover_aux_thickRight c₁ c₂), c₂.Punctured))
    (hfk : ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = a)
    (hfo : ∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl x.1) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = c₂.boundaryMap (r x)) :
    ContinuousMap.Homotopic ((connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂).comp f)
      (ContinuousMap.id _) := by
  classical
  let C := connectedSum_standardCover_aux_collar c₁
  let U := connectedSum_standardCover_aux_thickRight c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  have hiA (s : Sphere n) : c₁.boundaryMap s ∈ C := by
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₁.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Sum.inl '' C ∪ Set.range Sum.inr :=
    connectedSum_standardCover_aux_right_aux_quotient_aux_preimage c₁ c₂ hiA
  let P : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' C ∪ Set.range Sum.inr
  have hP : IsOpen P := by
    exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
      (Y := c₂.Punctured)).isOpenMap _
        (hopen₁.preimage continuous_subtype_val)).union
      (by simpa only [Set.image_univ] using
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap _ isOpen_univ))
  have hglue (s : Sphere n) :
      q (.inl (c₁.boundaryMap s)) = q (.inr (c₂.boundaryMap s)) :=
    Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
  let Kraw : unitInterval × ConnectedSum c₁ c₂ → ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ C then
        H (⟨a, ha⟩, unitInterval.symm p.1) else a)))
      (fun b => q (.inr b))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                simp only [Sum.elim_inl, Sum.elim_inr]
                rw [dif_pos (hiA s), hHfix s]
                exact hglue s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  have Kraw_inl (t : unitInterval) (a : c₁.Punctured) (ha : a ∈ C) :
      Kraw (t, q (.inl a)) =
        q (.inl (H (⟨a, ha⟩, unitInterval.symm t))) := by
    simp [Kraw, q, ha]
  have Kraw_inr (t : unitInterval) (b : c₂.Punctured) :
      Kraw (t, q (.inr b)) = q (.inr b) := by
    simp [Kraw, q]
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨Sum.inl (H (⟨a, ha⟩, unitInterval.symm p.1)),
        Or.inl ⟨_, hHC _, rfl⟩, by
          rw [← heq]
          exact (Kraw_inl p.1 a ha).symm⟩
    · exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, by
          rw [← heq]
          exact (Kraw_inr p.1 b).symm⟩⟩
  have hK : Continuous K := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U P hP hpre K
    apply connectedSum_standardCover_aux_right_aux_quotient_aux_cont C
      (hopen₁.preimage continuous_subtype_val)
    · have he : (fun p : unitInterval × ↥C =>
          K (p.1, ⟨q (Sum.inl p.2.1),
            (Set.ext_iff.mp hpre (Sum.inl p.2.1)).mpr
              (Or.inl ⟨p.2.1, p.2.2, rfl⟩)⟩)) =
          fun p => (⟨q (Sum.inl (H (p.2, unitInterval.symm p.1))), by
            exact ⟨Sum.inl (H (p.2, unitInterval.symm p.1)),
              Or.inl ⟨_, hHC _, rfl⟩, rfl⟩⟩ : U) := by
          funext p
          apply Subtype.ext
          exact Kraw_inl p.1 p.2 p.2.2
      rw [he]
      exact Continuous.subtype_mk
        (continuous_coinduced_rng.comp (continuous_inl.comp
          (H.continuous.comp (continuous_snd.prodMk
            (unitInterval.continuous_symm.comp continuous_fst))))) _
    · have he : (fun p : unitInterval × c₂.Punctured =>
          K (p.1, ⟨q (Sum.inr p.2),
            (Set.ext_iff.mp hpre (Sum.inr p.2)).mpr
              (Or.inr ⟨p.2, rfl⟩)⟩)) =
          fun p => (⟨q (Sum.inr p.2),
            ⟨Sum.inr p.2, Or.inr ⟨p.2, rfl⟩, rfl⟩⟩ : U) := by
          funext p
          apply Subtype.ext
          exact Kraw_inr p.1 p.2
      rw [he]
      exact Continuous.subtype_mk
        (continuous_coinduced_rng.comp (continuous_inr.comp continuous_snd)) _
  exact ⟨{
    toFun := K
    continuous_toFun := hK
    map_zero_left := by
      intro x
      apply Subtype.ext
      rcases x.2 with ⟨z, hz, heq⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
      · have hx : x = ⟨q (.inl a), by
            exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩⟩ :=
          Subtype.ext heq.symm
        subst x
        change Kraw (0, q (.inl a)) = q (.inr (f _))
        rw [hfo ⟨a, ha⟩]
        rw [Kraw_inl, unitInterval.symm_zero, hH1]
        exact hglue (r ⟨a, ha⟩)
      · have hx : x = ⟨q (.inr b), by
            exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, rfl⟩⟩ :=
          Subtype.ext heq.symm
        subst x
        change Kraw (0, q (.inr b)) = q (.inr (f _))
        rw [hfk b]
        exact Kraw_inr 0 b
    map_one_left := by
      intro x
      apply Subtype.ext
      rcases x.2 with ⟨z, hz, heq⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
      · change Kraw (1, x.1) = x.1
        rw [← heq]
        rw [Kraw_inl (ha := show a ∈ C from ha), unitInterval.symm_one, hH0]
      · change Kraw (1, x.1) = x.1
        rw [← heq]
        exact Kraw_inr 1 b }⟩

/-- ASSEMBLY (from `_aux_left_aux_quotient_aux_forward` and `_aux_homotopy`). Quotient step for the left thickening: a radial retraction of the
second collar gives a homotopy equivalence from `thickLeft` to the first
punctured summand that sends each `[inl a]` to `a`.  Sketch: `f [inl a] = a`,
`f [inr x] = c₁.boundaryMap (r x)` (well defined by `hr` and
`GlueRel.boundary`), `g a = [inl a]`; `f ∘ g = id` exactly, and `g ∘ f ≃ id`
by `[inl a] ↦ [inl a]`, `[inr x] ↦ [inr H (x, t)]` (compatible on glued points
by `hHfix`).  Continuity: the preimage of `thickLeft` is open and saturated
(`_aux_open`), so the restricted quotient map is a quotient map
(`IsQuotientMap.restrictPreimage_isOpen`), and stays one after `× unitInterval`
(locally compact).  Proved dimension-3 analogue, to port:
`apm_t00A01_collared_standardCover_aux_left_aux_quotient`; the extra clause
`e₁.toFun [inl a] = a` holds by definition of `f`. -/
theorem connectedSum_standardCover_aux_left_aux_quotient {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₂), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₂) × unitInterval,
      c₂.Punctured))
    (hr : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₂.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₂)
    (hHfix : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) t,
      H (⟨_, h⟩, t) = c₂.boundaryMap s) :
    ∃ e₁ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂) c₁.Punctured,
      ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈
          connectedSum_standardCover_aux_thickLeft c₁ c₂),
        e₁.toFun ⟨_, h⟩ = a := by
  obtain ⟨f, hfk, hfo⟩ := connectedSum_standardCover_aux_left_aux_quotient_aux_forward c₁ c₂ hopen₁ hopen₂ r hr
  have hright : f.comp (connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂) = ContinuousMap.id _ := by
    ext1 a
    exact hfk a _
  exact ⟨⟨f, connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂,
      connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy c₁ c₂ hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix f hfk hfo,
      by rw [hright]⟩, hfk⟩

/-- ASSEMBLY (from `_aux_right_aux_quotient_aux_forward` and `_aux_homotopy`). Mirror of `_aux_left_aux_quotient`: a radial retraction of the
first collar gives a homotopy equivalence from `thickRight` to the second
punctured summand that sends each `[inr b]` to `b`.  Sketch: `f [inr b] = b`,
`f [inl x] = c₂.boundaryMap (r x)` (well defined: `[inl c₁.boundaryMap s] =
[inr c₂.boundaryMap s]` and `hr`), `g b = [inr b]`; `f ∘ g = id`, and
`g ∘ f ≃ id` by `[inl x] ↦ [inl H (x, t)]`, `[inr b] ↦ [inr b]`; at `t = 1`,
`[inl c₁.boundaryMap (r x)] = [inr c₂.boundaryMap (r x)]`.  Continuity as in
`_aux_left_aux_quotient`.  Dimension-3 analogue: the mirror lemma after
`apm_t00A01_collared_standardCover_aux_left_aux_quotient`. -/
theorem connectedSum_standardCover_aux_right_aux_quotient {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₁), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₁) × unitInterval,
      c₁.Punctured))
    (hr : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₁.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₁)
    (hHfix : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁) t,
      H (⟨_, h⟩, t) = c₁.boundaryMap s) :
    ∃ e₂ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickRight c₁ c₂) c₂.Punctured,
      ∀ b (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr b) ∈
          connectedSum_standardCover_aux_thickRight c₁ c₂),
        e₂.toFun ⟨_, h⟩ = b := by
  obtain ⟨f, hfk, hfo⟩ := connectedSum_standardCover_aux_right_aux_quotient_aux_forward c₁ c₂ hopen₁ hopen₂ r hr
  have hright : f.comp (connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂) = ContinuousMap.id _ := by
    ext1 a
    exact hfk a _
  exact ⟨⟨f, connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂,
      connectedSum_standardCover_aux_right_aux_quotient_aux_homotopy c₁ c₂ hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix f hfk hfo,
      by rw [hright]⟩, hfk⟩

/-- ASSEMBLY (from `_aux_radial` on the second collar and
`_aux_left_aux_quotient`). The left thickening deformation retracts onto the
first punctured summand, and this equivalence sends the glued sphere to the
first collar boundary: it fixes `[inl a] ↦ a`, so the composite is equal to
`c₁.boundaryMap`. -/
theorem connectedSum_standardCover_aux_left {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₁ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂) c₁.Punctured,
      ∀ g : C(Sphere n, ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂)),
        (∀ s, (g s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s))) →
        ContinuousMap.Homotopic (e₁.toFun.comp g)
          ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ := by
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ := connectedSum_standardCover_aux_radial c₂
  obtain ⟨e₁, he₁⟩ := connectedSum_standardCover_aux_left_aux_quotient c₁ c₂
    hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix
  refine ⟨e₁, fun g hg ↦ ?_⟩
  have hcomp : e₁.toFun.comp g = ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ := by
    ext1 s
    have key : ∀ z : ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂),
        z.1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s)) → e₁.toFun z = c₁.boundaryMap s := by
      rintro ⟨z, hz⟩ hzs
      subst hzs
      exact he₁ _ hz
    exact key (g s) (hg s)
  rw [hcomp]

/-- ASSEMBLY (from `_aux_radial` on the first collar and
`_aux_right_aux_quotient`). The right thickening retracts onto the second
punctured summand, compatibly with the glued sphere, which equals the `inr`
image of the second collar boundary by `GlueRel.boundary`. -/
theorem connectedSum_standardCover_aux_right {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₂ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickRight c₁ c₂) c₂.Punctured,
      ∀ g : C(Sphere n, ↥(connectedSum_standardCover_aux_thickRight c₁ c₂)),
        (∀ s, (g s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s))) →
        ContinuousMap.Homotopic (e₂.toFun.comp g)
          ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩ := by
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ := connectedSum_standardCover_aux_radial c₁
  obtain ⟨e₂, he₂⟩ := connectedSum_standardCover_aux_right_aux_quotient c₁ c₂
    hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix
  refine ⟨e₂, fun g hg ↦ ?_⟩
  have hcomp : e₂.toFun.comp g = ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩ := by
    ext1 s
    have hglue : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
        (Sum.inl (c₁.boundaryMap s)) =
        Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inr (c₂.boundaryMap s)) :=
      Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
    have key : ∀ z : ↥(connectedSum_standardCover_aux_thickRight c₁ c₂),
        z.1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inr (c₂.boundaryMap s)) → e₂.toFun z = c₂.boundaryMap s := by
      rintro ⟨z, hz⟩ hzs
      subst hzs
      exact he₂ _ hz
    exact key (g s) ((hg s).trans hglue)
  rw [hcomp]

/-- LEAF. The overlap of the two thickenings is the union of the two open
collars glued along the sphere, an open annulus `S^{n-1} × (0, 2)` in radial
coordinates; it retracts onto the glued sphere, whose inclusion is the
inverse.  Dimension-3 analogue: `apm_t00A01_collared_standardCover_aux_inter`. -/
def connectedSum_standardCover_aux_inter_aux_thickLeft {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (CB : Set c₂.Punctured) : Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Set.range Sum.inl ∪ Sum.inr '' CB)

def connectedSum_standardCover_aux_inter_aux_thickRight {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (CA : Set c₁.Punctured) : Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Sum.inl '' CA ∪ Set.range Sum.inr)

lemma connectedSum_standardCover_aux_inter_aux_mk_eq {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (s : Sphere n) :
    Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl (c₁.boundaryMap s)) =
      Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr (c₂.boundaryMap s)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))

def connectedSum_standardCover_aux_inter_aux_spherePoint (m : ℕ) : Sphere (m + 1) :=
  ⟨EuclideanSpace.single ⟨0, Nat.succ_pos _⟩ 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

lemma connectedSum_standardCover_aux_inter_aux_saturated
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (CA : Set c₁.Punctured) (CB : Set c₂.Punctured) (hiA : ∀ s, c₁.boundaryMap s ∈ CA) (hiB : ∀ s, c₂.boundaryMap s ∈ CB)
    {x y : Sum c₁.Punctured c₂.Punctured} (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Sum.inl '' CA ∪ Sum.inr '' CB) ↔
      (y ∈ Sum.inl '' CA ∪ Sum.inr '' CB) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s => simp [hiA s, hiB s]
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

set_option maxHeartbeats 800000 in
lemma connectedSum_standardCover_aux_inter_aux_quotient
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (CA : Set c₁.Punctured) (CB : Set c₂.Punctured) (hCA : IsOpen CA) (hCB : IsOpen CB)
    (hiA : ∀ s, c₁.boundaryMap s ∈ CA) (hiB : ∀ s, c₂.boundaryMap s ∈ CB)
    (hiAc : Continuous c₁.boundaryMap)
    (s0 : Sphere n)
    (rA : C(↥CA, Sphere n)) (HA : C(↥CA × unitInterval, c₁.Punctured))
    (rB : C(↥CB, Sphere n)) (HB : C(↥CB × unitInterval, c₂.Punctured))
    (hrA : ∀ s, rA ⟨c₁.boundaryMap s, hiA s⟩ = s)
    (hrB : ∀ s, rB ⟨c₂.boundaryMap s, hiB s⟩ = s)
    (hHA0 : ∀ x, HA (x, 0) = x.1) (hHB0 : ∀ x, HB (x, 0) = x.1)
    (hHA1 : ∀ x, HA (x, 1) = c₁.boundaryMap (rA x))
    (hHB1 : ∀ x, HB (x, 1) = c₂.boundaryMap (rB x))
    (hHACA : ∀ p, HA p ∈ CA) (hHBCB : ∀ p, HB p ∈ CB)
    (hHAfix : ∀ s t, HA (⟨c₁.boundaryMap s, hiA s⟩, t) = c₁.boundaryMap s)
    (hHBfix : ∀ s t, HB (⟨c₂.boundaryMap s, hiB s⟩, t) = c₂.boundaryMap s) :
    ∃ e : ContinuousMap.HomotopyEquiv
      ↥(connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB ∩ connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA)
      (Sphere n), ∀ s, (e.invFun s).1 =
        Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s)) := by
  classical
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ := fun z => Quotient.mk _ z
  let U := connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB ∩ connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA
  have hpreL : q ⁻¹' connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB =
      Set.range Sum.inl ∪ Sum.inr '' CB := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (GlueRel c₁ c₂) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Set.range Sum.inl ∪ Sum.inr '' CB) ↔
          w ∈ Set.range Sum.inl ∪ Sum.inr '' CB := by
        simpa [Set.image_univ] using
          connectedSum_standardCover_aux_inter_aux_saturated
            c₁ c₂ Set.univ CB (fun _ => Set.mem_univ _) hiB hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpreR : q ⁻¹' connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA =
      Sum.inl '' CA ∪ Set.range Sum.inr := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (GlueRel c₁ c₂) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Sum.inl '' CA ∪ Set.range Sum.inr) ↔
          w ∈ Sum.inl '' CA ∪ Set.range Sum.inr := by
        simpa [Set.image_univ] using
          connectedSum_standardCover_aux_inter_aux_saturated
            c₁ c₂ CA Set.univ hiA (fun _ => Set.mem_univ _) hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpre : q ⁻¹' U = Sum.inl '' CA ∪ Sum.inr '' CB := by
    rw [Set.preimage_inter, hpreL, hpreR]
    ext z
    cases z <;> simp
  have hU : IsOpen U := by
    rw [isOpen_coinduced]
    change IsOpen (q ⁻¹' U)
    rw [hpre]
    exact
      ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap CA hCA).union
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap CB hCB)
  let ra : c₁.Punctured → Sphere n := fun a =>
    if ha : a ∈ CA then rA ⟨a, ha⟩ else s0
  let rb : c₂.Punctured → Sphere n := fun b =>
    if hb : b ∈ CB then rB ⟨b, hb⟩ else s0
  have hra (s) : ra (c₁.boundaryMap s) = s := by simp [ra, hiA s, hrA s]
  have hrb (s) : rb (c₂.boundaryMap s) = s := by simp [rb, hiB s, hrB s]
  let f0 : ConnectedSum c₁ c₂ → Sphere n :=
    Quotient.lift (Sum.elim ra rb) (by
      intro x y hxy
      induction hxy with
      | rel x y h => cases h with | boundary s => simp [hra s, hrb s]
      | refl => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)
  let f : U → Sphere n := fun x => f0 x.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) ≃ₜ q ⁻¹' U :=
      Homeomorph.setCongr hpre.symm
    have hn : Continuous (fun z : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) =>
        f ((U.restrictPreimage q) (e z))) := by
      let eL : CA → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) :=
        fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
      let eR : CB → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) :=
        fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
      have heL : Topology.IsOpenEmbedding eL := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inl.comp continuous_subtype_val
        · intro a a' h
          exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
            hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have heR : Topology.IsOpenEmbedding eR := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inr.comp continuous_subtype_val
        · intro b b' h
          exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
            hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have hcL : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) = rA by
          funext a
          change Sum.elim ra rb (e (eL a)).1 = rA a
          rw [show (e (eL a)).1 = Sum.inl a.1 by rfl]
          simp [ra, a.2]]
        exact rA.continuous
      have hcR : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) = rB by
          funext b
          change Sum.elim ra rb (e (eR b)).1 = rB b
          rw [show (e (eR b)).1 = Sum.inr b.1 by rfl]
          simp [rb, b.2]]
        exact rB.continuous
      rw [← continuousOn_univ]
      have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
        ext ⟨z, hz⟩
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, *]
      rw [← hcover]
      have hcLi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eL '' Set.univ) := heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
      have hcRi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eR '' Set.univ) := heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
      have hoL : IsOpen (eL '' Set.univ) := by
        simpa only [Set.image_univ] using heL.isOpen_range
      have hoR : IsOpen (eR '' Set.univ) := by
        simpa only [Set.image_univ] using heR.isOpen_range
      simpa only [Set.image_univ] using
        hcLi.union_of_isOpen hcRi hoL hoR
    rw [show f ∘ U.restrictPreimage q =
        (fun z => f ((U.restrictPreimage q) (e z))) ∘ e.symm by funext x; rfl]
    exact hn.comp e.symm.continuous
  let g : Sphere n → U := fun s =>
    ⟨q (.inl (c₁.boundaryMap s)),
      ⟨⟨.inl (c₁.boundaryMap s), Or.inl ⟨c₁.boundaryMap s, rfl⟩, rfl⟩,
       ⟨.inl (c₁.boundaryMap s), Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩, rfl⟩⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_coinduced_rng.comp (continuous_inl.comp
      hiAc)
  let Kraw : unitInterval × ConnectedSum c₁ c₂ →
      ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ CA then HA (⟨a, ha⟩, p.1) else a)))
      (fun b => q (.inr (if hb : b ∈ CB then HB (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                simp [hiA s, hiB s, hHAfix s p.1, hHBfix s p.1, q]
                exact connectedSum_standardCover_aux_inter_aux_mk_eq c₁ c₂ s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    obtain ⟨z, heq⟩ := Quotient.exists_rep p.2.1
    have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
      rw [← hpre]
      change Quotient.mk _ z ∈ U
      rw [heq]
      exact p.2.2
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · refine ⟨⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, rfl⟩, ?_⟩,
        ⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, hHACA _, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, ha]
    · refine ⟨⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, hHBCB _, rfl⟩, ?_⟩,
        ⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, hb]
    ⟩
  have hK : Continuous K := by
    let P : Set (Sum c₁.Punctured c₂.Punctured) := Sum.inl '' CA ∪ Sum.inr '' CB
    have hP : IsOpen P :=
      ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap CA hCA).union
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap CB hCB)
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U P hP hpre K
    let jL : CA → P := fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
    let jR : CB → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
    have hjL : Topology.IsOpenEmbedding jL := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inl.comp continuous_subtype_val
      · intro a a' h; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
          hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    have hjR : Topology.IsOpenEmbedding jR := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inr.comp continuous_subtype_val
      · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
          hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    let eL : unitInterval × CA → unitInterval × P := fun p => (p.1, jL p.2)
    let eR : unitInterval × CB → unitInterval × P := fun p => (p.1, jR p.2)
    have heL : Topology.IsOpenEmbedding eL :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
    have heR : Topology.IsOpenEmbedding eR :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
    let L := fun p : unitInterval × P =>
      K (p.1, ⟨q p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)
    have hcL : Continuous (L ∘ eL) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eL, jL, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inl.comp
          (HA.continuous.comp (continuous_snd.prodMk continuous_fst)))
    have hcR : Continuous (L ∘ eR) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eR, jR, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inr.comp
          (HB.continuous.comp (continuous_snd.prodMk continuous_fst)))
    rw [show (fun p : unitInterval × P =>
      K (p.1, ⟨Quotient.mk _ p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)) = L by rfl]
    rw [← continuousOn_univ]
    have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
      ext ⟨t, z, hz⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, jL, jR, *]
    rw [← hcover]
    have hcLi := (heL.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcL.continuousOn
    have hcRi := (heR.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcR.continuousOn
    simpa only [Set.image_univ] using
      hcLi.union_of_isOpen hcRi (by simpa only [Set.image_univ] using heL.isOpen_range) (by simpa only [Set.image_univ] using heR.isOpen_range)
  let F : C(U, Sphere n) := ⟨f, hf⟩
  let G : C(Sphere n, U) := ⟨g, hg⟩
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · apply ContinuousMap.Homotopic.symm
    exact ⟨{
      toFun := fun p => K (p.1, p.2)
      continuous_toFun := hK
      map_zero_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (0, x.1) = x.1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · simp [Kraw, q, ha, hHA0]
        · simp [Kraw, q, hb, hHB0]
      map_one_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (1, x.1) = (G.comp F x).1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · have fx : f x = rA ⟨a, ha⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, ra, ha]
          simp [Kraw, G, F, g, q, ha, hHA1, fx]
        · have fx : f x = rB ⟨b, hb⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, rb, hb]
          simp [Kraw, G, F, g, q, hb, hHB1, fx]
          exact (connectedSum_standardCover_aux_inter_aux_mk_eq c₁ c₂ (rB ⟨b, hb⟩)).symm }⟩
  · have heq : F.comp G = ContinuousMap.id (Sphere n) := by
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      exact congrArg Subtype.val (hra s)
    rw [heq]
  · intro s
    rfl


theorem connectedSum_standardCover_aux_inter {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₀ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂ ∩
          connectedSum_standardCover_aux_thickRight c₁ c₂) (Sphere n),
      ∀ s, (e₀.invFun s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
        (Sum.inl (c₁.boundaryMap s)) := by
  cases n with
  | zero =>
    let U := connectedSum_standardCover_aux_thickLeft c₁ c₂ ∩
      connectedSum_standardCover_aux_thickRight c₁ c₂
    have hsphere (s : Sphere 0) : False := by
      have hv : s.1 = 0 := Subsingleton.elim _ _
      have := s.2
      rw [hv] at this
      simpa [Metric.mem_sphere] using this
    have hiA : ∀ s : Sphere 0, c₁.boundaryMap s ∈ (∅ : Set c₁.Punctured) :=
      fun s ↦ (hsphere s).elim
    have hInv {x y : Sum c₁.Punctured c₂.Punctured}
        (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
        (x ∈ Sum.inl '' (∅ : Set c₁.Punctured) ∪ Sum.inr '' Set.univ) ↔
          y ∈ Sum.inl '' (∅ : Set c₁.Punctured) ∪ Sum.inr '' Set.univ :=
      connectedSum_standardCover_aux_inter_aux_saturated c₁ c₂ ∅ Set.univ
        hiA (fun _ ↦ Set.mem_univ _) hxy
    have hUempty : U = ∅ := by
      ext x
      constructor
      · rintro ⟨hxL, hxR⟩
        rcases hxL with ⟨z, hz, rfl⟩
        rcases hxR with ⟨w, hw, heq⟩
        rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
        · rcases hw with ⟨a', ha', rfl⟩ | ⟨b, rfl⟩
          · rcases ha' with ⟨y, _, hyeq⟩
            have hy0 : y.1 = 0 := Subsingleton.elim _ _
            have hge := connectedSum_standardCover_aux_left_aux_norm_ge_one
              c₁ a' y hyeq
            rw [hy0, norm_zero] at hge
            norm_num at hge
          · have hrel : Relation.EqvGen (GlueRel c₁ c₂) (Sum.inl a) (Sum.inr b) :=
              (Quotient.exact heq).symm
            have := (hInv hrel).mpr (by simp)
            simpa using this
        · rcases hb with ⟨y, _, hyeq⟩
          have hy0 : y.1 = 0 := Subsingleton.elim _ _
          have hge := connectedSum_standardCover_aux_left_aux_norm_ge_one
            c₂ b y hyeq
          rw [hy0, norm_zero] at hge
          norm_num at hge
      · simp
    have hemptyU (x : ↥U) : False := by
      have hx : x.1 ∈ (∅ : Set (ConnectedSum c₁ c₂)) := hUempty ▸ x.2
      exact hx
    let F : C(↥U, Sphere 0) :=
      ⟨fun x ↦ (hemptyU x).elim, by
        rw [continuous_iff_continuousAt]
        intro x
        exact (hemptyU x).elim⟩
    let G : C(Sphere 0, ↥U) :=
      ⟨fun s ↦ (hsphere s).elim, continuous_of_discreteTopology⟩
    let e₀ : ContinuousMap.HomotopyEquiv ↥U (Sphere 0) :=
      { toFun := F
        invFun := G
        left_inv := by
          have heq : G.comp F = ContinuousMap.id _ := by
            ext x
            exact (hemptyU x).elim
          rw [heq]
        right_inv := by
          have heq : F.comp G = ContinuousMap.id _ := by
            ext s
            exact (hsphere s).elim
          rw [heq] }
    exact ⟨e₀, fun s ↦ (hsphere s).elim⟩
  | succ m =>
    obtain ⟨r₁, H₁, hr₁, hH₁zero, hH₁one, hH₁C, hH₁fix⟩ :=
      connectedSum_standardCover_aux_radial c₁
    obtain ⟨r₂, H₂, hr₂, hH₂zero, hH₂one, hH₂C, hH₂fix⟩ :=
      connectedSum_standardCover_aux_radial c₂
    have hC₁ := connectedSum_standardCover_aux_collar_open c₁ hopen₁
    have hC₂ := connectedSum_standardCover_aux_collar_open c₂ hopen₂
    obtain ⟨e₀, he₀⟩ := connectedSum_standardCover_aux_inter_aux_quotient c₁ c₂
      _ _ hC₁.1 hC₂.1 hC₁.2 hC₂.2 c₁.continuous_boundaryMap
      (connectedSum_standardCover_aux_inter_aux_spherePoint m)
      r₁ H₁ r₂ H₂ (fun s ↦ hr₁ s (hC₁.2 s)) (fun s ↦ hr₂ s (hC₂.2 s))
      hH₁zero hH₂zero hH₁one hH₂one hH₁C hH₂C
      (fun s t ↦ hH₁fix s (hC₁.2 s) t) (fun s t ↦ hH₂fix s (hC₂.2 s) t)
    exact ⟨e₀, he₀⟩

theorem connectedSum_standardCover {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    HasStandardCover c₁ c₂ := by
  obtain ⟨hU, hV, hUV⟩ := connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₁, he₁⟩ := connectedSum_standardCover_aux_left c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₂, he₂⟩ := connectedSum_standardCover_aux_right c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₀, he₀⟩ := connectedSum_standardCover_aux_inter c₁ c₂ hopen₁ hopen₂
  exact ⟨_, _, hU, hV, hUV, e₁, e₂, e₀,
    he₁ _ fun s ↦ he₀ s, he₂ _ fun s ↦ he₀ s⟩

end BallCollar

/-- **LIBRARY (B9a).** The standard cover is connected in degree zero. -/
theorem connectedSum_mayerVietoris_zero
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hzero₁ : Nonempty (H 0 c₁.Punctured ≅ ModuleCat.of ℤ ℤ))
    (hzero₂ : Nonempty (H 0 c₂.Punctured ≅ ModuleCat.of ℤ ℤ))
    (hcover : HasStandardCover c₁ c₂) :
    Nonempty (H 0 (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) := by
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  let p₁ := Classical.choice hzero₁
  let p₂ := Classical.choice hzero₂
  let eUmod : H 0 U ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₁ 0 ≪≫ p₁
  let eVmod : H 0 V ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₂ 0 ≪≫ p₂
  let eSmod : H 0 (Sphere n) ≅ ModuleCat.of ℤ ℤ :=
    by
      have hdim : n - 1 + 1 = n := by omega
      rw [← hdim]
      exact ConstructionTargets.SphereHomology.sphereModuleH0IsoInt
        (n - 1) (by omega)
  let eImod : H 0 (U ∩ V : Set (ConnectedSum c₁ c₂)) ≅
      ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ 0 ≪≫ eSmod
  letI : Nonempty U :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eUmod
  letI : Nonempty V :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eVmod
  letI : Nonempty (U ∩ V : Set (ConnectedSum c₁ c₂)) :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eImod
  let eU :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of U) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eUmod
  let eV :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of V) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eVmod
  let eI :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂))) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eImod
  let eX :=
    ConstructionTargets.T00A01MayerVietorisAdapters.openCoverH0IsoOfCoordinates
      U V hU hV hUV eI eU eV
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of (ConnectedSum c₁ c₂)) 0 (ModuleCat.of ℤ ℤ) eX⟩

/-- **LIBRARY (B9b).** Mayer--Vietoris in the strict middle degrees. -/
lemma connectedSum_mayerVietoris_middle_aux_overlap_module_zero
    {n k : ℕ} {X : Type} [TopologicalSpace X]
    (I : Set X) (e : ContinuousMap.HomotopyEquiv I (Sphere n))
    (hk0 : k ≠ 0) (hktop : k ≠ n - 1) (hn : 1 ≤ n) :
    IsZero (H k I) := by
  have hdim : n - 1 + 1 = n := by omega
  have hs : IsZero (H k (Sphere n)) := by
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
      (n - 1) k hk0 hktop
  exact hs.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e k)

/-- In the middle degrees the Mayer--Vietoris map out of the overlap vanishes:
below `n - 1` the overlap (a sphere) has no homology, and in degree `n - 1`
the two components are the collar boundary maps up to the cover homotopies,
which vanish by `hboundary₁`, `hboundary₂`. -/
lemma connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
    {n k : ℕ} {M X : Type} [TopologicalSpace M] [TopologicalSpace X]
    (c : BallCollar n M) (U I : Set X)
    (eU : ContinuousMap.HomotopyEquiv U c.Punctured)
    (eI : ContinuousMap.HomotopyEquiv I (Sphere n))
    (inc : C(I, U))
    (hh : ContinuousMap.Homotopic (eU.toFun.comp (inc.comp eI.invFun))
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩)
    (hb : boundaryHomologyMap c k = 0) :
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition inc) k = 0 := by
  let G := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)
  have hbG : G.map (TopCat.ofHom
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩) = 0 := by
    open ConstructionTargets.IntegralSingularHomologyComparison in
      have hn := singularHomologyComparison_naturality
        (TopCat.ofHom ⟨c.boundaryMap, c.continuous_boundaryMap⟩) k
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom
        ⟨c.boundaryMap, c.continuous_boundaryMap⟩) = 0 at hb
    open ConstructionTargets.IntegralSingularHomologyComparison in
      rw [hb, forgetIntModules.map_zero, zero_comp] at hn
    rw [← cancel_epi
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere n)) k).hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn.symm
  rcases hh with ⟨K⟩
  have heq := ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder K)
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero K)
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one K) k
  have hcomp : G.map (TopCat.ofHom eI.invFun) ≫
      G.map (TopCat.ofHom inc) ≫ G.map (TopCat.ofHom eU.toFun) = 0 := by
    rw [← Category.assoc, ← G.map_comp, ← G.map_comp]
    change G.map (TopCat.ofHom (eU.toFun.comp (inc.comp eI.invFun))) = 0
    exact heq.trans hbG
  have homEq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
      {f g : C(A, B)} (h : ContinuousMap.Homotopic f g) :
      G.map (TopCat.ofHom f) = G.map (TopCat.ofHom g) := by
    rcases h with ⟨L⟩
    exact ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder L)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero L)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one L) k
  haveI : IsIso (G.map (TopCat.ofHom eI.invFun)) := by
    refine ⟨⟨G.map (TopCat.ofHom eI.toFun), ?_, ?_⟩⟩
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eI.toFun.comp eI.invFun)) = _
      rw [homEq eI.right_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eI.invFun.comp eI.toFun)) = _
      rw [homEq eI.left_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
  haveI : IsIso (G.map (TopCat.ofHom eU.toFun)) := by
    refine ⟨⟨G.map (TopCat.ofHom eU.invFun), ?_, ?_⟩⟩
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eU.invFun.comp eU.toFun)) = _
      rw [homEq eU.left_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eU.toFun.comp eU.invFun)) = _
      rw [homEq eU.right_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
  have hm : G.map (TopCat.ofHom inc) = 0 := by
    rw [← cancel_epi (G.map (TopCat.ofHom eI.invFun)),
      ← cancel_mono (G.map (TopCat.ofHom eU.toFun))]
    simpa only [zero_comp, comp_zero] using hcomp
  simpa [ConstructionTargets.SingularSubdivision.singularHomologyFunctor_map_eq_singularPostcomposition]
    using hm

lemma connectedSum_mayerVietoris_middle_aux_inter_zero
    (n : ℕ) (hn : 2 ≤ n) {X₁ X₂ : Type}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (U V : Set (ConnectedSum c₁ c₂))
    (e₁ : ContinuousMap.HomotopyEquiv U c₁.Punctured)
    (e₂ : ContinuousMap.HomotopyEquiv V c₂.Punctured)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n))
    (he₁ : ContinuousMap.Homotopic
      (e₁.toFun.comp ((ContinuousMap.inclusion Set.inter_subset_left).comp e₀.invFun))
      ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩)
    (he₂ : ContinuousMap.Homotopic
      (e₂.toFun.comp ((ContinuousMap.inclusion Set.inter_subset_right).comp e₀.invFun))
      ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      U V k = 0 := by
  by_cases hktop : k = n - 1
  · subst k
    let i₁ : C((U ∩ V : Set (ConnectedSum c₁ c₂)), U) :=
      ContinuousMap.inclusion Set.inter_subset_left
    let i₂ : C((U ∩ V : Set (ConnectedSum c₁ c₂)), V) :=
      ContinuousMap.inclusion Set.inter_subset_right
    have hi₁ := connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
      c₁ U (U ∩ V) e₁ e₀ i₁ he₁ hboundary₁
    have hi₂ := connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
      c₂ V (U ∩ V) e₂ e₀ i₂ he₂ hboundary₂
    unfold ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
    change biprod.lift
      (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition i₁) (n - 1))
      (-HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition i₂) (n - 1)) = 0
    rw [hi₁, hi₂, neg_zero]
    apply biprod.hom_ext <;> simp
  · have hm : IsZero (H k (U ∩ V : Set (ConnectedSum c₁ c₂))) :=
      connectedSum_mayerVietoris_middle_aux_overlap_module_zero
        (U ∩ V) e₀ (Nat.ne_of_gt hk0) hktop (by omega)
    have hg : IsZero (ConstructionTargets.SingularHomologyConcrete.SingularHomology k
        (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂)))) :=
      ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
        (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂))) k hm
    exact hg.eq_of_src _ _

/-- In the middle degrees the Mayer--Vietoris reassembly map is onto: for
`2 ≤ k` the overlap has no `H (k - 1)`; for `k = 1` the overlap is nonempty, so
its `H 0` injects into `H 0 U ⊞ H 0 V`. -/
lemma connectedSum_mayerVietoris_middle_aux_epi_aux_inter_mono_zero
    (n : ℕ) (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (U V : Set X)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n)) :
    Mono (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      U V 0) := by
  let eSmod : H 0 (Sphere n) ≅ ModuleCat.of ℤ ℤ := by
    have hdim : n - 1 + 1 = n := by omega
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleH0IsoInt
      (n - 1) (by omega)
  let eImod : H 0 (U ∩ V : Set X) ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ 0 ≪≫ eSmod
  let eI : ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
      (TopCat.of (U ∩ V : Set X)) ≅
      AddCommGrpCat.of ℤ :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (U ∩ V : Set X)) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eImod
  letI : Nonempty (U ∩ V : Set X) :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_singularH0_iso_int eI
  let fi : C((U ∩ V : Set X), U) :=
    ⟨fun x ↦ ⟨x.1, Set.inter_subset_left x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let imap := HomologicalComplex.homologyMap
    (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.toSSet.map
        (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
          (X := X) (A := U ∩ V) (B := U) Set.inter_subset_left))) 0
  have himap : Mono imap := by
    rw [show imap = HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition fi) 0 from
        ConstructionTargets.SingularExcision.topologicalSubspaceInclusion_homologyMap
          _ 0]
    have haugIso : IsIso
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) :=
      ConstructionTargets.SingularH0Augmentation.h0Augmentation_isIso_of_iso_int eI
    letI : IsIso
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) := haugIso
    have haugMono : Mono
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) := inferInstance
    have hnat :=
      ConstructionTargets.SingularH0Augmentation.h0Augmentation_naturality fi
    constructor
    intro Z g h heq
    apply (cancel_mono
      (ConstructionTargets.SingularH0Augmentation.h0Augmentation
        (X := (U ∩ V : Set X)))).1
    rw [← hnat]
    exact congrArg
      (fun q ↦ q ≫
        ConstructionTargets.SingularH0Augmentation.h0Augmentation (X := U)) heq
  letI : Mono imap := himap
  unfold ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
  change Mono (biprod.lift imap _)
  apply ConstructionTargets.MayerVietorisExactnessIsZero.mono_signedBiprodLift_of_mono_left

lemma connectedSum_mayerVietoris_middle_aux_epi
    (n : ℕ) (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n))
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    Epi (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) := by
  have hk : k - 1 + 1 = k := by omega
  rw [← hk]
  apply (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
    U V hU hV hUV (k - 1)).epi_f_iff.mpr
  by_cases hk1 : k = 1
  · subst k
    have hm : Mono
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
          U V 0) :=
      connectedSum_mayerVietoris_middle_aux_epi_aux_inter_mono_zero n hn U V e₀
    exact (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_intersection
      U V hU hV hUV 0).mono_g_iff.mp hm
  · have hzero : IsZero (H (k - 1) (U ∩ V : Set X)) :=
      connectedSum_mayerVietoris_middle_aux_overlap_module_zero
        (I := U ∩ V) e₀ (by omega) (by omega) (by omega)
    have hgroup : IsZero
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology
          (k - 1) (TopCat.of (U ∩ V : Set X))) :=
      ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
        (TopCat.of (U ∩ V : Set X)) (k - 1) hzero
    exact hgroup.eq_of_tgt _ _

/-- An isomorphic reassembly map, transported to integral module homology. -/
lemma connectedSum_mayerVietoris_middle_aux_assemble
    {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ)
    [IsIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k)]
    {A B : ModuleCat ℤ} (eu : H k U ≅ A) (ev : H k V ≅ B) :
    Nonempty (H k X ≅ ModuleCat.of ℤ (A × B)) := by
  let F := ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  let cU := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of U) k
  let cV := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of V) k
  let cX := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of X) k
  let eP := asIso
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V k)
  let eAB : H k U ⊞ H k V ≅ ModuleCat.of ℤ (A × B) :=
    ConstructionTargets.IntegralSingularHomologyComparison.moduleIsoOfUnderlyingIso
      (F.mapBiprod (H k U) (H k V) ≪≫
        biprod.mapIso (F.mapIso eu) (F.mapIso ev) ≪≫
        AddCommGrpCat.biprodIsoProd (F.obj A) (F.obj B))
  refine ⟨ConstructionTargets.IntegralSingularHomologyComparison.moduleIsoOfUnderlyingIso ?_ ≪≫
    eAB⟩
  exact cX ≪≫ eP.symm ≪≫
    (biprod.mapIso cU.symm cV.symm) ≪≫
    (F.mapBiprod (H k U) (H k V)).symm

theorem connectedSum_mayerVietoris_middle
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hpunct₁ :
      (∀ k, 0 < k → k < n → Nonempty (H k c₁.Punctured ≅ H k X₁)) ∧
      (∀ k, n ≤ k → IsZero (H k c₁.Punctured)))
    (hpunct₂ :
      (∀ k, 0 < k → k < n → Nonempty (H k c₂.Punctured ≅ H k X₂)) ∧
      (∀ k, n ≤ k → IsZero (H k c₂.Punctured)))
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (hcover : HasStandardCover c₁ c₂) :
    ∀ k, 0 < k → k < n → Nonempty (H k (ConnectedSum c₁ c₂) ≅
      ModuleCat.of ℤ ((H k X₁) × (H k X₂))) := by
  intro k hk0 hkn
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  haveI : Mono (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
      U V hU hV hUV k).mono_g_iff.mpr
      (connectedSum_mayerVietoris_middle_aux_inter_zero n hn c₁ c₂ hboundary₁ hboundary₂
        U V e₁ e₂ e₀ he₁ he₂ k hk0 hkn)
  haveI := connectedSum_mayerVietoris_middle_aux_epi n hn U V hU hV hUV e₀ k hk0 hkn
  haveI : IsIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) := isIso_of_mono_of_epi _
  exact connectedSum_mayerVietoris_middle_aux_assemble U V k
    ((ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₁ k).trans
      (Classical.choice (hpunct₁.1 k hk0 hkn)))
    ((ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₂ k).trans
      (Classical.choice (hpunct₂.1 k hk0 hkn)))

/-- **LIBRARY (B9c).** Mayer--Vietoris above the manifold dimension. -/
lemma connectedSum_mayerVietoris_above_aux_empty
    (X : Type) [TopologicalSpace X] [IsEmpty X] (k : ℕ) : IsZero (H k X) := by
  apply ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  letI := Classical.decEq
    (ConstructionTargets.SingularSubdivision.SingularSimplex (TopCat.of X) k)
  have hempty : IsEmpty
      (ConstructionTargets.SingularSubdivision.SingularSimplex (TopCat.of X) k) :=
    ⟨fun σ ↦ by
      let p : (SimplexCategory.toTop.obj (SimplexCategory.mk k)) :=
        Classical.choice inferInstance
      exact isEmptyElim (σ.down.hom p)⟩
  letI := hempty
  have hz : IsZero (AddCommGrpCat.of
      (DirectSum (ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of X) k) (fun _ ↦ ℤ))) := by
    apply AddCommGrpCat.isZero_of_subsingleton
  exact hz.of_iso
    (ConstructionTargets.SingularSubdivision.addCommGrpCoproductIsoDirectSum
      (ConstructionTargets.SingularSubdivision.SingularSimplex (TopCat.of X) k))

theorem connectedSum_mayerVietoris_above
    (n : ℕ) (X₁ X₂ : Type) [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (h₁ : ∀ k, n ≤ k → IsZero (H k c₁.Punctured))
    (h₂ : ∀ k, n ≤ k → IsZero (H k c₂.Punctured))
    (hcover : HasStandardCover c₁ c₂) :
    ∀ k, n < k → IsZero (H k (ConnectedSum c₁ c₂)) := by
  intro k hnk
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  have hUk : IsZero (H k U) :=
    (h₁ k hnk.le).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        e₁ k)
  have hVk : IsZero (H k V) :=
    (h₂ k hnk.le).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        e₂ k)
  have hUg : IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of U)) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of U) k hUk
  have hVg : IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of V)) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of V) k hVk
  have hpieces : IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of U) ⊞
        ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of V)) :=
    (biprod_isZero_iff _ _).mpr ⟨hUg, hVg⟩
  have hkpred : k - 1 + 1 = k := by omega
  have hImod : IsZero (H (k - 1) (U ∩ V : Set (ConnectedSum c₁ c₂))) := by
    apply IsZero.of_iso
      (e := ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        e₀ (k - 1))
    by_cases hn0 : n = 0
    · subst n
      have hsphere : IsEmpty (Sphere 0) := ⟨fun s ↦ by
        have hs0 : s.1 = 0 := Subsingleton.elim _ _
        have hs := s.2
        rw [hs0, Metric.mem_sphere, dist_self] at hs
        norm_num at hs⟩
      letI : IsEmpty (Sphere 0) := hsphere
      exact connectedSum_mayerVietoris_above_aux_empty (Sphere 0) (k - 1)
    · have hdim : n - 1 + 1 = n := by omega
      rw [← hdim]
      exact ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
          (n - 1) (k - 1) (by omega) (by omega)
  have hIg : IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology (k - 1)
        (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂)))) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂))) (k - 1) hImod
  have hepi : Epi
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
        U V (k - 1 + 1)) :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
      U V hU hV hUV (k - 1)).epi_f_iff.mpr (hIg.eq_of_tgt _ _)
  rw [hkpred] at hepi
  have hXg : IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology k
        (TopCat.of (ConnectedSum c₁ c₂))) := by
    rw [IsZero.iff_id_eq_zero]
    apply hepi.left_cancellation
    exact hpieces.eq_of_src _ _
  exact ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
    (TopCat.of (ConnectedSum c₁ c₂)) k hXg

/-- **LIBRARY (B10).** The top connecting map supplies the single top class. -/
noncomputable def connectedSum_topConnecting_iso_aux_cylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (K : ContinuousMap.Homotopy f g) :=
  TopCat.ofHom ⟨fun p : X × TopCat.I ↦ K (TopCat.I.homeomorph p.2, p.1),
    K.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

lemma connectedSum_topConnecting_iso_aux_map_eq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (K : ContinuousMap.Homotopic f g) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) =
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g) := by
  rcases K with ⟨K⟩
  apply ConstructionTargets.CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy
    (R := ℤ)
    (connectedSum_topConnecting_iso_aux_cylinder K) _ _ k
  · ext x
    change K (0, x) = f x
    simp
  · ext x
    change K (1, x) = g x
    simp

lemma connectedSum_topConnecting_iso_aux_inclusion_zero
    {n : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    {I A : Set X} (eI : ContinuousMap.HomotopyEquiv I (Sphere n))
    (c : BallCollar n X') (eU : ContinuousMap.HomotopyEquiv A c.Punctured)
    (hsub : I ⊆ A)
    (h : ContinuousMap.Homotopic
      (eU.toFun.comp ((ContinuousMap.inclusion hsub).comp eI.invFun))
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩)
    (k : ℕ) (hz : boundaryHomologyMap c k = 0) :
    IntegralMV.mvIncl hsub k = 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  have hI : IsIso (F.map (TopCat.ofHom eI.invFun)) := by
    change IsIso
      (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
        ℤ eI.symm k).hom
    infer_instance
  have hU : IsIso (F.map (TopCat.ofHom eU.toFun)) := by
    change IsIso
      (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
        ℤ eU k).hom
    infer_instance
  let i : C(I, A) := ContinuousMap.inclusion hsub
  have hcomp : F.map (TopCat.ofHom eI.invFun) ≫ F.map (TopCat.ofHom i) ≫
      F.map (TopCat.ofHom eU.toFun) = 0 := by
    rw [← F.map_comp, ← F.map_comp]
    change F.map (TopCat.ofHom
      (eU.toFun.comp ((ContinuousMap.inclusion hsub).comp eI.invFun))) = 0
    rw [connectedSum_topConnecting_iso_aux_map_eq h k]
    exact hz
  apply (cancel_epi (F.map (TopCat.ofHom eI.invFun))).1
  apply (cancel_mono (F.map (TopCat.ofHom eU.toFun))).1
  simpa [IntegralMV.mvIncl, i, Category.assoc] using hcomp

theorem connectedSum_topConnecting_iso
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hz₁ : IsZero (H n c₁.Punctured)) (hz₂ : IsZero (H n c₂.Punctured))
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (hcover : HasStandardCover c₁ c₂) :
    Nonempty (H n (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) := by
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  obtain ⟨δ, -, hex₂, hex₃⟩ := IntegralMV.integralMayerVietoris U V hU hV hUV
  have hUn : IsZero (H n U) := hz₁.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₁ n)
  have hVn : IsZero (H n V) := hz₂.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₂ n)
  have hJsrc : IsZero (Limits.biprod (H n U) (H n V)) :=
    (biprod_isZero_iff _ _).mpr ⟨hUn, hVn⟩
  have hleft := connectedSum_topConnecting_iso_aux_inclusion_zero e₀ c₁ e₁
    Set.inter_subset_left he₁ (n - 1) hboundary₁
  have hright := connectedSum_topConnecting_iso_aux_inclusion_zero e₀ c₂ e₂
    Set.inter_subset_right he₂ (n - 1) hboundary₂
  have hIzero : IntegralMV.mvI U V (n - 1) = 0 := by
    rw [IntegralMV.mvI, hleft, hright]
    apply biprod.hom_ext <;> simp
  have hdim : n - 1 + 1 = n := by omega
  have hd_inj : Function.Injective (δ (n - 1)).hom := by
    rw [← LinearMap.ker_eq_bot, ← hex₂ (n - 1), LinearMap.range_eq_bot]
    rw [hdim]
    exact congrArg ModuleCat.Hom.hom (hJsrc.eq_of_src _ 0)
  have hd_surj : Function.Surjective (δ (n - 1)).hom := by
    rw [← LinearMap.range_eq_top, hex₃ (n - 1), LinearMap.ker_eq_top]
    exact congrArg ModuleCat.Hom.hom hIzero
  let eS : H (n - 1) (Sphere n) ≅ ModuleCat.of ℤ ℤ := by
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleTopHomologyIsoInt
      (n - 1) (by omega)
  let eI : H (n - 1) (U ∩ V : Set (ConnectedSum c₁ c₂)) ≅
      ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ (n - 1) ≪≫ eS
  letI : IsIso (δ (n - 1)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hd_inj, hd_surj⟩
  have eTop := asIso (δ (n - 1)) ≪≫ eI
  exact ⟨by simpa only [hdim] using eTop⟩

/-- Integral homology of a collared connected sum. -/
theorem connectedSum_homology
    (n : ℕ) (hn : 2 ≤ n)
    (X₁ X₂ : Type)
    [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
    [PathConnectedSpace X₁] [ChartedSpace (E n) X₁]
    [IsManifold (I n) (⊤ : ℕ∞) X₁]
    [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
    [PathConnectedSpace X₂] [ChartedSpace (E n) X₂]
    [IsManifold (I n) (⊤ : ℕ∞) X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (htop₁ : Nonempty (H n X₁ ≅ ModuleCat.of ℤ ℤ))
    (htop₂ : Nonempty (H n X₂ ≅ ModuleCat.of ℤ ℤ))
    (habove₁ : ∀ k, n < k → IsZero (H k X₁))
    (habove₂ : ∀ k, n < k → IsZero (H k X₂)) :
    let Y := ConnectedSum c₁ c₂
    Nonempty (H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, 0 < k → k < n →
      Nonempty (H k Y ≅ ModuleCat.of ℤ ((H k X₁) × (H k X₂)))) ∧
    Nonempty (H n Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, n < k → IsZero (H k Y)) := by
  have ho₁ := c₁.largeInterior_isOpen n X₁
  have ho₂ := c₂.largeInterior_isOpen n X₂
  letI := c₁.punctured_pathConnected n hn X₁ ho₁
  letI := c₂.punctured_pathConnected n hn X₂ ho₂
  have hz₁ := c₁.punctured_topHomology_zero n hn X₁ htop₁ ho₁
  have hz₂ := c₂.punctured_topHomology_zero n hn X₂ htop₂ ho₂
  have hb₁ := c₁.boundary_homology_zero n hn X₁ htop₁ ho₁
  have hb₂ := c₂.boundary_homology_zero n hn X₂ htop₂ ho₂
  have hp₁ := c₁.punctured_homology n hn X₁ htop₁ habove₁ ho₁ inferInstance hz₁
  have hp₂ := c₂.punctured_homology n hn X₂ htop₂ habove₂ ho₂ inferInstance hz₂
  have hc := BallCollar.connectedSum_standardCover c₁ c₂ ho₁ ho₂
  exact ⟨connectedSum_mayerVietoris_zero n hn X₁ X₂ c₁ c₂ hp₁.1 hp₂.1 hc,
    connectedSum_mayerVietoris_middle n hn X₁ X₂ c₁ c₂ hp₁.2 hp₂.2 hb₁ hb₂ hc,
    connectedSum_topConnecting_iso n hn X₁ X₂ c₁ c₂ hz₁ hz₂ hb₁ hb₂ hc,
    connectedSum_mayerVietoris_above n X₁ X₂ c₁ c₂ hp₁.2.2 hp₂.2.2 hc⟩

#print axioms continuous_unitToLarge
#print axioms continuous_sphereToDisk
#print axioms BallCollar.largeMap_unitToLarge
#print axioms BallCollar.continuous_boundaryMap
#print axioms BallCollar.radialRegion_isOpen
#print axioms BallCollar.largeInteriorHomeomorphBall
#print axioms BallCollar.largeInteriorMap_isEmbedding
#print axioms BallCollar.range_largeInteriorMap
#print axioms BallCollar.largeInterior_isOpen_of_isOpenMap

end ConstructionTargets.CollaredConnectedSumHomology
