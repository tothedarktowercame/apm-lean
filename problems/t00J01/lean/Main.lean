import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00J01 — three false manifold claims

The three counterexamples are concrete: a Klein-bottle quotient times a
circle, the identity map of the genuine two-sphere, and an explicit folding
self-map of the genuine circle.  For part (b), the Lefschetz number is the
actual alternating trace of the endomorphisms induced on rational singular
homology.

## Statement repairs

None.

## Encoding questions

The required rational-homology identifications of `S²` are explicit witnesses
inside `t00J01HasSphereLefschetzNumber`; their induced maps and traces cannot be
detached from the self-map under study.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t00j01_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t00j01_S2 := Metric.sphere (0 : apm_t00j01_E3) 1

abbrev apm_t00j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

abbrev T00J01RationalHomology (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def t00J01RationalHomologyMap {X : Type} [TopologicalSpace X]
    (k : ℕ) (f : C(X, X)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)

/-- The standard square presentation of the Klein bottle. -/
inductive apm_t00j01_kleinRel : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | horizontal (x y : ℝ) : apm_t00j01_kleinRel (x, y) (x + 1, y)
  | twisted (x y : ℝ) : apm_t00j01_kleinRel (x, y) (-x, y + 1)

def apm_t00j01_Klein :=
  Quotient (Relation.EqvGen.setoid apm_t00j01_kleinRel)

noncomputable instance : TopologicalSpace apm_t00j01_Klein :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ => Quotient.mk (Relation.EqvGen.setoid apm_t00j01_kleinRel) p)
    inferInstance

abbrev apm_t00j01_nonorientable3 := apm_t00j01_Klein × Circle

def apm_t00j01_isThreeManifold (M : Type) [TopologicalSpace M] : Prop :=
  IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) ∧
  ∀ x : M, ∃ (U : Set M) (V : Set apm_t00j01_E3),
    x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V)

def t00J01SphereIdentityHomeomorph : apm_t00j01_S2 ≃ₜ apm_t00j01_S2 :=
  Homeomorph.refl apm_t00j01_S2

def t00J01SphereIdentity : C(apm_t00j01_S2, apm_t00j01_S2) :=
  ⟨t00J01SphereIdentityHomeomorph, t00J01SphereIdentityHomeomorph.continuous⟩

/-- `L` is the alternating trace of the maps genuinely induced by `f`, after
identifying `H₀(S²;ℚ)`, `H₁(S²;ℚ)`, and `H₂(S²;ℚ)` with `ℚ`, `0`, and `ℚ`. -/
def t00J01HasSphereLefschetzNumber
    (f : C(apm_t00j01_S2, apm_t00j01_S2)) (L : ℚ) : Prop :=
  ∃ h0 : T00J01RationalHomology 0 apm_t00j01_S2 ≅ ModuleCat.of ℚ ℚ,
    ∃ h1 : T00J01RationalHomology 1 apm_t00j01_S2 ≅
        ModuleCat.of ℚ (Fin 0 → ℚ),
      ∃ h2 : T00J01RationalHomology 2 apm_t00j01_S2 ≅ ModuleCat.of ℚ ℚ,
        L =
          LinearMap.trace ℚ ℚ
              (h0.inv ≫ t00J01RationalHomologyMap 0 f ≫ h0.hom).hom -
            LinearMap.trace ℚ (Fin 0 → ℚ)
              (h1.inv ≫ t00J01RationalHomologyMap 1 f ≫ h1.hom).hom +
            LinearMap.trace ℚ ℚ
              (h2.inv ≫ t00J01RationalHomologyMap 2 f ≫ h2.hom).hom

/-- The degree-one circle fold with lift `θ ↦ θ + 2 sin θ`. -/
def apm_t00j01_fold (z : Circle) : Circle :=
  z * Circle.exp (2 * (z : ℂ).im)

def apm_t00j01_foldLift (θ : ℝ) : ℝ := θ + 2 * Real.sin θ

lemma apm_t00j01_fold_exp (θ : ℝ) :
    apm_t00j01_fold (Circle.exp θ) =
      Circle.exp (apm_t00j01_foldLift θ) := by
  rw [apm_t00j01_fold, apm_t00j01_foldLift, Circle.exp_add]
  congr 2
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

lemma apm_t00j01_hasDerivAt_foldLift (θ : ℝ) :
    HasDerivAt apm_t00j01_foldLift (1 + 2 * Real.cos θ) θ := by
  simpa [apm_t00j01_foldLift] using
    (hasDerivAt_id θ).add ((Real.hasDerivAt_sin θ).const_mul 2)

@[simp] lemma apm_t00j01_deriv_foldLift (θ : ℝ) :
    deriv apm_t00j01_foldLift θ = 1 + 2 * Real.cos θ :=
  (apm_t00j01_hasDerivAt_foldLift θ).deriv

/-- For this explicit lift, regularity is nonvanishing of its derivative at
every lift of a point in the fiber. -/
def apm_t00j01_foldRegular (y : Circle) : Prop :=
  ∀ θ : ℝ, apm_t00j01_fold (Circle.exp θ) = y →
  1 + 2 * Real.cos θ ≠ 0

lemma apm_t00j01_fold_continuous : Continuous apm_t00j01_fold := by
  unfold apm_t00j01_fold
  fun_prop

/-- The evident preimage of `1` is regular. -/
lemma apm_t00j01_fold_zero : apm_t00j01_fold (Circle.exp 0) = 1 := by
  rw [apm_t00j01_fold_exp]
  simp [apm_t00j01_foldLift]

lemma apm_t00j01_fold_zero_deriv_ne : 1 + 2 * Real.cos 0 ≠ 0 := by
  norm_num

/-- The evident preimage of `exp π` is regular. -/
lemma apm_t00j01_fold_pi :
    apm_t00j01_fold (Circle.exp Real.pi) = Circle.exp Real.pi := by
  rw [apm_t00j01_fold_exp]
  simp [apm_t00j01_foldLift]

lemma apm_t00j01_fold_pi_deriv_ne :
    1 + 2 * Real.cos Real.pi ≠ 0 := by
  norm_num

theorem apm_t00j01 :
    (apm_t00j01_isThreeManifold apm_t00j01_nonorientable3 ∧
      Limits.IsZero (apm_t00j01_H 3 apm_t00j01_nonorientable3)) ∧
    (t00J01HasSphereLefschetzNumber t00J01SphereIdentity 2 ∧
      ¬t00J01HasSphereLefschetzNumber t00J01SphereIdentity 1) ∧
    (Continuous apm_t00j01_fold ∧
      apm_t00j01_foldRegular (Circle.exp Real.pi) ∧
      apm_t00j01_foldRegular 1 ∧
      Nat.card {z : Circle // apm_t00j01_fold z = Circle.exp Real.pi} = 3 ∧
      Nat.card {z : Circle // apm_t00j01_fold z = 1} = 1) := by
  /-
  CLOSER HOP 3 boundary. The frozen repair at commit `da7d3d2` replaced the
  detached Lefschetz arithmetic by `t00J01HasSphereLefschetzNumber`, but also
  removed the compatible circle helpers described by the earlier hop record.
  This hop ports those facts to the repaired statement:
  `apm_t00j01_fold_exp` identifies the circle fold with its real lift,
  `apm_t00j01_hasDerivAt_foldLift` and `apm_t00j01_deriv_foldLift` compute the
  derivative, and `apm_t00j01_fold_continuous` closes continuity. Going beyond
  restoration, `apm_t00j01_fold_zero` and `apm_t00j01_fold_pi` exhibit the
  evident points of the two target fibers, while the corresponding `_deriv_ne`
  lemmas prove both are regular preimages.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, related Klein,
  Lefschetz, circle-covering, and sphere artifacts, Mathlib's circle
  exponential/root APIs, singular homology, quotient/manifold sources, and git
  history found no packaged exact root count for `θ + 2 sin θ` modulo `2π`,
  no singular-homology computation for this metric `S²`, and no theorem making
  the concrete coinduced Klein quotient a compact 2-manifold. The remaining
  circle proof needs a fundamental-interval root classification with
  monotonicity split at `cos θ = -1/2`; the topology conjuncts require the
  independent missing quotient-manifold and homology infrastructure. The
  theorem statement is unchanged.

  HOP 4 (2026-08-09): further searches did not expose a bridge below these
  three independent exact contracts:

    theorem apm_t00j01_klein_product_bridge :
      apm_t00j01_isThreeManifold apm_t00j01_nonorientable3 ∧
        Limits.IsZero (apm_t00j01_H 3 apm_t00j01_nonorientable3)

    theorem apm_t00j01_sphere_identity_bridge :
      t00J01HasSphereLefschetzNumber t00J01SphereIdentity 2 ∧
        ¬t00J01HasSphereLefschetzNumber t00J01SphereIdentity 1

    theorem apm_t00j01_fold_fibers_bridge :
      apm_t00j01_foldRegular (Circle.exp Real.pi) ∧
        apm_t00j01_foldRegular 1 ∧
        Nat.card {z : Circle //
          apm_t00j01_fold z = Circle.exp Real.pi} = 3 ∧
        Nat.card {z : Circle // apm_t00j01_fold z = 1} = 1

  The first needs quotient charts plus the nonorientable top-homology
  calculation. The second needs the rational singular homology of the metric
  two-sphere and functoriality for the identity. The third is the exact
  fundamental-interval classification for `θ + 2 sin θ` modulo `2π`, including
  exclusion of critical roots. Together with `apm_t00j01_fold_continuous`,
  these contracts are exactly the frozen conjunction.
  -/
  sorry
