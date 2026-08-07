import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00A02: Finite coverings of surfaces and a projective-plane wedge

## Statement repairs

Part (a) must concern connected `10`-fold coverings. Without connectedness,
disjoint unions with total degree `10` give nonhomeomorphic covering spaces.
We add the standard connectedness hypothesis, as does the supplied solution.

## Encoding questions

Mathlib has covering maps and manifolds but no packaged surface genus. The
genus-five hypothesis is encoded by an actual compact connected 2-manifold
with its characteristic integral homology groups. `ℝP²`, its antipodal cover,
and the wedge are genuine quotient spaces. Regularity is transitivity of the
actual deck-homeomorphism action on each fiber.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev apm_t00A02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00A02_I2 := 𝓘(ℝ, apm_t00A02_E2)
abbrev apm_t00A02_Sphere2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

abbrev apm_t00A02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00A02_hasGenusFiveHomology (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (apm_t00A02_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00A02_H 1 X ≅ ModuleCat.of ℤ (Fin 10 → ℤ)) ∧
  Nonempty (apm_t00A02_H 2 X ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00A02_H k X)

def apm_t00A02_isNfoldCover {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (n : ℕ) (p : E → B) : Prop :=
  IsCoveringMap p ∧ ∀ b : B, Nat.card {e : E // p e = b} = n

def apm_t00A02_isRegularCover {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  ∀ x y : E, p x = p y →
    ∃ h : E ≃ₜ E, (∀ z : E, p (h z) = p z) ∧ h x = y

inductive apm_t00A02_antipodalRel :
    apm_t00A02_Sphere2 → apm_t00A02_Sphere2 → Prop
  | antipodal (x : apm_t00A02_Sphere2) :
      apm_t00A02_antipodalRel x (-x)

def apm_t00A02_RP2 :=
  Quotient (Relation.EqvGen.setoid apm_t00A02_antipodalRel)

noncomputable instance : TopologicalSpace apm_t00A02_RP2 :=
  TopologicalSpace.coinduced
    (fun x : apm_t00A02_Sphere2 ↦
      Quotient.mk (Relation.EqvGen.setoid apm_t00A02_antipodalRel) x)
    inferInstance

def apm_t00A02_antipodalCover : apm_t00A02_Sphere2 → apm_t00A02_RP2 :=
  fun x ↦ Quotient.mk _ x

inductive apm_t00A02_wedgeRel (r₀ : apm_t00A02_RP2) :
    Sum apm_t00A02_RP2 apm_t00A02_RP2 →
      Sum apm_t00A02_RP2 apm_t00A02_RP2 → Prop
  | base : apm_t00A02_wedgeRel r₀ (Sum.inl r₀) (Sum.inr r₀)

def apm_t00A02_wedge (r₀ : apm_t00A02_RP2) :=
  Quotient (Relation.EqvGen.setoid (apm_t00A02_wedgeRel r₀))

noncomputable instance (r₀ : apm_t00A02_RP2) :
    TopologicalSpace (apm_t00A02_wedge r₀) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t00A02_RP2 apm_t00A02_RP2 ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t00A02_wedgeRel r₀)) z)
    inferInstance

structure apm_t00A02_coverWitness (B : Type) [TopologicalSpace B]
    (n : ℕ) (regular : Bool) where
  E : Type
  topology : TopologicalSpace E
  p : E → B
  covering : @apm_t00A02_isNfoldCover E B topology _ n p
  connected : @IsConnected E topology (Set.univ : Set E)
  regularity : if regular then
    @apm_t00A02_isRegularCover E B topology _ p
  else ¬@apm_t00A02_isRegularCover E B topology _ p

theorem apm_t00a02 :
    (∀ (F E₁ E₂ : Type)
        [TopologicalSpace F] [T2Space F] [CompactSpace F]
        [PathConnectedSpace F] [ChartedSpace apm_t00A02_E2 F]
        [IsManifold apm_t00A02_I2 ⊤ F]
        [TopologicalSpace E₁] [PathConnectedSpace E₁]
        [TopologicalSpace E₂] [PathConnectedSpace E₂]
        (hF : apm_t00A02_hasGenusFiveHomology F)
        (p₁ : E₁ → F) (p₂ : E₂ → F),
      apm_t00A02_isNfoldCover 10 p₁ →
      apm_t00A02_isNfoldCover 10 p₂ → Nonempty (E₁ ≃ₜ E₂)) ∧
    apm_t00A02_isNfoldCover 2 apm_t00A02_antipodalCover ∧
    (∀ r₀ : apm_t00A02_RP2,
      Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 true) ∧
      Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 false)) := by
  /-
  Boundary (skipped): I searched Mathlib's covering-map, quotient-covering,
  monodromy, manifold, and singular-homology APIs. The library has general
  monodromy and properly-discontinuous quotient machinery, but no
  classification theorem for compact connected surfaces, no theorem that
  Euler characteristic multiplies under a finite covering, and no packaged
  construction/classification of covers of a wedge from permutation actions.
  Moreover, the custom `RP2` quotient is not definitionally the orbit quotient
  expected by `IsQuotientCoveringMap`, so even the antipodal-cover conjunct
  requires a substantial bridge between the generated relation and a `ZMod 2`
  action. The partial sibling `t01A04` confirms that concrete wedge-cover
  constructions and their deck/fundamental-group properties lack a packaged
  route, while the closed sibling `t91A02` succeeds only because Euler
  multiplicativity is included explicitly as witness data. No relevant lemma
  occurs in `ConstructionTargets/` or `YoungL2.lean`. These missing
  developments exceed this pass.
  -/
  sorry
