import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.CoefficientH0
import ConstructionTargets.t97A04Closure

/-!
# APM t97A04 — homological data of an integral linear torus map

The torus is `(ℝ/ℤ)²`, and `Lbar` is the genuine continuous map induced by
`(x,y) ↦ (2x+y,y-x)`.  Its invariants are stated through the maps actually
induced on integral singular homology.  Identifications of `H₀`, `H₁`, and
`H₂` with `ℤ`, `ℤ²`, and `ℤ` are explicit witnesses, and all three induced
maps are pinned under those identifications before the Lefschetz trace is
formed.

## Statement repairs

Part (a) says “degree of `L`,” although degree here is the degree of the
induced torus self-map `Lbar`; this is forced by the surrounding text and the
supplied solution.

## Encoding questions

None.
-/

open CategoryTheory
open ConstructionTargets.T97A04FrozenH1Coordinate

noncomputable section

abbrev apm_t97a04_RealPlane := Fin 2 → ℝ
abbrev apm_t97a04_IntPlane := Fin 2 → ℤ
abbrev apm_t97a04_Torus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

def apm_t97a04_L (p : apm_t97a04_RealPlane) : apm_t97a04_RealPlane :=
  ![2 * p 0 + p 1, p 1 - p 0]

/-- The continuous map on `(ℝ/ℤ)²` induced by the integral linear lift `L`. -/
def apm_t97a04_Lbar : C(apm_t97a04_Torus, apm_t97a04_Torus) :=
  ⟨fun p ↦ (2 • p.1 + p.2, p.2 - p.1), by fun_prop⟩

def apm_t97a04_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(2 : ℤ), 1; -1, 1]

abbrev T97A04Homology (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97a04_Torus))

def t97A04HomologyMap (k : ℕ)
    (f : C(apm_t97a04_Torus, apm_t97a04_Torus)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- The frozen homology-map wrapper has the expected composition law. -/
lemma t97A04HomologyMap_comp (k : ℕ)
    (g f : C(apm_t97a04_Torus, apm_t97a04_Torus)) :
    t97A04HomologyMap k (g.comp f) =
      t97A04HomologyMap k f ≫ t97A04HomologyMap k g := by
  unfold t97A04HomologyMap
  simpa using
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom f) (TopCat.ofHom g)

/-- The identity torus map induces the identity on every homology degree. -/
lemma t97A04HomologyMap_id (k : ℕ) :
    t97A04HomologyMap k (ContinuousMap.id apm_t97a04_Torus) = 𝟙 _ := by
  unfold t97A04HomologyMap
  simpa using
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map_id (TopCat.of apm_t97a04_Torus)

/-- The complete homological computation for a torus self-map.  The matrix,
degree, and Lefschetz number are conclusions about `f` because the equations
below use the actual singular-homology maps induced by `f`. -/
def t97A04HasHomologicalData
    (f : C(apm_t97a04_Torus, apm_t97a04_Torus))
    (A : Matrix (Fin 2) (Fin 2) ℤ) (degree lefschetz : ℤ) : Prop :=
  ∃ h0 : T97A04Homology 0 ≅ ModuleCat.of ℤ ℤ,
    ∃ h1 : T97A04Homology 1 ≅ ModuleCat.of ℤ apm_t97a04_IntPlane,
    ∃ h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ,
      (∀ a : T97A04Homology 0,
        h0.hom (t97A04HomologyMap 0 f a) = h0.hom a) ∧
      (∀ a : T97A04Homology 1,
        h1.hom (t97A04HomologyMap 1 f a) = A.mulVec (h1.hom a)) ∧
      (∀ a : T97A04Homology 2,
        h2.hom (t97A04HomologyMap 2 f a) = degree * h2.hom a) ∧
      lefschetz = 1 - Matrix.trace A + degree

lemma apm_t97a04_matrix_trace : Matrix.trace apm_t97a04_matrix = 3 := by
  norm_num [Matrix.trace, apm_t97a04_matrix]

/-- The determinant controlling the top-dimensional action is three. -/
lemma apm_t97a04_matrix_det : Matrix.det apm_t97a04_matrix = 3 := by
  norm_num [Matrix.det_fin_two, apm_t97a04_matrix]

/-- Coordinate form of the claimed action on the two standard first-homology
generators. -/
lemma apm_t97a04_matrix_mulVec (v : apm_t97a04_IntPlane) :
    apm_t97a04_matrix.mulVec v = ![2 * v 0 + v 1, v 1 - v 0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, apm_t97a04_matrix] <;> ring

/-- The displayed real lift has exactly the same coordinate formula as the
integer matrix after scalar extension. -/
lemma apm_t97a04_L_eq_matrix_mulVec (p : apm_t97a04_RealPlane) :
    apm_t97a04_L p =
      (apm_t97a04_matrix.map ((Int.castRingHom ℝ))).mulVec p := by
  funext i
  fin_cases i <;>
    simp [apm_t97a04_L, apm_t97a04_matrix, Matrix.mulVec, dotProduct] <;> ring

lemma apm_t97a04_lefschetz_arithmetic :
    (1 : ℤ) = 1 - Matrix.trace apm_t97a04_matrix + 3 := by
  rw [apm_t97a04_matrix_trace]
  norm_num

lemma t97A04HasHomologicalData.of_maps
    (h0 : T97A04Homology 0 ≅ ModuleCat.of ℤ ℤ)
    (h1 : T97A04Homology 1 ≅ ModuleCat.of ℤ apm_t97a04_IntPlane)
    (h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ)
    (H0 : ∀ a : T97A04Homology 0,
      h0.hom (t97A04HomologyMap 0 apm_t97a04_Lbar a) = h0.hom a)
    (H1 : ∀ a : T97A04Homology 1,
      h1.hom (t97A04HomologyMap 1 apm_t97a04_Lbar a) =
        apm_t97a04_matrix.mulVec (h1.hom a))
    (H2 : ∀ a : T97A04Homology 2,
      h2.hom (t97A04HomologyMap 2 apm_t97a04_Lbar a) = 3 * h2.hom a) :
    t97A04HasHomologicalData apm_t97a04_Lbar apm_t97a04_matrix 3 1 := by
  exact ⟨h0, h1, h2, H0, H1, H2, apm_t97a04_lefschetz_arithmetic⟩

/-- Why this unblocks the degree-zero homology component of `apm_t97a04`:
the torus is connected, so its integral `H₀` is `ℤ`, and every self-map acts
as the identity under the component generator. -/
theorem apm_t97A04_bridge_1 :
    ∃ h0 : T97A04Homology 0 ≅ ModuleCat.of ℤ ℤ,
      ∀ a : T97A04Homology 0,
        h0.hom (t97A04HomologyMap 0 apm_t97a04_Lbar a) = h0.hom a := by
  letI : PathConnectedSpace apm_t97a04_Torus :=
    { nonempty := ⟨0⟩
      joined := fun x y =>
        ⟨(PathConnectedSpace.somePath x.1 y.1).prod
          (PathConnectedSpace.somePath x.2 y.2)⟩ }
  refine ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ
    (0 : apm_t97a04_Torus), fun a => ?_⟩
  have h := ConstructionTargets.CoefficientH0.h0Augmentation_naturality
    ℤ apm_t97a04_Lbar
  exact congrArg (fun g => g.hom a) h

/-- Why this unblocks the first-homology component of `apm_t97a04`: under
the two coordinate-circle generators of `H₁(T²;ℤ)`, the induced map of the
concrete torus map is multiplication by its displayed integral matrix.  The
witness is the aligned frozen-torus ModuleCat coordinate. -/
theorem apm_t97A04_bridge_2 :
    ∃ h1 : T97A04Homology 1 ≅ ModuleCat.of ℤ apm_t97a04_IntPlane,
      ∀ a : T97A04Homology 1,
        h1.hom (t97A04HomologyMap 1 apm_t97a04_Lbar a) =
          apm_t97a04_matrix.mulVec (h1.hom a) := by
  refine ⟨frozenTorusAlignedH1ModuleIsoFinTwo, ?_⟩
  intro a
  have h := congrArg (fun f => f a) frozenLbarModuleH1_map_commutes
  change frozenTorusAlignedH1ModuleIsoFinTwo.hom
      (t97A04HomologyMap 1 apm_t97a04_Lbar a) =
    frozenMatrixAddHom
      (frozenTorusAlignedH1ModuleIsoFinTwo.hom a) at h
  rw [h]
  funext i
  by_cases hi : i = 0
  · simp [hi, frozenMatrixAddHom, apm_t97a04_matrix,
      Matrix.mulVec, dotProduct]
  · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst i
    change @Fin.cases 1 (fun _ => ℤ)
        (2 * frozenTorusAlignedH1ModuleIsoFinTwo.hom a 0 +
          frozenTorusAlignedH1ModuleIsoFinTwo.hom a 1)
        (fun _ : Fin 1 => frozenTorusAlignedH1ModuleIsoFinTwo.hom a 1 -
          frozenTorusAlignedH1ModuleIsoFinTwo.hom a 0)
        (Fin.succ 0) = _
    rw [Fin.cases_succ]
    simp [apm_t97a04_matrix, Matrix.mulVec, dotProduct]
    ring

/-- Why this unblocks the top-homology component of `apm_t97a04`: under the
product fundamental-class generator of `H₂(T²;ℤ)`, the induced map multiplies
by the determinant `3` of the integral lift. -/
theorem apm_t97A04_bridge_3 :
    ∃ h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ,
      ∀ a : T97A04Homology 2,
        h2.hom (t97A04HomologyMap 2 apm_t97a04_Lbar a) =
          3 * h2.hom a := by
  refine ⟨ConstructionTargets.T97A04Closure.frozenTorusH2ModuleIsoInt, ?_⟩
  intro a
  have h := congrArg (fun f => f a)
    ConstructionTargets.T97A04Closure.frozenLbarModuleH2_map_commutes
  change ConstructionTargets.T97A04Closure.frozenTorusH2ModuleIsoInt.hom
      (t97A04HomologyMap 2 apm_t97a04_Lbar a) =
    (3 • 𝟙 (ModuleCat.of ℤ ℤ))
      (ConstructionTargets.T97A04Closure.frozenTorusH2ModuleIsoInt.hom a) at h
  simpa using h

theorem apm_t97a04 :
    t97A04HasHomologicalData apm_t97a04_Lbar apm_t97a04_matrix 3 1 := by
  let hcore :
      ∃ h0 : T97A04Homology 0 ≅ ModuleCat.of ℤ ℤ,
      ∃ h1 : T97A04Homology 1 ≅ ModuleCat.of ℤ apm_t97a04_IntPlane,
      ∃ h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ,
        (∀ a : T97A04Homology 0,
          h0.hom (t97A04HomologyMap 0 apm_t97a04_Lbar a) = h0.hom a) ∧
        (∀ a : T97A04Homology 1,
          h1.hom (t97A04HomologyMap 1 apm_t97a04_Lbar a) =
            apm_t97a04_matrix.mulVec (h1.hom a)) ∧
        (∀ a : T97A04Homology 2,
          h2.hom (t97A04HomologyMap 2 apm_t97a04_Lbar a) = 3 * h2.hom a) := by
    /-
    CLOSER HOP 2 boundary. The concrete matrix trace is compiled as `3`,
    and `apm_t97a04_lefschetz_arithmetic` proves the final formula
    `1 = 1 - trace A + 3`. The packaging lemma above reduces the main theorem
    exactly to three homology isomorphisms and their induced-map equations.

    Going beyond hop 1, `apm_t97a04_matrix_det` now proves the determinant is
    three, `apm_t97a04_matrix_mulVec` expands the claimed action on arbitrary
    integral coordinates, and `apm_t97a04_L_eq_matrix_mulVec` proves that the
    concrete real lift is literally scalar extension of that same matrix.
    Hence no determinant or coordinate-identification algebra remains after a
    future generator-level homology comparison.

    The remaining bridge is the integral singular homology of
    `(AddCircle 1) × (AddCircle 1)` with explicit natural generators: construct
    `H₀ ≅ ℤ`, `H₁ ≅ ℤ²`, and `H₂ ≅ ℤ`, then compute that the
    concrete `Lbar` acts as identity, the displayed matrix, and multiplication
    by three respectively. Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
    torus and circle siblings, Mathlib's singular-homology, AddCircle, product,
    Eilenberg--Zilber/Künneth, and induced-map sources, and git history found no
    compiled circle/torus homology computation or generator-level product map.
    The frozen statement is unchanged.

    CLOSER HOP 3 (2026-08-08): the categorical functoriality layer of the
    frozen wrapper is now compiled as `t97A04HomologyMap_comp` and
    `t97A04HomologyMap_id`, following the proven sphere-map pattern in sibling
    `t94J08`. Future generator calculations can therefore decompose `Lbar`
    into simpler torus maps without reopening `TopCat` or functor composition
    bookkeeping. A renewed search for coordinate inclusions/projections and
    product homology found the continuous torus maps themselves but still no
    Künneth/Eilenberg--Zilber comparison or circle generator through which
    these laws could compute `H₁` and `H₂`. Thus the remaining bridge is
    purely the three explicit torus homology identifications and their
    generator-level actions; no categorical composition obligations remain.
    The frozen statement is unchanged.
    -/
    rcases apm_t97A04_bridge_1 with ⟨h0, H0⟩
    rcases apm_t97A04_bridge_2 with ⟨h1, H1⟩
    rcases apm_t97A04_bridge_3 with ⟨h2, H2⟩
    exact ⟨h0, h1, h2, H0, H1, H2⟩
  rcases hcore with ⟨h0, h1, h2, H0, H1, H2⟩
  exact t97A04HasHomologicalData.of_maps h0 h1 h2 H0 H1 H2

#print axioms apm_t97A04_bridge_3
#print axioms apm_t97a04
