import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

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
    CLOSER HOP 1 boundary. The concrete matrix trace is now compiled as `3`,
    and `apm_t97a04_lefschetz_arithmetic` proves the final formula
    `1 = 1 - trace A + 3`. The packaging lemma above reduces the main theorem
    exactly to three homology isomorphisms and their induced-map equations.

    The remaining bridge is the integral singular homology of
    `(AddCircle 1) × (AddCircle 1)` with explicit natural generators: construct
    `H₀ ≅ ℤ`, `H₁ ≅ ℤ²`, and `H₂ ≅ ℤ`, then compute that the
    concrete `Lbar` acts as identity, the displayed matrix, and multiplication
    by three respectively. Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
    torus and circle siblings, Mathlib's singular-homology, AddCircle, product,
    Eilenberg--Zilber/Künneth, and induced-map sources, and git history found no
    compiled circle/torus homology computation or generator-level product map.
    -/
    sorry
  rcases hcore with ⟨h0, h1, h2, H0, H1, H2⟩
  exact t97A04HasHomologicalData.of_maps h0 h1 h2 H0 H1 H2
