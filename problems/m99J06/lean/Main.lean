import Mathlib

/-!
# APM m99J06: Galerkin approximation in `H¹₀(0,1)`

## Statement repairs

Part (d) says that `uₙ` itself converges weakly, but the suggested boundedness
argument guarantees only a weakly convergent subsequence. We state that precise
conclusion, as does the supplied solution. Uniqueness can subsequently upgrade
it to convergence of the full sequence, but that is not needed for part (e).

## Encoding questions

None. `H¹₀(0,1)` is represented by its exact one-dimensional realization:
absolutely continuous functions with `L²` weak derivative and zero endpoint
trace. An explicit Hilbert-space model retains genuine finite-dimensional
subspaces and Mathlib's genuine weak topology.
-/

open Filter MeasureTheory Set

noncomputable section

def apm_m99J06_isH01Pair (u du : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval u 0 1 ∧
  MemLp u 2 (volume.restrict (Icc 0 1)) ∧
  MemLp du 2 (volume.restrict (Icc 0 1)) ∧
  (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt u (du x) x) ∧
  u 0 = 0 ∧ u 1 = 0

structure apm_m99J06_H01Model (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  val : H → ℝ → ℝ
  weakDeriv : H → ℝ → ℝ
  represents : ∀ u : H, apm_m99J06_isH01Pair (val u) (weakDeriv u)
  realizes : ∀ (u du : ℝ → ℝ), apm_m99J06_isH01Pair u du →
    ∃ w : H, val w = u ∧ weakDeriv w = du
  inner_eq : ∀ u v : H,
    inner ℝ u v = ∫ x in Icc (0 : ℝ) 1,
      val u x * val v x + weakDeriv u x * weakDeriv v x

def apm_m99J06_weakSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∀ v : H, inner ℝ u v = ∫ x in Icc (0 : ℝ) 1, f x * M.val v x

def apm_m99J06_strongSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∃ ddu : ℝ → ℝ,
    MemLp ddu 2 (volume.restrict (Icc 0 1)) ∧
    AbsolutelyContinuousOnInterval (M.weakDeriv u) 0 1 ∧
    (∀ᵐ x ∂volume.restrict (Icc 0 1),
      HasDerivAt (M.weakDeriv u) (ddu x) x) ∧
    (∀ᵐ x ∂volume.restrict (Icc 0 1), M.val u x - ddu x = f x)

def apm_m99J06_galerkinEquation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) (u : V) : Prop :=
  ∀ v : V, inner ℝ (u : H) (v : H) =
    ∫ x in Icc (0 : ℝ) 1, f x * M.val (v : H) x

lemma apm_m99J06_galerkin_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (V : Submodule ℝ H) (u : V)
    (hu : apm_m99J06_galerkinEquation M f V u) :
    ‖(u : H)‖ ^ 2 = ∫ x in Icc (0 : ℝ) 1, f x * M.val (u : H) x := by
  simpa [real_inner_self_eq_norm_sq] using hu u

/-- Coercivity of the ambient inner product gives uniqueness of every
Galerkin solution, independently of finite dimensionality. -/
lemma apm_m99J06_galerkin_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (V : Submodule ℝ H) (u v : V)
    (hu : apm_m99J06_galerkinEquation M f V u)
    (hv : apm_m99J06_galerkinEquation M f V v) : u = v := by
  have hinner : inner ℝ ((u - v : V) : H) ((u - v : V) : H) = 0 := by
    have heq := (hu (u - v)).trans (hv (u - v)).symm
    rw [Submodule.coe_sub, inner_sub_left]
    exact sub_eq_zero.mpr heq
  have hnorm : ‖((u - v : V) : H)‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hinner
  have hzero : ((u - v : V) : H) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

/-- The finite-dimensional Riesz step in the Galerkin argument, isolated
from the representative-level construction of the forcing functional. -/
lemma apm_m99J06_exists_unique_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] ℝ) :
    ∃! u : E, ∀ v : E, inner ℝ u v = L v := by
  let u : E := (InnerProductSpace.toDual ℝ E).symm L
  refine ⟨u, ?_, ?_⟩
  · intro v
    change inner ℝ u v = L v
    simpa [u] using
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v) (y := L))
  · intro y hy
    apply ext_inner_right ℝ
    intro v
    change inner ℝ y v = inner ℝ u v
    exact (hy v).trans ((show inner ℝ u v = L v by
      simpa [u] using
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v) (y := L))).symm)

/-- The function/weak-derivative pair carried by the frozen model determines
the Hilbert-space element uniquely. -/
lemma apm_m99J06_model_ext
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) {u v : H}
    (hu : M.val u = M.val v) (hdu : M.weakDeriv u = M.weakDeriv v) :
    u = v := by
  apply ext_inner_right ℝ
  intro w
  rw [M.inner_eq, M.inner_eq, hu, hdu]

theorem apm_m99j06
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Icc 0 1))) :
    (∀ u : H,
      apm_m99J06_weakSolution M f u ↔
        apm_m99J06_strongSolution M f u) ∧
    (∀ V : ℕ → Submodule ℝ H,
      (∀ n : ℕ, FiniteDimensional ℝ (V n)) →
      (∀ n : ℕ, V n ≤ V (n + 1)) →
      Dense (⋃ n : ℕ, (V n : Set H)) →
        (∀ n : ℕ, ∃! u : V n, apm_m99J06_galerkinEquation M f (V n) u) ∧
        ∀ uSeq : ∀ n : ℕ, V n,
          (∀ n, apm_m99J06_galerkinEquation M f (V n) (uSeq n)) →
          (∀ n, ‖(uSeq n : H)‖ ≤
            (eLpNorm f 2 (volume.restrict (Icc 0 1))).toReal) ∧
          ∃ k : ℕ → ℕ, StrictMono k ∧
            ∃ u : H,
              Tendsto (fun j ↦ toWeakSpace ℝ H (uSeq (k j) : H)) atTop
                (nhds (toWeakSpace ℝ H u)) ∧
              apm_m99J06_weakSolution M f u) := by
  have hweak_unique :
      ∀ u v : H,
        apm_m99J06_weakSolution M f u →
        apm_m99J06_weakSolution M f v → u = v := by
    intro u v hu hv
    apply ext_inner_right ℝ
    intro w
    rw [hu w, hv w]
  /-
  Boundary (closer hop 2): uniqueness of the weak solution, the Galerkin
  energy identity, and now uniqueness of every Galerkin solution
  (`apm_m99J06_galerkin_unique`) are proved above. The latter closes the
  coercivity half of finite-dimensional solvability by testing the difference
  of two solutions against itself.

  `apm_m99J06_exists_unique_inner_eq` now closes the abstract
  finite-dimensional Riesz-representation stage using
  `InnerProductSpace.toDual`; once the forcing term has been bundled as a
  continuous linear functional on `V n`, existence and uniqueness follow
  immediately. The remaining obstruction in this stage is earlier and
  specific to the frozen model: `M.val` is merely a function field, with its
  linearity encoded only indirectly by `M.inner_eq`. Converting that identity
  into a continuous linear map
  `v ↦ ∫ x in Icc 0 1, f x * M.val v x` requires proving equality of
  representatives in `L²` from the norm induced by `inner_eq`.

  Completing the frozen theorem still also requires (1) a
  Sobolev integration-by-parts/regularity theorem for the custom
  `AbsolutelyContinuousOnInterval` plus a.e. `HasDerivAt` representation,
  (2) the representative-level functional construction just described,
  and (3) weak sequential compactness of a bounded Hilbert-space sequence
  followed by passage to the limit on a dense increasing union. I searched
  `integral_mul_le_Lp_mul_Lq_of_nonneg`, finite-dimensional duality,
  `FiniteDimensional.surjective_of_injective`, `toWeakSpace`, and
  `isCompact_closure_of_isBounded`. The last compactness theorem is not by
  itself sequential compactness without an additional metrizability bridge.
  `ConstructionTargets.LusinN` supplies interval absolute-continuity
  identities, but not the Sobolev regularity theorem required here.

  Closer hop 3 proves `apm_m99J06_model_ext`: equality of both concrete
  representatives `M.val` and `M.weakDeriv` implies equality of the ambient
  Hilbert-space elements. The proof rewrites all inner products with
  `M.inner_eq` and applies `ext_inner_right`. This closes the descent/uniqueness
  step once representative-level addition and scalar multiplication have been
  constructed. It does not by itself supply those operations: the remaining
  forcing-functional bridge still needs closure of `apm_m99J06_isH01Pair`
  under linear combinations and product-integrability identities. The Sobolev
  regularity and weak sequential compactness/dense-limit boundaries remain.
  -/
  sorry
