import Mathlib

/-!
# APM m02J02

## Statement repairs

None.  "Basis" is made precise as a linearly independent family whose finite
linear span is dense in the `H¹` graph norm.  No orthogonality is asserted:
the Hermite functions are a natural complete family on the unbounded domains,
but are not orthogonal for the ordinary `H¹` inner product.

## Encoding notes

Because Mathlib has no packaged Sobolev-space type, `H¹₀(Ω)` is encoded
directly as value/weak-derivative pairs that are graph-norm limits of smooth
compactly supported functions.  Thus the central Sobolev object is retained,
including its distributional derivative and closure definition.
-/

open MeasureTheory Polynomial Set
open scoped BigOperators ContDiff ENNReal

def apm_m02j02_IsWeakDerivativeOn (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m02j02_InH10 (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  MemLp u 2 (volume.restrict s) ∧ MemLp du 2 (volume.restrict s) ∧
  apm_m02j02_IsWeakDerivativeOn s u du ∧
  ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ s ∧
    eLpNorm (u - φ) 2 (volume.restrict s) +
      eLpNorm (du - deriv φ) 2 (volume.restrict s) < ENNReal.ofReal ε

def apm_m02j02_IsH10Basis
    (s : Set ℝ) (e de : ℕ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, apm_m02j02_InH10 s (e n) (de n)) ∧
  LinearIndependent ℝ (fun n ↦ (e n, de n)) ∧
  ∀ u du : ℝ → ℝ, apm_m02j02_InH10 s u du →
    ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ,
      eLpNorm (u - c.sum fun n a ↦ a • e n) 2 (volume.restrict s) +
        eLpNorm (du - c.sum fun n a ↦ a • de n) 2 (volume.restrict s) <
          ENNReal.ofReal ε

noncomputable def apm_m02j02_sine (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_sineDeriv (n : ℕ) (x : ℝ) : ℝ :=
  (n + 1 : ℝ) * Real.pi * Real.cos ((n + 1 : ℝ) * Real.pi * x)

noncomputable def apm_m02j02_hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.eval x ((Polynomial.hermite n).map (Int.castRingHom ℝ)) *
    Real.exp (-(x ^ 2) / 4)

noncomputable def apm_m02j02_hermiteFunctionDeriv (n : ℕ) (x : ℝ) : ℝ :=
  deriv (apm_m02j02_hermiteFunction n) x

lemma apm_m02j02_hasDerivAt_sine (n : ℕ) (x : ℝ) :
    HasDerivAt (apm_m02j02_sine n) (apm_m02j02_sineDeriv n x) x := by
  convert (((hasDerivAt_id x).const_mul ((n + 1 : ℝ) * Real.pi)).sin) using 1 <;>
    simp [apm_m02j02_sineDeriv, id_eq] <;> ring

lemma apm_m02j02_deriv_sine (n : ℕ) (x : ℝ) :
    deriv (apm_m02j02_sine n) x = apm_m02j02_sineDeriv n x :=
  (apm_m02j02_hasDerivAt_sine n x).deriv

lemma apm_m02j02_sine_zero (n : ℕ) : apm_m02j02_sine n 0 = 0 := by
  simp [apm_m02j02_sine]

lemma apm_m02j02_sine_one (n : ℕ) : apm_m02j02_sine n 1 = 0 := by
  simp [apm_m02j02_sine, add_mul]

/-- Each interval basis function is smooth on the ambient real line. -/
lemma apm_m02j02_sine_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_sine n) := by
  unfold apm_m02j02_sine
  fun_prop

lemma apm_m02j02_sineDeriv_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_sineDeriv n) := by
  unfold apm_m02j02_sineDeriv
  fun_prop

/-- The Hermite-Gaussian functions occurring in both unbounded-domain
families are smooth. -/
lemma apm_m02j02_hermiteFunction_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (apm_m02j02_hermiteFunction n) := by
  let p : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => Polynomial.eval x p) := by
    simpa [Polynomial.aeval_def] using Polynomial.contDiff_aeval p ∞
  unfold apm_m02j02_hermiteFunction
  exact hp.mul (by fun_prop)

lemma apm_m02j02_hermiteFunction_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (apm_m02j02_hermiteFunction n)
      (apm_m02j02_hermiteFunctionDeriv n x) x := by
  simpa [apm_m02j02_hermiteFunctionDeriv] using
    ((apm_m02j02_hermiteFunction_contDiff n).differentiable
      (by simp)).differentiableAt.hasDerivAt

theorem apm_m02j02 :
    apm_m02j02_IsH10Basis (Ioo (0 : ℝ) 1)
        apm_m02j02_sine apm_m02j02_sineDeriv ∧
    apm_m02j02_IsH10Basis (Ioi (0 : ℝ))
        (fun n ↦ apm_m02j02_hermiteFunction (2 * n + 1))
        (fun n ↦ apm_m02j02_hermiteFunctionDeriv (2 * n + 1)) ∧
    apm_m02j02_IsH10Basis (Set.univ : Set ℝ)
        apm_m02j02_hermiteFunction apm_m02j02_hermiteFunctionDeriv := by
  /-
  Boundary (closer hop 1): the definition expands
  `H¹₀` into weak-derivative and graph-norm approximation clauses, so proving
  the three basis assertions requires, in particular, graph-norm density of
  sine series and of the full/odd Hermite families, plus compactly supported
  smooth approximation of every displayed Hermite function.

  This hop closes the elementary differential and boundary-value layer for the
  interval family: `apm_m02j02_hasDerivAt_sine` and
  `apm_m02j02_deriv_sine` identify the frozen derivative exactly, while
  `apm_m02j02_sine_zero` and `apm_m02j02_sine_one` prove the two Dirichlet
  endpoint values.

  Searches of Mathlib and compiled problem artifacts found polynomial identities
  for `Polynomial.hermite` (and local uses in `a96A04`) and general eLp/Sobolev
  inequalities, but no Hermite completeness theorem, Fourier-sine density
  theorem, or packaged Sobolev space whose basis result could discharge these
  exact `eLpNorm` approximation goals. Searches also covered
  `LEMMA-INDEX.md`, all solved artifacts, `ConstructionTargets/`, Mathlib's
  Hermite Gaussian file and Sobolev inequality source, and git history. Sibling
  `a96A04` uses Hermite polynomials only for finite Gaussian derivative
  formulas, and `m95A02` provides no reusable Fourier density theorem.
  Establishing the three spectral completeness theorems remains open.

  Closer hop 2 closes the ambient smoothness layer for every displayed
  family. `apm_m02j02_sine_contDiff` and
  `apm_m02j02_sineDeriv_contDiff` prove global smoothness of the interval
  functions and their frozen derivatives. For the unbounded families,
  `apm_m02j02_hermiteFunction_contDiff` combines
  `Polynomial.contDiff_aeval` with smoothness of the Gaussian factor, and
  `apm_m02j02_hermiteFunction_hasDerivAt` certifies the frozen derivative at
  every point. This removes ordinary differentiability/regularity from the
  remaining obligations. Renewed searches of orthonormal-basis, Schwartz,
  Fourier-sine, and Hermite sources still found no completeness theorem that
  transports to the custom value/derivative-pair graph norm. Membership via
  compactly supported approximation, linear independence, and the three
  density clauses therefore remain open.
  -/
  sorry
