import Mathlib

/-!
# APM m95J01: decaying polynomials and the second derivative

## Statement repairs

None.

## Encoding questions

The function space is represented by an abstract inner-product space together
with an exact linear equivalence to polynomials of degree at most `n` and an
exact realization map `f(x)=e⁻ˣP(x)`. The integral identity pins its inner
product to the one printed in the problem, so this is not a coefficient-space
surrogate with the wrong geometry.
-/

noncomputable section

open MeasureTheory Set


/-- The polynomial model fixes the dimension before any integral or
Gram--Schmidt calculation is needed. -/
lemma apm_m95J01_finrank_of_equiv
    {n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) :
    Module.finrank ℝ H = n + 1 := by
  rw [← Polynomial.degreeLT_succ_eq_degreeLE] at P
  rw [LinearEquiv.finrank_eq P,
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1))]
  simp

theorem apm_m95j01
    (n : ℕ) (hn : 0 < n)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n)
    (realize : H → ℝ → ℝ)
    (hrealize : ∀ (f : H) (x : ℝ),
      realize f x = Real.exp (-x) * (P f : Polynomial ℝ).eval x)
    (hinner : ∀ f g : H,
      inner ℝ f g = ∫ x in Set.Ioi (0 : ℝ), realize f x * realize g x)
    (monomial : Fin (n + 1) → H)
    (hmonomial : ∀ k : Fin (n + 1),
      (P (monomial k) : Polynomial ℝ) = Polynomial.X ^ (k : ℕ))
    (T : H →ₗ[ℝ] H)
    (hT : ∀ f : H,
      (P (T f) : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) +
          (P f : Polynomial ℝ)) :
    Nonempty (CompleteSpace H) ∧
    Module.finrank ℝ H = n + 1 ∧
    (∀ g : H,
      (∃ f : H, T f - f = g) ↔ (P g : Polynomial ℝ).coeff n = 0) ∧
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ H,
      ∀ k : Fin (n + 1),
        b k ∈ Submodule.span ℝ (monomial '' Set.Iic k) := by
  -- SKIPPED: multi-part problem on e^{-x}·P(x) function space.
  -- (1) H is complete (finite-dim ⟹ Banach). (2) finrank = n+1.
  -- (3) T-I surjectivity characterization via constant term of P''-2P'+P.
  -- (4) Gram-Schmidt orthonormal basis adapted to monomial filtration.
  -- Blocker: requires inner product integral evaluation, Laguerre polynomial theory,
  -- Gram-Schmidt construction, and operator surjectivity analysis.
  -- APIs: `InnerProductSpace`, `Polynomial.derivative`, `Module.finrank`, `OrthonormalBasis`.
  --
  -- Closer hop 1 proves `apm_m95J01_finrank_of_equiv`, transporting dimension
  -- through `P`, rewriting `degreeLE n` as `degreeLT (n+1)`, and applying
  -- `Polynomial.degreeLTEquiv`. Thus the second conjunct is closed
  -- independently of the integral geometry. Mathlib's
  -- `gramSchmidtNormed_orthonormal'` and
  -- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` provide the
  -- likely adapted-basis route once linear independence of the supplied
  -- monomials and equality of their filtration spans are established.
  --
  -- For the third conjunct, `Polynomial.coeff_derivative` confirms that
  -- `P'' - 2P'` has vanishing top coefficient. The converse still needs a
  -- finite triangular recursion (or nilpotent inverse) internal to
  -- `Polynomial.degreeLE`. Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  -- polynomial siblings, and git history found no packaged image theorem for
  -- this operator. Completeness then follows from the now-known finite
  -- dimension, but the exact instance-installation and the two remaining
  -- operator/basis constructions were not completed. The statement is unchanged.
  sorry
