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

/-- Completeness transports from the finite-dimensional polynomial model.
This closes the first frozen conjunct independently of the operator and
Gram--Schmidt constructions. -/
lemma apm_m95J01_complete_of_equiv
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) : Nonempty (CompleteSpace H) := by
  letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  letI : FiniteDimensional ℝ H := P.symm.finiteDimensional
  exact ⟨FiniteDimensional.complete ℝ H⟩

/-- The differential part `P'' - 2P'` strictly lowers degree, hence has zero
coefficient in the top slot of `degreeLE n`. -/
lemma apm_m95J01_top_coeff_derivative_sub
    {n : ℕ} (p : Polynomial.degreeLE ℝ n) :
    (Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
      2 • Polynomial.derivative (p : Polynomial ℝ)).coeff n = 0 := by
  have hpdeg : (p : Polynomial ℝ).degree ≤ (n : WithBot ℕ) :=
    Polynomial.mem_degreeLE.mp p.property
  have hcoeff1 : (p : Polynomial ℝ).coeff (n + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hpdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self n))
  have hcoeff2 : (p : Polynomial ℝ).coeff (n + 2) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hpdeg.trans_lt (by exact_mod_cast (by omega : n < n + 2)))
  simp [Polynomial.coeff_derivative, hcoeff1, hcoeff2]

/-- The top-coefficient condition in the frozen range characterization is
necessary: it follows directly from the encoded formula for `T`. -/
lemma apm_m95J01_range_top_coeff_zero
    {n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) (T : H →ₗ[ℝ] H)
    (hT : ∀ f : H,
      (P (T f) : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) +
          (P f : Polynomial ℝ))
    {f g : H} (hfg : T f - f = g) :
    (P g : Polynomial ℝ).coeff n = 0 := by
  have hp : P (T f - f) = P g := congrArg P hfg
  rw [map_sub] at hp
  have hpoly := congrArg
    (fun q : Polynomial.degreeLE ℝ n ↦ (q : Polynomial ℝ)) hp
  change (P (T f) : Polynomial ℝ) - (P f : Polynomial ℝ) =
    (P g : Polynomial ℝ) at hpoly
  rw [hT f] at hpoly
  have hdiff :
      (P g : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) := by
    rw [← hpoly]
    abel
  rw [hdiff]
  exact apm_m95J01_top_coeff_derivative_sub (P f)

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
  --
  -- Closer hop 2 compiles the necessary half of the range characterization.
  -- `apm_m95J01_top_coeff_derivative_sub` uses membership in `degreeLE n`
  -- and `Polynomial.coeff_derivative` to prove directly that `P'' - 2P'`
  -- has zero coefficient at `n`. `apm_m95J01_range_top_coeff_zero` then
  -- transports an equation `T f - f = g` through the supplied linear
  -- equivalence, rewrites it with `hT`, and concludes `(P g).coeff n = 0`.
  -- Hence the forward implication of the third frozen conjunct is closed.
  --
  -- Searches beyond hop 1 inspected the polynomial derivative and
  -- `degreeLE` sources, normalized Gram--Schmidt users, `LEMMA-INDEX.md`,
  -- `ConstructionTargets/`, and polynomial siblings. No theorem packages the
  -- reverse triangular recursion. That converse, completeness-instance
  -- installation, monomial filtration independence, and the adapted
  -- orthonormal-basis construction remain open. The frozen statement is
  -- unchanged.
  --
  -- Closer hop 3 routes around the still-open triangular recursion and closes
  -- another independent frozen component. `apm_m95J01_complete_of_equiv`
  -- transports the existing `FiniteDimensional` instance on
  -- `Polynomial.degreeLE ℝ n` back through `P.symm`, then invokes
  -- `FiniteDimensional.complete`; hence `Nonempty (CompleteSpace H)` is now
  -- compiled without using the integral geometry. Renewed searches of the
  -- derivative, nilpotent, and degree-filtration APIs found no packaged
  -- inverse for `P'' - 2P'` on the codimension-one top-coefficient kernel.
  -- That converse and the adapted Gram--Schmidt basis remain open without an
  -- unproved assertion; the frozen statement is unchanged.
  sorry
