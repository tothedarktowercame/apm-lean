import Mathlib

/-!
# APM m94J02

## Statement repairs

The claimed bound `‖fg‖ ≤ ‖f‖‖g‖` is false for the printed weight
`n² + 1`: for `f = g = z`, the two sides are `5` and `4`. It is
minimally repaired to the sharp bound `‖fg‖ ≤ (5/4)‖f‖‖g‖`, which still
makes the complete normed space a Banach algebra.

## Encoding questions

The space is encoded by its unique coefficient sequences. Compactness of the
dilation is stated in the sequential form for its unit ball, and the spectrum
uses the usual bounded two-sided-inverse definition, both with the displayed
weighted norm.
-/

open Filter Set

/-- Membership in the weighted `ℓ¹` coefficient space. -/
def apm_m94J02_mem (a : ℕ → ℂ) : Prop :=
  Summable (fun n ↦ ‖a n‖ * ((n : ℝ) ^ 2 + 1))

/-- The norm printed in the problem. -/
noncomputable def apm_m94J02_norm (a : ℕ → ℂ) : ℝ :=
  ∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1)

/-- Evaluation of the represented power series. -/
noncomputable def apm_m94J02_eval (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, a n * z ^ n

/-- Cauchy-product coefficients. -/
noncomputable def apm_m94J02_mul (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficients of the `m`th pointwise power. -/
noncomputable def apm_m94J02_pow (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun n ↦ if n = 0 then 1 else 0
  | m + 1 => apm_m94J02_mul (apm_m94J02_pow a m) a

/-- The coefficient action of `Tf(z)=f(z/2)`. -/
noncomputable def apm_m94J02_T (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (-(n : ℤ)) * a n

/-- Scalars for which `T - λI` has no bounded two-sided inverse on `X`. -/
def apm_m94J02_spectrum : Set ℂ :=
  {z | ¬∃ S : (ℕ → ℂ) → (ℕ → ℂ),
    (∀ a, apm_m94J02_mem a → apm_m94J02_mem (S a)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ a, apm_m94J02_mem a →
      apm_m94J02_norm (S a) ≤ C * apm_m94J02_norm a) ∧
    (∀ a, apm_m94J02_mem a →
      S (fun n ↦ apm_m94J02_T a n - z * a n) = a) ∧
    (∀ a, apm_m94J02_mem a →
      (fun n ↦ apm_m94J02_T (S a) n - z * (S a) n) = a)}

/-- Every displayed diagonal entry is in the custom spectrum. -/
lemma apm_m94J02_eigenvalue_mem_spectrum (j : ℕ) :
    (2 : ℂ) ^ (-(j : ℤ)) ∈ apm_m94J02_spectrum := by
  intro hS
  rcases hS with ⟨S, _, _, hleft, _⟩
  let e : ℕ → ℂ := fun n => if n = j then 1 else 0
  have he_mem : apm_m94J02_mem e := by
    unfold apm_m94J02_mem e
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton j).subset (by
      intro n hn
      by_contra hnj
      apply hn
      dsimp
      rw [if_neg (by simpa using hnj)]
      simp)
  have hz_mem : apm_m94J02_mem (fun _ : ℕ => (0 : ℂ)) := by
    unfold apm_m94J02_mem
    simp
  have hzero : (fun n => apm_m94J02_T e n - (2 : ℂ) ^ (-(j : ℤ)) * e n) =
      (fun _ => 0) := by
    funext n
    by_cases hnj : n = j
    · subst n
      simp [apm_m94J02_T, e]
    · simp [apm_m94J02_T, e, hnj]
  have hSe : S (fun _ : ℕ => (0 : ℂ)) = e := by
    rw [← hzero]
    exact hleft e he_mem
  have hSz : S (fun _ : ℕ => (0 : ℂ)) = (fun _ => 0) := by
    simpa [apm_m94J02_T] using hleft (fun _ : ℕ => (0 : ℂ)) hz_mem
  have hej : e j = 1 := by simp [e]
  have : e = (fun _ => 0) := hSe.symm.trans hSz
  have := congrFun this j
  simp [hej] at this

/-- The dilation is a contraction for the displayed weighted norm. -/
lemma apm_m94J02_norm_T_le (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    apm_m94J02_norm (apm_m94J02_T a) ≤ apm_m94J02_norm a := by
  unfold apm_m94J02_norm
  unfold apm_m94J02_mem at ha
  simp only [apm_m94J02_T]
  have hleft : Summable
      (fun n : ℕ ↦ ‖(2 : ℂ) ^ (-(n : ℤ)) * a n‖ * ((n : ℝ) ^ 2 + 1)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) ha
    rw [norm_mul]
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs) (by positivity)
  exact Summable.tsum_le_tsum (fun n ↦ by
    rw [norm_mul]
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs) (by positivity)) hleft ha

theorem apm_m94j02 :
    (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k)) →
        (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
        ∃ b, apm_m94J02_mem b ∧
          ∀ ε > 0, ∃ N, ∀ n ≥ N,
            apm_m94J02_norm (fun k ↦ a n k - b k) < ε) ∧
      (∀ a, apm_m94J02_mem a →
        ContinuousOn (apm_m94J02_eval a) (Metric.closedBall 0 1)) ∧
      (∀ a b, apm_m94J02_mem a → apm_m94J02_mem b →
        apm_m94J02_mem (apm_m94J02_mul a b) ∧
        apm_m94J02_norm (apm_m94J02_mul a b) ≤
          (5 / 4 : ℝ) * apm_m94J02_norm a * apm_m94J02_norm b) ∧
      (∀ a, apm_m94J02_mem a →
        ∃ L : ℝ, Tendsto
          (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
            ((n : ℝ)⁻¹)) atTop (nhds L)) ∧
      (∀ a, apm_m94J02_mem a → apm_m94J02_mem (apm_m94J02_T a)) ∧
      (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
          Tendsto (fun k ↦ apm_m94J02_norm
            (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0)) ∧
      apm_m94J02_spectrum =
        {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) := by
  have hT_mem : ∀ a, apm_m94J02_mem a →
      apm_m94J02_mem (apm_m94J02_T a) := by
    intro a ha
    unfold apm_m94J02_mem at ha ⊢
    simp only [apm_m94J02_T]
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) ha
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs)
      (by positivity)
  /-
  Boundary: the remaining clauses require a full weighted-`ℓ¹` completeness
  proof, uniform convergence of the coefficient series on the closed disk,
  rearrangement of a nonnegative double series for the Cauchy product, and
  the sharp weight inequality with factor `5/4`. The power-limit clause then
  needs a Fekete/subadditivity argument that also handles zero powers.

  Compactness requires diagonal subsequence extraction for every unit-ball
  sequence and weighted tail control. The spectrum equality requires
  constructing bounded diagonal inverses away from the closed eigenvalue set,
  and exhibiting failure of surjectivity at zero in the statement's custom
  two-sided-inverse encoding. The local lemma
  `apm_m94J02_eigenvalue_mem_spectrum` now proves that every `2^(-n)` has no
  inverse, directly from the coordinate vector and the zero vector. I searched
  Mathlib's summability, Fekete, and diagonal operator APIs; no compiled
  sibling assembled these custom weighted-sequence arguments within this
  pass. The elementary dilation membership clause is proved above.

  Closer hop 2 additionally proves `apm_m94J02_norm_T_le`: the diagonal
  dilation is a contraction in the exact weighted norm.  This uses
  `Summable.tsum_le_tsum` with the coordinate estimate `‖2⁻ⁿ‖ ≤ 1` and
  supplies the quantitative input for both diagonal tail compactness and the
  bounded-inverse contradiction at zero.  Searches of `LEMMA-INDEX.md`, all
  closed artifacts, Mathlib diagonal-operator/summability sources, and the
  construction libraries found no packaged weighted-ℓ¹ compactness or custom
  spectrum theorem.  The remaining bridge therefore still requires the
  diagonal subsequence/tail construction and explicit reciprocal multiplier
  bounds away from `{0} ∪ range (2⁻ⁿ)`.
  -/
  have hremaining :
      (∀ a : ℕ → ℕ → ℂ,
          (∀ k, apm_m94J02_mem (a k)) →
          (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
            apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
          ∃ b, apm_m94J02_mem b ∧
            ∀ ε > 0, ∃ N, ∀ n ≥ N,
              apm_m94J02_norm (fun k ↦ a n k - b k) < ε) ∧
        (∀ a, apm_m94J02_mem a →
          ContinuousOn (apm_m94J02_eval a) (Metric.closedBall 0 1)) ∧
        (∀ a b, apm_m94J02_mem a → apm_m94J02_mem b →
          apm_m94J02_mem (apm_m94J02_mul a b) ∧
          apm_m94J02_norm (apm_m94J02_mul a b) ≤
            (5 / 4 : ℝ) * apm_m94J02_norm a * apm_m94J02_norm b) ∧
        (∀ a, apm_m94J02_mem a →
          ∃ L : ℝ, Tendsto
            (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
              ((n : ℝ)⁻¹)) atTop (nhds L)) ∧
        (∀ a : ℕ → ℕ → ℂ,
          (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
            Tendsto (fun k ↦ apm_m94J02_norm
              (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0)) ∧
        apm_m94J02_spectrum =
          {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) := by
    sorry
  exact ⟨hremaining.1, hremaining.2.1, hremaining.2.2.1,
    hremaining.2.2.2.1, hT_mem, hremaining.2.2.2.2.1,
    hremaining.2.2.2.2.2⟩
