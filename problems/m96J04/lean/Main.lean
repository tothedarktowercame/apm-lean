import Mathlib

/-!
# APM m96J04

## Statement repairs

None.

## Encoding questions

The Hilbert-space example is stated on two copies of `ℓ²(ℕ,ℝ)`. The Banach-space
example is pinned to the Volterra operator on `C([0,1],ℝ)` by its pointwise
integral formula, rather than represented by an anonymous compact operator.
-/

noncomputable section

abbrev apm_m96j04_H := ℓ²(ℕ, ℝ) × ℓ²(ℕ, ℝ)
abbrev apm_m96j04_C := C(Set.Icc (0 : ℝ) 1, ℝ)

def apm_m96j04_extend (f : apm_m96j04_C) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

/-- The block operator from the Hilbert-space example, together with its
pointwise formula and compactness of all powers from the second onward. -/
lemma apm_m96j04_block_exists :
    ∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H,
      (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧
      ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n) := by
  let A : apm_m96j04_H →L[ℝ] apm_m96j04_H :=
    (ContinuousLinearMap.inl ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))
  refine ⟨A, ?_, ?_⟩
  · intro x y
    simp [A]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hzero : A ^ (2 + k) = 0 := by
      rw [pow_add]
      simp [show A ^ 2 = 0 by ext z <;> simp [A, pow_two]]
    rw [hzero]
    exact isCompactOperator_zero

theorem apm_m96j04 :
    (∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H,
      (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧
      ¬IsCompactOperator A ∧
      ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n)) ∧
    ∃ V : apm_m96j04_C →L[ℝ] apm_m96j04_C,
      (∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
        V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) ∧
      IsCompactOperator V ∧
      ∀ eigenvalue : ℝ, eigenvalue ≠ 0 →
        ∀ f : apm_m96j04_C, V f = eigenvalue • f → f = 0 := by
  /-
  PARTIAL.  `apm_m96j04_block_exists` constructs the required block map,
  proves its displayed action, proves `A ^ 2 = 0`, and hence proves compactness
  of every `A ^ n` for `2 ≤ n` using `isCompactOperator_zero`.

  For noncompactness, composing a hypothetical compact `A` with
  `ContinuousLinearMap.inr` and `ContinuousLinearMap.fst` makes the identity
  on `ℓ²(ℕ,ℝ)` compact; `FiniteDimensional.of_isCompactOperator_id`
  then gives finite dimensionality.  Searches of Mathlib's `lp`, Hilbert-basis,
  and finite-dimensional APIs did not expose the final packaged contradiction
  that `ℓ²(ℕ,ℝ)` is infinite-dimensional.

  The Volterra clause requires first bundling the parameter-dependent interval
  integral as a continuous linear map into `C(Icc 0 1,ℝ)`.  Compactness then
  needs converting its uniformly bounded Lipschitz image of the unit ball into
  the pointwise-compact hypothesis of
  `ArzelaAscoli.isCompact_of_equicontinuous`.  The eigenvalue clause requires
  an interval FTC/ODE uniqueness bridge.  Mathlib contains the generic Ascoli
  and FTC ingredients, but neither the closed corpus nor `ConstructionTargets/`
  contains this Volterra assembly.
  -/
  sorry
