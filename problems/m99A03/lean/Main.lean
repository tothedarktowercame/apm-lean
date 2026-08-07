import Mathlib

/-! # APM m99A03: compact powers and normal nilpotent operators

## Statement repairs

Part (b) cannot hold on every Hilbert space (for example, not on a
finite-dimensional one).  Its instruction to “construct an example” is encoded
as an existential example on the explicit infinite-dimensional Hilbert space
`m99A03ExampleSpace`.
-/

noncomputable section

abbrev m99A03L2 := lp (fun _ : ℕ => ℂ) 2
abbrev m99A03ExampleSpace := m99A03L2 × m99A03L2 × m99A03L2

/-- The three-step block shift used in the non-normal counterexample. -/
def m99A03Shift : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace where
  toFun x := (x.2.1, x.2.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  cont := by fun_prop

@[simp] lemma m99A03Shift_apply (x : m99A03ExampleSpace) :
    m99A03Shift x = (x.2.1, x.2.2, 0) := rfl

lemma m99A03Shift_sq_apply (x : m99A03ExampleSpace) :
    (m99A03Shift ^ 2) x = (x.2.2, 0, 0) := by
  simp [pow_two]

lemma m99A03Shift_cube : m99A03Shift ^ 3 = 0 := by
  ext x <;> simp [pow_succ]

/-- Unit vectors witnessing that the first shift contains an identity block. -/
def m99A03FirstTest (n : ℕ) : m99A03ExampleSpace :=
  (0, lp.single 2 n 1, 0)

/-- Unit vectors witnessing that the squared shift contains an identity block. -/
def m99A03SecondTest (n : ℕ) : m99A03ExampleSpace :=
  (0, 0, lp.single 2 n 1)

@[simp] lemma m99A03Shift_firstTest (n : ℕ) :
    m99A03Shift (m99A03FirstTest n) = (lp.single 2 n 1, 0, 0) := rfl

@[simp] lemma m99A03Shift_sq_secondTest (n : ℕ) :
    (m99A03Shift ^ 2) (m99A03SecondTest n) = (lp.single 2 n 1, 0, 0) := by
  simp [m99A03Shift_sq_apply, m99A03SecondTest]

@[simp] lemma norm_m99A03FirstTest (n : ℕ) : ‖m99A03FirstTest n‖ = 1 := by
  simp [m99A03FirstTest, lp.norm_single]

@[simp] lemma norm_m99A03SecondTest (n : ℕ) : ‖m99A03SecondTest n‖ = 1 := by
  simp [m99A03SecondTest, lp.norm_single]

/-- Distinct coordinate vectors in the first block stay uniformly apart. -/
lemma m99A03_firstBlock_separated (n m : ℕ) (hnm : n ≠ m) :
    1 ≤ dist ((lp.single 2 n 1, 0, 0) : m99A03ExampleSpace)
      (lp.single 2 m 1, 0, 0) := by
  have hcoord := lp.norm_apply_le_norm (by norm_num)
    ((lp.single 2 n (1 : ℂ) : m99A03L2) -
      (lp.single 2 m (1 : ℂ) : m99A03L2)) n
  have hval : (((lp.single 2 n (1 : ℂ) : m99A03L2) -
      (lp.single 2 m (1 : ℂ) : m99A03L2)) n) = 1 := by
    change (lp.single 2 n (1 : ℂ) : m99A03L2) n -
      (lp.single 2 m (1 : ℂ) : m99A03L2) n = 1
    rw [lp.single_apply_self,
      lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 m (1 : ℂ) hnm]
    norm_num
  rw [dist_eq_norm]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Prod.norm_def,
    norm_zero]
  rw [hval] at hcoord
  norm_num at hcoord
  simpa [max_eq_left (norm_nonneg _)] using hcoord

/-- A continuous linear map with a uniformly separated image of a unit-ball
sequence cannot be compact. -/
lemma m99A03_not_isCompactOperator_of_separated_unit
    (A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace)
    (u : ℕ → m99A03ExampleSpace)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hsep : ∀ n m, n ≠ m → 1 ≤ dist (A (u n)) (A (u m))) :
    ¬ IsCompactOperator A := by
  intro hcompact
  obtain ⟨K, hK, hAK⟩ := hcompact.image_closedBall_subset_compact 1
  have hmem : ∀ n, A (u n) ∈ K := by
    intro n
    apply hAK
    exact ⟨u n, by simpa [Metric.mem_closedBall, dist_eq_norm] using hu n, rfl⟩
  obtain ⟨x, hx, φ, hφ, htend⟩ := hK.tendsto_subseq hmem
  have hcauchy : CauchySeq (A ∘ u ∘ φ) := htend.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hcauchy) 1 zero_lt_one
  have hlt := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hne : φ N ≠ φ (N + 1) :=
    ne_of_lt (hφ (Nat.lt_succ_self N))
  have hge := hsep (φ N) (φ (N + 1)) hne
  exact (not_lt_of_ge hge) (by simpa [Function.comp_apply] using hlt)

theorem apm_m99a03 :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → IsStarNormal A → A ^ 3 = 0 → A = 0) ∧
    (∃ A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace,
      ¬IsCompactOperator A ∧
      ¬IsCompactOperator
        ((A ^ 2 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace) ∧
      IsCompactOperator
        ((A ^ 3 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace)) := by
  constructor
  · intro H _ _ _ A _hcompact hnormal hcube
    have hfourth : A ^ 4 = 0 := by
      calc
        A ^ 4 = A ^ 3 * A := by noncomm_ring
        _ = 0 := by rw [hcube, zero_mul]
    letI : IsStarNormal A := hnormal
    have hrad : spectralRadius ℂ A = 0 := by
      have hp := spectrum.spectralRadius_pow_le (𝕜 := ℂ) A 4 (by norm_num)
      rw [hfourth, spectrum.spectralRadius_zero] at hp
      have hp0 : (spectralRadius ℂ A) ^ 4 = 0 := le_antisymm hp bot_le
      exact eq_zero_of_pow_eq_zero hp0
    have hnorm : ‖A‖₊ = 0 := by
      have hs := IsStarNormal.spectralRadius_eq_nnnorm A
      rw [hrad] at hs
      simpa using hs.symm
    exact nnnorm_eq_zero.mp hnorm
  · refine ⟨m99A03Shift, ?_, ?_, ?_⟩
    · apply m99A03_not_isCompactOperator_of_separated_unit
        m99A03Shift m99A03FirstTest
      · intro n
        simp
      · intro n m hnm
        simpa [m99A03FirstTest] using m99A03_firstBlock_separated n m hnm
    · apply m99A03_not_isCompactOperator_of_separated_unit
        (m99A03Shift ^ 2) m99A03SecondTest
      · intro n
        simp
      · intro n m hnm
        simpa [m99A03SecondTest, m99A03Shift_sq_apply] using
          m99A03_firstBlock_separated n m hnm
    · rw [m99A03Shift_cube]
      exact isCompactOperator_zero
