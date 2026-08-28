import Mathlib

/-!
# APM a98A03

## Statement repairs

None.

## Encoding notes

The problem's functions on `[0, 1]` are represented by functions on `ℝ`, with
all hypotheses restricted to the unit interval.  Since Mathlib's integral is
the Lebesgue integral, the Riemann-integrable strengthening is expressed using
the tagged-partition definition below, including its proposed integral value.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-- `g` has Riemann integral `I` on `[0, 1]`, expressed by convergence of all
tagged sums as the mesh tends to zero. -/
def HasRiemannIntegralOnUnitInterval (g : ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ) (tag : Fin n → ℝ),
        x 0 = 0 → x (Fin.last n) = 1 → StrictMono x →
        (∀ i : Fin n, x i.castSucc ≤ tag i ∧ tag i ≤ x i.succ) →
        (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
        |(∑ i, g (tag i) * (x i.succ - x i.castSucc)) - I| < ε

/-- Mean-value tags in exactly the increment form required by the custom
tagged Riemann sums. -/
lemma apm_a98a03_exists_mvt_tag
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) :
    ∃ t ∈ Ioo a b, f b - f a = f' t * (b - a) := by
  have hcont : ContinuousOn f (Icc a b) := hf_cont.mono fun x hx ↦
    ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x := by
    intro x hx
    exact hf_deriv x ⟨ha.1.trans_lt hx.1, hx.2.trans_le hb.2⟩
  obtain ⟨t, ht, hslope⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  refine ⟨t, ht, ?_⟩
  rw [hslope]
  exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')).symm

/-- Adjacent increments along a `Fin`-indexed partition telescope to the
endpoint increment.  This is the finite algebraic step needed after choosing
the mean-value tags above. -/
lemma apm_a98a03_sum_adjacent_sub
    {G : Type*} [AddCommGroup G] (n : ℕ) (f : ℝ → G)
    (x : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f (x i.succ) - f (x i.castSucc))) =
      f (x (Fin.last n)) - f (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [← Fin.castSucc_succ]
      rw [ih (fun i ↦ x i.castSucc)]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      abel

/-- A uniform `Fin`-indexed partition of `[0,1]` can be chosen with mesh
smaller than any prescribed positive number. -/
lemma apm_a98a03_exists_fine_uniform_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ),
      x 0 = 0 ∧ x (Fin.last n) = 1 ∧ StrictMono x ∧
      ∀ i : Fin n, x i.succ - x i.castSucc < δ := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  let n := k + 1
  have hn : 0 < n := Nat.succ_pos k
  let x : Fin (n + 1) → ℝ := fun i ↦ (i : ℝ) / n
  refine ⟨n, hn, x, ?_, ?_, ?_, ?_⟩
  · simp [x]
  · simp [x, n, Nat.cast_add, Nat.cast_one,
      show (k : ℝ) + 1 ≠ 0 by positivity]
  · intro i j hij
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)
  · intro i
    calc
      x i.succ - x i.castSucc = 1 / (n : ℝ) := by
        simp only [x, Fin.val_castSucc]
        rw [show (i.succ.val : ℝ) = i.val + 1 by norm_num]
        field_simp
        ring
      _ < δ := by simpa [n, Nat.cast_add, Nat.cast_one] using hk

/-- The tagged-sum definition implies the FTC when every interior derivative
exists: choose mean-value tags on one sufficiently fine partition. -/
lemma apm_a98a03_riemann_ftc
    (f f' : ℝ → ℝ) (I : ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hriem : HasRiemannIntegralOnUnitInterval f' I) :
    f 1 - f 0 = I := by
  by_contra hne
  have heps : 0 < |(f 1 - f 0) - I| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ, hδ, hsum⟩ := hriem _ heps
  obtain ⟨n, hn, x, hx0, hx1, hxmono, hmesh⟩ :=
    apm_a98a03_exists_fine_uniform_partition hδ
  have hcell (i : Fin n) :
      ∃ t ∈ Ioo (x i.castSucc) (x i.succ),
        f (x i.succ) - f (x i.castSucc) =
          f' t * (x i.succ - x i.castSucc) := by
    apply apm_a98a03_exists_mvt_tag hf_cont hf_deriv
    · constructor
      · rw [← hx0]
        exact hxmono.monotone (Fin.zero_le _)
      · rw [← hx1]
        exact hxmono.monotone (Fin.le_last _)
    · constructor
      · rw [← hx0]
        exact hxmono.monotone (Fin.zero_le _)
      · rw [← hx1]
        exact hxmono.monotone (Fin.le_last _)
    · exact hxmono Fin.castSucc_lt_succ
  choose tag htag htag_eq using hcell
  have htag_closed (i : Fin n) :
      x i.castSucc ≤ tag i ∧ tag i ≤ x i.succ :=
    ⟨(htag i).1.le, (htag i).2.le⟩
  have hclose := hsum n hn x tag hx0 hx1 hxmono htag_closed hmesh
  have htel : (∑ i : Fin n, f' (tag i) *
      (x i.succ - x i.castSucc)) = f 1 - f 0 := by
    rw [← hx0, ← hx1, ← apm_a98a03_sum_adjacent_sub n f x]
    apply Finset.sum_congr rfl
    intro i _
    exact (htag_eq i).symm
  rw [htel] at hclose
  exact (lt_irrefl _ hclose)

/-- The binary value of the canonical Boolean address of a point in the
ternary Cantor set.  This is the continuous core of the devil's staircase. -/
def apm_a98a03_cantorCore (x : cantorSet) : ℝ :=
  (Real.fromBinary (cantorSetHomeomorphNatToBool x) : ℝ)

lemma apm_a98a03_cantorCore_eq_ofDigits (x : cantorSet) :
    apm_a98a03_cantorCore x =
      Real.ofDigits (fun i ↦ if (cantorToBinary (x : ℝ)).get i then
        (1 : Fin 2) else 0) := by
  change Real.ofDigits
      ((Homeomorph.piCongrRight fun _ : ℕ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
        (cantorSetEquivNatToBool x)) = _
  congr 1
  funext i
  simp only [Homeomorph.piCongrRight_apply, cantorSetEquivNatToBool]
  change finTwoEquiv.symm ((cantorToBinary (x : ℝ)).get i) = _
  cases (cantorToBinary (x : ℝ)).get i <;> rfl

def apm_a98a03_ternaryDigit (a : ℕ → Bool) (i : ℕ) : Fin 3 :=
  if a i then 2 else 0

def apm_a98a03_binaryDigit (a : ℕ → Bool) (i : ℕ) : Fin 2 :=
  if a i then 1 else 0

lemma apm_a98a03_ternary_lt_of_first_false_true
    (a b : ℕ → Bool) (n : ℕ)
    (hp : ∀ i < n, a i = b i) (ha : a n = false) (hb : b n = true) :
    Real.ofDigits (apm_a98a03_ternaryDigit a) <
      Real.ofDigits (apm_a98a03_ternaryDigit b) := by
  have hsum : (∑ i ∈ Finset.range n,
      Real.ofDigitsTerm (apm_a98a03_ternaryDigit a) i) =
      ∑ i ∈ Finset.range n,
        Real.ofDigitsTerm (apm_a98a03_ternaryDigit b) i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi := hp i (Finset.mem_range.mp hi)
    simp [Real.ofDigitsTerm, apm_a98a03_ternaryDigit, hi]
  rw [Real.ofDigits_eq_sum_add_ofDigits (apm_a98a03_ternaryDigit a) (n + 1),
    Real.ofDigits_eq_sum_add_ofDigits (apm_a98a03_ternaryDigit b) (n + 1),
    Finset.sum_range_succ, Finset.sum_range_succ, hsum]
  rw [show Real.ofDigitsTerm (apm_a98a03_ternaryDigit a) n = 0 by
      simp [Real.ofDigitsTerm, apm_a98a03_ternaryDigit, ha],
    show Real.ofDigitsTerm (apm_a98a03_ternaryDigit b) n =
        2 * ((3 : ℝ) ^ (n + 1))⁻¹ by
      simp [Real.ofDigitsTerm, apm_a98a03_ternaryDigit, hb]]
  let P := ∑ i ∈ Finset.range n,
    Real.ofDigitsTerm (apm_a98a03_ternaryDigit b) i
  let ta := Real.ofDigits (fun i ↦ apm_a98a03_ternaryDigit a (i + (n + 1)))
  let tb := Real.ofDigits (fun i ↦ apm_a98a03_ternaryDigit b (i + (n + 1)))
  change P + 0 + ((3 : ℝ) ^ (n + 1))⁻¹ * ta <
    P + 2 * ((3 : ℝ) ^ (n + 1))⁻¹ + ((3 : ℝ) ^ (n + 1))⁻¹ * tb
  have hta : ta ≤ 1 := Real.ofDigits_le_one _
  have htb : 0 ≤ tb := Real.ofDigits_nonneg _
  have hpow : 0 < ((3 : ℝ) ^ (n + 1))⁻¹ := by positivity
  nlinarith

lemma apm_a98a03_binary_le_of_first_false_true
    (a b : ℕ → Bool) (n : ℕ)
    (hp : ∀ i < n, a i = b i) (ha : a n = false) (hb : b n = true) :
    Real.ofDigits (apm_a98a03_binaryDigit a) ≤
      Real.ofDigits (apm_a98a03_binaryDigit b) := by
  have hsum : (∑ i ∈ Finset.range n,
      Real.ofDigitsTerm (apm_a98a03_binaryDigit a) i) =
      ∑ i ∈ Finset.range n,
        Real.ofDigitsTerm (apm_a98a03_binaryDigit b) i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi := hp i (Finset.mem_range.mp hi)
    simp [Real.ofDigitsTerm, apm_a98a03_binaryDigit, hi]
  rw [Real.ofDigits_eq_sum_add_ofDigits (apm_a98a03_binaryDigit a) (n + 1),
    Real.ofDigits_eq_sum_add_ofDigits (apm_a98a03_binaryDigit b) (n + 1),
    Finset.sum_range_succ, Finset.sum_range_succ, hsum]
  rw [show Real.ofDigitsTerm (apm_a98a03_binaryDigit a) n = 0 by
      simp [Real.ofDigitsTerm, apm_a98a03_binaryDigit, ha],
    show Real.ofDigitsTerm (apm_a98a03_binaryDigit b) n =
        ((2 : ℝ) ^ (n + 1))⁻¹ by
      simp [Real.ofDigitsTerm, apm_a98a03_binaryDigit, hb]]
  let P := ∑ i ∈ Finset.range n,
    Real.ofDigitsTerm (apm_a98a03_binaryDigit b) i
  let ta := Real.ofDigits (fun i ↦ apm_a98a03_binaryDigit a (i + (n + 1)))
  let tb := Real.ofDigits (fun i ↦ apm_a98a03_binaryDigit b (i + (n + 1)))
  change P + 0 + ((2 : ℝ) ^ (n + 1))⁻¹ * ta ≤
    P + ((2 : ℝ) ^ (n + 1))⁻¹ + ((2 : ℝ) ^ (n + 1))⁻¹ * tb
  have hta : ta ≤ 1 := Real.ofDigits_le_one _
  have htb : 0 ≤ tb := Real.ofDigits_nonneg _
  have hpow : 0 < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  nlinarith

lemma apm_a98a03_binary_ofDigits_mono_of_ternary
    (a b : ℕ → Bool)
    (h : Real.ofDigits (apm_a98a03_ternaryDigit a) ≤
      Real.ofDigits (apm_a98a03_ternaryDigit b)) :
    Real.ofDigits (apm_a98a03_binaryDigit a) ≤
      Real.ofDigits (apm_a98a03_binaryDigit b) := by
  by_cases hab : a = b
  · simp [hab]
  have hex : ∃ n, a n ≠ b n := Function.ne_iff.mp hab
  let n := Nat.find hex
  have hn : a n ≠ b n := Nat.find_spec hex
  have hp : ∀ i < n, a i = b i := fun i hi ↦ by
    by_contra hne
    exact (Nat.find_min hex hi) hne
  cases ha : a n <;> cases hb : b n
  · exact (hn (by simp [ha, hb])).elim
  · exact apm_a98a03_binary_le_of_first_false_true a b n hp ha hb
  · have hbad := apm_a98a03_ternary_lt_of_first_false_true b a n
      (fun i hi ↦ (hp i hi).symm) hb ha
    exact (not_lt_of_ge h hbad).elim
  · exact (hn (by simp [ha, hb])).elim

lemma apm_a98a03_ofDigits_ternaryDigit_cantor (x : cantorSet) :
    Real.ofDigits (apm_a98a03_ternaryDigit (cantorToBinary (x : ℝ)).get) = x := by
  have hdigit : apm_a98a03_ternaryDigit (cantorToBinary (x : ℝ)).get =
      (cantorToTernary (x : ℝ)).get := by
    funext i
    simp only [apm_a98a03_ternaryDigit, cantorToTernary, Stream'.get_map,
      Bool.cond_eq_ite]
  rw [hdigit, ofDigits_cantorToTernary x.property]

lemma apm_a98a03_cantorCore_monotone :
    Monotone apm_a98a03_cantorCore := by
  intro x y hxy
  rw [apm_a98a03_cantorCore_eq_ofDigits, apm_a98a03_cantorCore_eq_ofDigits]
  apply apm_a98a03_binary_ofDigits_mono_of_ternary
  rw [apm_a98a03_ofDigits_ternaryDigit_cantor,
    apm_a98a03_ofDigits_ternaryDigit_cantor]
  exact hxy

lemma apm_a98a03_cantorCore_continuous :
    Continuous apm_a98a03_cantorCore := by
  exact continuous_subtype_val.comp
    (Real.fromBinary_continuous.comp cantorSetHomeomorphNatToBool.continuous)

/-- The Cantor core already attains every value in `[0,1]`; extending it
constantly across complementary gaps will therefore retain endpoint change. -/
lemma apm_a98a03_cantorCore_surjOn :
    Set.SurjOn apm_a98a03_cantorCore Set.univ (Icc (0 : ℝ) 1) := by
  intro y hy
  let yu : unitInterval := ⟨y, hy⟩
  obtain ⟨b, hb⟩ := Real.fromBinary_surjective yu
  obtain ⟨x, hx⟩ := cantorSetHomeomorphNatToBool.surjective b
  refine ⟨x, Set.mem_univ x, ?_⟩
  simp only [apm_a98a03_cantorCore, hx, hb, yu]

/-- Left-envelope extension of the Cantor core.  Once order compatibility of
the canonical digit maps is supplied, this is the devil's staircase itself. -/
def apm_a98a03_cantorExtension (x : ℝ) : ℝ :=
  sSup (apm_a98a03_cantorCore '' {z : cantorSet | (z : ℝ) ≤ x})

lemma apm_a98a03_cantorCore_le_one (z : cantorSet) :
    apm_a98a03_cantorCore z ≤ 1 := by
  exact (Real.fromBinary (cantorSetHomeomorphNatToBool z)).property.2

lemma apm_a98a03_cantorCore_nonneg (z : cantorSet) :
    0 ≤ apm_a98a03_cantorCore z := by
  exact (Real.fromBinary (cantorSetHomeomorphNatToBool z)).property.1

lemma apm_a98a03_cantorCore_zero :
    apm_a98a03_cantorCore ⟨0, zero_mem_cantorSet⟩ = 0 := by
  have hz (n : ℕ) : (Stream'.iterate cantorStep 0).get n = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Stream'.get_succ_iterate', ih]
        simp [cantorStep]
  have hb : cantorSetHomeomorphNatToBool ⟨0, zero_mem_cantorSet⟩ =
      (fun _ ↦ false) := by
    change cantorSetEquivNatToBool ⟨0, zero_mem_cantorSet⟩ = (fun _ ↦ false)
    ext n
    simp [cantorSetEquivNatToBool, cantorToBinary, cantorSequence,
      Stream'.get_map, hz n]
  rw [apm_a98a03_cantorCore, hb]
  simp [Real.fromBinary, Real.ofDigits, Real.ofDigitsTerm]

lemma apm_a98a03_cantorExtension_monotone :
    Monotone apm_a98a03_cantorExtension := by
  intro x y hxy
  simp only [apm_a98a03_cantorExtension]
  let sx := apm_a98a03_cantorCore '' {z : cantorSet | (z : ℝ) ≤ x}
  let sy := apm_a98a03_cantorCore '' {z : cantorSet | (z : ℝ) ≤ y}
  change sSup sx ≤ sSup sy
  have hsub : sx ⊆ sy := image_mono fun z hz ↦ hz.trans hxy
  have hby : BddAbove sy := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact apm_a98a03_cantorCore_le_one z
  by_cases hsx : sx.Nonempty
  · exact csSup_le_csSup hby hsx hsub
  · rw [not_nonempty_iff_eq_empty] at hsx
    rw [hsx, Real.sSup_empty]
    by_cases hsy : sy.Nonempty
    · obtain ⟨v, hv⟩ := hsy
      obtain ⟨z, hz, rfl⟩ := hv
      exact (apm_a98a03_cantorCore_nonneg z).trans
        (le_csSup hby ⟨z, hz, rfl⟩)
    · rw [not_nonempty_iff_eq_empty] at hsy
      simp [hsy]

lemma apm_a98a03_cantorExtension_le_one (x : ℝ) :
    apm_a98a03_cantorExtension x ≤ 1 := by
  by_cases hne :
      (apm_a98a03_cantorCore '' {z : cantorSet | (z : ℝ) ≤ x}).Nonempty
  · apply csSup_le hne
    rintro _ ⟨z, _, rfl⟩
    exact apm_a98a03_cantorCore_le_one z
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [apm_a98a03_cantorExtension, hne]

lemma apm_a98a03_cantorExtension_eq_core (x : cantorSet) :
    apm_a98a03_cantorExtension x = apm_a98a03_cantorCore x := by
  have hne : (apm_a98a03_cantorCore ''
      {z : cantorSet | (z : ℝ) ≤ (x : ℝ)}).Nonempty :=
    ⟨apm_a98a03_cantorCore x,
      ⟨x, (show (x : ℝ) ≤ (x : ℝ) from le_rfl), rfl⟩⟩
  have hbound : BddAbove (apm_a98a03_cantorCore ''
      {z : cantorSet | (z : ℝ) ≤ (x : ℝ)}) := by
    refine ⟨apm_a98a03_cantorCore x, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact apm_a98a03_cantorCore_monotone hz
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨z, hz, rfl⟩
    exact apm_a98a03_cantorCore_monotone hz
  · apply le_csSup hbound
    exact ⟨x, (show (x : ℝ) ≤ (x : ℝ) from le_rfl), rfl⟩

lemma apm_a98a03_cantorExtension_one :
    apm_a98a03_cantorExtension 1 = 1 := by
  apply le_antisymm (apm_a98a03_cantorExtension_le_one 1)
  obtain ⟨z, _, hz⟩ :=
    apm_a98a03_cantorCore_surjOn (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hbound : BddAbove
      (apm_a98a03_cantorCore '' {w : cantorSet | (w : ℝ) ≤ (1 : ℝ)}) := by
    exact ⟨1, by rintro _ ⟨w, _, rfl⟩; exact apm_a98a03_cantorCore_le_one w⟩
  calc
    (1 : ℝ) = apm_a98a03_cantorCore z := hz.symm
    _ ≤ apm_a98a03_cantorExtension 1 := by
      apply le_csSup hbound
      exact ⟨z, (cantorSet_subset_unitInterval z.property).2, rfl⟩

lemma apm_a98a03_cantorExtension_zero :
    apm_a98a03_cantorExtension 0 = 0 := by
  have hset : apm_a98a03_cantorCore ''
      {z : cantorSet | (z : ℝ) ≤ (0 : ℝ)} = {(0 : ℝ)} := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz0 : (z : ℝ) = 0 := le_antisymm hz
        (cantorSet_subset_unitInterval z.property).1
      have hzsub : z = ⟨0, zero_mem_cantorSet⟩ := Subtype.ext hz0
      rw [hzsub, apm_a98a03_cantorCore_zero]
      simp
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      subst v
      exact ⟨⟨0, zero_mem_cantorSet⟩, by simp, apm_a98a03_cantorCore_zero⟩
  simp [apm_a98a03_cantorExtension, hset]

/-- Off the closed Cantor set, a small interval contains no new Cantor points,
so the left-envelope defining the extension is locally constant. -/
lemma apm_a98a03_cantorExtension_eventuallyEq (x : ℝ) (hx : x ∉ cantorSet) :
    apm_a98a03_cantorExtension =ᶠ[𝓝 x]
      (fun _ ↦ apm_a98a03_cantorExtension x) := by
  have hnh : cantorSetᶜ ∈ 𝓝 x := isClosed_cantorSet.isOpen_compl.mem_nhds hx
  rw [Metric.mem_nhds_iff] at hnh
  obtain ⟨ε, hε, hball⟩ := hnh
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  apply congrArg sSup
  apply congrArg (apm_a98a03_cantorCore '' ·)
  ext z
  simp only [mem_setOf_eq]
  constructor
  · intro hzy
    by_contra hzx
    have hxz : x < (z : ℝ) := lt_of_not_ge hzx
    have hdist : dist (z : ℝ) x ≤ dist y x := by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxz.le),
        abs_of_nonneg (sub_nonneg.mpr (hxz.le.trans hzy))]
      linarith
    exact (hball (hdist.trans_lt hy)) z.property
  · intro hzx
    by_contra hzy
    have hyz : y < (z : ℝ) := lt_of_not_ge hzy
    have hdist : dist (z : ℝ) x ≤ dist y x := by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hzx),
        abs_of_nonpos (sub_nonpos.mpr (hyz.le.trans hzx))]
      linarith
    exact (hball (hdist.trans_lt hy)) z.property

lemma apm_a98a03_cantorExtension_hasDerivAt_zero
    (x : ℝ) (hx : x ∉ cantorSet) :
    HasDerivAt apm_a98a03_cantorExtension 0 x := by
  exact hasDerivAt_const (x := x) (c := apm_a98a03_cantorExtension x) |>.congr_of_eventuallyEq
    (apm_a98a03_cantorExtension_eventuallyEq x hx)

lemma apm_a98a03_cantorSet_measure_zero : volume cantorSet = 0 := by
  have hscale : volume ((fun x : ℝ => x / 3) '' cantorSet) =
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    rw [show (fun x : ℝ => x / 3) = fun x => (3 : ℝ)⁻¹ * x by funext x; ring,
      show (fun x : ℝ => 3⁻¹ * x) '' cantorSet =
          (fun x : ℝ => 3 * x) ⁻¹' cantorSet by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨3 * x, hx, by ring⟩,
      Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have htranslate : volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) =
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    have himage : (fun x : ℝ => (2 + x) / 3) '' cantorSet =
        (fun x : ℝ => 2 / 3 + x) '' ((fun x : ℝ => x / 3) '' cantorSet) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y / 3, ⟨y, hy, rfl⟩, by ring⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by ring⟩
    rw [himage, image_add_left, measure_preimage_add, hscale]
  have hle : volume cantorSet ≤ ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    calc
      volume cantorSet = volume ((fun x : ℝ => x / 3) '' cantorSet ∪
          (fun x : ℝ => (2 + x) / 3) '' cantorSet) :=
        congrArg volume cantorSet_eq_union_halves
      _ ≤ volume ((fun x : ℝ => x / 3) '' cantorSet) +
          volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) := measure_union_le _ _
      _ = _ := by rw [hscale, htranslate]
  have hfin : volume cantorSet ≠ ⊤ :=
    ne_of_lt ((measure_mono cantorSet_subset_unitInterval).trans_lt (by simp))
  have hzreal : (volume cantorSet).toReal = 0 := by
    have hmul : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have hrhs : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hmul, hmul⟩
    have hreal := ENNReal.toReal_mono hrhs hle
    rw [ENNReal.toReal_add hmul hmul] at hreal
    simp only [ENNReal.toReal_mul] at hreal
    norm_num at hreal
    exact le_antisymm (by linarith [ENNReal.toReal_nonneg (a := volume cantorSet)])
      ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with hzero | htop
  · exact hzero
  · exact (hfin htop).elim

lemma apm_a98a03_cantorExtension_ae_hasDerivAt_zero :
    ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      HasDerivAt apm_a98a03_cantorExtension 0 x := by
  apply ae_restrict_of_ae
  filter_upwards [(ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using
      apm_a98a03_cantorSet_measure_zero) :
    ∀ᵐ x ∂volume, x ∉ cantorSet)] with x hx
  exact apm_a98a03_cantorExtension_hasDerivAt_zero x hx

lemma apm_a98a03_cantorExtension_continuousOn :
    ContinuousOn apm_a98a03_cantorExtension (Icc (0 : ℝ) 1) := by
  let F : {x : ℝ // x ∈ Icc (0 : ℝ) 1} → {y : ℝ // y ∈ Icc (0 : ℝ) 1} :=
    fun x ↦ ⟨apm_a98a03_cantorExtension x,
      ⟨by
        calc
          (0 : ℝ) = apm_a98a03_cantorExtension 0 :=
            apm_a98a03_cantorExtension_zero.symm
          _ ≤ apm_a98a03_cantorExtension x :=
            apm_a98a03_cantorExtension_monotone x.property.1,
       apm_a98a03_cantorExtension_le_one x⟩⟩
  have hmono : Monotone F := by
    intro x y hxy
    exact apm_a98a03_cantorExtension_monotone hxy
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨z, _, hz⟩ := apm_a98a03_cantorCore_surjOn y.property
    let x : {x : ℝ // x ∈ Icc (0 : ℝ) 1} :=
      ⟨z, cantorSet_subset_unitInterval z.property⟩
    refine ⟨x, Subtype.ext ?_⟩
    change apm_a98a03_cantorExtension (z : ℝ) = (y : ℝ)
    rw [apm_a98a03_cantorExtension_eq_core, hz]
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun x : {x : ℝ // x ∈ Icc (0 : ℝ) 1} ↦
    (F x : ℝ))
  exact (hmono.continuous_of_surjective hsurj).subtype_val

lemma apm_a98a03_counterexample_of_continuous
    (hcont : ContinuousOn apm_a98a03_cantorExtension (Icc (0 : ℝ) 1)) :
    ∃ (f f' : ℝ → ℝ),
      ContinuousOn f (Icc 0 1) ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt f (f' x) x) ∧
      (∃ C : ℝ, ∀ᵐ x ∂volume.restrict (Icc 0 1), f' x ≤ C) ∧
      f 1 - f 0 ≠ ∫ x in Icc (0 : ℝ) 1, f' x ∂volume := by
  refine ⟨apm_a98a03_cantorExtension, fun _ ↦ 0, hcont,
    apm_a98a03_cantorExtension_ae_hasDerivAt_zero, ⟨0, ?_⟩, ?_⟩
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl
  · rw [apm_a98a03_cantorExtension_one, apm_a98a03_cantorExtension_zero]
    simp

theorem apm_a98a03 :
    (∃ (f f' : ℝ → ℝ),
      ContinuousOn f (Icc 0 1) ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt f (f' x) x) ∧
      (∃ C : ℝ, ∀ᵐ x ∂volume.restrict (Icc 0 1), f' x ≤ C) ∧
      f 1 - f 0 ≠ ∫ x in Icc (0 : ℝ) 1, f' x ∂volume) ∧
    (∀ (f f' : ℝ → ℝ) (I : ℝ),
      ContinuousOn f (Icc 0 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x) →
      HasRiemannIntegralOnUnitInterval f' I →
      f 1 - f 0 = I) := by
  /-
  CLOSER HOP 4: the strengthened FTC half is now closed by the compiled lemma
  `apm_a98a03_riemann_ftc`.  It chooses a fine uniform partition, obtains a
  dependent family of MVT tags cell-by-cell, applies the defining tagged-sum
  estimate, and rewrites the sum using `apm_a98a03_sum_adjacent_sub`.

  The counterexample half remains the hard boundary.  Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/` (including `LusinN` and
  `BanachZarecki`), Mathlib's real/cardinality, singular-function, measure, and
  bounded-variation sources, prior Riemann-integral artifacts `a95A01` and
  `a94A02`, and git history found no devil's staircase or equivalent continuous
  singular function with derivative zero almost everywhere.  Mathlib's
  `Cardinal.cantorFunction` parametrizes binary sequences and is not the Cantor
  staircase on `[0,1]`.  `ConstructionTargets.LusinN` proves FTC and null-set
  preservation for already absolutely continuous functions, so it cannot
  produce the required non-AC witness.

  Hop 5 constructs the continuous Cantor core on the closed ternary set by
  composing Mathlib's canonical Cantor/Boolean homeomorphism with its binary
  value map.  The compiled surjectivity lemma is its non-vacuity witness.  The
  Hop 8 closes continuity. First-difference estimates show that ternary digit
  order implies binary value order, so the Cantor core is monotone. The
  supremum extension therefore agrees with the core on `cantorSet`; restricted
  to `[0,1]` it is a monotone surjection, hence continuous. Together with the
  local constancy/nullity argument and the independent Riemann FTC proof, this
  closes both conjuncts.

  Going beyond the prior named searches, I inspected Mathlib's measure
  decomposition and `AbsolutelyContinuousFun` developments for a distribution
  function of a singular measure. They provide Radon--Nikodym/Lebesgue
  decomposition and prove rigidity for already absolutely continuous
  functions, but do not construct a nonzero atomless singular measure or its
  continuous cumulative distribution. The real-cardinality digit series also
  lacks an inverse/extension from the ternary Cantor set. Consequently the
  Cantor-staircase construction remains the independent open boundary; the
  statement is unchanged.
  -/
  exact ⟨apm_a98a03_counterexample_of_continuous
    apm_a98a03_cantorExtension_continuousOn, apm_a98a03_riemann_ftc⟩

#print axioms apm_a98a03
