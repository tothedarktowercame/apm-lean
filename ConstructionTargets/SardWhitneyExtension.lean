import ConstructionTargets.SardConvexDomain
import ConstructionTargets.SardHighOrderSard

open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace ConstructionTargets.SardWhitneyExtension

/-! We work coordinate-free in a finite-dimensional real inner-product source `E` and a
finite-dimensional real normed target `F`.  Local finiteness below is deliberately relative
to `Kᶜ`: `SardConvexDomain.not_locallyFinite_whitneyNetQuarterBalls_of_frontier_nonempty`
shows that ambient local finiteness at the frontier is false. -/

/-- The canonical order-`k` within jet used in the finite-order construction. -/
def convexJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : E → F) (K : Set E) (x : E) : E[×k]→L[ℝ] F :=
  iteratedFDerivWithin ℝ k f K x

/-- The degree-`m` Taylor polynomial with prescribed multilinear jet `J` at `a`. -/
def taylorPolynomial
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (k : ℕ) → E → E[×k]→L[ℝ] F) (a x : E) : F :=
  ∑ k ∈ Finset.range (m + 1), ((k.factorial : ℝ)⁻¹) • J k a (fun _ ↦ x - a)

/-- Finite differentiability on a convex set with interior gives continuous symmetric
canonical within jets through the requested order.  Prove this by the finite-order versions
of the iterated-derivative continuity and Schwarz lemmas used by `ContDiffOn.convexWithinJet`. -/
theorem convexWithinJet_nat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    (∀ k ≤ m + 1, ContinuousOn (convexJet k f K) K) ∧
      (∀ x ∈ K, convexJet 0 f K x (fun i ↦ Fin.elim0 i) = f x) ∧
      (∀ x ∈ K, ∀ v, convexJet 1 f K x (fun _ ↦ v) = fderivWithin ℝ f K x v) ∧
      ∀ k ≤ m + 1, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin k),
        (convexJet k f K x).domDomCongr σ = convexJet k f K x := by
  have hu : UniqueDiffOn ℝ K := uniqueDiffOn_convex hK hKi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) hu
  · intro x hx
    exact iteratedFDerivWithin_zero_apply _
  · intro x hx v
    exact iteratedFDerivWithin_one_apply (hu x hx) _
  · intro k hk x hx σ
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F ≃ₗᵢ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F :=
      ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F σ
    have hle : (k : WithTop ENat) ≤ (m + 1 : ℕ) := by exact_mod_cast hk
    have hc := (hf x hx).continuousWithinAt_iteratedFDerivWithin hu hle hx
    apply ContinuousWithinAt.eq_of_eqOn_interior_of_mem_closure
      (by
        rw [hK.closure_interior_eq_closure_of_nonempty_interior hKi]
        exact subset_closure hx)
      (L.continuous.continuousAt.comp_continuousWithinAt hc) hc
    intro y hy
    exact ((hf y (interior_subset hy)).of_le hle).domDomCongr_iteratedFDerivWithin_of_nat_of_mem_interior
      hu k hy σ

/-- Exact derivative formula for the Taylor polynomial.  Evaluate on `v`, differentiate
the diagonal monomials, use symmetry to identify all injections of the `k` derivative
variables, and cancel `j!/(j-k)!` against `j!`; the surviving factor is `(j-k)!⁻¹`. -/
-- Transport a multilinear-map evaluation across an index-type equality cast.
theorem iteratedFDeriv_taylorPolynomial_exact_aux_cast
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : (n : ℕ) → E[×n]→L[ℝ] F) {p r : ℕ} (h : p = r) (v : Fin r → E) :
    M p (fun i ↦ v (Fin.cast h i)) = M r v := by
  subst h
  rfl

-- `Fin.append` is `Sum.elim` transported along `finSumFinEquiv`.
theorem iteratedFDeriv_taylorPolynomial_exact_aux_append
    {E : Type*} {k q : ℕ} (u : Fin k → E) (z : Fin q → E) :
    (fun i ↦ Sum.elim u z (finSumFinEquiv.symm i)) = Fin.append u z := by
  funext i
  refine Fin.addCases (motive := fun i ↦
      Sum.elim u z (finSumFinEquiv.symm i) = Fin.append u z i)
    (fun i₀ ↦ ?_) (fun j₀ ↦ ?_) i
  · simp [finSumFinEquiv_symm_apply_castAdd]
  · simp [finSumFinEquiv_symm_apply_natAdd]

-- Evaluation of a continuous multilinear map at a tuple, as a continuous multilinear map
-- of the tuple (valued in continuous linear maps on multilinear maps).
noncomputable def iteratedFDeriv_taylorPolynomial_exact_auxEval
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q ↦ E) ((E[×q]→L[ℝ] F) →L[ℝ] F) :=
  by
  refine MultilinearMap.mkContinuous (𝕜 := ℝ) (ι := Fin q) (E := fun _ : Fin q ↦ E)
    (G := (E[×q]→L[ℝ] F) →L[ℝ] F) ?_ 1 ?_
  · exact
    { toFun := fun z ↦ ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F z
      map_update_add' := fun z i x y ↦ by
        ext M
        simp [ContinuousMultilinearMap.map_update_add]
      map_update_smul' := fun z i r y ↦ by
        ext M
        simp [ContinuousMultilinearMap.map_update_smul, ContinuousLinearMap.smul_apply] }
  · intro z
    show ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F z‖ ≤ 1 * ∏ i, ‖z i‖
    rw [one_mul]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F z).opNorm_le_bound
      (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
      (fun M ↦ by
        rw [mul_comm]
        exact M.le_opNorm z)

theorem iteratedFDeriv_taylorPolynomial_exact_auxEval_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (z : Fin q → E) (M : E[×q]→L[ℝ] F) :
    iteratedFDeriv_taylorPolynomial_exact_auxEval E F q z M = M z := rfl

theorem iteratedFDeriv_taylorPolynomial_exact_auxEval_eq_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (z : Fin q → E) :
    iteratedFDeriv_taylorPolynomial_exact_auxEval E F q z =
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F z := rfl

-- Currying off the last `q` variables of a `k + q`-linear map.
noncomputable def iteratedFDeriv_taylorPolynomial_exact_auxCurried
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (M : E[×(k+q)]→L[ℝ] F) :
    E[×k]→L[ℝ] (E[×q]→L[ℝ] F) :=
  ContinuousMultilinearMap.currySum (M.domDomCongr finSumFinEquiv.symm)

theorem iteratedFDeriv_taylorPolynomial_exact_auxCurried_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (M : E[×(k+q)]→L[ℝ] F) (u : Fin k → E) (z : Fin q → E) :
    iteratedFDeriv_taylorPolynomial_exact_auxCurried M u z = M (Fin.append u z) := by
  rw [iteratedFDeriv_taylorPolynomial_exact_auxCurried,
    ContinuousMultilinearMap.currySum_apply, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  exact iteratedFDeriv_taylorPolynomial_exact_aux_append u z

/-- Symmetry step: a `w` inserted at position `k + j` of `(u, c^(q+1))` can be moved to the
front, giving `(w, u, c^q)`, by symmetry of the multilinear map. -/
theorem iteratedFDeriv_taylorPolynomial_exact_aux_symm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (M : E[×(k + (q + 1))]→L[ℝ] F)
    (hM : ∀ σ : Equiv.Perm (Fin (k + (q + 1))), M.domDomCongr σ = M)
    (u : Fin k → E) (w c : E) (j : Fin (q + 1)) :
    M (Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c)) (Fin.natAdd k j) w) =
      M (fun i ↦ Fin.append (Fin.cons w u) (fun _ : Fin q ↦ c)
        (Fin.cast (by omega : k + (q + 1) = k + 1 + q) i)) := by
  classical
  set S := Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c)) (Fin.natAdd k j) w with hS
  have hb : ∀ t : ℕ, t < k + (q + 1) →
      (if t = 0 then k + j.val else if t ≤ k + j.val then t - 1 else t) < k + (q + 1) := by
    intro t ht
    have hj := j.isLt
    split_ifs with h0 hle <;> omega
  let σf : Fin (k + (q + 1)) → Fin (k + (q + 1)) := fun i ↦
    ⟨if i.val = 0 then k + j.val else if i.val ≤ k + j.val then i.val - 1 else i.val,
     hb _ i.isLt⟩
  have hinj : Function.Injective σf := by
    intro i₁ i₂ h
    have h₁ := i₁.isLt
    have h₂ := i₂.isLt
    have hj := j.isLt
    apply Fin.ext
    have hh := congrArg Fin.val h
    replace hh :
        (if i₁.val = 0 then k + j.val else if i₁.val ≤ k + j.val then i₁.val - 1 else i₁.val)
        = (if i₂.val = 0 then k + j.val
           else if i₂.val ≤ k + j.val then i₂.val - 1 else i₂.val) := hh
    split_ifs at hh <;> omega
  have hsurj : Function.Surjective σf := (Finite.injective_iff_surjective).mp hinj
  let σ : Equiv.Perm (Fin (k + (q + 1))) := Equiv.ofBijective σf ⟨hinj, hsurj⟩
  have hσ : ∀ i : Fin (k + (q + 1)), σ i = σf i := fun _ ↦ rfl
  have hvec : S ∘ σ = fun i ↦ Fin.append (Fin.cons w u) (fun _ : Fin q ↦ c)
      (Fin.cast (by omega : k + (q + 1) = k + 1 + q) i) := by
    funext i
    rcases i with ⟨t, ht⟩
    have hj := j.isLt
    show S (σ ⟨t, ht⟩) = _
    rw [hσ]
    have huj : ∀ p, (⟨k + j.val, p⟩ : Fin (k + (q + 1))) = Fin.natAdd k j :=
      fun _ ↦ Fin.ext rfl
    by_cases h0 : t = 0
    · subst h0
      have hrc : ∀ (h : k + (q + 1) = k + 1 + q),
          Fin.cast h ⟨0, ht⟩ = Fin.castAdd q (0 : Fin (k + 1)) := fun _ ↦ Fin.ext rfl
      rw [hrc, Fin.append_left, Fin.cons_zero]
      have hσv : ∀ p, σf ⟨0, p⟩ = ⟨k + j.val, by have := j.isLt; omega⟩ := fun p ↦
        Fin.ext (show (if (0 : ℕ) = 0 then k + j.val
            else if 0 ≤ k + j.val then 0 - 1 else 0) = k + j.val by rw [if_pos rfl])
      rw [hσv, hS, huj, Function.update_self]
    · by_cases hle : t ≤ k + j.val
      · have hσv : ∀ p, σf ⟨t, p⟩ = ⟨t - 1, by omega⟩ := fun p ↦
          Fin.ext (show (if t = 0 then k + j.val else if t ≤ k + j.val then t - 1 else t)
            = t - 1 by rw [if_neg h0, if_pos hle])
        by_cases htk : t - 1 < k
        · have htk1 : t < k + 1 := by omega
          have hrc : ∀ (h : k + (q + 1) = k + 1 + q),
              Fin.cast h ⟨t, ht⟩ = Fin.castAdd q ⟨t, htk1⟩ := fun _ ↦ Fin.ext rfl
          have hts : ∀ (p : t < k + 1), (⟨t, p⟩ : Fin (k + 1)) = (⟨t - 1, htk⟩ : Fin k).succ :=
            fun _ ↦ Fin.ext (show t = t - 1 + 1 by omega)
          rw [hrc, Fin.append_left, hts, Fin.cons_succ]
          have hne : ∀ p, (⟨t - 1, p⟩ : Fin (k + (q + 1))) ≠ Fin.natAdd k j := fun p hh ↦ by
            have h2 := congrArg Fin.val hh
            change t - 1 = k + j.val at h2
            omega
          have hca : ∀ p, (⟨t - 1, p⟩ : Fin (k + (q + 1))) = Fin.castAdd (q + 1) ⟨t - 1, htk⟩ :=
            fun _ ↦ Fin.ext rfl
          rw [hσv, hS, Function.update_of_ne (hne _), hca, Fin.append_left]
        · have htk1 : k + 1 ≤ t := by omega
          have hrc : ∀ (h : k + (q + 1) = k + 1 + q),
              Fin.cast h ⟨t, ht⟩ = Fin.natAdd (k + 1) ⟨t - (k + 1), by omega⟩ :=
            fun _ ↦ Fin.ext (show t = (k + 1) + (t - (k + 1)) by omega)
          rw [hrc, Fin.append_right]
          have hne : ∀ p, (⟨t - 1, p⟩ : Fin (k + (q + 1))) ≠ Fin.natAdd k j := fun p hh ↦ by
            have h2 := congrArg Fin.val hh
            change t - 1 = k + j.val at h2
            omega
          have hna : ∀ p, (⟨t - 1, p⟩ : Fin (k + (q + 1))) =
              Fin.natAdd k ⟨t - 1 - k, by omega⟩ :=
            fun _ ↦ Fin.ext (show t - 1 = k + (t - 1 - k) by omega)
          rw [hσv, hS, Function.update_of_ne (hne _), hna, Fin.append_right]
      · have htk1 : k + 1 ≤ t := by omega
        have hrc : ∀ (h : k + (q + 1) = k + 1 + q),
            Fin.cast h ⟨t, ht⟩ = Fin.natAdd (k + 1) ⟨t - (k + 1), by omega⟩ :=
          fun _ ↦ Fin.ext (show t = (k + 1) + (t - (k + 1)) by omega)
        rw [hrc, Fin.append_right]
        have hσv : ∀ p, σf ⟨t, p⟩ = ⟨t, p⟩ := fun p ↦
          Fin.ext (show (if t = 0 then k + j.val else if t ≤ k + j.val then t - 1 else t)
            = t by rw [if_neg h0, if_neg hle])
        have hne : ∀ p, (⟨t, p⟩ : Fin (k + (q + 1))) ≠ Fin.natAdd k j := fun p hh ↦ by
          have h2 := congrArg Fin.val hh
          change t = k + j.val at h2
          omega
        have hna : ∀ p, (⟨t, p⟩ : Fin (k + (q + 1))) = Fin.natAdd k ⟨t - k, by omega⟩ :=
          fun _ ↦ Fin.ext (show t = k + (t - k) by omega)
        rw [hσv, hS, Function.update_of_ne (hne _), hna, Fin.append_right]
  rw [← hvec]
  have h2 : M (S ∘ σ) = M S := by
    conv_rhs => rw [← hM σ]
    rfl
  rw [h2]

/-- Inner sum over all `Fin (k + (q+1))` positions in the derivative of a diagonal
monomial: the first `k` positions contribute `0` (constant coordinates), and the last
`q + 1` positions all give the same value by symmetry. -/
theorem iteratedFDeriv_taylorPolynomial_exact_aux_inner
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (M : E[×(k + (q + 1))]→L[ℝ] F)
    (hM : ∀ σ : Equiv.Perm (Fin (k + (q + 1))), M.domDomCongr σ = M)
    (u : Fin k → E) (w c : E) :
    ∑ i : Fin (k + (q + 1)), M (Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c)) i
        (if (i : ℕ) < k then 0 else w)) =
      (q + 1) • M (fun i ↦ Fin.append (Fin.cons w u) (fun _ : Fin q ↦ c)
        (Fin.cast (by omega : k + (q + 1) = k + 1 + q) i)) := by
  rw [Fin.sum_univ_add (fun i ↦ M (Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c)) i
      (if (i : ℕ) < k then 0 else w)))]
  have hzero : ∑ i₀ : Fin k, M (Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c))
      (Fin.castAdd (q + 1) i₀)
      (if ((Fin.castAdd (q + 1) i₀ : Fin (k + (q + 1))) : ℕ) < k then 0 else w)) = 0 := by
    apply Finset.sum_eq_zero
    intro i₀ _
    have hc : ((Fin.castAdd (q + 1) i₀ : Fin (k + (q + 1))) : ℕ) < k := i₀.isLt
    rw [if_pos hc]
    exact M.map_update_zero _ _
  rw [hzero, zero_add]
  have hall : ∀ j : Fin (q + 1), M (Function.update (Fin.append u (fun _ : Fin (q + 1) ↦ c))
      (Fin.natAdd k j)
      (if ((Fin.natAdd k j : Fin (k + (q + 1))) : ℕ) < k then 0 else w)) =
      M (fun i ↦ Fin.append (Fin.cons w u) (fun _ : Fin q ↦ c)
        (Fin.cast (by omega : k + (q + 1) = k + 1 + q) i)) := by
    intro j
    have hval : ((Fin.natAdd k j : Fin (k + (q + 1))) : ℕ) = k + j.val := rfl
    rw [if_neg (by rw [hval]; omega)]
    exact iteratedFDeriv_taylorPolynomial_exact_aux_symm M hM u w c j
  rw [Finset.sum_congr rfl (fun j _ ↦ hall j), Finset.sum_const, Finset.card_fin]

/-- Factorial cancellation: `((q+1)!)⁻¹ • ((q+1) • X) = (q!)⁻¹ • X`. -/
theorem iteratedFDeriv_taylorPolynomial_exact_aux_coeff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (X : F) :
    ((q + 1).factorial : ℝ)⁻¹ • ((q + 1 : ℕ) • X) = (q.factorial : ℝ)⁻¹ • X := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev,
    mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)), mul_one]

theorem iteratedFDeriv_taylorPolynomial_exact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m k : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a x : E)
    (hk : k ≤ m) (v : Fin k → E)
    (hJ : ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j),
      (J j a).domDomCongr σ = J j a) :
    iteratedFDeriv ℝ k (taylorPolynomial m J a) x v =
      ∑ q ∈ Finset.range (m + 1 - k), (q.factorial : ℝ)⁻¹ •
        J (k + q) a (Fin.append v (fun _ : Fin q ↦ x - a)) := by
  classical
  have hP : ContDiff ℝ ⊤ (taylorPolynomial m J a) := by
    show ContDiff ℝ ⊤ (fun x ↦ ∑ j ∈ Finset.range (m + 1),
      ((j.factorial : ℝ)⁻¹) • J j a (fun _ ↦ x - a))
    apply ContDiff.sum
    intro j _
    apply ContDiff.const_smul
    exact (ContinuousMultilinearMap.contDiff _).comp
      (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)
  induction k generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_apply, Nat.sub_zero]
    show (∑ j ∈ Finset.range (m + 1), ((j.factorial : ℝ)⁻¹) • J j a (fun _ ↦ x - a)) = _
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    have happ : Fin.append v (fun _ : Fin q ↦ x - a) =
        fun i ↦ (fun _ : Fin q ↦ x - a) (Fin.cast (zero_add q) i) := by
      funext i
      have hi : i = Fin.natAdd 0 (Fin.cast (zero_add q) i) :=
        Fin.ext (Nat.zero_add _).symm
      conv_lhs => rw [hi, Fin.append_right]
    rw [happ]
    exact (iteratedFDeriv_taylorPolynomial_exact_aux_cast (fun n ↦ J n a) (zero_add q)
      (fun _ : Fin q ↦ x - a)).symm
  | succ k ih =>
    have hkm : k ≤ m := by omega
    rw [iteratedFDeriv_succ_apply_left]
    have hGd : DifferentiableAt ℝ (iteratedFDeriv ℝ k (taylorPolynomial m J a)) x :=
      hP.contDiffAt.differentiableAt_iteratedFDeriv (by simp)
    have hstep1 : fderiv ℝ (iteratedFDeriv ℝ k (taylorPolynomial m J a)) x (v 0) (Fin.tail v)
        = fderiv ℝ (fun y ↦ ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
            (Fin.tail v) (iteratedFDeriv ℝ k (taylorPolynomial m J a) y)) x (v 0) := by
      show ((fderiv ℝ (iteratedFDeriv ℝ k (taylorPolynomial m J a)) x) (v 0)) (Fin.tail v)
          = (fderiv ℝ (⇑(ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v))
              ∘ iteratedFDeriv ℝ k (taylorPolynomial m J a)) x) (v 0)
      rw [(ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
          (Fin.tail v)).hasFDerivAt.comp x hGd.hasFDerivAt |>.fderiv]
      rfl
    rw [hstep1]
    have hfun : (fun y ↦ ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
          (Fin.tail v) (iteratedFDeriv ℝ k (taylorPolynomial m J a) y)) =
        fun y ↦ ∑ q ∈ Finset.range (m + 1 - k), (q.factorial : ℝ)⁻¹ •
          J (k + q) a (Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a)) := by
      funext y
      exact ih y hkm (Fin.tail v)
    rw [hfun]
    have hterm : ∀ q ∈ Finset.range (m + 1 - k),
        HasFDerivAt (fun y ↦ (q.factorial : ℝ)⁻¹ •
            J (k + q) a (Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a)))
          ((q.factorial : ℝ)⁻¹ •
            ∑ i : Fin (k + q), (J (k + q) a).toContinuousLinearMap
              (Fin.append (Fin.tail v) (fun _ : Fin q ↦ x - a)) i ∘L
              (if (i : ℕ) < k then (0 : E →L[ℝ] E) else ContinuousLinearMap.id ℝ E)) x := by
      intro q _
      refine (HasFDerivAt.multilinear_comp (J (k + q) a) ?_).const_smul _
      intro i
      by_cases hi : (i : ℕ) < k
      · rw [if_pos hi]
        have hgi : (fun y ↦ Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a) i) =
            fun _ ↦ Fin.tail v ⟨i, hi⟩ := by
          funext y
          have he : i = Fin.castAdd q ⟨i, hi⟩ := Fin.ext rfl
          conv_lhs => rw [he, Fin.append_left]
        rw [hgi]
        exact hasFDerivAt_const _ _
      · rw [if_neg hi]
        have hgi : (fun y ↦ Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a) i) =
            fun y ↦ y - a := by
          funext y
          have he : i = Fin.natAdd k ⟨i - k, by have := i.isLt; omega⟩ :=
            Fin.ext (by have := i.isLt; show (i : ℕ) = k + (i - k); omega)
          conv_lhs => rw [he, Fin.append_right]
        rw [hgi]
        exact (hasFDerivAt_id x).sub_const a
    rw [show (fun y ↦ ∑ q ∈ Finset.range (m + 1 - k), (q.factorial : ℝ)⁻¹ •
          J (k + q) a (Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a))) =
        (∑ q ∈ Finset.range (m + 1 - k), fun y ↦ (q.factorial : ℝ)⁻¹ •
          J (k + q) a (Fin.append (Fin.tail v) (fun _ : Fin q ↦ y - a))) from
      by funext y; rw [Finset.sum_apply]]
    rw [(HasFDerivAt.sum hterm).fderiv]
    have happ : ∀ q : ℕ, ((q.factorial : ℝ)⁻¹ •
          ∑ i : Fin (k + q), (J (k + q) a).toContinuousLinearMap
            (Fin.append (Fin.tail v) (fun _ : Fin q ↦ x - a)) i ∘L
            (if (i : ℕ) < k then (0 : E →L[ℝ] E) else ContinuousLinearMap.id ℝ E)) (v 0) =
        (q.factorial : ℝ)⁻¹ • ∑ i : Fin (k + q), J (k + q) a
          (Function.update (Fin.append (Fin.tail v) (fun _ : Fin q ↦ x - a)) i
            (if (i : ℕ) < k then 0 else v 0)) := by
      intro q
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : ℕ) < k
      · rw [if_pos hi, if_pos hi, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.zero_apply,
          ContinuousMultilinearMap.toContinuousLinearMap_apply]
      · rw [if_neg hi, if_neg hi, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply,
          ContinuousMultilinearMap.toContinuousLinearMap_apply]
    rw [ContinuousLinearMap.sum_apply]
    conv_lhs => arg 2; ext q; rw [happ q]
    have hr1 : m + 1 - k = (m - k) + 1 := by omega
    have hr2 : m + 1 - (k + 1) = m - k := by omega
    rw [hr1, Finset.sum_range_succ', hr2]
    have hInn0 : (∑ i : Fin (k + 0), J (k + 0) a (Function.update
        (Fin.append (Fin.tail v) (fun _ : Fin 0 ↦ x - a)) i
        (if (i : ℕ) < k then 0 else v 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : (i : ℕ) < k := by have := i.isLt; omega
      rw [if_pos hi]
      exact (J (k + 0) a).map_update_zero _ _
    rw [hInn0, smul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    rw [iteratedFDeriv_taylorPolynomial_exact_aux_inner (J (k + (q + 1)) a)
      (hJ _ (by omega)) (Fin.tail v) (v 0) (x - a),
      iteratedFDeriv_taylorPolynomial_exact_aux_coeff]
    congr 1
    refine (iteratedFDeriv_taylorPolynomial_exact_aux_cast (fun n ↦ J n a)
      (show k + (q + 1) = k + 1 + q by omega)
      (Fin.append (Fin.cons (v 0) (Fin.tail v)) (fun _ : Fin q ↦ x - a))).trans ?_
    exact congrArg (fun t ↦ J (k + 1 + q) a (Fin.append t (fun _ : Fin q ↦ x - a)))
      (Fin.cons_self_tail v)

/-- Norm consequence of the exact shifted-jet formula.  Apply the multilinear norm bound
to every summand of `iteratedFDeriv_taylorPolynomial_exact`; note in particular that the
coefficient is `(j-k)!⁻¹`, not `j!⁻¹`. -/
theorem iteratedFDeriv_taylorPolynomial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m k : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a x : E)
    (hk : k ≤ m)
    (hJ : ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j),
      (J j a).domDomCongr σ = J j a) :
    ‖iteratedFDeriv ℝ k (taylorPolynomial m J a) x‖ ≤
      ∑ j ∈ Finset.Icc k m,
        (((j - k).factorial : ℝ)⁻¹) * ‖J j a‖ * ‖x - a‖ ^ (j - k) := by
  classical
  let B := ∑ q ∈ Finset.range (m + 1 - k),
    ((q.factorial : ℝ)⁻¹) * ‖J (k + q) a‖ * ‖x - a‖ ^ q
  have hB : ‖iteratedFDeriv ℝ k (taylorPolynomial m J a) x‖ ≤ B := by
    apply ContinuousMultilinearMap.opNorm_le_bound
    · dsimp [B]
      apply Finset.sum_nonneg
      intro q hq
      positivity
    · intro v
      rw [iteratedFDeriv_taylorPolynomial_exact m k J a x hk v hJ]
      calc
        ‖∑ q ∈ Finset.range (m + 1 - k), (q.factorial : ℝ)⁻¹ •
            J (k + q) a (Fin.append v (fun _ : Fin q ↦ x - a))‖ ≤
            ∑ q ∈ Finset.range (m + 1 - k), ‖(q.factorial : ℝ)⁻¹ •
              J (k + q) a (Fin.append v (fun _ : Fin q ↦ x - a))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ q ∈ Finset.range (m + 1 - k),
              (((q.factorial : ℝ)⁻¹ * ‖J (k + q) a‖ * ‖x - a‖ ^ q) *
                ∏ i, ‖v i‖) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_smul]
          have hmap := (J (k + q) a).le_opNorm
            (Fin.append v (fun _ : Fin q ↦ x - a))
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ ((q.factorial : ℝ)⁻¹))]
          simpa [Fin.prod_univ_add, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hmap (by positivity : 0 ≤ ((q.factorial : ℝ)⁻¹))
        _ = B * ∏ i, ‖v i‖ := by
          dsimp [B]
          rw [Finset.sum_mul]
  refine hB.trans_eq ?_
  dsimp [B]
  apply Finset.sum_bij (fun q _ ↦ k + q)
  · intro q hq
    simp only [Finset.mem_range] at hq
    simp only [Finset.mem_Icc]
    omega
  · intro q₁ hq₁ q₂ hq₂ heq
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro q hq
    simp

/-- On a compact convex set, continuity of the top within derivative gives one uniform
Taylor constant for every lower jet.  Apply the Banach-valued segment integral remainder
on `K`, bound the top jet on the compact set, and absorb factorial constants into `C`. -/
-- Bundled linear map "evaluate the last `q` arguments at the fixed tuple `c`".
noncomputable def compactConvex_taylor_remainder_bound_auxPhi
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (c : Fin q → E) :
    (E[×(k+q)]→L[ℝ] F) →L[ℝ] (E[×k]→L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := fun M ↦ (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c
          ).compContinuousMultilinearMap
          (ContinuousMultilinearMap.currySum (M.domDomCongr finSumFinEquiv.symm))
      map_add' := fun M₁ M₂ ↦ by
        ext u
        show (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
            (((M₁ + M₂).domDomCongr finSumFinEquiv.symm).currySum u) =
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
            ((M₁.domDomCongr finSumFinEquiv.symm).currySum u) +
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
            ((M₂.domDomCongr finSumFinEquiv.symm).currySum u)
        rw [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
          ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.add_apply,
          ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
          ContinuousMultilinearMap.domDomCongr_apply,
          ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
          ContinuousMultilinearMap.domDomCongr_apply]
      map_smul' := fun r M ↦ by
        ext u
        show (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
            (((r • M).domDomCongr finSumFinEquiv.symm).currySum u) =
          r • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
            ((M.domDomCongr finSumFinEquiv.symm).currySum u))
        rw [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
          ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply,
          ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
          ContinuousMultilinearMap.domDomCongr_apply] }
    ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c‖
    (fun M ↦ by
      show ‖(ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c
          ).compContinuousMultilinearMap
          (ContinuousMultilinearMap.currySum (M.domDomCongr finSumFinEquiv.symm))‖ ≤
        ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c‖ * ‖M‖
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      gcongr
      have h1 : ContinuousMultilinearMap.currySum (M.domDomCongr finSumFinEquiv.symm) =
          ContinuousMultilinearMap.currySumEquiv ℝ (Fin k) (Fin q) E F
            (M.domDomCongr finSumFinEquiv.symm) := rfl
      rw [h1, LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_domDomCongr])


theorem compactConvex_taylor_remainder_bound_auxPhi_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (c : Fin q → E) (M : E[×(k+q)]→L[ℝ] F) (u : Fin k → E) :
    compactConvex_taylor_remainder_bound_auxPhi c M u = M (Fin.append u c) := by
  show (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q ↦ E) F c)
      ((M.domDomCongr finSumFinEquiv.symm).currySum u) = M (Fin.append u c)
  rw [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.currySum_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  exact iteratedFDeriv_taylorPolynomial_exact_aux_append u c

theorem compactConvex_taylor_remainder_bound_aux_norm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k q : ℕ} (c : Fin q → E) (M : E[×(k+q)]→L[ℝ] F) :
    ‖compactConvex_taylor_remainder_bound_auxPhi c M‖ ≤ ‖M‖ * ∏ i, ‖c i‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ norm_nonneg _))
  intro u
  rw [compactConvex_taylor_remainder_bound_auxPhi_apply]
  calc ‖M (Fin.append u c)‖ ≤ ‖M‖ * ∏ i, ‖Fin.append u c i‖ := M.le_opNorm _
    _ = ‖M‖ * ((∏ i : Fin k, ‖u i‖) * ∏ i : Fin q, ‖c i‖) := by
        rw [Fin.prod_univ_add]
        have hA : (∏ i : Fin k, ‖Fin.append u c (Fin.castAdd q i)‖) = ∏ i : Fin k, ‖u i‖ :=
          Finset.prod_congr rfl fun i _ ↦ by rw [Fin.append_left]
        have hB : (∏ i : Fin q, ‖Fin.append u c (Fin.natAdd k i)‖) = ∏ i : Fin q, ‖c i‖ :=
          Finset.prod_congr rfl fun i _ ↦ by rw [Fin.append_right]
        rw [hA, hB]
    _ = (‖M‖ * ∏ i, ‖c i‖) * ∏ i, ‖u i‖ := by ring

theorem compactConvex_taylor_remainder_bound_aux_jet_cast
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} {n₁ n₂ : ℕ} (h : n₁ = n₂) (y : E) :
    convexJet n₁ f K y = (convexJet n₂ f K y).domDomCongr (finCongr h).symm := by
  subst h
  ext w
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1


-- Along the segment from `a` to `x`, the `q`-th iterated derivative of the `k`-jet is the
-- `(k+q)`-jet with the last `q` slots filled by `x - a`.
theorem compactConvex_taylor_remainder_bound_aux_formula
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K)
    {a x : E} (ha : a ∈ K) (hx : x ∈ K) {k : ℕ} (hk : k ≤ m) :
    ∀ q : ℕ, q ≤ m + 1 - k → ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      iteratedDerivWithin q (fun (s : ℝ) ↦ convexJet k f K (a + s • (x - a))) (Icc 0 1) t =
        compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - a)
          (convexJet (k + q) f K (a + t • (x - a))) := by
  have huK : UniqueDiffOn ℝ K := uniqueDiffOn_convex hK hKi
  have hmap : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → a + s • (x - a) ∈ K := by
    intro s hs
    have heq : a + s • (x - a) = (1 - s) • a + s • x := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [heq]
    exact hK ha hx (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
  have hAder : ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 → HasFDerivWithinAt (fun (s : ℝ) ↦ a + s • (x - a))
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (x - a)) (Icc 0 1) t := fun t _ ↦
    ((hasFDerivAt_id t).smul_const (x - a)).const_add a |>.hasFDerivWithinAt
  intro q
  induction q with
  | zero =>
    intro _ t ht
    ext u
    rw [iteratedDerivWithin_zero]
    rw [compactConvex_taylor_remainder_bound_auxPhi_apply]
    apply congrArg (convexJet k f K (a + t • (x - a)))
    funext ⟨i, hi⟩
    show u ⟨i, hi⟩ = Fin.append u (fun _ : Fin 0 ↦ x - a) ⟨i, by omega⟩
    rw [show (⟨i, by omega⟩ : Fin (k + 0)) = Fin.castAdd 0 ⟨i, hi⟩ from Fin.ext rfl,
      Fin.append_left]
    exact congrArg u (Fin.ext rfl)
  | succ q ih =>
    intro hq t ht
    have huIcc : UniqueDiffWithinAt ℝ (Icc 0 1) t := uniqueDiffOn_Icc zero_lt_one t ht
    have hJd : HasFDerivWithinAt (convexJet (k + q) f K)
        (fderivWithin ℝ (convexJet (k + q) f K) K (a + t • (x - a))) K (a + t • (x - a)) := by
      apply ((hf.differentiableOn_iteratedFDerivWithin ?_ huK) _
        (hmap t ht)).hasFDerivWithinAt
      exact_mod_cast (by omega : k + q < m + 1)
    have hcomp : HasFDerivWithinAt
        (compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - a) ∘
          (convexJet (k + q) f K ∘ (fun (s : ℝ) ↦ a + s • (x - a))))
        ((compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - a)).comp
          ((fderivWithin ℝ (convexJet (k + q) f K) K (a + t • (x - a))).comp
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (x - a))))
        (Icc 0 1) t :=
      ((compactConvex_taylor_remainder_bound_auxPhi _).hasFDerivAt).hasFDerivWithinAt.comp t
        (hJd.comp t (hAder t ht) (fun s hs ↦ hmap s hs)) (mapsTo_univ _ _)
    have hder : HasDerivWithinAt
        (fun (s : ℝ) ↦ compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - a)
          (convexJet (k + q) f K (a + s • (x - a))))
        (compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - a)
          (fderivWithin ℝ (convexJet (k + q) f K) K (a + t • (x - a)) (x - a)))
        (Icc 0 1) t := by
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      convert hcomp using 2
      ext r
      simp [ContinuousLinearMap.smulRight_apply, one_smul]
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun y hy ↦ ih (by omega) y hy) (ih (by omega) t ht)]
    rw [hder.derivWithin huIcc]
    ext u
    rw [compactConvex_taylor_remainder_bound_auxPhi_apply,
      compactConvex_taylor_remainder_bound_auxPhi_apply]
    have hsy := (convexWithinJet_nat hK hKi hf).2.2.2 (k + (q + 1)) (by omega) _
      (hmap t ht)
    have hrot : convexJet (k + (q + 1)) f K (a + t • (x - a))
          (Fin.append u (fun _ : Fin (q + 1) ↦ x - a))
        = fderivWithin ℝ (convexJet (k + q) f K) K (a + t • (x - a)) (x - a)
          (Fin.append u (fun _ : Fin q ↦ x - a)) := by
      have hupd := Function.update_eq_self
        (Fin.natAdd k (⟨q, by omega⟩ : Fin (q + 1)))
        (Fin.append u (fun _ : Fin (q + 1) ↦ x - a))
      rw [Fin.append_right] at hupd
      have hM := iteratedFDeriv_taylorPolynomial_exact_aux_symm
        (convexJet (k + (q + 1)) f K (a + t • (x - a))) hsy u (x - a) (x - a)
        (⟨q, by omega⟩ : Fin (q + 1))
      rw [hupd] at hM
      rw [hM]
      have htail : Fin.tail (fun i : Fin ((k + q) + 1) ↦ Fin.append (Fin.cons (x - a) u)
            (fun _ : Fin q ↦ x - a) (Fin.cast (by omega : (k + q) + 1 = k + 1 + q) i)) =
          Fin.append u (fun _ : Fin q ↦ x - a) := by
        funext ⟨i, hi⟩
        show Fin.append (Fin.cons (x - a) u) (fun _ : Fin q ↦ x - a)
            (Fin.cast (by omega : (k + q) + 1 = k + 1 + q) ⟨i + 1, by omega⟩) =
          Fin.append u (fun _ : Fin q ↦ x - a) ⟨i, hi⟩
        by_cases hi2 : i < k
        · have e1 : (⟨i, hi⟩ : Fin (k + q)) = Fin.castAdd q ⟨i, hi2⟩ := Fin.ext rfl
          have e2 : Fin.cast (by omega : (k + q) + 1 = k + 1 + q) ⟨i + 1, by omega⟩ =
              Fin.castAdd q (⟨i + 1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
          have e3 : (⟨i + 1, by omega⟩ : Fin (k + 1)) = (⟨i, hi2⟩ : Fin k).succ :=
            Fin.ext rfl
          rw [e1, Fin.append_left, e2, Fin.append_left, e3, Fin.cons_succ]
        · have e1 : (⟨i, hi⟩ : Fin (k + q)) = Fin.natAdd k ⟨i - k, by omega⟩ :=
            Fin.ext (by show i = k + (i - k); omega)
          have e2 : Fin.cast (by omega : (k + q) + 1 = k + 1 + q) ⟨i + 1, by omega⟩ =
              Fin.natAdd (k + 1) ⟨i - k, by omega⟩ :=
            Fin.ext (by show i + 1 = (k + 1) + (i - k); omega)
          rw [e1, Fin.append_right, e2, Fin.append_right]
      have hhead : Fin.append (Fin.cons (x - a) u) (fun _ : Fin q ↦ x - a)
            (Fin.cast (by omega : (k + q) + 1 = k + 1 + q) (0 : Fin ((k + q) + 1))) =
          x - a := by
        have e1 : Fin.cast (by omega : (k + q) + 1 = k + 1 + q) (0 : Fin ((k + q) + 1)) =
            Fin.castAdd q (0 : Fin (k + 1)) := Fin.ext rfl
        rw [e1, Fin.append_left, Fin.cons_zero]
      have h2 := iteratedFDerivWithin_succ_apply_left (𝕜 := ℝ) (f := f) (s := K)
        (x := a + t • (x - a)) (n := k + q)
        (m := fun i : Fin ((k + q) + 1) ↦ Fin.append (Fin.cons (x - a) u)
          (fun _ : Fin q ↦ x - a) (Fin.cast (by omega : (k + q) + 1 = k + 1 + q) i))
      rw [htail, hhead] at h2
      exact h2
    exact hrot.symm


theorem compactConvex_taylor_remainder_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ a ∈ K, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x -
          convexJet k f K x‖ ≤ C * ‖x - a‖ ^ (m + 1 - k) := by
  classical
  have huK : UniqueDiffOn ℝ K := uniqueDiffOn_convex hK hKi
  obtain ⟨hcont, hzero, hone, hsymm⟩ := convexWithinJet_nat hK hKi hf
  have hKne : K.Nonempty := hKi.mono interior_subset
  obtain ⟨y₀, hy₀, hB⟩ := hKc.exists_isMaxOn hKne ((hcont (m + 1) le_rfl).norm)
  refine ⟨‖convexJet (m + 1) f K y₀‖, norm_nonneg _, ?_⟩
  intro k hk a ha x hx
  have hmap : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → a + s • (x - a) ∈ K := by
    intro s hs
    have heq : a + s • (x - a) = (1 - s) • a + s • x := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [heq]
    exact hK ha hx (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
  have hB' : ∀ y ∈ K, ‖convexJet (m + 1) f K y‖ ≤ ‖convexJet (m + 1) f K y₀‖ :=
    fun y hy ↦ isMaxOn_iff.mp hB y hy
  have hAcont : ContinuousOn (fun (s : ℝ) ↦ a + s • (x - a)) (Icc 0 1) :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have hCg : ContDiffOn ℝ ((m - k) + 1 : ℕ)
      (fun (s : ℝ) ↦ convexJet k f K (a + s • (x - a))) (Icc 0 1) := by
    rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
      (uniqueDiffOn_Icc zero_lt_one)]
    constructor
    · intro r hr
      apply ContinuousOn.congr _
        (fun t ht ↦ compactConvex_taylor_remainder_bound_aux_formula hK hKi hf ha hx hk r
          (by omega) t ht)
      exact (compactConvex_taylor_remainder_bound_auxPhi _).continuous.comp_continuousOn
        ((hcont (k + r) (by omega)).comp hAcont (fun s hs ↦ hmap s hs))
    · intro r hr
      apply DifferentiableOn.congr _
        (fun t ht ↦ compactConvex_taylor_remainder_bound_aux_formula hK hKi hf ha hx hk r
          (by omega) t ht)
      have hdA : DifferentiableOn ℝ (fun (s : ℝ) ↦ a + s • (x - a)) (Icc 0 1) :=
        ((differentiable_id.smul (differentiable_const (x - a))).const_add a).differentiableOn
      have hdJ : DifferentiableOn ℝ (convexJet (k + r) f K) K :=
        hf.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (by omega : k + r < m + 1)) huK
      exact ((compactConvex_taylor_remainder_bound_auxPhi _).differentiable).differentiableOn.comp
        (hdJ.comp hdA (fun s hs ↦ hmap s hs)) (mapsTo_univ _ _)
  have hub : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin ((m - k) + 1) (fun (s : ℝ) ↦ convexJet k f K (a + s • (x - a)))
          (Icc 0 1) y‖ ≤ ‖convexJet (m + 1) f K y₀‖ * ‖x - a‖ ^ (m + 1 - k) := by
    intro y hy
    have h2 : (m - k) + 1 = m + 1 - k := by omega
    have h1 := compactConvex_taylor_remainder_bound_aux_formula hK hKi hf ha hx hk
      (m + 1 - k) le_rfl y hy
    rw [h2, h1]
    have hkq : k + (m + 1 - k) = m + 1 := by omega
    have hnrm : ‖convexJet (k + (m + 1 - k)) f K (a + y • (x - a))‖ =
        ‖convexJet (m + 1) f K (a + y • (x - a))‖ := by
      rw [compactConvex_taylor_remainder_bound_aux_jet_cast hkq]
      exact ContinuousMultilinearMap.norm_domDomCongr ℝ E F (finCongr hkq).symm _
    calc ‖compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin (m + 1 - k) ↦ x - a)
            (convexJet (k + (m + 1 - k)) f K (a + y • (x - a)))‖
        ≤ ‖convexJet (k + (m + 1 - k)) f K (a + y • (x - a))‖ *
            ∏ i : Fin (m + 1 - k), ‖(fun _ ↦ x - a) i‖ :=
          compactConvex_taylor_remainder_bound_aux_norm _ _
      _ = ‖convexJet (k + (m + 1 - k)) f K (a + y • (x - a))‖ * ‖x - a‖ ^ (m + 1 - k) := by
          simp [Finset.prod_const]
      _ ≤ ‖convexJet (m + 1) f K y₀‖ * ‖x - a‖ ^ (m + 1 - k) :=
          mul_le_mul_of_nonneg_right
            (by rw [hnrm]; exact hB' _ (hmap y hy)) (pow_nonneg (norm_nonneg _) _)
  have hrem := taylor_mean_remainder_bound (zero_le_one : (0 : ℝ) ≤ 1) hCg
    (right_mem_Icc.mpr zero_le_one) hub
  rw [sub_zero, one_pow, mul_one] at hrem
  have hfac : (‖convexJet (m + 1) f K y₀‖ * ‖x - a‖ ^ (m + 1 - k)) /
        ((Nat.factorial (m - k) : ℕ) : ℝ) ≤
      ‖convexJet (m + 1) f K y₀‖ * ‖x - a‖ ^ (m + 1 - k) :=
    div_le_self (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (Nat.one_le_cast.mpr (Nat.factorial_pos _))
  have hg1 : (fun (s : ℝ) ↦ convexJet k f K (a + s • (x - a))) 1 = convexJet k f K x := by
    show convexJet k f K (a + 1 • (x - a)) = convexJet k f K x
    rw [one_smul, add_sub_cancel]
  have hte : taylorWithinEval (fun (s : ℝ) ↦ convexJet k f K (a + s • (x - a))) (m - k)
        (Icc 0 1) 0 1 =
      ∑ r ∈ Finset.range (m + 1 - k), (r.factorial : ℝ)⁻¹ •
        compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin r ↦ x - a)
          (convexJet (k + r) f K a) := by
    rw [taylor_within_apply]
    have h3 : m - k + 1 = m + 1 - k := by omega
    rw [h3]
    apply Finset.sum_congr rfl
    intro r hr
    rw [sub_zero, one_pow, mul_one]
    congr 1
    have hr' : r ≤ m + 1 - k := by
      have := Finset.mem_range.mp hr; omega
    have hh := compactConvex_taylor_remainder_bound_aux_formula hK hKi hf ha hx hk r hr' 0
      (left_mem_Icc.mpr zero_le_one)
    rw [zero_smul, add_zero] at hh
    exact hh
  have hexact : iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x =
      ∑ r ∈ Finset.range (m + 1 - k), (r.factorial : ℝ)⁻¹ •
        compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin r ↦ x - a)
          (convexJet (k + r) f K a) := by
    apply ContinuousMultilinearMap.ext
    intro u
    rw [iteratedFDeriv_taylorPolynomial_exact m k (fun j ↦ convexJet j f K) a x hk u
      (fun j hj σ ↦ hsymm j (by omega) a ha σ)]
    rw [ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    rw [ContinuousMultilinearMap.smul_apply,
      compactConvex_taylor_remainder_bound_auxPhi_apply]
  rw [hexact, ← hte, ← hg1, norm_sub_rev]
  exact hrem.trans hfac


/-- Taylor polynomials based at two points of `K` differ to the full Whitney order.
Expand `P_a-P_b` at `b`; its derivatives there are controlled by the compact convex
remainder estimate, then evaluate that finite polynomial using the exact formula above. -/
/- Taylor polynomials are smooth (finite sums of diagonal monomials). -/
theorem taylor_difference_bound_aux_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a : E) :
    ContDiff ℝ ⊤ (taylorPolynomial m J a) := by
  show ContDiff ℝ ⊤ (fun x ↦ ∑ j ∈ Finset.range (m + 1),
    ((j.factorial : ℝ)⁻¹) • J j a (fun _ ↦ x - a))
  apply ContDiff.sum
  intro j _
  apply ContDiff.const_smul
  exact (ContinuousMultilinearMap.contDiff _).comp
    (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)

/- The `(m+1)`-th derivative of a degree-`m` Taylor polynomial vanishes. -/
theorem taylor_difference_bound_aux_top
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a : E)
    (hJ : ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j), (J j a).domDomCongr σ = J j a) :
    ∀ k : ℕ, m + 1 ≤ k → ∀ x : E, iteratedFDeriv ℝ k (taylorPolynomial m J a) x = 0 := by
  have hDm : ∀ y : E, iteratedFDeriv ℝ m (taylorPolynomial m J a) y = J m a := by
    intro y
    ext v
    rw [iteratedFDeriv_taylorPolynomial_exact m m J a y le_rfl v hJ]
    have h1 : m + 1 - m = 1 := by omega
    rw [h1, Finset.sum_range_one]
    rw [show (((Nat.factorial 0 : ℕ) : ℝ))⁻¹ = 1 from by simp, one_smul]
    have happ : Fin.append v (fun _ : Fin 0 ↦ y - a) =
        fun i ↦ v (Fin.cast (Nat.add_zero m) i) := by
      funext i
      have hi : i = Fin.castAdd 0 (Fin.cast (Nat.add_zero m) i) := Fin.ext rfl
      conv_lhs => rw [hi, Fin.append_left]
    rw [happ]
    exact iteratedFDeriv_taylorPolynomial_exact_aux_cast (fun n ↦ J n a) (Nat.add_zero m) v
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro x
    ext w
    rw [iteratedFDeriv_succ_apply_left]
    have hfun : iteratedFDeriv ℝ m (taylorPolynomial m J a) = fun _ ↦ J m a := funext hDm
    rw [hfun]
    simp
  | succ k hk ih =>
    intro x
    ext w
    rw [iteratedFDeriv_succ_apply_left]
    rw [show iteratedFDeriv ℝ k (taylorPolynomial m J a) = 0 from funext ih]
    simp

/- Iterated derivatives commute with pointwise subtraction of smooth maps. -/
theorem taylor_difference_bound_aux_iteratedFDeriv_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ ψ : E → F} (hφ : ContDiff ℝ ⊤ φ) (hψ : ContDiff ℝ ⊤ ψ) (k : ℕ) :
    ∀ (x : E) (u : Fin k → E),
      iteratedFDeriv ℝ k (fun y ↦ φ y - ψ y) x u =
        iteratedFDeriv ℝ k φ x u - iteratedFDeriv ℝ k ψ x u := by
  induction k with
  | zero =>
    intro x u
    rw [iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro x u
    have hfun : iteratedFDeriv ℝ k (fun z ↦ φ z - ψ z) =
        iteratedFDeriv ℝ k φ - iteratedFDeriv ℝ k ψ := by
      funext y
      rw [Pi.sub_apply]
      ext v
      rw [ContinuousMultilinearMap.sub_apply]
      exact ih y v
    rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left,
      iteratedFDeriv_succ_apply_left, hfun]
    have hA : DifferentiableAt ℝ (iteratedFDeriv ℝ k φ) x :=
      (hφ.contDiffAt.differentiableAt_iteratedFDeriv (by simp))
    have hB : DifferentiableAt ℝ (iteratedFDeriv ℝ k ψ) x :=
      (hψ.contDiffAt.differentiableAt_iteratedFDeriv (by simp))
    rw [fderiv_sub hA hB, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]

theorem taylor_difference_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ r
          (fun y ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a y -
            taylorPolynomial m (fun j ↦ convexJet j f K) b y) x‖ ≤
        C * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
  classical
  obtain ⟨C₁, hC₁nn, hC₁⟩ := compactConvex_taylor_remainder_bound hKc hK hKi hf
  obtain ⟨hcont, hzero, hone, hsymm⟩ := convexWithinJet_nat hK hKi hf
  have hJ : ∀ c ∈ K, ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j),
      (convexJet j f K c).domDomCongr σ = convexJet j f K c :=
    fun c _ j hj σ ↦ hsymm j (by omega) c (by assumption) σ
  have hPa : ∀ c : E, ContDiff ℝ ⊤ (taylorPolynomial m (fun j ↦ convexJet j f K) c) :=
    fun c ↦ taylor_difference_bound_aux_contDiff m _ c
  refine ⟨C₁ * (m + 1 : ℝ) * 2 ^ (m + 1),
    mul_nonneg (mul_nonneg hC₁nn (by positivity)) (pow_nonneg (by norm_num) _), ?_⟩
  intro r hr a ha b hb x
  have hQtop : ContDiff ℝ ⊤ (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
      taylorPolynomial m (fun j ↦ convexJet j f K) b z) := (hPa a).sub (hPa b)
  have hQon : ContDiffOn ℝ (m + 1) (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
      taylorPolynomial m (fun j ↦ convexJet j f K) b z) univ :=
    (hQtop.of_le (show ((m + 1 : ℕ) : WithTop ENat) ≤ ⊤ from le_top)).contDiffOn
  -- Segment derivative formula along the line from `b` to `x` (ambient-space version of
  -- `compactConvex_taylor_remainder_bound_aux_formula` with `K = univ`).
  have hform : ∀ (q : ℕ), q ≤ m + 1 - r → ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin q (fun s ↦ iteratedFDeriv ℝ r
          (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + s • (x - b)))
          (Icc 0 1) t =
        compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin q ↦ x - b)
          (iteratedFDeriv ℝ (r + q)
            (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
              taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + t • (x - b))) := by
    intro q hq t ht
    have h := compactConvex_taylor_remainder_bound_aux_formula (K := (univ : Set E))
      (f := fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z)
      convex_univ (by rw [interior_univ]; exact ⟨0, trivial⟩) hQon (mem_univ b) (mem_univ x)
      hr q hq t ht
    simp only [convexJet, iteratedFDerivWithin_univ] at h
    exact h
  -- The top line-derivative vanishes because both `(m+1)`-th derivatives do.
  have htop : ∀ (k : ℕ), m + 1 ≤ k → ∀ y : E, iteratedFDeriv ℝ k
      (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z) y = 0 := by
    intro k hk y
    ext u
    rw [taylor_difference_bound_aux_iteratedFDeriv_sub (hPa a) (hPa b) k y u,
      taylor_difference_bound_aux_top m _ a (hJ a ha) k hk y,
      taylor_difference_bound_aux_top m _ b (hJ b hb) k hk y,
      ContinuousMultilinearMap.zero_apply, sub_self]
  have hub : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin ((m - r) + 1) (fun s ↦ iteratedFDeriv ℝ r
          (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + s • (x - b)))
          (Icc 0 1) y‖ ≤ (0 : ℝ) := by
    intro y hy
    have h2 : (m - r) + 1 = m + 1 - r := by omega
    rw [h2, hform (m + 1 - r) le_rfl y hy]
    rw [htop (r + (m + 1 - r)) (by omega) _, map_zero, norm_zero]
  have hline : ContDiff ℝ ⊤ (fun s : ℝ ↦ b + s • (x - b)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hjet : ContDiff ℝ ⊤ (iteratedFDeriv ℝ r
      (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z)) :=
    hQtop.iteratedFDeriv_right (m := ⊤) le_top
  have hCg : ContDiff ℝ ⊤ (fun s ↦ iteratedFDeriv ℝ r
      (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + s • (x - b))) :=
    hjet.comp hline
  have hrem := taylor_mean_remainder_bound (zero_le_one : (0 : ℝ) ≤ 1)
    ((hCg.contDiffOn.mono (subset_univ _)).of_le le_top)
    (right_mem_Icc.mpr zero_le_one) hub
  rw [sub_zero, one_pow, mul_one, zero_div] at hrem
  have heq : iteratedFDeriv ℝ r (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z) x =
      taylorWithinEval (fun s ↦ iteratedFDeriv ℝ r
        (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
          taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + s • (x - b)))
        (m - r) (Icc 0 1) 0 1 := by
    have h0 := sub_eq_zero.mp (norm_le_zero_iff.mp hrem)
    rwa [one_smul, add_sub_cancel] at h0
  have hte : taylorWithinEval (fun s ↦ iteratedFDeriv ℝ r
        (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
          taylorPolynomial m (fun j ↦ convexJet j f K) b z) (b + s • (x - b)))
        (m - r) (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range (m + 1 - r), (j.factorial : ℝ)⁻¹ •
        compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin j ↦ x - b)
          (iteratedFDeriv ℝ (r + j) (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) b) := by
    rw [taylor_within_apply]
    have h3 : m - r + 1 = m + 1 - r := by omega
    rw [h3]
    apply Finset.sum_congr rfl
    intro j hj
    rw [sub_zero, one_pow, mul_one]
    congr 1
    have hh := hform j (by have := Finset.mem_range.mp hj; omega) 0
      (left_mem_Icc.mpr zero_le_one)
    rw [zero_smul, add_zero] at hh
    exact hh
  rw [heq, hte]
  -- Termwise bound, then sum.
  have hterm : ∀ j ∈ Finset.range (m + 1 - r),
      ‖(j.factorial : ℝ)⁻¹ • compactConvex_taylor_remainder_bound_auxPhi
          (fun _ : Fin j ↦ x - b)
          (iteratedFDeriv ℝ (r + j) (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) b)‖ ≤
        C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
    intro j hj
    have hjT : j < m + 1 - r := Finset.mem_range.mp hj
    have hrj : r + j ≤ m := by omega
    have hb0 : iteratedFDeriv ℝ (r + j) (taylorPolynomial m (fun j ↦ convexJet j f K) b) b =
        convexJet (r + j) f K b := by
      have h := hC₁ (r + j) hrj b hb b hb
      rw [sub_self, norm_zero, zero_pow (by omega : m + 1 - (r + j) ≠ 0), mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have hsub : iteratedFDeriv ℝ (r + j)
        (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
          taylorPolynomial m (fun j ↦ convexJet j f K) b z) b =
        iteratedFDeriv ℝ (r + j) (taylorPolynomial m (fun j ↦ convexJet j f K) a) b -
          convexJet (r + j) f K b := by
      ext u
      rw [ContinuousMultilinearMap.sub_apply,
        taylor_difference_bound_aux_iteratedFDeriv_sub (hPa a) (hPa b) (r + j) b u, hb0]
    have hnorm : ‖iteratedFDeriv ℝ (r + j)
        (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
          taylorPolynomial m (fun j ↦ convexJet j f K) b z) b‖ ≤
        C₁ * ‖b - a‖ ^ (m + 1 - r - j) := by
      rw [hsub]
      have h := hC₁ (r + j) hrj a ha b hb
      have hT : m + 1 - (r + j) = m + 1 - r - j := by omega
      rwa [hT] at h
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (j.factorial : ℝ)⁻¹)]
    have hfac : (j.factorial : ℝ)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos j))
    have hAn := compactConvex_taylor_remainder_bound_aux_norm (fun _ : Fin j ↦ x - b)
      (iteratedFDeriv ℝ (r + j) (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
        taylorPolynomial m (fun j ↦ convexJet j f K) b z) b)
    have hprod : ∏ i : Fin j, ‖(fun _ ↦ x - b) i‖ = ‖x - b‖ ^ j := by
      simp [Finset.prod_const, Finset.card_fin]
    have hpow : ‖b - a‖ ^ (m + 1 - r - j) * ‖x - b‖ ^ j ≤
        (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
      calc ‖b - a‖ ^ (m + 1 - r - j) * ‖x - b‖ ^ j
          ≤ (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r - j) * (‖b - a‖ + ‖x - b‖) ^ j :=
            mul_le_mul
              (pow_le_pow_left₀ (norm_nonneg _)
                (le_add_of_nonneg_right (norm_nonneg _)) _)
              (pow_le_pow_left₀ (norm_nonneg _)
                (le_add_of_nonneg_left (norm_nonneg _)) _)
              (pow_nonneg (norm_nonneg _) _)
              (pow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)
        _ = (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
            rw [← pow_add]
            congr 2
            omega
    calc (j.factorial : ℝ)⁻¹ * ‖compactConvex_taylor_remainder_bound_auxPhi
            (fun _ : Fin j ↦ x - b)
            (iteratedFDeriv ℝ (r + j)
              (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
                taylorPolynomial m (fun j ↦ convexJet j f K) b z) b)‖
        ≤ (j.factorial : ℝ)⁻¹ * (C₁ * (‖b - a‖ ^ (m + 1 - r - j) * ‖x - b‖ ^ j)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ‖compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin j ↦ x - b)
                (iteratedFDeriv ℝ (r + j)
                  (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
                    taylorPolynomial m (fun j ↦ convexJet j f K) b z) b)‖
              ≤ ‖iteratedFDeriv ℝ (r + j)
                  (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
                    taylorPolynomial m (fun j ↦ convexJet j f K) b z) b‖ * ‖x - b‖ ^ j := by
                rwa [hprod] at hAn
            _ ≤ (C₁ * ‖b - a‖ ^ (m + 1 - r - j)) * ‖x - b‖ ^ j :=
                mul_le_mul_of_nonneg_right hnorm (pow_nonneg (norm_nonneg _) _)
            _ = C₁ * (‖b - a‖ ^ (m + 1 - r - j) * ‖x - b‖ ^ j) := by ring
      _ ≤ 1 * (C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r)) := by
          apply mul_le_mul hfac _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hpow hC₁nn
      _ = C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) := one_mul _
  calc ‖∑ j ∈ Finset.range (m + 1 - r), (j.factorial : ℝ)⁻¹ •
          compactConvex_taylor_remainder_bound_auxPhi (fun _ : Fin j ↦ x - b)
            (iteratedFDeriv ℝ (r + j)
              (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
                taylorPolynomial m (fun j ↦ convexJet j f K) b z) b)‖
      ≤ ∑ j ∈ Finset.range (m + 1 - r), C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (↑m + 1 - ↑r : ℝ) * (C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        rw [Nat.cast_sub (by omega : r ≤ m + 1), Nat.cast_add, Nat.cast_one]
    _ ≤ C₁ * (m + 1 : ℝ) * 2 ^ (m + 1) * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
        have hSnn : 0 ≤ ‖x - a‖ + ‖x - b‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
        have hba : ‖b - a‖ ≤ ‖x - a‖ + ‖x - b‖ := by
          have h1 : ‖b - a‖ ≤ ‖b - x‖ + ‖x - a‖ := by
            have he : b - a = (b - x) + (x - a) := by abel
            rw [he]
            exact norm_add_le _ _
          have h2 : ‖b - x‖ = ‖x - b‖ := norm_sub_rev _ _
          linarith
        have hscale : (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r) ≤
            (2 * (‖x - a‖ + ‖x - b‖)) ^ (m + 1 - r) := by
          apply pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
          have hxa : 0 ≤ ‖x - a‖ := norm_nonneg _
          linarith
        rw [mul_pow] at hscale
        have hrnn : (0 : ℝ) ≤ ↑m + 1 - ↑r :=
          sub_nonneg.mpr (by exact_mod_cast hr.trans (Nat.le_succ m))
        have hcount : (↑m + 1 - ↑r) * (C₁ * (‖b - a‖ + ‖x - b‖) ^ (m + 1 - r)) ≤
            (↑m + 1 - ↑r) * (C₁ * (2 ^ (m + 1 - r) * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hscale hC₁nn) hrnn
        refine hcount.trans ?_
        have h2mono : (2 : ℝ) ^ (m + 1 - r) ≤ 2 ^ (m + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hrm : (↑m + 1 - ↑r : ℝ) ≤ (↑m + 1 : ℝ) := sub_le_self _ (by positivity)
        have hS : 0 ≤ (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r) := pow_nonneg hSnn _
        calc (↑m + 1 - ↑r) * (C₁ * (2 ^ (m + 1 - r) * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r)))
            = ((↑m + 1 - ↑r) * 2 ^ (m + 1 - r)) *
                (C₁ * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r)) := by ring
          _ ≤ ((↑m + 1 : ℝ) * 2 ^ (m + 1)) * (C₁ * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r)) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC₁nn hS)
              exact mul_le_mul hrm h2mono (pow_nonneg (by norm_num) _) (by positivity)
          _ = C₁ * (↑m + 1) * 2 ^ (m + 1) * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r) := by ring

/-- Smooth partition data on the complement, indexed by the already constructed dyadic
Whitney nets.  Supports use half-distance balls while quarter-distance balls cover; only
complement-local finiteness is asserted, as ambient local finiteness is false. -/
structure WhitneySmoothPartition
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) where
  phi : SardConvexDomain.WhitneyNetIndex K → E → ℝ
  contDiff_phi : ∀ i, ContDiff ℝ ∞ (phi i)
  support_subset : ∀ i, Function.support (phi i) ⊆
    Metric.ball i.center (Metric.infDist i.center K / 2)
  nonneg : ∀ i x, 0 ≤ phi i x
  sum_one : ∀ x ∉ K, HasSum (fun i ↦ phi i x) 1
  locallyFinite_compl : ∀ x ∉ K, ∃ U ∈ nhds x,
    {i | (U ∩ Function.support (phi i)).Nonempty}.Finite
  derivConstant : ℕ → ℝ
  derivConstant_nonneg : ∀ k, 0 ≤ derivConstant k
  deriv_bound : ∀ k i x,
    ‖iteratedFDeriv ℝ k (phi i) x‖ ≤
      derivConstant k * (Metric.infDist i.center K)⁻¹ ^ k

/-- Construct unnormalised smooth bumps equal to one on the quarter-balls and supported in
the half-balls, with scale-correct derivative bounds.  Rescale one fixed Euclidean bump;
the existing half-ball incidence theorem supplies complement-local finiteness. -/
theorem exists_whitney_bump_family_aux_half_localFinite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∀ x ∉ K, ∃ U ∈ nhds x,
      {i : SardConvexDomain.WhitneyNetIndex K |
        (U ∩ Metric.ball i.center (Metric.infDist i.center K / 2)).Nonempty}.Finite := by
  intro x hx
  let r := Metric.infDist x K / 16
  let I : Set (SardConvexDomain.WhitneyNetIndex K) := {i |
    (Metric.ball x r ∩ Metric.ball i.center
      (Metric.infDist i.center K / 2)).Nonempty}
  have hxpos : 0 < Metric.infDist x K := (hK.notMem_iff_infDist_pos hKn).1 hx
  have hscale (i : SardConvexDomain.WhitneyNetIndex K) (hi : i ∈ I) :
      5 * Metric.infDist x K < 8 * Metric.infDist i.center K ∧
        8 * Metric.infDist i.center K < 17 * Metric.infDist x K := by
    obtain ⟨y, hyx, hyi⟩ := hi
    have ha : dist x y < Metric.infDist x K / 16 := by
      simpa [r, dist_comm] using Metric.mem_ball.1 hyx
    have hb : dist y i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hyi
    have hxy := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := y)
    have hyx' := Metric.infDist_le_infDist_add_dist (s := K) (x := y) (y := x)
    have hc := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hyi
    have had : dist y x = dist x y := dist_comm _ _
    constructor <;> nlinarith
  have hfiber (k : ℤ) : {i | i.1 = k ∧ i ∈ I}.Finite := by
    let f : SardConvexDomain.WhitneyNetIndex K → E :=
      SardConvexDomain.WhitneyNetIndex.center
    have hinj : Set.InjOn f {i | i.1 = k ∧ i ∈ I} := by
      intro i hi j hj hij
      have hk : i.1 = j.1 := hi.1.trans hj.1.symm
      cases i with
      | mk ik ic =>
        cases j with
        | mk jk jc =>
          dsimp at hk hij ⊢
          subst jk
          exact congrArg (Sigma.mk ik) (Subtype.ext hij)
    apply Set.Finite.of_finite_image (f := f) _ hinj
    apply (SardConvexDomain.finite_inter_whitneyStratumNet_of_isCompact K k
      (isCompact_closedBall x (4 * (2 : ℝ) ^ (k + 1)))).subset
    rintro c ⟨i, hi, rfl⟩
    constructor
    · change i.2.1 ∈ SardConvexDomain.whitneyStratumNet K k
      rw [← hi.1]
      exact i.2.2
    · obtain ⟨y, hyx, hyi⟩ := hi.2
      apply Metric.mem_closedBall.2
      have ha : dist x y < Metric.infDist x K / 16 := by
        simpa [r, dist_comm] using Metric.mem_ball.1 hyx
      have hb : dist y i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hyi
      have hs := hscale i hi.2
      have hstr : Metric.infDist i.center K < (2 : ℝ) ^ (k + 1) := by
        simpa only [hi.1] using
          ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.2
      have ht := dist_triangle x y i.center
      have hp : 0 < (2 : ℝ) ^ (k + 1) := by positivity
      rw [show dist (f i) x = dist x i.center by simp [f, dist_comm]]
      nlinarith
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x (by dsimp [r]; positivity), ?_⟩
  change I.Finite
  by_cases hI : I.Nonempty
  · obtain ⟨i, hi⟩ := hI
    have hfinite := (Set.finite_Icc (i.1 - 3) (i.1 + 3)).biUnion
      (fun k _ => hfiber k)
    apply hfinite.subset
    intro j hj
    have hsi := hscale i hi
    have hsj := hscale j hj
    have hik : (2 : ℝ) ^ i.1 ≤ Metric.infDist i.center K :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.1
    have hjk : Metric.infDist j.center K < (2 : ℝ) ^ (j.1 + 1) :=
      ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2).2.2
    have hjlow : (2 : ℝ) ^ j.1 ≤ Metric.infDist j.center K :=
      ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2).2.1
    have hiup : Metric.infDist i.center K < (2 : ℝ) ^ (i.1 + 1) :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.2
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hjk hiup
    norm_num at hjk hiup
    have hlo : i.1 - 3 ≤ j.1 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (j.1 + 4) ≤ (2 : ℝ) ^ i.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hp
      norm_num at hp
      have hpi : 0 < (2 : ℝ) ^ i.1 := by positivity
      have hpj : 0 < (2 : ℝ) ^ j.1 := by positivity
      nlinarith
    have hhi : j.1 ≤ i.1 + 3 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (i.1 + 4) ≤ (2 : ℝ) ^ j.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hp
      norm_num at hp
      have hpi : 0 < (2 : ℝ) ^ i.1 := by positivity
      have hpj : 0 < (2 : ℝ) ^ j.1 := by positivity
      nlinarith
    exact Set.mem_iUnion₂.2 ⟨j.1, ⟨hlo, hhi⟩, ⟨rfl, hj⟩⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hI]
    exact Set.finite_empty

theorem exists_whitney_bump_family
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∃ psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (psi i)) ∧
      (∀ i x, 0 ≤ psi i x ∧ psi i x ≤ 1) ∧
      (∀ i, Metric.ball i.center (Metric.infDist i.center K / 4) ⊆
        {x | psi i x = 1}) ∧
      (∀ i, Function.support (psi i) ⊆ Metric.ball i.center (Metric.infDist i.center K / 2)) ∧
      (∀ x ∉ K, ∃ U ∈ nhds x, {i | (U ∩ Function.support (psi i)).Nonempty}.Finite) ∧
      ∃ C : ℕ → ℝ, ∀ k i x,
        ‖iteratedFDeriv ℝ k (psi i) x‖ ≤
          C k * (Metric.infDist i.center K)⁻¹ ^ k := by
  let b : ContDiffBump (0 : E) :=
    ⟨(1 : ℝ) / 4, (1 : ℝ) / 2, by norm_num, by norm_num⟩
  let psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ := fun i x =>
    b ((Metric.infDist i.center K)⁻¹ • (x - i.center))
  have hcenter (i : SardConvexDomain.WhitneyNetIndex K) : i.center ∉ K :=
    ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).1
  have hd (i : SardConvexDomain.WhitneyNetIndex K) : 0 < Metric.infDist i.center K :=
    (hK.notMem_iff_infDist_pos hKn).1 (hcenter i)
  have hbdd : ∀ k : ℕ, ∃ B : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ k (b : E → ℝ) x‖ ≤ B := by
    intro k
    have hc : HasCompactSupport (iteratedFDeriv ℝ k (b : E → ℝ)) :=
      b.hasCompactSupport.iteratedFDeriv k
    have hcont : Continuous (iteratedFDeriv ℝ k (b : E → ℝ)) :=
      b.contDiff.continuous_iteratedFDeriv (mod_cast le_top)
    have hbound := hcont.norm.bddAbove_range_of_hasCompactSupport hc.norm
    rw [bddAbove_def] at hbound
    simpa only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using hbound
  choose C hC using hbdd
  refine ⟨psi, ?_, ?_, ?_, ?_, ?_, C, ?_⟩
  · intro i
    exact b.contDiff.comp
      (contDiff_const.smul (contDiff_id.sub contDiff_const))
  · intro i x
    exact ⟨b.nonneg, b.le_one⟩
  · intro i x hx
    apply b.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)]
    have hx' := Metric.mem_ball.1 hx
    rw [dist_eq_norm] at hx'
    rw [inv_mul_le_iff₀ (hd i)]
    exact (le_of_lt hx').trans_eq (by ring)
  · intro i x hx
    change b ((Metric.infDist i.center K)⁻¹ • (x - i.center)) ≠ 0 at hx
    have hbmem : (Metric.infDist i.center K)⁻¹ • (x - i.center) ∈
        Metric.ball (0 : E) ((1 : ℝ) / 2) := by
      rwa [← b.support_eq]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)] at hbmem
    rw [Metric.mem_ball, dist_eq_norm]
    rw [inv_mul_lt_iff₀ (hd i)] at hbmem
    simpa using hbmem
  · intro x hx
    obtain ⟨U, hU, hfin⟩ :=
      exists_whitney_bump_family_aux_half_localFinite hK hKn x hx
    refine ⟨U, hU, hfin.subset ?_⟩
    intro i hi
    obtain ⟨y, hyU, hypsi⟩ := hi
    refine ⟨y, hyU, ?_⟩
    apply (show Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2) from ?_) hypsi
    intro z hz
    change b ((Metric.infDist i.center K)⁻¹ • (z - i.center)) ≠ 0 at hz
    have hbmem : (Metric.infDist i.center K)⁻¹ • (z - i.center) ∈
        Metric.ball (0 : E) ((1 : ℝ) / 2) := by rwa [← b.support_eq]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)] at hbmem
    rw [inv_mul_lt_iff₀ (hd i)] at hbmem
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hbmem
  · intro k i x
    change ‖iteratedFDeriv ℝ k
      (fun z => b ((Metric.infDist i.center K)⁻¹ • (z - i.center))) x‖ ≤ _
    rw [iteratedFDeriv_comp_sub (f := fun z => b ((Metric.infDist i.center K)⁻¹ • z))]
    rw [iteratedFDeriv_comp_const_smul _ b.contDiff]
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv,
      abs_of_pos (hd i)]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (hC k ((Metric.infDist i.center K)⁻¹ • (x - i.center)))
        (pow_nonneg (inv_nonneg.2 (hd i).le) k))

/-- The sum of incident unnormalised bumps is locally a finite smooth positive function on
the complement, bounded below by one.  Use quarter-ball coverage for positivity and the
half-ball local-finiteness result to replace the `tsum` by a finite sum near each point. -/
theorem whitney_bump_sum_positive_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty)
    (psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ)
    (hnonneg : ∀ i x, 0 ≤ psi i x)
    (hone : ∀ i, Metric.ball i.center (Metric.infDist i.center K / 4) ⊆
      {x | psi i x = 1})
    (hsupp : ∀ i, Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2))
    (hlocal : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (psi i)).Nonempty}.Finite)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (psi i)) :
    ∀ x ∉ K, 1 ≤ ∑' i, psi i x ∧
      ContDiffAt ℝ ∞ (fun y ↦ ∑' i, psi i y) x := by
  intro x hx
  have hxK : x ∈ Kᶜ := by simpa using hx
  obtain ⟨i0, hi0⟩ : ∃ i0 : SardConvexDomain.WhitneyNetIndex K,
      x ∈ Metric.ball i0.center (Metric.infDist i0.center K / 4) := by
    have hsub := SardConvexDomain.compl_subset_iUnion_whitneyNetQuarterBalls hK hKn
    simpa using Set.mem_iUnion.1 (hsub hxK)
  obtain ⟨U, hUnhds, hTfin⟩ := hlocal x hx
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.1 hUnhds
  obtain ⟨F, hF⟩ := hTfin.exists_finset_coe
  have hzero : ∀ y ∈ V, ∀ i ∉ (F : Set _), psi i y = 0 := by
    intro y hy i hi
    by_contra hne
    exact hi (hF ▸ (show (U ∩ Function.support (psi i)).Nonempty from
      ⟨y, ⟨hVU hy, hne⟩⟩))
  have heq : ∀ y ∈ V, (∑' i, psi i y) = ∑ i ∈ F, psi i y := by
    intro y hy
    rw [tsum_eq_sum (s := F) (fun i hi ↦ hzero y hy i hi)]
  have hi0F : i0 ∈ F := by
    have hne : psi i0 x ≠ 0 := by
      rw [hone i0 hi0]; norm_num
    have : i0 ∈ (↑F : Set _) := hF ▸ ⟨x, ⟨hVU hxV, hne⟩⟩
    exact Finset.mem_coe.1 this
  refine ⟨?_, ?_⟩
  · have h1 : psi i0 x = 1 := hone i0 hi0
    have := Finset.single_le_sum (fun i _ ↦ hnonneg i x) hi0F
    rwa [h1, ← heq x hxV] at this
  · have hsmoothg : ContDiff ℝ ∞ (fun y ↦ ∑ i ∈ F, psi i y) :=
      ContDiff.sum (fun i _ ↦ hsmooth i)
    refine hsmoothg.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hVopen.mem_nhds hxV] with y hy
    exact heq y hy

/-- Uniform, rather than merely pointwise finite, incidence of Whitney half-balls.
Adjacent incident strata have comparable scales; within each stratum the net centers are
uniformly separated and lie in a comparable ball, so a finite-dimensional volume packing
argument using additive Haar measure gives a bound independent of `x`. -/
theorem whitney_bounded_overlap_aux_normalized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (k : ℤ) (x c : E)
    (hc : c ∈ SardConvexDomain.whitneyScaleStratum s k)
    (hxc : x ∈ Metric.ball c (Metric.infDist c s / 2)) :
    SardConvexDomain.whitneyNormalize k x c ∈ Metric.closedBall (0 : E) 1 := by
  apply Metric.mem_closedBall.2
  have hdist : dist c x < (2 : ℝ) ^ (k + 1) / 2 := by
    have h := Metric.mem_ball.1 hxc
    rw [dist_comm]
    exact h.trans (div_lt_div_of_pos_right hc.2.2 (by norm_num))
  exact le_of_lt (calc
    dist (SardConvexDomain.whitneyNormalize k x c) 0 =
        ((2 : ℝ) ^ k)⁻¹ * dist c x := by
      simpa [SardConvexDomain.whitneyNormalize] using
        SardConvexDomain.dist_whitneyNormalize k x c x
    _ < ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ (k + 1) / 2) :=
      mul_lt_mul_of_pos_left hdist (inv_pos.mpr (by positivity))
    _ = 1 := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp)

theorem whitney_bounded_overlap_aux_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (k : ℤ) (x : E) :
    {i : SardConvexDomain.WhitneyNetIndex s | i.1 = k ∧
      x ∈ Metric.ball i.center (Metric.infDist i.center s / 2)}.encard ≤
      Metric.packingNumber ((1 : NNReal) / 8) (Metric.closedBall (0 : E) 1) := by
  let I : Set (SardConvexDomain.WhitneyNetIndex s) := {i | i.1 = k ∧
    x ∈ Metric.ball i.center (Metric.infDist i.center s / 2)}
  let f : SardConvexDomain.WhitneyNetIndex s → E := fun i =>
    SardConvexDomain.whitneyNormalize k x i.center
  have hinj : Set.InjOn f I := by
    intro i hi j hj hij
    have hk : i.1 = j.1 := hi.1.trans hj.1.symm
    have hcent : i.center = j.center := by
      have hz : ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center = 0 := by
        rw [← SardConvexDomain.dist_whitneyNormalize k x i.center j.center]
        have hij' : SardConvexDomain.whitneyNormalize k x i.center =
            SardConvexDomain.whitneyNormalize k x j.center := by simpa [f] using hij
        rw [hij', dist_self]
      exact dist_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
        (ne_of_gt (inv_pos.mpr (by positivity))))
    cases i with
    | mk ik ic =>
      cases j with
      | mk jk jc =>
        dsimp at hk hcent ⊢
        subst jk
        exact congrArg (Sigma.mk ik) (Subtype.ext hcent)
  rw [← hinj.encard_image]
  refine (?_ : Metric.IsSeparated (↑((1 : NNReal) / 8)) (f '' I)).encard_le_packingNumber ?_
  · apply Set.Pairwise.image
    intro (i : SardConvexDomain.WhitneyNetIndex s) hi j hj hne
    have hcne : i.center ≠ j.center := by
      intro h
      apply hne
      have hk : i.1 = j.1 := hi.1.trans hj.1.symm
      cases i with
      | mk ik ic =>
        cases j with
        | mk jk jc =>
          dsimp at hk h ⊢
          subst jk
          exact congrArg (Sigma.mk ik) (Subtype.ext h)
    have hsep := (SardConvexDomain.whitneyStratumNet_spec s k).2.1
      (by rw [← hi.1]; exact i.2.2) (by rw [← hj.1]; exact j.2.2) hcne
    have hr : (2 : ℝ) ^ k / 8 < dist i.center j.center := by
      simpa [SardConvexDomain.whitneyStratumRadius, edist_dist] using hsep
    have hn := SardConvexDomain.dist_whitneyNormalize k x i.center j.center
    have hfixed : (1 / 8 : ℝ) < dist (f i) (f j) := by
      change (1 / 8 : ℝ) < dist (SardConvexDomain.whitneyNormalize k x i.center)
        (SardConvexDomain.whitneyNormalize k x j.center)
      rw [hn]
      calc
        (1 / 8 : ℝ) = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k / 8) := by field_simp
        _ < ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center :=
          mul_lt_mul_of_pos_left hr (inv_pos.mpr (by positivity))
    dsimp only [Function.onFun]
    rw [edist_dist]
    simpa using (ENNReal.ofReal_lt_ofReal_iff
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 8) hfixed)).2 hfixed
  · rintro _ ⟨i, hi, rfl⟩
    exact whitney_bounded_overlap_aux_normalized s k x i.center
      ((SardConvexDomain.whitneyStratumNet_spec s k).1 (by rw [← hi.1]; exact i.2.2)) hi.2

theorem whitney_bounded_overlap
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∃ N : ℕ, ∀ x : E,
      Set.ncard {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} ≤ N := by
  let P := Metric.packingNumber ((1 : NNReal) / 8) (Metric.closedBall (0 : E) 1)
  have hP : P ≠ ⊤ := by
    exact (isCompact_closedBall (0 : E) 1).packingNumber_ne_top _ (by norm_num)
  refine ⟨P.toNat * 5, fun x => ?_⟩
  let I : Set (SardConvexDomain.WhitneyNetIndex K) :=
    {i | x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)}
  have hfin : I.Finite := SardConvexDomain.finite_whitneyNetHalfIncidence K x
  by_cases hne : I.Nonempty
  · obtain ⟨i, hi⟩ := hne
    let J : ℤ → Set (SardConvexDomain.WhitneyNetIndex K) := fun k =>
      {j | j.1 = k ∧ j ∈ I}
    have hJ (k : ℤ) : (J k).ncard ≤ P.toNat := by
      have he := whitney_bounded_overlap_aux_fiber K k x
      have ht := ENat.toNat_le_toNat he hP
      simpa [J, I, P] using ht
    have hsub : I ⊆ J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪ J (i.1 + 2) := by
      intro j hj
      have hb := SardConvexDomain.whitneyStratum_indices_le_add_two_of_mem_half_balls K
        ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2)
        ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2) hi hj
      have hor : j.1 = i.1 - 2 ∨ j.1 = i.1 - 1 ∨ j.1 = i.1 ∨
          j.1 = i.1 + 1 ∨ j.1 = i.1 + 2 := by omega
      rcases hor with e | e | e | e | e <;> simp [J, e, hj]
    have hJfin (k : ℤ) : (J k).Finite := hfin.subset (fun _ h => h.2)
    have hUfin : (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪
        J (i.1 + 2)).Finite :=
      ((((hJfin (i.1 - 2)).union (hJfin (i.1 - 1))).union (hJfin i.1)).union
        (hJfin (i.1 + 1))).union (hJfin (i.1 + 2))
    have hn := Set.ncard_le_ncard hsub hUfin
    have hu1 := Set.ncard_union_le (J (i.1 - 2)) (J (i.1 - 1))
    have hu2 := Set.ncard_union_le (J (i.1 - 2) ∪ J (i.1 - 1)) (J i.1)
    have hu3 := Set.ncard_union_le (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1) (J (i.1 + 1))
    have hu4 := Set.ncard_union_le
      (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1)) (J (i.1 + 2))
    calc
      I.ncard ≤ (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪
        J (i.1 + 2)).ncard := hn
      _ ≤ (J (i.1 - 2)).ncard + (J (i.1 - 1)).ncard + (J i.1).ncard +
          (J (i.1 + 1)).ncard + (J (i.1 + 2)).ncard := by
        omega
      _ ≤ P.toNat * 5 := by
        have h1 := hJ (i.1 - 2)
        have h2 := hJ (i.1 - 1)
        have h3 := hJ i.1
        have h4 := hJ (i.1 + 1)
        have h5 := hJ (i.1 + 2)
        omega
  · have hz : {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      simpa [I] using hne
    rw [hz]
    simp

/-- Scale-correct derivative bounds for a reciprocal.  For each order and list of input
bounds there is a universal output bound: differentiate `S * S⁻¹ = 1`, isolate the top
derivative of `S⁻¹`, and induct using the multilinear Leibniz formula and `1 ≤ S x`. -/
theorem iteratedFDeriv_inv_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (A : ℕ → ℝ) :
    ∃ B ≥ 0, ∀ (S : E → ℝ) (x : E) (r : ℝ), 0 < r → 1 ≤ S x →
      ContDiffAt ℝ k S x →
      (∀ j ≤ k, ‖iteratedFDeriv ℝ j S x‖ ≤ A j * r⁻¹ ^ j) →
      ‖iteratedFDeriv ℝ k (fun y ↦ (S y)⁻¹) x‖ ≤ B * r⁻¹ ^ k := by
  -- Total scale of the input bounds; absorbs every `A j`.
  set M : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), |A j| with hMdef
  have hM1 : 1 ≤ M := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun j _ => abs_nonneg (A j))
    linarith
  refine ⟨(k.factorial : ℝ) * (k.factorial : ℝ) * M ^ k, by positivity, ?_⟩
  intro S x r hr hSx hS hA
  have hrinv : 0 < r⁻¹ := inv_pos.2 hr
  have hSx0 : (0 : ℝ) < S x := zero_lt_one.trans_le hSx
  -- An open neighborhood of `x` where `S` is `C^k` and `S > 1/2`.
  obtain ⟨u, hu, hSu⟩ := hS.contDiffOn (m := (k : WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨u₀, hu₀u, hu₀open, hxu₀⟩ := mem_nhds_iff.1 hu
  have hcont : ContinuousAt S x := hS.continuousAt
  have hs₀ : u₀ ∩ S ⁻¹' Set.Ioi (1 / 2 : ℝ) ∈ nhds x :=
    Filter.inter_mem (hu₀open.mem_nhds hxu₀)
      (hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by linarith : (1 / 2 : ℝ) < S x)))
  obtain ⟨s, hss₀, hsopen, hxs⟩ := mem_nhds_iff.1 hs₀
  have hSus : ContDiffOn ℝ (k : WithTop ℕ∞) S s :=
    hSu.mono (hss₀.trans (Set.inter_subset_left.trans hu₀u))
  have hmap : Set.MapsTo S s (Set.Ioi (1 / 2 : ℝ)) := fun y hy => (hss₀ hy).2
  -- Derivative bounds for `Inv.inv` at `S x ≥ 1`.
  have hC : ∀ i, i ≤ k →
      ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) (Set.Ioi (1 / 2 : ℝ)) (S x)‖ ≤ (k.factorial : ℝ) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi
      (by simp only [Set.mem_Ioi]; linarith : S x ∈ Set.Ioi (1 / 2 : ℝ))]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hform : iteratedDeriv i (Inv.inv : ℝ → ℝ) (S x) =
        (-1 : ℝ) ^ i * (i.factorial : ℝ) * (S x) ^ (-1 - i : ℤ) := by
      rw [iteratedDeriv_eq_iterate]; exact iter_deriv_inv i (S x)
    rw [hform]
    have hzp : (0 : ℝ) < (S x) ^ (-1 - i : ℤ) := zpow_pos hSx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      show |(-1 : ℝ) ^ i| = 1 by rw [abs_pow, abs_neg, abs_one, one_pow],
      show |(i.factorial : ℝ)| = (i.factorial : ℝ) from abs_of_nonneg (by positivity),
      show |(S x) ^ (-1 - i : ℤ)| = (S x) ^ (-1 - i : ℤ) from abs_of_pos hzp,
      one_mul]
    calc (i.factorial : ℝ) * (S x) ^ (-1 - i : ℤ) ≤ (k.factorial : ℝ) * 1 := by
          apply mul_le_mul
          · exact_mod_cast Nat.factorial_le hi
          · exact zpow_le_one_of_nonpos₀ hSx (by omega)
          · exact hzp.le
          · positivity
      _ = (k.factorial : ℝ) := mul_one _
  -- Geometric bound for the derivatives of `S`.
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i S s x‖ ≤ (r⁻¹ * M) ^ i := by
    intro i hi1 hik
    rw [iteratedFDerivWithin_of_isOpen i hsopen hxs]
    have hAi : A i ≤ M := by
      calc A i ≤ |A i| := le_abs_self _
        _ ≤ ∑ j ∈ Finset.range (k + 1), |A j| :=
            Finset.single_le_sum (f := fun j ↦ |A j|) (fun j _ => abs_nonneg _)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hik))
        _ ≤ M := by linarith
    calc ‖iteratedFDeriv ℝ i S x‖ ≤ A i * r⁻¹ ^ i := hA i hik
      _ ≤ M * r⁻¹ ^ i := mul_le_mul_of_nonneg_right hAi (pow_nonneg hrinv.le _)
      _ ≤ M ^ i * r⁻¹ ^ i := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hrinv.le _)
          have h : (M : ℝ) ^ 1 ≤ M ^ i := pow_le_pow_right₀ hM1 (by omega)
          rwa [pow_one] at h
      _ = (r⁻¹ * M) ^ i := by rw [mul_pow]; ring
  -- Composition bound.
  have hg : ContDiffOn ℝ (k : WithTop ℕ∞) (Inv.inv : ℝ → ℝ) (Set.Ioi (1 / 2 : ℝ)) :=
    (contDiffOn_inv ℝ).mono fun y hy =>
      ne_of_gt (lt_trans (show (0:ℝ) < 1 / 2 by norm_num) (Set.mem_Ioi.1 hy))
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hg hSus le_rfl
    isOpen_Ioi.uniqueDiffOn hsopen.uniqueDiffOn hmap hxs hC hD
  rw [iteratedFDerivWithin_of_isOpen k hsopen hxs] at key
  have hcomp : (Inv.inv : ℝ → ℝ) ∘ S = fun y ↦ (S y)⁻¹ := rfl
  rw [hcomp] at key
  calc ‖iteratedFDeriv ℝ k (fun y ↦ (S y)⁻¹) x‖
      ≤ (k.factorial : ℝ) * (k.factorial : ℝ) * (r⁻¹ * M) ^ k := key
    _ = (k.factorial : ℝ) * (k.factorial : ℝ) * M ^ k * r⁻¹ ^ k := by rw [mul_pow]; ring

/-- A smooth function vanishing outside an open ball has every iterated derivative vanishing
outside it, including on the sphere. For `r ≤ 0` the function is zero. Outside the closed ball
the function is zero near the point. On the sphere, points `x + t • (x - c)` with `t > 0` lie
outside the closed ball and tend to `x`, so use continuity of the iterated derivative. -/
theorem iteratedFDeriv_eq_zero_of_support_subset_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ ∞ u) {c : E} {r : ℝ}
    (hsupp : Function.support u ⊆ Metric.ball c r) (k : ℕ) {x : E}
    (hx : x ∉ Metric.ball c r) : iteratedFDeriv ℝ k u x = 0 := by
  by_cases hr : 0 < r
  swap
  · have hu0 : u = 0 := by
      funext y
      by_contra hy
      have hyball := hsupp (show y ∈ Function.support u from hy)
      exact (not_lt_of_ge (le_of_not_gt hr))
        (lt_of_le_of_lt (dist_nonneg : 0 ≤ dist y c) (by simpa [dist_comm] using hyball))
    subst u
    simp
  by_contra hxderiv
  have hxderiv' : x ∈ Function.support (iteratedFDeriv ℝ k u) := hxderiv
  have hopen : IsOpen (Function.support (iteratedFDeriv ℝ k u)) :=
    (hu.continuous_iteratedFDeriv (mod_cast le_top)).isOpen_support
  have hclosed : Function.support (iteratedFDeriv ℝ k u) ⊆ Metric.closedBall c r :=
    (support_iteratedFDeriv_subset k).trans
      (closure_minimal (hsupp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hxint : x ∈ interior (Metric.closedBall c r) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hopen.mem_nhds hxderiv') hclosed
  rw [interior_closedBall c hr.ne'] at hxint
  exact hx hxint

/-- Normalising the bump family gives a partition of unity with derivative bounds at every
order needed by the extension.  Combine the reciprocal leaf with the uniform-overlap leaf,
then apply local finite-sum product estimates and comparability of incident scales. -/
theorem exists_whitneySmoothPartition_aux_deriv_bound_aux_inside
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ)
    (C : ℕ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (psi i))
    (hsupp : ∀ i, Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2))
    (hlocal : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (psi i)).Nonempty}.Finite)
    (hC : ∀ k i x, ‖iteratedFDeriv ℝ k (psi i) x‖ ≤
      C k * (Metric.infDist i.center K)⁻¹ ^ k)
    (hpositive : ∀ x ∉ K, 1 ≤ ∑' i, psi i x)
    (hoverlap : ∃ N : ℕ, ∀ x : E,
      Set.ncard {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} ≤ N) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧ ∀ k i x,
      x ∈ Metric.ball i.center (Metric.infDist i.center K / 2) →
      ‖iteratedFDeriv ℝ k
        (fun y => psi i y * (∑' j, psi j y)⁻¹) x‖ ≤
          D k * (Metric.infDist i.center K)⁻¹ ^ k := by
  classical
  obtain ⟨N, hN⟩ := hoverlap
  -- Uniform scale for the sum derivatives: `A j * dᵢ⁻¹ʲ`.
  set A : ℕ → ℝ := fun j ↦ (N : ℝ) * |C j| * 3 ^ j with hAdef
  have hBall : ∀ k : ℕ, ∃ B ≥ 0, ∀ (S : E → ℝ) (x : E) (r : ℝ), 0 < r → 1 ≤ S x →
      ContDiffAt ℝ k S x → (∀ j ≤ k, ‖iteratedFDeriv ℝ j S x‖ ≤ A j * r⁻¹ ^ j) →
      ‖iteratedFDeriv ℝ k (fun y ↦ (S y)⁻¹) x‖ ≤ B * r⁻¹ ^ k :=
    fun k ↦ iteratedFDeriv_inv_bound E k A
  choose B hBnn hB using hBall
  refine ⟨fun k ↦ ∑ p ∈ Finset.range (k + 1), (k.choose p : ℝ) * |C p| * (B (k - p)),
    fun k ↦ Finset.sum_nonneg fun p _ ↦ by
      have h0 := (hBnn (k - p))
      positivity, ?_⟩
  intro k i x hx
  set di : ℝ := Metric.infDist i.center K with hdidef
  have hdi : 0 < di :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ i.1)
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.1
  have hdpos : ∀ l : SardConvexDomain.WhitneyNetIndex K,
      0 < Metric.infDist l.center K :=
    fun l ↦ lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ l.1)
      ((SardConvexDomain.whitneyStratumNet_spec K l.1).1 l.2.2).2.1
  have hxK : x ∉ K := by
    intro hxm
    have hle := Metric.infDist_le_dist_of_mem (x := i.center) hxm
    rw [dist_comm] at hle
    have hlt : dist x i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hx
    linarith
  set S : E → ℝ := fun y ↦ ∑' j, psi j y with hSdef
  have hSx : 1 ≤ S x := hpositive x hxK
  have hcomp_i0 := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hx
  rw [← hdidef] at hcomp_i0
  have hcomp_i := hcomp_i0
  -- The half-ball incidence set at `x`.
  set Fset : Set (SardConvexDomain.WhitneyNetIndex K) :=
    {l | x ∈ Metric.ball l.center (Metric.infDist l.center K / 2)} with hFsetdef
  have hFfin : Fset.Finite := by
    have hfib : ∀ k : ℤ,
        {l : SardConvexDomain.WhitneyNetIndex K | l.1 = k ∧ l ∈ Fset}.Finite := by
      intro k
      let f : SardConvexDomain.WhitneyNetIndex K → E :=
        SardConvexDomain.WhitneyNetIndex.center
      have hinj : Set.InjOn f {l | l.1 = k ∧ l ∈ Fset} := by
        intro a ha b hb hab
        have hk : a.1 = b.1 := ha.1.trans hb.1.symm
        cases a with
        | mk ak ac =>
          cases b with
          | mk bk bc =>
            dsimp at hk hab ⊢
            subst bk
            exact congrArg (Sigma.mk ak) (Subtype.ext hab)
      apply Set.Finite.of_finite_image (f := f) _ hinj
      apply (SardConvexDomain.finite_inter_whitneyStratumNet_of_isCompact K k
        (isCompact_closedBall x (3 * di))).subset
      rintro c ⟨l, hl, rfl⟩
      constructor
      · change l.2.1 ∈ SardConvexDomain.whitneyStratumNet K k
        rw [← hl.1]
        exact l.2.2
      · apply Metric.mem_closedBall.2
        have hlt : dist x l.center < Metric.infDist l.center K / 2 :=
          Metric.mem_ball.1 hl.2
        have hcomp := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hl.2
        have hdc : dist l.center x = dist x l.center := dist_comm _ _
        show dist l.center x ≤ 3 * di
        linarith [hcomp.1, hcomp_i.2]
    apply (Set.Finite.biUnion (Finset.finite_toSet (Finset.Icc (i.1 - 2) (i.1 + 2)))
      (fun k _ ↦ hfib k)).subset
    intro l hl
    have hlo : (2 : ℝ) ^ l.1 ≤ Metric.infDist l.center K :=
      ((SardConvexDomain.whitneyStratumNet_spec K l.1).1 l.2.2).2.1
    have hup : Metric.infDist l.center K < (2 : ℝ) ^ (l.1 + 1) :=
      ((SardConvexDomain.whitneyStratumNet_spec K l.1).1 l.2.2).2.2
    have hcomp := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hl
    have hloi : (2 : ℝ) ^ i.1 ≤ di :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.1
    have hupi : di < 2 * (2 : ℝ) ^ i.1 := by
      have h : di < (2 : ℝ) ^ (i.1 + 1) :=
        ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.2
      rw [zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one] at h
      linarith [h]
    have hup2 : Metric.infDist l.center K < 2 * (2 : ℝ) ^ l.1 := by
      rw [zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one] at hup
      linarith [hup]
    have hk1 : i.1 - 2 ≤ l.1 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (l.1 + 3) ≤ (2 : ℝ) ^ i.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)] at hp
      norm_num at hp
      have hpl : (0 : ℝ) < (2 : ℝ) ^ l.1 := by positivity
      nlinarith
    have hk2 : l.1 ≤ i.1 + 2 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (i.1 + 3) ≤ (2 : ℝ) ^ l.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)] at hp
      norm_num at hp
      have hpi : (0 : ℝ) < (2 : ℝ) ^ i.1 := by positivity
      nlinarith
    exact Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨Finset.mem_Icc.2 ⟨hk1, hk2⟩, rfl, hl⟩⟩
  set Fs := hFfin.toFinset with hFsdef
  have hcard : (Fs.card : ℝ) ≤ N := by
    have h1 := hN x
    rw [Set.ncard_eq_toFinset_card _ hFfin] at h1
    exact_mod_cast h1
  -- Local finiteness data at `x`.
  obtain ⟨U, hU, hT⟩ := hlocal x hxK
  have hxU : x ∈ U := mem_of_mem_nhds hU
  set TF := hT.toFinset with hTFdef
  have hG : ContDiff ℝ ∞ (fun y ↦ ∑ l ∈ TF, psi l y) :=
    ContDiff.sum fun l _ ↦ hsmooth l
  have hSG : S =ᶠ[nhds x] (fun y ↦ ∑ l ∈ TF, psi l y) := by
    filter_upwards [hU] with y hy
    exact tsum_eq_sum (fun l hl ↦ by
      by_contra hne
      exact hl (hT.mem_toFinset.2 ⟨y, hy, hne⟩))
  have hSc : ContDiffAt ℝ ∞ S x := hG.contDiffAt.congr_of_eventuallyEq hSG
  -- Every derivative of the sum at `x` is the sum over the incident indices.
  have hsum : ∀ j : ℕ, iteratedFDeriv ℝ j S x =
      ∑ l ∈ Fs, iteratedFDeriv ℝ j (psi l) x := by
    intro j
    have h1 : iteratedFDeriv ℝ j S x =
        iteratedFDeriv ℝ j (fun y ↦ ∑ l ∈ TF, psi l y) x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hSG j).eq_of_nhds
    rw [h1, iteratedFDeriv_fun_sum_apply (fun l _ ↦ (hsmooth l).contDiffAt.of_le (mod_cast le_top))]
    have hA1 : ∑ l ∈ TF, iteratedFDeriv ℝ j (psi l) x =
        ∑ l ∈ TF ∩ Fs, iteratedFDeriv ℝ j (psi l) x := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro l _hlT hlnot
      have hxnot : x ∉ Metric.ball l.center (Metric.infDist l.center K / 2) := by
        intro hb
        exact hlnot (Finset.mem_inter.2 ⟨_hlT, hFfin.mem_toFinset.2 hb⟩)
      exact iteratedFDeriv_eq_zero_of_support_subset_ball (hsmooth l) (hsupp l) j hxnot
    have hA2 : ∑ l ∈ Fs, iteratedFDeriv ℝ j (psi l) x =
        ∑ l ∈ TF ∩ Fs, iteratedFDeriv ℝ j (psi l) x := by
      symm
      apply Finset.sum_subset Finset.inter_subset_right
      intro l hlF hlnot
      have hlT : l ∉ TF := fun h ↦ hlnot (Finset.mem_inter.2 ⟨h, hlF⟩)
      have hzero : psi l =ᶠ[nhds x] 0 := by
        filter_upwards [hU] with y hy
        by_contra hne
        exact hlT (hT.mem_toFinset.2 ⟨y, hy, hne⟩)
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hzero j).eq_of_nhds]
      simp
    rw [hA1, ← hA2]
  -- Scale bound for the derivatives of `S` at `x`.
  have hSbound : ∀ j : ℕ, ‖iteratedFDeriv ℝ j S x‖ ≤ A j * di⁻¹ ^ j := by
    intro j
    rw [hsum j]
    calc ‖∑ l ∈ Fs, iteratedFDeriv ℝ j (psi l) x‖
        ≤ ∑ l ∈ Fs, ‖iteratedFDeriv ℝ j (psi l) x‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Fs, |C j| * (3 * di⁻¹) ^ j := by
          apply Finset.sum_le_sum
          intro l hl
          have hlF : l ∈ Fset := hFfin.mem_toFinset.1 hl
          have hcomp := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hlF
          have h1 : di < 3 * Metric.infDist l.center K := lt_trans hcomp_i.1 hcomp.2
          have h2 : (Metric.infDist l.center K)⁻¹ ≤ 3 * di⁻¹ := by
            calc (Metric.infDist l.center K)⁻¹ ≤ (di / 3)⁻¹ :=
                  inv_anti₀ (by positivity) (by linarith)
              _ = 3 * di⁻¹ := by rw [inv_div, div_eq_mul_inv]
          have hC0 : 0 ≤ (Metric.infDist l.center K)⁻¹ ^ j :=
            pow_nonneg (inv_nonneg.2 (hdpos l).le) _
          calc ‖iteratedFDeriv ℝ j (psi l) x‖
              ≤ C j * (Metric.infDist l.center K)⁻¹ ^ j := hC j l x
            _ ≤ |C j| * (Metric.infDist l.center K)⁻¹ ^ j :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hC0
            _ ≤ |C j| * (3 * di⁻¹) ^ j :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (inv_nonneg.2 (hdpos l).le) h2 j) (abs_nonneg _)
      _ = (Fs.card : ℝ) * (|C j| * (3 * di⁻¹) ^ j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (|C j| * (3 * di⁻¹) ^ j) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = A j * di⁻¹ ^ j := by rw [hAdef, mul_pow]; ring
  -- An open neighborhood of `x` where `S` is smooth and `> 1/2`.
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.1 hU
  have hGV : ∀ y ∈ V, S y = ∑ l ∈ TF, psi l y := fun y hy ↦ by
    have hyn : V ∈ nhds y := hVopen.mem_nhds hy
    have : S =ᶠ[nhds y] (fun z ↦ ∑ l ∈ TF, psi l z) := by
      filter_upwards [hyn] with z hz
      exact tsum_eq_sum (fun l hl ↦ by
        by_contra hne
        exact hl (hT.mem_toFinset.2 ⟨z, hVU hz, hne⟩))
    exact this.eq_of_nhds
  have hSGV : EqOn S (fun y ↦ ∑ l ∈ TF, psi l y) V := fun y hy ↦ hGV y hy
  have hSon : ContDiffOn ℝ ∞ S V := hG.contDiffOn.congr hSGV
  have hcont : ContinuousAt S x := hSc.continuousAt
  have hsV : V ∩ S ⁻¹' Set.Ioi (1 / 2 : ℝ) ∈ nhds x :=
    Filter.inter_mem (hVopen.mem_nhds hxV)
      (hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by linarith : (1 / 2 : ℝ) < S x)))
  obtain ⟨s, hssV, hsopen, hxs⟩ := mem_nhds_iff.1 hsV
  have hmapS : Set.MapsTo S s (Set.Ioi (1 / 2 : ℝ)) := fun y hy ↦ (hssV hy).2
  have hSs : ContDiffOn ℝ ∞ S s := hSon.mono (hssV.trans Set.inter_subset_left)
  have hSinv : ContDiffOn ℝ ∞ (fun y ↦ (S y)⁻¹) s :=
    hSs.inv fun y hy ↦ ne_of_gt (lt_trans (by norm_num) (hmapS hy))
  -- Product (Leibniz) bound on `s`, then convert to global derivatives.
  have hprod := norm_iteratedFDerivWithin_mul_le
    (f := psi i) (g := fun y ↦ (S y)⁻¹) (N := (∞ : WithTop ℕ∞)) (n := k)
    ((hsmooth i).contDiffOn.mono (Set.subset_univ s))
    hSinv (hsopen.uniqueDiffOn) hxs (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hsopen hxs] at hprod
  have hconv1 : ∀ p : ℕ, iteratedFDerivWithin ℝ p (psi i) s x =
      iteratedFDeriv ℝ p (psi i) x :=
    fun p ↦ iteratedFDerivWithin_of_isOpen p hsopen hxs
  have hconv2 : ∀ p : ℕ, ‖iteratedFDerivWithin ℝ p (fun y ↦ (S y)⁻¹) s x‖ ≤
      (B p) * di⁻¹ ^ p := by
    intro p
    rw [iteratedFDerivWithin_of_isOpen p hsopen hxs]
    have h0 := (hBnn p)
    have h1 := hB p S x di hdi hSx (hSc.of_le (mod_cast le_top))
      (fun j _ ↦ hSbound j)
    exact h1
  calc ‖iteratedFDeriv ℝ k (fun y => psi i y * (S y)⁻¹) x‖
      ≤ ∑ p ∈ Finset.range (k + 1), (k.choose p : ℝ) * |C p| * di⁻¹ ^ p *
          ((B (k - p)) * di⁻¹ ^ (k - p)) := by
        refine hprod.trans (Finset.sum_le_sum fun p hp ↦ ?_)
        have hpk : p ≤ k := Nat.le_of_lt_succ (Finset.mem_range.1 hp)
        have h1 : ‖iteratedFDerivWithin ℝ p (psi i) s x‖ ≤ |C p| * di⁻¹ ^ p := by
          rw [hconv1 p]
          calc ‖iteratedFDeriv ℝ p (psi i) x‖ ≤ C p * di⁻¹ ^ p := hC p i x
            _ ≤ |C p| * di⁻¹ ^ p :=
                mul_le_mul_of_nonneg_right (le_abs_self _)
                  (pow_nonneg (inv_nonneg.2 hdi.le) _)
        have h2 : ‖iteratedFDerivWithin ℝ (k - p) (fun y ↦ (S y)⁻¹) s x‖ ≤
            (B (k - p)) * di⁻¹ ^ (k - p) := hconv2 (k - p)
        have hc0 : (0 : ℝ) ≤ (k.choose p : ℝ) := by positivity
        have hX0 : (0 : ℝ) ≤ |C p| * di⁻¹ ^ p := by positivity
        have hY0 : (0 : ℝ) ≤ (B (k - p)) * di⁻¹ ^ (k - p) := by
          have := (hBnn (k - p))
          positivity
        have h3 : (k.choose p : ℝ) * ‖iteratedFDerivWithin ℝ p (psi i) s x‖ ≤
            (k.choose p : ℝ) * |C p| * di⁻¹ ^ p := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left h1 hc0
        exact mul_le_mul h3 h2 (norm_nonneg _)
          (mul_nonneg (mul_nonneg hc0 (abs_nonneg _)) (pow_nonneg (inv_nonneg.2 hdi.le) _))
    _ = (∑ p ∈ Finset.range (k + 1), (k.choose p : ℝ) * |C p| * (B (k - p))) *
          di⁻¹ ^ k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        have hpk : p ≤ k := Nat.le_of_lt_succ (Finset.mem_range.1 hp)
        have hpow : di⁻¹ ^ p * di⁻¹ ^ (k - p) = di⁻¹ ^ k := by
          rw [← pow_add, Nat.add_sub_cancel' hpk]
        calc (k.choose p : ℝ) * |C p| * di⁻¹ ^ p * ((B (k - p)) * di⁻¹ ^ (k - p))
            = (k.choose p : ℝ) * |C p| * (B (k - p)) * (di⁻¹ ^ p * di⁻¹ ^ (k - p)) :=
              by ring
          _ = (k.choose p : ℝ) * |C p| * (B (k - p)) * di⁻¹ ^ k := by rw [hpow]

theorem exists_whitneySmoothPartition_aux_deriv_bound_aux_outside_aux_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {c x : E} {r : ℝ}
    (hu : ContDiffAt ℝ ∞ u x)
    (hsupp : Function.support u ⊆ Metric.ball c r)
    (hx : x ∉ Metric.ball c r) (k : ℕ) :
    iteratedFDeriv ℝ k u x = 0 := by
  by_cases hr : 0 < r
  swap
  · have hu0 : u = 0 := by
      funext y
      by_contra hy
      have hyball := hsupp (show y ∈ Function.support u from hy)
      exact (not_lt_of_ge (le_of_not_gt hr))
        (lt_of_le_of_lt (dist_nonneg : 0 ≤ dist y c) (by simpa [dist_comm] using hyball))
    subst u
    simp
  by_contra hxderiv
  have hcont : ContinuousAt (iteratedFDeriv ℝ k u) x :=
    hu.continuousAt_iteratedFDeriv (mod_cast le_top)
  have hn : {y | iteratedFDeriv ℝ k u y ≠ 0} ∈ nhds x :=
    hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hxderiv)
  have hclosed : Function.support (iteratedFDeriv ℝ k u) ⊆ Metric.closedBall c r :=
    (support_iteratedFDeriv_subset k).trans
      (closure_minimal (hsupp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hxint : x ∈ interior (Metric.closedBall c r) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset hn hclosed
  exact hx (by simpa only [interior_closedBall c hr.ne'] using hxint)

theorem exists_whitneySmoothPartition_aux_deriv_bound_aux_outside
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (psi i))
    (hsupp : ∀ i, Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2))
    (hlocal : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (psi i)).Nonempty}.Finite)
    (hpositive : ∀ x ∉ K, 1 ≤ ∑' i, psi i x) :
    ∀ k i x, x ∉ Metric.ball i.center (Metric.infDist i.center K / 2) →
      iteratedFDeriv ℝ k
        (fun y => psi i y * (∑' j, psi j y)⁻¹) x = 0 := by
  intro k i x hx
  let r := Metric.infDist i.center K / 2
  let u : E → ℝ := fun y => psi i y * (∑' j, psi j y)⁻¹
  have husupp : Function.support u ⊆ Metric.ball i.center r := by
    intro y hy
    by_contra hyball
    have hpsi : psi i y = 0 := by
      by_contra hne
      exact hyball (hsupp i (show y ∈ Function.support (psi i) from hne))
    exact hy (by simp [u, hpsi])
  by_cases hxc : x ∈ Metric.closedBall i.center r
  · have hdist : dist x i.center = r := by
      apply le_antisymm
      · simpa [Metric.mem_closedBall, dist_comm] using hxc
      · exact le_of_not_gt (by simpa [r, Metric.mem_ball, dist_comm] using hx)
    have hdpos : 0 < Metric.infDist i.center K := by
      have hlo := ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.1
      exact lt_of_lt_of_le (by positivity : 0 < (2 : ℝ) ^ i.1) hlo
    have hxK : x ∉ K := by
      intro hxmem
      have hle := Metric.infDist_le_dist_of_mem (x := i.center) hxmem
      rw [dist_comm, hdist] at hle
      dsimp [r] at hle
      linarith
    obtain ⟨U, hUnhds, hTfin⟩ := hlocal x hxK
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.1 hUnhds
    obtain ⟨F, hF⟩ := hTfin.exists_finset_coe
    have hzero : ∀ y ∈ V, ∀ j ∉ (F : Set _), psi j y = 0 := by
      intro y hy j hj
      by_contra hne
      exact hj (hF ▸ (show (U ∩ Function.support (psi j)).Nonempty from
        ⟨y, ⟨hVU hy, hne⟩⟩))
    have heq : ∀ y ∈ V, (∑' j, psi j y) = ∑ j ∈ F, psi j y := by
      intro y hy
      rw [tsum_eq_sum (s := F) (fun j hj ↦ hzero y hy j hj)]
    have hsum : ContDiffAt ℝ ∞ (fun y => ∑' j, psi j y) x := by
      have hf : ContDiff ℝ ∞ (fun y => ∑ j ∈ F, psi j y) :=
        ContDiff.sum (fun j _ ↦ hsmooth j)
      refine hf.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      exact heq y hy
    have hsum0 : (∑' j, psi j x) ≠ 0 := by
      have hp := hpositive x hxK
      linarith
    have hu : ContDiffAt ℝ ∞ u x := by
      exact (hsmooth i).contDiffAt.mul (hsum.inv hsum0)
    exact exists_whitneySmoothPartition_aux_deriv_bound_aux_outside_aux_local
      hu husupp (by simpa [r] using hx) k
  · have hevent : u =ᶠ[nhds x] 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxc] with y hy
      have hyball : y ∉ Metric.ball i.center r :=
        fun h => hy (Metric.ball_subset_closedBall h)
      have hpsi : psi i y = 0 := by
        by_contra hne
        exact hyball (hsupp i (show y ∈ Function.support (psi i) from hne))
      simp [u, hpsi]
    exact ((Filter.EventuallyEq.iteratedFDeriv ℝ hevent k).eq_of_nhds :
      iteratedFDeriv ℝ k u x = iteratedFDeriv ℝ k 0 x) |>.trans (by simp)

theorem exists_whitneySmoothPartition_aux_deriv_bound
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ)
    (C : ℕ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (psi i))
    (hsupp : ∀ i, Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2))
    (hlocal : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (psi i)).Nonempty}.Finite)
    (hC : ∀ k i x, ‖iteratedFDeriv ℝ k (psi i) x‖ ≤
      C k * (Metric.infDist i.center K)⁻¹ ^ k)
    (hpositive : ∀ x ∉ K, 1 ≤ ∑' i, psi i x)
    (hoverlap : ∃ N : ℕ, ∀ x : E,
      Set.ncard {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} ≤ N) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧ ∀ k i x,
      ‖iteratedFDeriv ℝ k
        (fun y => psi i y * (∑' j, psi j y)⁻¹) x‖ ≤
          D k * (Metric.infDist i.center K)⁻¹ ^ k := by
  obtain ⟨D, hD0, hD⟩ :=
    exists_whitneySmoothPartition_aux_deriv_bound_aux_inside E psi C hsmooth hsupp
      hlocal hC hpositive hoverlap
  refine ⟨D, hD0, ?_⟩
  intro k i x
  by_cases hx : x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)
  · exact hD k i x hx
  · rw [exists_whitneySmoothPartition_aux_deriv_bound_aux_outside E psi hsmooth hsupp
      hlocal hpositive k i x hx, norm_zero]
    exact mul_nonneg (hD0 k) (pow_nonneg (inv_nonneg.2 Metric.infDist_nonneg) _)

theorem exists_whitneySmoothPartition
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    Nonempty (WhitneySmoothPartition E K) := by
  obtain ⟨psi, hsmooth, hbnd, hone, hsupp, hlocal, C, hC⟩ :=
    exists_whitney_bump_family E hK hKn
  obtain ⟨N, hN⟩ := whitney_bounded_overlap E hK hKn
  let S : E → ℝ := fun x => ∑' i, psi i x
  let phi : SardConvexDomain.WhitneyNetIndex K → E → ℝ := fun i x => psi i x * (S x)⁻¹
  have hpsiK : ∀ i, ∀ x ∈ K, psi i x = 0 := by
    intro i x hx
    by_contra hne
    have hb := hsupp i (show x ∈ Function.support (psi i) from hne)
    have hd := Metric.mem_ball.1 hb
    rw [dist_comm] at hd
    have hle : Metric.infDist i.center K ≤ dist i.center x :=
      Metric.infDist_le_dist_of_mem hx
    have hc : i.center ∉ K :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).1
    have hdpos := (hK.notMem_iff_infDist_pos hKn).1 hc
    linarith
  have hSsmooth : ∀ x ∉ K, 1 ≤ S x ∧ ContDiffAt ℝ ∞ S x := by
    intro x hx
    simpa [S] using whitney_bump_sum_positive_smooth hK hKn psi
      (fun i x => (hbnd i x).1) hone hsupp hlocal hsmooth x hx
  have hphismooth : ∀ i, ContDiff ℝ ∞ (phi i) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ K
    · have hneigh : Metric.ball x (Metric.infDist i.center K / 4) ∈ nhds x := by
        apply Metric.ball_mem_nhds
        have hc : i.center ∉ K :=
          ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).1
        positivity [((hK.notMem_iff_infDist_pos hKn).1 hc)]
      have hevent : ∀ᶠ y in nhds x, phi i y = 0 := by
        filter_upwards [hneigh] with y hy
        apply mul_eq_zero_of_left
        by_contra hne
        have hb := hsupp i (show y ∈ Function.support (psi i) from hne)
        have hxy : dist y x < Metric.infDist i.center K / 4 := Metric.mem_ball.1 hy
        have hyc : dist y i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hb
        have hcx : Metric.infDist i.center K ≤ dist i.center x :=
          Metric.infDist_le_dist_of_mem hx
        have ht := dist_triangle i.center y x
        rw [dist_comm y i.center] at hyc
        have hc : i.center ∉ K :=
          ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).1
        have hdpos := (hK.notMem_iff_infDist_pos hKn).1 hc
        linarith
      exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ))).contDiffAt).congr_of_eventuallyEq hevent
    · exact (hsmooth i).contDiffAt.mul
        ((hSsmooth x hx).2.inv (ne_of_gt (zero_lt_one.trans_le (hSsmooth x hx).1)))
  have hsum : ∀ x ∉ K, HasSum (fun i => phi i x) 1 := by
    intro x hx
    obtain ⟨U, hU, hfin⟩ := hlocal x hx
    obtain ⟨F, hF⟩ := hfin.exists_finset_coe
    have hz : ∀ i ∉ F, psi i x = 0 := by
      intro i hi
      by_contra hn
      exact hi (Finset.mem_coe.1 (hF ▸ ⟨x, mem_of_mem_nhds hU, hn⟩))
    have hSt : HasSum (fun i => psi i x) (S x) := by
      change HasSum (fun i => psi i x) (∑' i, psi i x)
      exact (summable_of_ne_finset_zero hz).hasSum
    have hpos : 0 < S x := zero_lt_one.trans_le (hSsmooth x hx).1
    simpa [phi, hpos.ne', mul_inv_cancel₀] using hSt.mul_right (S x)⁻¹
  have hsuppphi : ∀ i, Function.support (phi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2) := by
    intro i x hx
    exact hsupp i (fun h => hx (by simp [phi, h]))
  have hnonneg : ∀ i x, 0 ≤ phi i x := by
    intro i x
    by_cases hx : x ∈ K
    · simp [phi, hpsiK i x hx]
    · exact mul_nonneg (hbnd i x).1 (inv_nonneg.2 (le_trans zero_le_one (hSsmooth x hx).1))
  have hlocalphi : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (phi i)).Nonempty}.Finite := by
    intro x hx
    obtain ⟨U, hU, hf⟩ := hlocal x hx
    refine ⟨U, hU, hf.subset ?_⟩
    intro i hi
    obtain ⟨y, hyU, hyphi⟩ := hi
    exact ⟨y, hyU, fun hz => hyphi (by simp [phi, hz])⟩
  obtain ⟨D, hD0, hD⟩ := exists_whitneySmoothPartition_aux_deriv_bound E psi C
    hsmooth hsupp hlocal hC (fun x hx => (hSsmooth x hx).1) ⟨N, hN⟩
  refine ⟨⟨phi, hphismooth, hsuppphi, hnonneg, hsum, hlocalphi, D, hD0, ?_⟩⟩
  simpa [phi, S] using hD

/-- At a point in a partition support, its center, anchor, and scale are uniformly comparable
to the point's distance from `K`.  Combine the half-ball comparison lemmas with the anchor
nearest-point identity and the 1-Lipschitz property of `infDist`. -/
theorem whitney_support_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) {i : SardConvexDomain.WhitneyNetIndex K}
    {x : E} (hx : x ∈ Function.support (P.phi i)) :
    Metric.infDist i.center K ≤ 2 * Metric.infDist x K ∧
      Metric.infDist x K ≤ 2 * Metric.infDist i.center K ∧
      dist x (SardConvexDomain.whitneyNetAnchor hK hKn i) ≤
        3 * Metric.infDist x K := by
  have hxb : x ∈ Metric.ball i.center (Metric.infDist i.center K / 2) :=
    P.support_subset i hx
  have hcomp :=
    SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hxb
  have hc0 : 0 ≤ Metric.infDist i.center K := Metric.infDist_nonneg
  have hdist : dist x i.center < Metric.infDist i.center K / 2 :=
    Metric.mem_ball.1 hxb
  have hanchor := SardConvexDomain.whitneyNetAnchor_nearest hK hKn i
  refine ⟨hcomp.1.le, by linarith, ?_⟩
  calc dist x (SardConvexDomain.whitneyNetAnchor hK hKn i)
      ≤ dist x i.center +
          dist i.center (SardConvexDomain.whitneyNetAnchor hK hKn i) :=
        dist_triangle _ _ _
    _ = dist x i.center + Metric.infDist i.center K := by rw [hanchor]
    _ ≤ Metric.infDist i.center K / 2 + Metric.infDist i.center K := by
        linarith [hdist.le]
    _ ≤ 3 * Metric.infDist x K := by linarith

/-- The off-set Whitney formula is a `tsum`; complement-local finiteness makes it a finite
sum in a neighborhood of every point where it is used. -/
def whitneyOffExtension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (m : ℕ) (f : E → F) (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) (x : E) : F :=
  ∑' i, P.phi i x • taylorPolynomial m (fun k ↦ convexJet k f K)
    (SardConvexDomain.whitneyNetAnchor hK hKn i) x

/-- The Whitney sum is `Cᵐ` on the complement.  Near a complement point reduce the `tsum`
to the finite support family supplied by `locallyFinite_compl`, then use smoothness of each
partition function and the polynomial nature of each Taylor term. -/
theorem whitneyOffExtension_contDiffOn_compl
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f : E → F} (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) :
    ContDiffOn ℝ m (whitneyOffExtension m f hK hKn P) Kᶜ := by
  intro x hx
  rcases P.locallyFinite_compl x hx with ⟨U, hU, hfin⟩
  let S : Finset (SardConvexDomain.WhitneyNetIndex K) := hfin.toFinset
  have hzero : ∀ y ∈ U, ∀ i ∉ S, P.phi i y = 0 := by
    intro y hy i hi
    by_contra hne
    have hys : y ∈ Function.support (P.phi i) := hne
    have hi' : i ∈ {i | (U ∩ Function.support (P.phi i)).Nonempty} := by
      exact ⟨y, hy, hys⟩
    exact hi (by simpa [S] using hi')
  have heq : ∀ y ∈ U,
      whitneyOffExtension m f hK hKn P y =
        ∑ i ∈ S, P.phi i y • taylorPolynomial m (fun k ↦ convexJet k f K)
          (SardConvexDomain.whitneyNetAnchor hK hKn i) y := by
    intro y hy
    unfold whitneyOffExtension
    exact tsum_eq_sum (fun i hi ↦ by simp [hzero y hy i hi])
  have hsmooth : ContDiff ℝ m (fun y : E ↦
      ∑ i ∈ S, P.phi i y • taylorPolynomial m (fun k ↦ convexJet k f K)
        (SardConvexDomain.whitneyNetAnchor hK hKn i) y) := by
    apply ContDiff.sum
    intro i hi
    apply (P.contDiff_phi i).of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) |>.smul
    unfold taylorPolynomial
    apply ContDiff.sum
    intro k hk
    apply contDiff_const.smul
    exact (ContinuousMultilinearMap.contDiff _).comp
      (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)
  apply hsmooth.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq
  · have hUw : ∀ᶠ y in nhdsWithin x Kᶜ, y ∈ U :=
      Filter.Eventually.filter_mono inf_le_left hU
    filter_upwards [hUw] with y hy
    exact heq y hy
  · exact heq x (mem_of_mem_nhds hU)

/-- The exact subtraction identity behind the off-set estimate.  Replace `1` by the locally
finite sum of the partition and distribute the common polynomial; no differentiated
partition-cancellation lemma is needed once subtraction occurs before differentiating. -/
theorem whitneyOffExtension_sub_taylor
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f : E → F}
    (hK : IsClosed K) (hKn : K.Nonempty) (P : WhitneySmoothPartition E K)
    {x a : E} (hx : x ∉ K) :
    whitneyOffExtension m f hK hKn P x -
        taylorPolynomial m (fun j ↦ convexJet j f K) a x =
      ∑' i, P.phi i x •
        (taylorPolynomial m (fun j ↦ convexJet j f K)
            (SardConvexDomain.whitneyNetAnchor hK hKn i) x -
          taylorPolynomial m (fun j ↦ convexJet j f K) a x) := by
  let Q : SardConvexDomain.WhitneyNetIndex K → F := fun i ↦
    taylorPolynomial m (fun j ↦ convexJet j f K)
      (SardConvexDomain.whitneyNetAnchor hK hKn i) x
  let T : F := taylorPolynomial m (fun j ↦ convexJet j f K) a x
  obtain ⟨U, hU, hfin⟩ := P.locallyFinite_compl x hx
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hfinite : (fun i ↦ P.phi i x • Q i).HasFiniteSupport := by
    refine hfin.subset ?_
    intro i hi
    have hphi : P.phi i x ≠ 0 := by
      intro hz
      apply hi
      simp [hz]
    exact ⟨x, hxU, hphi⟩
  have hQ : Summable (fun i ↦ P.phi i x • Q i) :=
    summable_of_hasFiniteSupport hfinite
  have hT : HasSum (fun i ↦ P.phi i x • T) T := by
    simpa using (P.sum_one x hx).smul_const T
  have hsub : HasSum (fun i ↦ P.phi i x • Q i - P.phi i x • T)
      ((∑' i, P.phi i x • Q i) - T) := hQ.hasSum.sub hT
  change (∑' i, P.phi i x • Q i) - T =
    ∑' i, P.phi i x • (Q i - T)
  rw [← hsub.tsum_eq]
  apply tsum_congr
  intro i
  exact (smul_sub (P.phi i x) (Q i) T).symm

/-- The complete finite-overlap estimate near the frontier, now relative to the Taylor
polynomial at a nearest point.  Differentiate the subtraction identity, use
`norm_iteratedFDeriv_smul_le`, `taylor_difference_bound`, support geometry, derivative
bounds, and uniform overlap; each Leibniz term has power `dist(x,K)^(m+1-k)`. -/
/- Variant of `whitney_bounded_overlap_aux_fiber`: stratum-`k` indices whose center is
within `(9/5)·2^(k+1)` of `x` are bounded by one fixed packing number. -/
theorem whitneyOffExtension_jet_bound_aux_fiber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (k : ℤ) (x : E) :
    {i : SardConvexDomain.WhitneyNetIndex K | i.1 = k ∧
      dist x i.center < (9 / 5 : ℝ) * (2 : ℝ) ^ (k + 1)}.encard ≤
      Metric.packingNumber ((1 : NNReal) / 8) (Metric.closedBall (0 : E) 4) := by
  let I : Set (SardConvexDomain.WhitneyNetIndex K) := {i | i.1 = k ∧
    dist x i.center < (9 / 5 : ℝ) * (2 : ℝ) ^ (k + 1)}
  let f : SardConvexDomain.WhitneyNetIndex K → E := fun i =>
    SardConvexDomain.whitneyNormalize k x i.center
  have hinj : Set.InjOn f I := by
    intro i hi j hj hij
    have hk : i.1 = j.1 := hi.1.trans hj.1.symm
    have hcent : i.center = j.center := by
      have hz : ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center = 0 := by
        rw [← SardConvexDomain.dist_whitneyNormalize k x i.center j.center]
        have hij' : SardConvexDomain.whitneyNormalize k x i.center =
            SardConvexDomain.whitneyNormalize k x j.center := by simpa [f] using hij
        rw [hij', dist_self]
      exact dist_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
        (ne_of_gt (inv_pos.mpr (by positivity))))
    cases i with
    | mk ik ic =>
      cases j with
      | mk jk jc =>
        dsimp at hk hcent ⊢
        subst jk
        exact congrArg (Sigma.mk ik) (Subtype.ext hcent)
  rw [← hinj.encard_image]
  refine (?_ : Metric.IsSeparated (↑((1 : NNReal) / 8)) (f '' I)).encard_le_packingNumber ?_
  · apply Set.Pairwise.image
    intro (i : SardConvexDomain.WhitneyNetIndex K) hi j hj hne
    have hcne : i.center ≠ j.center := by
      intro h
      apply hne
      have hk : i.1 = j.1 := hi.1.trans hj.1.symm
      cases i with
      | mk ik ic =>
        cases j with
        | mk jk jc =>
          dsimp at hk h ⊢
          subst jk
          exact congrArg (Sigma.mk ik) (Subtype.ext h)
    have hsep := (SardConvexDomain.whitneyStratumNet_spec K k).2.1
      (by rw [← hi.1]; exact i.2.2) (by rw [← hj.1]; exact j.2.2) hcne
    have hr : (2 : ℝ) ^ k / 8 < dist i.center j.center := by
      simpa [SardConvexDomain.whitneyStratumRadius, edist_dist] using hsep
    have hn := SardConvexDomain.dist_whitneyNormalize k x i.center j.center
    have hfixed : (1 / 8 : ℝ) < dist (f i) (f j) := by
      change (1 / 8 : ℝ) < dist (SardConvexDomain.whitneyNormalize k x i.center)
        (SardConvexDomain.whitneyNormalize k x j.center)
      rw [hn]
      calc
        (1 / 8 : ℝ) = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k / 8) := by field_simp
        _ < ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center :=
          mul_lt_mul_of_pos_left hr (inv_pos.mpr (by positivity))
    dsimp only [Function.onFun]
    rw [edist_dist]
    simpa using (ENNReal.ofReal_lt_ofReal_iff
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 8) hfixed)).2 hfixed
  · rintro _ ⟨i, hi, rfl⟩
    apply Metric.mem_closedBall.2
    have hdist : dist i.center x < (9 / 5 : ℝ) * (2 : ℝ) ^ (k + 1) := by
      rw [dist_comm]; exact hi.2
    refine le_of_lt (calc
      dist (SardConvexDomain.whitneyNormalize k x i.center) 0 =
          ((2 : ℝ) ^ k)⁻¹ * dist i.center x := by
        simpa [SardConvexDomain.whitneyNormalize] using
          SardConvexDomain.dist_whitneyNormalize k x i.center x
      _ < ((2 : ℝ) ^ k)⁻¹ * ((9 / 5 : ℝ) * (2 : ℝ) ^ (k + 1)) :=
        mul_lt_mul_of_pos_left hdist (inv_pos.mpr (by positivity))
      _ = 18 / 5 := by
        have h2k : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        rw [h2k]
        field_simp
        norm_num
      _ ≤ 4 := by norm_num)

/- The half-distance balls meeting the definite ball around a complement point form a
finite set of uniformly bounded cardinality: at most five strata, each packing-bounded. -/
theorem whitneyOffExtension_jet_bound_aux_count
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) {x : E} :
    ∃ S : Finset (SardConvexDomain.WhitneyNetIndex K),
      (∀ i, i ∈ S ↔ (Metric.ball x (Metric.infDist x K / 16) ∩
          Metric.ball i.center (Metric.infDist i.center K / 2)).Nonempty) ∧
      S.card ≤ 5 * (Metric.packingNumber ((1 : NNReal) / 8)
        (Metric.closedBall (0 : E) 4)).toNat := by
  classical
  set d := Metric.infDist x K with hd_def
  set T : Set (SardConvexDomain.WhitneyNetIndex K) :=
    {i | (Metric.ball x (d / 16) ∩
      Metric.ball i.center (Metric.infDist i.center K / 2)).Nonempty} with hT_def
  set P₀ : ℕ∞ := Metric.packingNumber ((1 : NNReal) / 8)
    (Metric.closedBall (0 : E) 4) with hP₀_def
  have hP₀ : P₀ ≠ ⊤ := (isCompact_closedBall (0 : E) 4).packingNumber_ne_top _
    (by norm_num)
  set fib : ℤ → Set (SardConvexDomain.WhitneyNetIndex K) := fun k =>
    {i | i.1 = k ∧ dist x i.center < (9 / 5 : ℝ) * (2 : ℝ) ^ (k + 1)} with hfib_def
  have hfib_encard : ∀ k, (fib k).encard ≤ P₀ := fun k => by
    exact whitneyOffExtension_jet_bound_aux_fiber K k x
  have hfib_fin : ∀ k, (fib k).Finite := fun k => by
    rw [← Set.encard_ne_top_iff]
    exact ((hfib_encard k).trans_lt (lt_top_iff_ne_top.2 hP₀)).ne
  by_cases hT : T.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hT
    obtain ⟨z₀, hz₀x, hz₀b⟩ := hi₀
    have hz₀x' : dist x z₀ < d / 16 := by
      rw [dist_comm]; exact Metric.mem_ball.1 hz₀x
    have hcomp₀ := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hz₀b
    have hlipxz₀ := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := z₀)
    have hlipzx₀ := Metric.infDist_le_infDist_add_dist (s := K) (x := z₀) (y := x)
    rw [dist_comm z₀ x] at hlipzx₀
    have he₀lo : (5 / 8 : ℝ) * d < Metric.infDist i₀.center K := by linarith [hcomp₀.2]
    have he₀hi : Metric.infDist i₀.center K < (17 / 8 : ℝ) * d := by linarith [hcomp₀.1]
    have hspec₀ := (SardConvexDomain.whitneyStratumNet_spec K i₀.1).1 i₀.2.2
    have hsub : T ⊆ ⋃ k ∈ Finset.Icc (i₀.1 - 2) (i₀.1 + 2), fib k := by
      intro i hi
      obtain ⟨z, hzx, hzb⟩ := hi
      have hzx' : dist x z < d / 16 := by
        rw [dist_comm]; exact Metric.mem_ball.1 hzx
      have hcomp := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hzb
      have hlipxz := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := z)
      have hlipzx := Metric.infDist_le_infDist_add_dist (s := K) (x := z) (y := x)
      rw [dist_comm z x] at hlipzx
      have helo : (5 / 8 : ℝ) * d < Metric.infDist i.center K := by linarith [hcomp.2]
      have hehi : Metric.infDist i.center K < (17 / 8 : ℝ) * d := by linarith [hcomp.1]
      have hspec_i := (SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2
      have hsilo : (2 : ℝ) ^ i.1 ≤ Metric.infDist i.center K := hspec_i.2.1
      have hsihi : Metric.infDist i.center K < (2 : ℝ) ^ (i.1 + 1) := hspec_i.2.2
      have hs₀lo : (2 : ℝ) ^ i₀.1 ≤ Metric.infDist i₀.center K := hspec₀.2.1
      have hs₀hi : Metric.infDist i₀.center K < (2 : ℝ) ^ (i₀.1 + 1) := hspec₀.2.2
      have hklo : i₀.1 - 2 ≤ i.1 := by
        by_contra hlt
        push_neg at hlt
        have h1 : (2 : ℝ) ^ (i.1 + 1) ≤ (2 : ℝ) ^ (i₀.1 - 2) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (i₀.1 - 2) = (2 : ℝ) ^ i₀.1 / 4 := by
          rw [show (i₀.1 - 2) = i₀.1 + (-2 : ℤ) from by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num]
          ring
        linarith
      have hkhi : i.1 ≤ i₀.1 + 2 := by
        by_contra hlt
        push_neg at hlt
        have h1 : (2 : ℝ) ^ (i₀.1 + 3) ≤ (2 : ℝ) ^ i.1 :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (i₀.1 + 3) = 8 * (2 : ℝ) ^ i₀.1 := by
          rw [show (i₀.1 + 3) = i₀.1 + (3 : ℤ) from by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            show (2 : ℝ) ^ (3 : ℤ) = 8 from by norm_num]
          ring
        have h5 : (2 : ℝ) ^ (i₀.1 + 1) = 2 * (2 : ℝ) ^ i₀.1 := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
          ring
        linarith
      have hdist : dist x i.center < (9 / 5 : ℝ) * (2 : ℝ) ^ (i.1 + 1) := by
        have hzc : dist z i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hzb
        calc dist x i.center ≤ dist x z + dist z i.center := dist_triangle _ _ _
          _ < d / 16 + Metric.infDist i.center K / 2 := add_lt_add hzx' hzc
          _ < d / 16 + ((17 / 8 : ℝ) * d) / 2 := by linarith [hehi]
          _ = (9 / 8 : ℝ) * d := by ring
          _ = (9 / 5 : ℝ) * ((5 / 8 : ℝ) * d) := by ring
          _ < (9 / 5 : ℝ) * Metric.infDist i.center K :=
            mul_lt_mul_of_pos_left helo (by norm_num)
          _ < (9 / 5 : ℝ) * (2 : ℝ) ^ (i.1 + 1) :=
            mul_lt_mul_of_pos_left hspec_i.2.2 (by norm_num)
      refine Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2
        ⟨Finset.mem_Icc.2 ⟨hklo, hkhi⟩, rfl, hdist⟩⟩
    have hTfin : T.Finite :=
      ((Finset.finite_toSet (Finset.Icc (i₀.1 - 2) (i₀.1 + 2))).biUnion
        (fun k _ ↦ hfib_fin k)).subset hsub
    have henc : T.encard ≤ 5 * P₀ := calc
      T.encard ≤ (⋃ k ∈ Finset.Icc (i₀.1 - 2) (i₀.1 + 2), fib k).encard :=
        Set.encard_le_encard hsub
      _ ≤ ∑ k ∈ Finset.Icc (i₀.1 - 2) (i₀.1 + 2), (fib k).encard :=
        Finset.set_encard_biUnion_le _ _
      _ ≤ ∑ k ∈ Finset.Icc (i₀.1 - 2) (i₀.1 + 2), P₀ :=
        Finset.sum_le_sum (fun k _ ↦ hfib_encard k)
      _ = 5 * P₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.Icc (i₀.1 - 2) (i₀.1 + 2)).card = 5 := by
          rw [Int.card_Icc]
          have h5 : i₀.1 + 2 + 1 - (i₀.1 - 2) = (5 : ℤ) := by omega
          rw [h5]
          rfl
        rw [hcard]
        norm_cast
    have hcast : (5 : ℕ∞) * P₀ = ((5 * P₀.toNat : ℕ) : ℕ∞) := by
      conv_lhs => rw [← ENat.coe_toNat hP₀]
      rw [ENat.coe_mul]
      norm_cast
    refine ⟨hTfin.toFinset, ?_, ?_⟩
    · intro i
      rw [Set.Finite.mem_toFinset]
      rfl
    · calc hTfin.toFinset.card = T.ncard := (Set.ncard_eq_toFinset_card T hTfin).symm
        _ = T.encard.toNat := Set.ncard_def T
        _ ≤ (5 * P₀).toNat :=
          ENat.toNat_le_toNat henc (by rw [hcast]; exact ENat.coe_ne_top _)
        _ = 5 * P₀.toNat := by rw [hcast, ENat.toNat_coe]
  · refine ⟨∅, ?_, by simp⟩
    intro i
    simp only [Finset.notMem_empty, false_iff]
    intro hi
    exact hT ⟨i, hi⟩

/- Iterated derivatives commute with pointwise subtraction of `C^∞` maps. -/
theorem whitneyOffExtension_jet_bound_aux_iteratedFDeriv_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ ψ : E → F} (hφ : ContDiff ℝ (∞ : WithTop ℕ∞) φ) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ) (k : ℕ) :
    ∀ (x : E) (u : Fin k → E),
      iteratedFDeriv ℝ k (fun y ↦ φ y - ψ y) x u =
        iteratedFDeriv ℝ k φ x u - iteratedFDeriv ℝ k ψ x u := by
  induction k with
  | zero =>
    intro x u
    rw [iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro x u
    have hfun : iteratedFDeriv ℝ k (fun z ↦ φ z - ψ z) =
        iteratedFDeriv ℝ k φ - iteratedFDeriv ℝ k ψ := by
      funext y
      rw [Pi.sub_apply]
      ext v
      rw [ContinuousMultilinearMap.sub_apply]
      exact ih y v
    rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left,
      iteratedFDeriv_succ_apply_left, hfun]
    have hlt : (k : WithTop ℕ∞) < (∞ : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.2 (ENat.coe_lt_top k)
    have hA : DifferentiableAt ℝ (iteratedFDeriv ℝ k φ) x :=
      hφ.contDiffAt.differentiableAt_iteratedFDeriv hlt
    have hB : DifferentiableAt ℝ (iteratedFDeriv ℝ k ψ) x :=
      hψ.contDiffAt.differentiableAt_iteratedFDeriv hlt
    rw [fderiv_sub hA hB, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]

theorem whitneyOffExtension_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f : E → F}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) (P : WhitneySmoothPartition E K) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ x ∉ K,
      ∃ a ∈ K, Metric.infDist x K = dist x a ∧
        ‖iteratedFDeriv ℝ k (whitneyOffExtension m f hKc.isClosed
              (hKi.mono interior_subset) P) x -
            iteratedFDeriv ℝ k
              (taylorPolynomial m (fun j ↦ convexJet j f K) a) x‖ ≤
          C * (Metric.infDist x K) ^ (m + 1 - k) := by
  classical
  set hKn : K.Nonempty := hKi.mono interior_subset
  set J : (k : ℕ) → E → E[×k]→L[ℝ] F := fun j ↦ convexJet j f K with hJ_def
  obtain ⟨C₁, hC₁0, hC₁⟩ := taylor_difference_bound hKc hK hKi hf
  set Nn : ℕ := 5 * (Metric.packingNumber ((1 : NNReal) / 8)
    (Metric.closedBall (0 : E) 4)).toNat with hNn_def
  set Wval : ℕ → ℕ → ℝ := fun p j ↦
    (p.choose j : ℝ) * P.derivConstant j * 2 ^ j * 5 ^ (m + 1 - p + j) with hWval_def
  set B : ℝ := ∑ p ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (p + 1), Wval p j
    with hB_def
  have hWval_nn : ∀ p j, 0 ≤ Wval p j := fun p j ↦ by
    rw [hWval_def]
    dsimp only
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (P.derivConstant_nonneg j)) (pow_nonneg (by norm_num) j))
      (pow_nonneg (by norm_num) _)
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun p _ ↦
    Finset.sum_nonneg fun j _ ↦ hWval_nn p j
  have hPa : ∀ c : E, ContDiff ℝ (∞ : WithTop ℕ∞) (taylorPolynomial m J c) :=
    fun c ↦ (taylor_difference_bound_aux_contDiff m J c).of_le le_top
  have hphi : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (P.phi i) := fun i ↦ P.contDiff_phi i
  refine ⟨(Nn : ℝ) * C₁ * B, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₁0) hBnn,
    fun k hk x hx ↦ ?_⟩
  set d := Metric.infDist x K with hd_def
  have hdpos : 0 < d := (hKc.isClosed.notMem_iff_infDist_pos hKn).1 hx
  obtain ⟨a, haK, hda⟩ := hKc.exists_infDist_eq_dist hKn x
  obtain ⟨S, hS, hScard⟩ := whitneyOffExtension_jet_bound_aux_count K (x := x)
  refine ⟨a, haK, hda, ?_⟩
  set anc : SardConvexDomain.WhitneyNetIndex K → E :=
    fun i ↦ SardConvexDomain.whitneyNetAnchor hKc.isClosed hKn i with hanc_def
  set Ta : E → F := taylorPolynomial m J a with hTa_def
  set W : E → F := whitneyOffExtension m f hKc.isClosed hKn P with hW_def
  set W' : E → F := fun y ↦ ∑ i ∈ S, P.phi i y • taylorPolynomial m J (anc i) y
    with hW'_def
  set G : E → F := fun y ↦ ∑ i ∈ S, P.phi i y •
    (taylorPolynomial m J (anc i) y - Ta y) with hG_def
  set V : Set E := Metric.ball x (d / 16) ∩ Kᶜ with hV_def
  have hVnhds : V ∈ nhds x :=
    Filter.inter_mem (Metric.ball_mem_nhds x (by linarith))
      (hKc.isClosed.isOpen_compl.mem_nhds hx)
  have hzeroV : ∀ y ∈ V, ∀ i ∉ S, P.phi i y = 0 := by
    intro y hy i hi
    by_contra hne
    apply hi
    rw [hS i]
    exact ⟨y, hy.1, P.support_subset i (Function.mem_support.2 hne)⟩
  have heqW : W =ᶠ[nhds x] W' := Filter.eventuallyEq_iff_exists_mem.2 ⟨V, hVnhds, fun y hy ↦ by
    rw [hW_def, hW'_def]
    unfold whitneyOffExtension
    exact tsum_eq_sum (fun i hi ↦ by simp [hzeroV y hy i hi])⟩
  have heqG : (fun y ↦ W' y - Ta y) =ᶠ[nhds x] G :=
    Filter.eventuallyEq_iff_exists_mem.2 ⟨V, hVnhds, fun y hy ↦ by
      have h1 : W y - Ta y = G y := by
        rw [hW_def, hG_def, hTa_def]
        rw [whitneyOffExtension_sub_taylor hKc.isClosed hKn P hy.2]
        exact tsum_eq_sum (fun i hi ↦ by simp [hzeroV y hy i hi])
      have h2 : W y = W' y := by
        rw [hW_def, hW'_def]
        unfold whitneyOffExtension
        exact tsum_eq_sum (fun i hi ↦ by simp [hzeroV y hy i hi])
      show W' y - Ta y = G y
      rw [← h2]
      exact h1⟩
  have hW'smooth : ContDiff ℝ (∞ : WithTop ℕ∞) W' := by
    rw [hW'_def]
    exact ContDiff.sum fun i _ ↦ (hphi i).smul (hPa (anc i))
  have hTa_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) Ta := hPa a
  have hGsmooth : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun y ↦ P.phi i y • (taylorPolynomial m J (anc i) y - Ta y)) :=
    fun i ↦ (hphi i).smul ((hPa (anc i)).sub hTa_smooth)
  have E1 : iteratedFDeriv ℝ k W x = iteratedFDeriv ℝ k W' x :=
    (heqW.iteratedFDeriv ℝ k).eq_of_nhds
  have E2 : iteratedFDeriv ℝ k (fun y ↦ W' y - Ta y) x =
      iteratedFDeriv ℝ k W' x - iteratedFDeriv ℝ k Ta x :=
    ContinuousMultilinearMap.ext fun u ↦
      whitneyOffExtension_jet_bound_aux_iteratedFDeriv_sub hW'smooth hTa_smooth k x u
  have E3 : iteratedFDeriv ℝ k (fun y ↦ W' y - Ta y) x = iteratedFDeriv ℝ k G x :=
    (heqG.iteratedFDeriv ℝ k).eq_of_nhds
  rw [E1, ← E2, E3]
  have hGsum : iteratedFDeriv ℝ k G x = ∑ i ∈ S, iteratedFDeriv ℝ k
      (fun y ↦ P.phi i y • (taylorPolynomial m J (anc i) y - Ta y)) x := by
    rw [hG_def]
    exact iteratedFDeriv_fun_sum_apply fun i _ ↦
      ((hGsmooth i).contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)
  rw [hGsum]
  -- Per-index bound, uniform over `S`.
  have hper : ∀ i ∈ S, ‖iteratedFDeriv ℝ k
      (fun y ↦ P.phi i y • (taylorPolynomial m J (anc i) y - Ta y)) x‖ ≤
      C₁ * d ^ (m + 1 - k) * B := by
    intro i hiS
    obtain ⟨z, hzx, hzb⟩ := (hS i).1 hiS
    have hzx' : dist x z < d / 16 := by
      rw [dist_comm]; exact Metric.mem_ball.1 hzx
    set e := Metric.infDist i.center K with he_def
    have hcomp := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hzb
    have hlipxz := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := z)
    have hlipzx := Metric.infDist_le_infDist_add_dist (s := K) (x := z) (y := x)
    rw [dist_comm z x] at hlipzx
    have helo : (5 / 8 : ℝ) * d < e := by linarith [hcomp.2]
    have hehi : e < (17 / 8 : ℝ) * d := by linarith [hcomp.1]
    have he_pos : 0 < e := lt_trans (by positivity) helo
    have hdist : dist x i.center < (9 / 8 : ℝ) * d := by
      have hzc : dist z i.center < e / 2 := Metric.mem_ball.1 hzb
      linarith [dist_triangle x z i.center]
    have hancd : dist x (anc i) ≤ 4 * d := by
      have h1 : dist x (anc i) ≤ dist x i.center + dist i.center (anc i) :=
        dist_triangle _ _ _
      have h2 : dist i.center (anc i) = e := by
        rw [hanc_def]
        dsimp only
        rw [← SardConvexDomain.whitneyNetAnchor_nearest hKc.isClosed hKn i]
      linarith
    have hsm := norm_iteratedFDeriv_smul_le (hphi i) ((hPa (anc i)).sub hTa_smooth) x
      (n := k) (WithTop.coe_le_coe.2 le_top)
    refine hsm.trans ?_
    -- Bound each Leibniz summand.
    have hjb : ∀ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (P.phi i) x‖ *
            ‖iteratedFDeriv ℝ (k - j)
              (fun y ↦ taylorPolynomial m J (anc i) y - Ta y) x‖ ≤
          C₁ * Wval k j * d ^ (m + 1 - k) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hder : ‖iteratedFDeriv ℝ j (P.phi i) x‖ ≤ P.derivConstant j * e⁻¹ ^ j :=
        P.deriv_bound j i x
      have heinv : e⁻¹ ≤ 2 * d⁻¹ := by
        have h1 : e⁻¹ ≤ ((5 / 8 : ℝ) * d)⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by positivity) helo.le
        refine h1.trans ?_
        rw [mul_inv, show ((5 / 8 : ℝ))⁻¹ = 8 / 5 from by norm_num]
        exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hdpos.le)
      have heinvj : e⁻¹ ^ j ≤ (2 * d⁻¹) ^ j :=
        pow_le_pow_left₀ (inv_nonneg.mpr he_pos.le) heinv j
      have hexp : m + 1 - (k - j) = m + 1 - k + j := by omega
      have hancK : anc i ∈ K := by
        rw [hanc_def]
        dsimp only
        exact SardConvexDomain.whitneyNetAnchor_mem hKc.isClosed hKn i
      have ht0 := hC₁ (k - j) (by omega) (anc i) hancK a haK x
      rw [hexp] at ht0
      have hnorm_a : ‖x - anc i‖ + ‖x - a‖ ≤ 5 * d := by
        have hna : ‖x - anc i‖ = dist x (anc i) := (dist_eq_norm x (anc i)).symm
        have hnb : ‖x - a‖ = dist x a := (dist_eq_norm x a).symm
        rw [hna, hnb, ← hda, hd_def]
        linarith [hancd]
      have htj : ‖iteratedFDeriv ℝ (k - j)
          (fun y ↦ taylorPolynomial m J (anc i) y - Ta y) x‖ ≤
          C₁ * (5 * d) ^ (m + 1 - k + j) := by
        refine ht0.trans (mul_le_mul_of_nonneg_left ?_ hC₁0)
        exact pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) hnorm_a _
      have hkey : (k.choose j : ℝ) * (P.derivConstant j * (2 * d⁻¹) ^ j) *
            (C₁ * (5 * d) ^ (m + 1 - k + j)) =
          C₁ * Wval k j * d ^ (m + 1 - k) := by
        have e1 : (2 * d⁻¹) ^ j = 2 ^ j * (d⁻¹) ^ j := mul_pow _ _ _
        have e2 : (5 * d) ^ (m + 1 - k + j) =
            5 ^ (m + 1 - k + j) * d ^ (m + 1 - k + j) := mul_pow _ _ _
        have e3 : d ^ (m + 1 - k + j) = d ^ (m + 1 - k) * d ^ j :=
          pow_add d (m + 1 - k) j
        have e4 : (d⁻¹) ^ j * d ^ j = 1 := by
          rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero j hdpos.ne')]
        rw [e1, e2, e3, hWval_def]
        trans (C₁ * ((k.choose j : ℝ) * P.derivConstant j * 2 ^ j *
            5 ^ (m + 1 - k + j)) * d ^ (m + 1 - k)) * ((d⁻¹) ^ j * d ^ j)
        · ring
        · rw [e4, mul_one]
      refine (mul_le_mul (mul_le_mul_of_nonneg_left
        (hder.trans (mul_le_mul_of_nonneg_left heinvj (P.derivConstant_nonneg j)))
        (Nat.cast_nonneg _)) htj (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (P.derivConstant_nonneg j)
          (pow_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hdpos.le)) _)))).trans
        hkey.le
    calc ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (P.phi i) x‖ *
            ‖iteratedFDeriv ℝ (k - j)
              (fun y ↦ taylorPolynomial m J (anc i) y - Ta y) x‖
        ≤ ∑ j ∈ Finset.range (k + 1), C₁ * Wval k j * d ^ (m + 1 - k) :=
          Finset.sum_le_sum hjb
      _ = (C₁ * d ^ (m + 1 - k)) * ∑ j ∈ Finset.range (k + 1), Wval k j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ (C₁ * d ^ (m + 1 - k)) * B := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₁0 (pow_nonneg hdpos.le _))
          rw [hB_def]
          exact Finset.single_le_sum (s := Finset.range (m + 1))
            (f := fun p ↦ ∑ j ∈ Finset.range (p + 1), Wval p j) (a := k)
            (fun p _ ↦ Finset.sum_nonneg fun j _ ↦ hWval_nn p j)
            (Finset.mem_range.2 (by omega))
      _ = C₁ * d ^ (m + 1 - k) * B := by ring
  calc ‖∑ i ∈ S, iteratedFDeriv ℝ k
        (fun y ↦ P.phi i y • (taylorPolynomial m J (anc i) y - Ta y)) x‖
      ≤ ∑ i ∈ S, ‖iteratedFDeriv ℝ k
        (fun y ↦ P.phi i y • (taylorPolynomial m J (anc i) y - Ta y)) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, C₁ * d ^ (m + 1 - k) * B := Finset.sum_le_sum hper
    _ = (S.card : ℝ) * (C₁ * d ^ (m + 1 - k) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nn : ℝ) * (C₁ * d ^ (m + 1 - k) * B) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (mul_nonneg hC₁0 (pow_nonneg hdpos.le _)) hBnn)
        exact Nat.cast_le.2 hScard
    _ = (Nn : ℝ) * C₁ * B * d ^ (m + 1 - k) := by ring

/-- The candidate global Taylor series: within jets on `K`, ordinary iterated derivatives
off `K`.  The order-zero terms are stored as continuous zero-linear maps, just as in
Mathlib's `FormalMultilinearSeries`. -/
def gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E) (f G : E → F) (x : E) : FormalMultilinearSeries ℝ E F := by
  classical
  exact fun k ↦ if x ∈ K then convexJet k f K x else iteratedFDeriv ℝ k G x

/-- Each component of the glued jet is continuous across `K`.  Off `K` this follows from
smoothness.  At `a' ∈ K`, choose a nearest `a` to an exterior `x`, compare through
`D^k P_a(x)`, then use the two-base-point Taylor bound and continuity of the within jet. -/
theorem continuous_gluedWhitneyJet_aux_base
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m k : ℕ} {f : E → F} {a : E}
    (hk : k ≤ m)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    (ha : a ∈ K) :
    iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) a =
      convexJet k f K a := by
  ext v
  rw [iteratedFDeriv_taylorPolynomial_exact m k _ a a hk v (fun j hj ↦ hsym j hj a ha)]
  rw [show m + 1 - k = (m - k) + 1 by omega, Finset.sum_range_succ']
  have hz : ∀ q ∈ Finset.range (m - k),
      (convexJet (k + (q + 1)) f K a)
        (Fin.append v (fun _ : Fin (q + 1) ↦ a - a)) = 0 := by
    intro q hq
    apply ContinuousMultilinearMap.map_coord_zero _ (Fin.natAdd k (0 : Fin (q + 1)))
    simp
  rw [Finset.sum_eq_zero (fun q hq ↦ by rw [hz q hq, smul_zero]), zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, zero_add]
  congr 1
  funext i
  simpa using Fin.append_left v (fun _ : Fin 0 ↦ (0 : E)) i

/-- A Taylor polynomial with fixed multilinear jets is a globally smooth function. -/ 
theorem continuous_gluedWhitneyJet_aux_poly
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a : E) :
    ContDiff ℝ ∞ (taylorPolynomial m J a) := by
  unfold taylorPolynomial
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.smul ((ContinuousMultilinearMap.contDiff _).comp
    (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const))

theorem continuous_gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hK : IsClosed K) (hKn : K.Nonempty)
    (hGo : ContDiffOn ℝ m G Kᶜ)
    (hjet : ∀ k ≤ m, ContinuousOn (convexJet k f K) K)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    (hdiff : ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ r
          (fun y ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a y -
            taylorPolynomial m (fun j ↦ convexJet j f K) b y) x‖ ≤
        C * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r))
    (hbound : ∀ k ≤ m, ∃ C ≥ 0, ∀ x ∉ K,
      ∃ a ∈ K, Metric.infDist x K = dist x a ∧
        ‖iteratedFDeriv ℝ k G x - iteratedFDeriv ℝ k
            (taylorPolynomial m (fun j ↦ convexJet j f K) a) x‖ ≤
          C * (Metric.infDist x K) ^ (m + 1 - k)) :
    ∀ k ≤ m, Continuous (fun x ↦ gluedWhitneyJet K f G x k) := by
  intro k hk
  rw [continuous_iff_continuousAt]
  intro b
  by_cases hb : b ∈ K
  · obtain ⟨D, hD0, hD⟩ := hdiff
    obtain ⟨C, hC0, hC⟩ := hbound k hk
    have hpolyb := continuous_gluedWhitneyJet_aux_poly m (fun j ↦ convexJet j f K) b
    have hpolya (a : E) := continuous_gluedWhitneyJet_aux_poly m (fun j ↦ convexJet j f K) a
    have hPc : Continuous (fun x ↦
      iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x) :=
      hpolyb.continuous_iteratedFDeriv (mod_cast le_top)
    have hPbase : iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) b =
        convexJet k f K b :=
      continuous_gluedWhitneyJet_aux_base hk hsym hb
    have hin : Filter.Tendsto (fun x ↦ convexJet k f K x) (nhdsWithin b K)
        (nhds (convexJet k f K b)) := (hjet k hk b hb).tendsto
    have hout : Filter.Tendsto (fun x ↦ iteratedFDeriv ℝ k G x) (nhdsWithin b Kᶜ)
        (nhds (convexJet k f K b)) := by
      have hnorm : Filter.Tendsto (fun x ↦ ‖iteratedFDeriv ℝ k G x -
          iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x‖)
          (nhdsWithin b Kᶜ) (nhds 0) := by
        have hto0 : Filter.Tendsto (fun x : E ↦ (C + D * 2 ^ (m + 1 - k)) * ‖x - b‖)
            (nhdsWithin b Kᶜ) (nhds 0) := by
          have hcont : Continuous (fun x : E ↦ (C + D * 2 ^ (m + 1 - k)) * ‖x - b‖) := by
            fun_prop
          have hca : ContinuousAt (fun x : E ↦ (C + D * 2 ^ (m + 1 - k)) * ‖x - b‖) b :=
            hcont.continuousAt
          simpa using (hca.continuousWithinAt (s := Kᶜ)).tendsto
        have hge0 : ∀ᶠ x in nhdsWithin b Kᶜ, (0 : ℝ) ≤ ‖iteratedFDeriv ℝ k G x -
            iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x‖ :=
          Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)
        have hmid : ∀ᶠ x in nhdsWithin b Kᶜ, (‖iteratedFDeriv ℝ k G x -
            iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x‖ : ℝ) ≤
            (C + D * 2 ^ (m + 1 - k)) * ‖x - b‖ := by
          have hn0 : Filter.Tendsto (fun x : E ↦ ‖x - b‖) (nhdsWithin b Kᶜ) (nhds 0) := by
            have hcn : Continuous (fun x : E ↦ ‖x - b‖) := by fun_prop
            have hcna : ContinuousAt (fun x : E ↦ ‖x - b‖) b := hcn.continuousAt
            simpa using (hcna.continuousWithinAt (s := Kᶜ)).tendsto
          have hlt : ∀ᶠ x in nhdsWithin b Kᶜ, ‖x - b‖ < 1 :=
            hn0.eventually (Iio_mem_nhds (by norm_num))
          filter_upwards [hlt, self_mem_nhdsWithin] with x hxb hxc
          obtain ⟨a, ha, hdist, hGa⟩ := hC x hxc
          have hinf : Metric.infDist x K ≤ ‖x - b‖ := by
            simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem hb
          have hda : ‖x - a‖ ≤ ‖x - b‖ := by
            rw [← dist_eq_norm, ← hdist]
            exact hinf
          have hp : 0 < m + 1 - k := by omega
          have hpow : ‖x - b‖ ^ (m + 1 - k) ≤ ‖x - b‖ := by
            have hn : m + 1 - k = (m + 1 - k - 1) + 1 := by omega
            rw [hn, pow_succ]
            calc ‖x - b‖ ^ (m + 1 - k - 1) * ‖x - b‖ ≤ 1 * ‖x - b‖ :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hxb.le)
                  (norm_nonneg _)
              _ = ‖x - b‖ := one_mul _
          have hab : ‖x - a‖ + ‖x - b‖ ≤ 2 * ‖x - b‖ := by linarith
          have hsub' := hD k hk a ha b hb x
          rw [show (fun y ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a y -
                  taylorPolynomial m (fun j ↦ convexJet j f K) b y) =
                (taylorPolynomial m (fun j ↦ convexJet j f K) a) -
                  (taylorPolynomial m (fun j ↦ convexJet j f K) b) from rfl] at hsub'
          rw [iteratedFDeriv_sub ((hpolya a).of_le (by exact_mod_cast le_top))
            (hpolyb.of_le (by exact_mod_cast le_top))] at hsub'
          simp only [Pi.sub_apply] at hsub'
          have h1 : C * Metric.infDist x K ^ (m + 1 - k) ≤
              C * ‖x - b‖ ^ (m + 1 - k) := by
            have hpn : (Metric.infDist x K : ℝ) ^ (m + 1 - k) ≤
                (‖x - b‖ : ℝ) ^ (m + 1 - k) :=
              pow_le_pow_left₀ Metric.infDist_nonneg hinf (m + 1 - k)
            exact mul_le_mul_of_nonneg_left hpn hC0
          have h2 : D * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - k) ≤
              D * (2 * ‖x - b‖) ^ (m + 1 - k) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hab _) hD0
          have hp2 : D * (2 * ‖x - b‖) ^ (m + 1 - k) ≤
              D * (2 ^ (m + 1 - k) * ‖x - b‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hD0
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
          calc ‖iteratedFDeriv ℝ k G x -
                iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x‖ ≤
              ‖iteratedFDeriv ℝ k G x - iteratedFDeriv ℝ k
                (taylorPolynomial m (fun j ↦ convexJet j f K) a) x‖ +
              ‖iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x -
                iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x‖ := by
                have he : iteratedFDeriv ℝ k G x -
                    iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x =
                    (iteratedFDeriv ℝ k G x -
                      iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x) +
                    (iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x -
                      iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x) := by
                  abel
                rw [he]
                exact norm_add_le _ _
            _ ≤ C * ‖x - b‖ ^ (m + 1 - k) +
                D * (2 * ‖x - b‖) ^ (m + 1 - k) :=
                add_le_add (hGa.trans h1) (hsub'.trans h2)
            _ ≤ C * ‖x - b‖ + D * (2 ^ (m + 1 - k) * ‖x - b‖) :=
                add_le_add (mul_le_mul_of_nonneg_left hpow hC0) hp2
            _ = (C + D * 2 ^ (m + 1 - k)) * ‖x - b‖ := by ring
        exact squeeze_zero' hge0 hmid hto0
      have herr : Filter.Tendsto (fun x ↦ iteratedFDeriv ℝ k G x -
          iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) b) x)
          (nhdsWithin b Kᶜ) (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact hnorm
      have hsum := herr.add (hPc.continuousAt.tendsto.mono_left inf_le_left)
      simpa [hPbase] using hsum
    have hval : gluedWhitneyJet K f G b k = convexJet k f K b := by
      simp only [gluedWhitneyJet, hb, if_true]
    show Filter.Tendsto (fun x ↦ gluedWhitneyJet K f G x k) (nhds b)
      (nhds (gluedWhitneyJet K f G b k))
    rw [hval]
    rw [show (nhds b) = nhdsWithin b Set.univ from (nhdsWithin_univ b).symm]
    simp only [gluedWhitneyJet]
    classical
    exact Filter.Tendsto.if_nhdsWithin (by rw [Set.univ_inter]; exact hin)
      (by rw [Set.univ_inter]; exact hout)
  · have hopen : Kᶜ ∈ nhds b := hK.isOpen_compl.mem_nhds hb
    have hAt : ContDiffAt ℝ (m : WithTop ℕ∞) G b := hGo.contDiffAt hopen
    have hGo' := hAt.continuousAt_iteratedFDeriv (by exact_mod_cast hk)
    exact hGo'.congr_of_eventuallyEq
      (Filter.Eventually.mono (Filter.eventually_iff.2 hopen) fun x hx ↦ by
        simp only [gluedWhitneyJet, if_neg hx])

/-- Off `K` the glued jet is the iterated derivative of `G`, and `Kᶜ` is open, so the
derivative of the `k`-th component is the next component (`ContDiffOn` on the open set,
`fderiv_iteratedFDeriv` and `iteratedFDeriv_succ_eq_comp_left`). -/
theorem hasFDerivAt_gluedWhitneyJet_of_not_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m k : ℕ} {f G : E → F} {x : E}
    (hK : IsClosed K) (hx : x ∉ K) (hk : k < m)
    (hGo : ContDiffOn ℝ m G Kᶜ) :
    HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x := by
  have hopen : IsOpen Kᶜ := hK.isOpen_compl
  have hAt : ContDiffAt ℝ (m : WithTop ℕ∞) G x := hGo.contDiffAt (hopen.mem_nhds hx)
  have hkm : (k : WithTop ℕ∞) < (m : WithTop ℕ∞) := by exact_mod_cast hk
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k G) x :=
    hAt.differentiableAt_iteratedFDeriv hkm
  have hfd : fderiv ℝ (iteratedFDeriv ℝ k G) x =
      (iteratedFDeriv ℝ (k + 1) G x).curryLeft := by
    rw [fderiv_iteratedFDeriv, Function.comp_apply]
    rfl
  have hmain : HasFDerivAt (fun y ↦ iteratedFDeriv ℝ k G y)
      (iteratedFDeriv ℝ (k + 1) G x).curryLeft x :=
    hfd ▸ hdiff.hasFDerivAt
  have heq : Filter.EventuallyEq (nhds x) (fun y ↦ gluedWhitneyJet K f G y k)
      (fun y ↦ iteratedFDeriv ℝ k G y) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp only [gluedWhitneyJet, if_neg hy]
  have hval : gluedWhitneyJet K f G x (k + 1) = iteratedFDeriv ℝ (k + 1) G x := by
    simp only [gluedWhitneyJet, if_neg hx]
  rw [hval]
  exact (heq.hasFDerivAt_iff).2 hmain

/-- Boundary differentiability of successive glued jets.  Subtract the linear term
`(J_(k+1)(a')).curryLeft (x-a')`; the exact Taylor formula at `a'` leaves order two,
while the off-set and two-base-point errors have exponent `m+1-k ≥ 2`. -/
theorem hasFDerivAt_gluedWhitneyJet_of_mem_aux_contDiff_taylor
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a : E) :
    ContDiff ℝ ⊤ (taylorPolynomial m J a) := by
  show ContDiff ℝ ⊤ (fun x ↦ ∑ j ∈ Finset.range (m + 1),
    ((j.factorial : ℝ)⁻¹) • J j a (fun _ ↦ x - a))
  apply ContDiff.sum
  intro j _
  apply ContDiff.const_smul
  exact (ContinuousMultilinearMap.contDiff _).comp
    (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)

/-- At the base point, the `k`-th derivative of the Taylor polynomial is the `k`-th jet:
every higher term of the exact formula carries a zero `a - a` argument. -/
theorem hasFDerivAt_gluedWhitneyJet_of_mem_aux_base
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f : E → F} {a : E} (ha : a ∈ K)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    {k : ℕ} (hk : k ≤ m) :
    iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) a =
      convexJet k f K a := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_taylorPolynomial_exact m k (fun j ↦ convexJet j f K) a a hk v
    (fun j hj σ ↦ hsym j hj a ha σ)]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, sub_self]
    have htuple : ∀ i : Fin (k + 0),
        Fin.append v (fun _ : Fin 0 => (0 : E)) i = v i := by
      intro i
      rw [show i = Fin.castAdd 0 ⟨i.val, by have h := i.isLt; omega⟩ from Fin.ext rfl,
        Fin.append_left]
      exact congrArg v (Fin.ext rfl)
    rw [funext htuple]
    rfl
  · intro q hq hq0
    simp only [sub_self]
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    rw [(convexJet (k + q) f K a).map_coord_zero (Fin.natAdd k ⟨0, hqpos⟩)
      (by rw [Fin.append_right]), smul_zero]
  · intro hmem
    exact (hmem (Finset.mem_range.mpr (by omega))).elim

theorem hasFDerivAt_gluedWhitneyJet_of_mem
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m k : ℕ} {f G : E → F} {x : E}
    (hK : IsClosed K) (hKn : K.Nonempty) (hx : x ∈ K) (hk : k < m)
    (hjet : ∀ r ≤ m, ContinuousOn (convexJet r f K) K)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    (hdiff : ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ y : E,
      ‖iteratedFDeriv ℝ r
          (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) y‖ ≤
        C * (‖y - a‖ + ‖y - b‖) ^ (m + 1 - r))
    (hbound : ∀ r ≤ m, ∃ C ≥ 0, ∀ y ∉ K,
      ∃ a ∈ K, Metric.infDist y K = dist y a ∧
        ‖iteratedFDeriv ℝ r G y - iteratedFDeriv ℝ r
            (taylorPolynomial m (fun j ↦ convexJet j f K) a) y‖ ≤
          C * (Metric.infDist y K) ^ (m + 1 - r)) :
    HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x := by
  classical
  set J := fun j ↦ convexJet j f K with hJdef
  set P := fun a ↦ taylorPolynomial m J a with hPdef
  set p := m + 1 - k with hpdef
  have hkle : k ≤ m := Nat.le_of_lt hk
  have hp2 : 2 ≤ p := by omega
  have hCT : ∀ a, ContDiff ℝ ⊤ (P a) :=
    fun a ↦ hasFDerivAt_gluedWhitneyJet_of_mem_aux_contDiff_taylor m J a
  have hbase : ∀ a ∈ K, ∀ k' ≤ m, iteratedFDeriv ℝ k' (P a) a = J k' a := by
    intro a ha k' hk'
    rw [hJdef]
    exact hasFDerivAt_gluedWhitneyJet_of_mem_aux_base ha hsym hk'
  obtain ⟨C1, hC1nn, hC1⟩ := hdiff
  obtain ⟨C2, hC2nn, hC2⟩ := hbound k hkle
  set C' := C2 + C1 * 2 ^ p with hC'def
  have hC'nn : 0 ≤ C' := by positivity
  -- The remainder `R y = GJ y k - D^k P_x y` is `O(‖y - x‖ ^ p)` with `p ≥ 2`.
  have hRbound : ∀ y, ‖gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y‖ ≤
      C' * ‖y - x‖ ^ p := by
    intro y
    by_cases hy : y ∈ K
    · have hGy : gluedWhitneyJet K f G y k = J k y := by
        simp only [gluedWhitneyJet, if_pos hy]; rfl
      have hb := hbase y hy k hkle
      have hsub := hC1 k hkle x hx y hy y
      rw [show (fun z ↦ taylorPolynomial m J x z - taylorPolynomial m J y z)
          = P x - P y from rfl,
        iteratedFDeriv_sub_apply ((hCT x).contDiffAt.of_le le_top)
          ((hCT y).contDiffAt.of_le le_top)] at hsub
      simp only [sub_self, norm_zero, add_zero] at hsub
      have h2p : (1 : ℝ) ≤ 2 ^ p := by simpa using pow_le_pow_left₀ (zero_le_one : (0:ℝ) ≤ 1) (one_le_two : (1:ℝ) ≤ 2) p
      have hC1le : C1 ≤ C' :=
        calc C1 = C1 * 1 := (mul_one _).symm
          _ ≤ C1 * 2 ^ p := mul_le_mul_of_nonneg_left h2p hC1nn
          _ ≤ C2 + C1 * 2 ^ p := le_add_of_nonneg_left hC2nn
      calc ‖gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y‖
          = ‖iteratedFDeriv ℝ k (P x) y - J k y‖ := by
            rw [hGy, norm_sub_rev]
        _ = ‖iteratedFDeriv ℝ k (P x) y - iteratedFDeriv ℝ k (P y) y‖ := by rw [hb]
        _ ≤ C1 * ‖y - x‖ ^ p := hsub
        _ ≤ C' * ‖y - x‖ ^ p :=
          mul_le_mul_of_nonneg_right hC1le (pow_nonneg (norm_nonneg _) _)
    · have hGy : gluedWhitneyJet K f G y k = iteratedFDeriv ℝ k G y := by
        simp only [gluedWhitneyJet, if_neg hy]
      obtain ⟨a, haK, hdist, hGb⟩ := hC2 y hy
      have hinf : Metric.infDist y K ≤ ‖y - x‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hx
      have hya : ‖y - a‖ ≤ ‖y - x‖ := by rw [← dist_eq_norm, ← hdist]; exact hinf
      have hsub := hC1 k hkle x hx a haK y
      rw [show (fun z ↦ taylorPolynomial m J x z - taylorPolynomial m J a z)
          = P x - P a from rfl,
        iteratedFDeriv_sub_apply ((hCT x).contDiffAt.of_le le_top)
          ((hCT a).contDiffAt.of_le le_top)] at hsub
      have hpow : (‖y - x‖ + ‖y - a‖) ^ p ≤ 2 ^ p * ‖y - x‖ ^ p :=
        calc (‖y - x‖ + ‖y - a‖) ^ p ≤ (2 * ‖y - x‖) ^ p :=
            pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (by linarith [hya]) p
          _ = 2 ^ p * ‖y - x‖ ^ p := mul_pow _ _ _
      calc ‖gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y‖
          = ‖(iteratedFDeriv ℝ k G y - iteratedFDeriv ℝ k (P a) y) +
              (iteratedFDeriv ℝ k (P a) y - iteratedFDeriv ℝ k (P x) y)‖ := by
            rw [hGy]; congr 1; abel
        _ ≤ ‖iteratedFDeriv ℝ k G y - iteratedFDeriv ℝ k (P a) y‖ +
              ‖iteratedFDeriv ℝ k (P a) y - iteratedFDeriv ℝ k (P x) y‖ :=
            norm_add_le _ _
        _ = ‖iteratedFDeriv ℝ k G y - iteratedFDeriv ℝ k (P a) y‖ +
              ‖iteratedFDeriv ℝ k (P x) y - iteratedFDeriv ℝ k (P a) y‖ := by
            rw [norm_sub_rev (iteratedFDeriv ℝ k (P a) y) (iteratedFDeriv ℝ k (P x) y)]
        _ ≤ C2 * Metric.infDist y K ^ p + C1 * (2 ^ p * ‖y - x‖ ^ p) :=
            add_le_add hGb (hsub.trans (mul_le_mul_of_nonneg_left hpow hC1nn))
        _ ≤ C2 * ‖y - x‖ ^ p + C1 * (2 ^ p * ‖y - x‖ ^ p) :=
            add_le_add_left
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ Metric.infDist_nonneg hinf p) hC2nn) _
        _ = C' * ‖y - x‖ ^ p := by rw [hC'def]; ring
  -- Hence `R = o(‖y - x‖)` near `x`.
  have hR : (fun y ↦ gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y)
      =o[nhds x] (fun y ↦ y - x) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hC'1 : (0 : ℝ) < C' + 1 := by linarith [hC'nn]
    filter_upwards [Metric.ball_mem_nhds x
      (show (0 : ℝ) < min 1 (c / (C' + 1)) from lt_min zero_lt_one (div_pos hc hC'1))]
      with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have ht1 : ‖y - x‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
    have htc : C' * ‖y - x‖ ≤ c := by
      have h1 : (C' + 1) * ‖y - x‖ < c := by
        have h2 := lt_of_lt_of_le hy (min_le_right _ _)
        rw [lt_div_iff₀ hC'1] at h2
        rwa [mul_comm] at h2
      have h3 : C' * ‖y - x‖ ≤ (C' + 1) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
      linarith [h3, h1]
    calc ‖gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y‖
        ≤ C' * ‖y - x‖ ^ p := hRbound y
      _ ≤ C' * ‖y - x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (norm_nonneg _) ht1 hp2) hC'nn
      _ = C' * ‖y - x‖ * ‖y - x‖ := by ring
      _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right htc (norm_nonneg _)
  -- The polynomial part contributes the exact linear term.
  have hAt : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (P x) x := (hCT x).contDiffAt
  have hkm : (k : WithTop ℕ∞) < (⊤ : WithTop ℕ∞) := WithTop.coe_lt_top _
  have hdiffAt : DifferentiableAt ℝ (iteratedFDeriv ℝ k (P x)) x :=
    hAt.differentiableAt_iteratedFDeriv hkm
  have hfd : fderiv ℝ (iteratedFDeriv ℝ k (P x)) x =
      (iteratedFDeriv ℝ (k + 1) (P x) x).curryLeft := by
    rw [fderiv_iteratedFDeriv, Function.comp_apply]
    rfl
  have hmainQ : HasFDerivAt (fun y ↦ iteratedFDeriv ℝ k (P x) y)
      (iteratedFDeriv ℝ (k + 1) (P x) x).curryLeft x := hfd ▸ hdiffAt.hasFDerivAt
  have hQ := hasFDerivAt_iff_isLittleO.mp hmainQ
  -- Assemble.
  have hbk : gluedWhitneyJet K f G x k = iteratedFDeriv ℝ k (P x) x := by
    have h1 : gluedWhitneyJet K f G x k = J k x := by
      simp only [gluedWhitneyJet, if_pos hx]; rfl
    rw [h1, ← hbase x hx k hkle]
  have hk1m : k + 1 ≤ m := by omega
  have he2 : gluedWhitneyJet K f G x (k + 1) = iteratedFDeriv ℝ (k + 1) (P x) x := by
    have h1 : gluedWhitneyJet K f G x (k + 1) = J (k + 1) x := by
      simp only [gluedWhitneyJet, if_pos hx]; rfl
    rw [h1, ← hbase x hx (k + 1) hk1m]
  rw [hasFDerivAt_iff_isLittleO, hbk, he2]
  exact (hR.add hQ).congr' (Filter.Eventually.of_forall fun y ↦ by
    show gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) y +
        (iteratedFDeriv ℝ k (P x) y - iteratedFDeriv ℝ k (P x) x -
          (iteratedFDeriv ℝ (k + 1) (P x) x).curryLeft (y - x)) =
      gluedWhitneyJet K f G y k - iteratedFDeriv ℝ k (P x) x -
        (iteratedFDeriv ℝ (k + 1) (P x) x).curryLeft (y - x)
    abel) (Filter.EventuallyEq.rfl)

/-- Assemble the zero-term identity, off-set derivatives, boundary derivative leaf, and
component continuity into Mathlib's `HasFTaylorSeriesUpTo` structure.  This isolates the
actual gluing argument from the standard Taylor-series-to-`ContDiff` conversion. -/
theorem hasFTaylorSeriesUpTo_gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hzero : ∀ x, (gluedWhitneyJet K f G x 0).curry0 = G x)
    (hcont : ∀ k ≤ m, Continuous (fun x ↦ gluedWhitneyJet K f G x k))
    (hderiv : ∀ k < m, ∀ x, HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x) :
    HasFTaylorSeriesUpTo (m : WithTop ℕ∞) G (gluedWhitneyJet K f G) := by
  refine {
    zero_eq := hzero
    fderiv := ?_
    cont := ?_
  }
  · intro k hk x
    apply hderiv k ?_ x
    exact_mod_cast hk
  · intro k hk
    apply hcont k
    exact_mod_cast hk

/-- A global Taylor series through order `m` gives `C^m`; identify its first component
with the ordinary derivative and the on-`K` component with the within derivative. -/
theorem contDiff_and_fderiv_eq_of_gluedTaylorSeries
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hm : 1 ≤ m)
    (hone : ∀ x ∈ K, ∀ v, convexJet 1 f K x (fun _ ↦ v) = fderivWithin ℝ f K x v)
    (hT : HasFTaylorSeriesUpTo (m : WithTop ℕ∞) G (gluedWhitneyJet K f G)) :
    ContDiff ℝ m G ∧ ∀ x ∈ K, fderiv ℝ G x = fderivWithin ℝ f K x := by
  constructor
  · exact hT.contDiff
  · intro x hx
    have hm0 : (m : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm)
    rw [(hT.hasFDerivAt hm0 x).fderiv]
    ext v
    simp only [gluedWhitneyJet, hx, if_pos]
    convert hone x hx v using 1

/-- Fixed-order Whitney extension on a compact convex domain.  For positive `m`, choose the
partition, apply the polynomial-relative off-set estimate, and assemble the Taylor series.
For `m=0`, use the separate `C¹` differentiable-extension leaf so the derivative conclusion
is not incorrectly inferred from an order-zero Taylor series. -/
theorem exists_contDiff_extension_compactConvex
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : Set E} {f : E → F} (m : ℕ) (hm : 1 ≤ m)
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ F' : E → F, ContDiff ℝ m F' ∧ Set.EqOn F' f K ∧
      ∀ x ∈ K, fderiv ℝ F' x = fderivWithin ℝ f K x := by
  sorry

/-- Intersecting a closed convex set with a sufficiently large closed ball about an interior
point remains compact convex with nonempty interior.  Use finite-dimensional properness and
the original interior point, choosing a positive radius. -/
theorem compactExhaustion_piece
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s)
    {p : E} (hp : p ∈ interior s) {R : ℝ} (hR : 0 < R) :
    IsCompact (s ∩ Metric.closedBall p R) ∧
      Convex ℝ (s ∩ Metric.closedBall p R) ∧
      (interior (s ∩ Metric.closedBall p R)).Nonempty := by
  refine ⟨(isCompact_closedBall p R).inter_left hs,
    hsc.inter (convex_closedBall p R), ?_⟩
  refine ⟨p, ?_⟩
  rw [interior_inter, interior_closedBall p (ne_of_gt hR)]
  exact ⟨hp, Metric.mem_ball_self hR⟩

/-- Inside the open ball, adding the closed-ball constraint does not change the within
derivative.  The two domains agree in a neighborhood of `x`; apply `fderivWithin_congr_set`
or the corresponding filter congruence lemma. -/
theorem fderivWithin_inter_closedBall_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (p : E) (R : ℝ) {x : E}
    (hx : x ∈ s ∩ Metric.ball p R) :
    fderivWithin ℝ f (s ∩ Metric.closedBall p R) x = fderivWithin ℝ f s x := by
  apply fderivWithin_congr_set
  filter_upwards [Metric.isOpen_ball.mem_nhds hx.2] with y hy
  apply propext
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, Metric.ball_subset_closedBall hy⟩

/-- Every point of `s` lies in an open ball of some positive integer radius about `p`.
This is the countable exhaustion needed to cover the relative critical image. -/
theorem subset_iUnion_inter_ball_nat
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (p : E) :
    s ⊆ ⋃ n : ℕ, s ∩ Metric.ball p (n + 1 : ℝ) := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x p)
  rw [Set.mem_iUnion]
  refine ⟨n, hx, ?_⟩
  rw [Metric.mem_ball]
  have hcast : (n : ℝ) < (n : ℝ) + 1 := by linarith
  exact hn.trans hcast

/-- On one compact exhaustion piece, the relative critical image is null.  Extend with
order `d(d+1)+2`, rewrite the within derivative on the open-ball core, and apply
`critical_image_null_of_high_order` to that arbitrary core set. -/
theorem compactExhaustion_critical_image_null
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) {p : E} (hp : p ∈ interior s)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) (n : ℕ) :
    mu (f '' {x | x ∈ s ∩ Metric.ball p (n + 1 : ℝ) ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- Sard for a closed convex domain with nonempty interior.  Cover its critical image by
the countable union of the compact-exhaustion critical images, apply the preceding nullity
leaf to each, and conclude with `measure_iUnion_null`. -/
theorem closedConvex_critical_image_null_innerProduct
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) (hsi : (interior s).Nonempty)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) :
    mu (f '' {x | x ∈ s ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- The same closed-convex Sard theorem for an arbitrary finite-dimensional normed source.
Choose a continuous linear equivalence with `EuclideanSpace ℝ (Fin (finrank ℝ E))`, transport
the set and map, apply the inner-product version, and conjugate the within derivative. -/
theorem closedConvex_critical_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) (hsi : (interior s).Nonempty)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) :
    mu (f '' {x | x ∈ s ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- Local chartwise Sard estimate used by both manifold consumers.  In the source chart at
`x`, choose `range I ∩ closedBall y r` inside the extended-chart target; it is closed convex
with nonempty interior because `y` lies in the closure of `interior (range I)`.  Apply the
normed-source theorem, use the open-ball derivative leaf, then transport `mfderiv`. -/
theorem manifold_local_critical_image_null
    {E H X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace X]
    [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (mu : Measure V) [mu.IsAddHaarMeasure] (g : X → V)
    (hg : ContMDiff I (modelWithCornersSelf ℝ V) ∞ g) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      mu (g '' ({z | ¬ Function.Surjective
        (mfderiv I (modelWithCornersSelf ℝ V) g z)} ∩ U)) = 0 := by
  sorry

end ConstructionTargets.SardWhitneyExtension
