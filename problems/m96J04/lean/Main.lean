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

/-- Any nonzero-eigenvalue eigenvector of an operator with the Volterra
pointwise formula has the required zero initial value. -/
lemma apm_m96j04_eigenvector_zero_at_zero
    (V : apm_m96j04_C →L[ℝ] apm_m96j04_C)
    (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
      V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s)
    (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C)
    (hf : V f = eigenvalue • f) :
    f ⟨0, by norm_num⟩ = 0 := by
  let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have h := congrArg (fun g : apm_m96j04_C ↦ g t0) hf
  change V f t0 = eigenvalue * f t0 at h
  rw [hV] at h
  have h' : 0 = eigenvalue * f t0 := by simpa [t0] using h
  have ht0 : f t0 = 0 := (mul_eq_zero.mp h'.symm).resolve_left heigen
  simpa [t0] using ht0

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
  constructor
  · obtain ⟨A, hA, hpow⟩ := apm_m96j04_block_exists
    refine ⟨A, hA, ?_, hpow⟩
    intro hcompact
    have hid : IsCompactOperator (id : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
      have hcomp := (hcompact.comp_clm
        (ContinuousLinearMap.inr ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))).clm_comp
          (ContinuousLinearMap.fst ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))
      convert hcomp using 1
      funext x
      simp [hA]
    -- (Sibling: m95A02)
    let b : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ) :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ ℓ²(ℕ, ℝ))
    letI : FiniteDimensional ℝ ℓ²(ℕ, ℝ) :=
      FiniteDimensional.of_isCompactOperator_id hid
    letI : Finite ℕ := b.orthonormal.linearIndependent.finite
    exact not_finite ℕ
  · /-
    PARTIAL boundary (Volterra operator).  The Hilbert-space clause is now
    closed, including noncompactness, by factoring a hypothetical compact block
    map into the identity and contradicting finiteness of the canonical
    `HilbertBasis ℕ ℝ ℓ²`.

    The remaining clause requires bundling the parameter-dependent interval
    integral as a continuous linear map into `C(Icc 0 1,ℝ)`.  Compactness then
    needs converting the uniformly bounded Lipschitz image of the unit ball
    into the pointwise-compact hypothesis of
    `ArzelaAscoli.isCompact_of_equicontinuous`.  The eigenvalue clause requires
    an interval FTC/ODE uniqueness bridge.  Searches of `LEMMA-INDEX.md`, 172
    closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, Mathlib's
    continuous-map integral APIs, Ascoli implementation, and interval FTC found
    no packaged Volterra continuous-linear-map construction or compactness
    theorem.  This assembly remains open.

    Closer hop 1 isolates and proves the initial-value part of the eigenvector
    argument as `apm_m96j04_eigenvector_zero_at_zero`: evaluating the frozen
    Volterra formula at `t = 0` forces every eigenvector for a nonzero
    eigenvalue to vanish at zero.  Additional searches covered
    `intervalIntegral.integral_hasDerivAt_right`, Gronwall/ODE uniqueness,
    `ContinuousMap` operator constructors, Ascoli, and all closed artifacts.
    The remaining eigenvector bridge is to turn the integral equation into
    `HasDerivAt f (f/eigenvalue)` on the subtype interval and apply uniqueness;
    compactness still requires constructing the continuous linear map and the
    equicontinuous compact image.
    -/
    sorry
