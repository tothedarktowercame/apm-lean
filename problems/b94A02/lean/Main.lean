import Mathlib

/-!
# APM b94A02

## Statement repairs

None.

## Encoding questions

The principal ideal `bR` is represented by `Ideal.span {b}`, and `R/I` by
`R ⧸ I`. A curried linear map into a linear-map space is the bundled form of
the requested balanced map. Its formula is stated for an arbitrary element of
the principal ideal together with a witness that the element is `b * r`.
-/

/-- The quotient-valued coefficient formula is independent of the chosen
coefficient witness. This is the central well-definedness fact needed for the
curried balanced map. -/
lemma apm_b94A02_coefficient_mul_mk_eq
    (R : Type*) [CommRing R] (I : Ideal R) (b : R)
    (hAnn : ∀ c : R, b * c = 0 → c ∈ I)
    {x r r' s : R} (hr : x = b * r) (hr' : x = b * r') :
    Ideal.Quotient.mk I (r * s) = Ideal.Quotient.mk I (r' * s) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hbr : b * r = b * r' := hr.symm.trans hr'
  have hdiff : r - r' ∈ I := hAnn (r - r') (by
    rw [mul_sub, hbr, sub_self])
  have hmul : (r - r') * s ∈ I := I.mul_mem_right s hdiff
  simpa [sub_mul] using hmul

/-- The coefficient of an element of `bR`, canonically valued in `R/I`.
This avoids choosing representatives: `R / ann(b) ≃ bR` is Mathlib's
`quotTorsionOfEquivSpanSingleton`, and `ann(b) ≤ I` induces the quotient map. -/
noncomputable def apm_b94A02_coefficientLinearMap
    (R : Type*) [CommRing R] (I : Ideal R) (b : R)
    (hAnn : ∀ c : R, b * c = 0 → c ∈ I) :
    Ideal.span {b} →ₗ[R] R ⧸ I :=
  let T := Ideal.torsionOf R R b
  let e := Ideal.quotTorsionOfEquivSpanSingleton R R b
  let hTI : T ≤ I := by
    intro c hc
    apply hAnn c
    have : c * b = 0 := (Ideal.mem_torsionOf_iff b c).mp hc
    simpa [mul_comm] using this
  (Submodule.mapQ T I (LinearMap.id) (by simpa using hTI)).comp e.symm.toLinearMap

/-- The canonical coefficient map has the expected value on every witnessed
multiple of the generator. -/
lemma apm_b94A02_coefficientLinearMap_apply
    (R : Type*) [CommRing R] (I : Ideal R) (b : R)
    (hAnn : ∀ c : R, b * c = 0 → c ∈ I)
    (x : Ideal.span {b}) (r : R) (hr : (x : R) = b * r) :
    apm_b94A02_coefficientLinearMap R I b hAnn x = Ideal.Quotient.mk I r := by
  let e := Ideal.quotTorsionOfEquivSpanSingleton R R b
  have he : e (Submodule.Quotient.mk r) = x := by
    change Ideal.quotTorsionOfEquivSpanSingleton R R b
      (Submodule.Quotient.mk r) = x
    rw [Ideal.quotTorsionOfEquivSpanSingleton_apply_mk]
    apply Subtype.ext
    change r * b = (x : R)
    simpa [mul_comm] using hr.symm
  simp only [apm_b94A02_coefficientLinearMap, LinearMap.comp_apply]
  change (Submodule.mapQ (Ideal.torsionOf R R b) I (LinearMap.id) _)
      ((Ideal.quotTorsionOfEquivSpanSingleton R R b).symm x) = _
  rw [show (Ideal.quotTorsionOfEquivSpanSingleton R R b).symm x =
      Submodule.Quotient.mk r by
    rw [← he, e.symm_apply_apply]]
  rfl

/-- The required curried balanced map, including its formula and
surjectivity.  Multiplication in `R/I` is composed with the canonical
coefficient map above. -/
lemma apm_b94A02_exists_balancedMap
    (R : Type*) [CommRing R] (I : Ideal R) (b : R)
    (hAnn : ∀ c : R, b * c = 0 → c ∈ I) :
    ∃ φ : (Ideal.span {b}) →ₗ[R] ((R ⧸ I) →ₗ[R] (R ⧸ I)),
      Function.Surjective (fun p : (Ideal.span {b}) × (R ⧸ I) ↦ φ p.1 p.2) ∧
      ∀ (x : Ideal.span {b}) (r s : R),
        (x : R) = b * r →
          φ x (Ideal.Quotient.mk I s) = Ideal.Quotient.mk I (r * s) := by
  let coeff := apm_b94A02_coefficientLinearMap R I b hAnn
  let φ := (LinearMap.mul R (R ⧸ I)).comp coeff
  refine ⟨φ, ?_, ?_⟩
  · intro q
    let x : Ideal.span {b} := ⟨b, Ideal.subset_span (Set.mem_singleton b)⟩
    refine ⟨(x, q), ?_⟩
    have hx : coeff x = Ideal.Quotient.mk I 1 := by
      apply apm_b94A02_coefficientLinearMap_apply R I b hAnn x 1
      simp [x]
    simp [φ, hx]
  · intro x r s hr
    have hx : coeff x = Ideal.Quotient.mk I r :=
      apm_b94A02_coefficientLinearMap_apply R I b hAnn x r hr
    simp [φ, hx]

theorem apm_b94a02 :
    ∀ (R : Type*) [CommRing R] (I : Ideal R) (b : R),
      I ≠ ⊤ →
      (∀ c : R, b * c = 0 → c ∈ I) →
      (∃ φ : (Ideal.span {b}) →ₗ[R] ((R ⧸ I) →ₗ[R] (R ⧸ I)),
          Function.Surjective (fun p : (Ideal.span {b}) × (R ⧸ I) ↦ φ p.1 p.2) ∧
          ∀ (x : Ideal.span {b}) (r s : R),
            (x : R) = b * r →
              φ x (Ideal.Quotient.mk I s) = Ideal.Quotient.mk I (r * s)) ∧
      Nonempty
        (TensorProduct R (Ideal.span {b}) (R ⧸ I) ≃ₗ[R] (R ⧸ I)) ∧
      (b ∈ I →
        ¬Function.Injective
          (TensorProduct.map (Ideal.span {b}).subtype
            (LinearMap.id (M := R ⧸ I)))) := by
  intro R _ I b hI hAnn
  have hb : b ≠ 0 := by
    intro hb0
    apply hI
    apply I.eq_top_iff_one.mpr
    apply hAnn 1
    simp [hb0]
  have hquotient_nontrivial : (1 : R ⧸ I) ≠ 0 := by
    intro hzero
    apply hI
    apply I.eq_top_iff_one.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hcoeff (x : Ideal.span {b}) : ∃ r : R, (x : R) = b * r := by
    have hx := x.property
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, by simpa [mul_comm] using hr⟩
  refine ⟨apm_b94A02_exists_balancedMap R I b hAnn, ?_⟩
  -- (Sibling: b93A03)
  /- PARTIAL boundary (closer hop 2):
     `apm_b94A02_coefficient_mul_mk_eq` now proves the exact independence
     statement that blocked the earlier witness-choice construction: if
     `x=b*r=b*r'`, then `r*s` and `r'*s` define the same class modulo `I`.
     It transports `b*(r-r')=0` through `hAnn` and ideal closure.

     Earlier work: `hb`, `hquotient_nontrivial`, and `hcoeff` prove
     that the generator is nonzero, `1 + I` is nonzero, and every element of
     the principal ideal has a coefficient.  I searched the principal-ideal,
     annihilator, quotient, and
     tensor APIs, including `Ideal.mem_span_singleton`,
     `Submodule.mem_annihilator_span_singleton`, `Submodule.liftQ`,
     `TensorProduct.lid`, `TensorProduct.map_tmul`, and the tensor-product
     quotient equivalences, especially
     `TensorProduct.tensorQuotEquivQuotSMul`.

     Closer hop 2 routes around witness-choice packaging altogether.
     `apm_b94A02_coefficientLinearMap` uses
     `Ideal.quotTorsionOfEquivSpanSingleton` to identify `bR` with
     `R/ann(b)`, then `Submodule.mapQ` and `ann(b) ≤ I` give the canonical
     coefficient map `bR → R/I`. Its application lemma proves the expected
     value on `b*r`. `apm_b94A02_exists_balancedMap` composes this with
     multiplication in the quotient and closes the entire first conjunct,
     including surjectivity and the displayed formula.

     The general quotient-tensor equivalence reduces the middle conjunct to
     the still-missing problem-specific linear equivalence
     `(Ideal.span {b}) / (I • ⊤) ≃ R ⧸ I`.  Sibling `b93A03` supplies the
     subsequent nonzero-tensor/map argument once that equivalence is built. -/
  sorry
