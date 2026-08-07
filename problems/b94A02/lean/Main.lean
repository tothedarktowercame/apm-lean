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
  -- (Sibling: b93A03)
  /- PARTIAL boundary (closer hop 1):
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
     `TensorProduct.tensorQuotEquivQuotSMul`.  The intended construction
     chooses `r` from a
     witness `x = b * r` and sends `(x, s + I)` to `r * s + I`; proving this
     independent of the chosen witness requires transporting
     `b * (r-r') = 0` through the annihilator hypothesis into `I`.  I could
     The remaining packaging is defining that choice as the required curried
     linear map and proving additivity/scalar compatibility. Equivalently,
     the general quotient-tensor equivalence reduces the middle conjunct to
     the still-missing problem-specific linear equivalence
     `(Ideal.span {b}) / (I • ⊤) ≃ R ⧸ I`.  Sibling `b93A03` supplies the
     subsequent nonzero-tensor/map argument once that equivalence is built. -/
  sorry
