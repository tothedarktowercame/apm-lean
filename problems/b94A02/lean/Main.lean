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
  /- PASS-1 boundary: searched the principal-ideal, annihilator, quotient, and
     tensor APIs, including `Ideal.mem_span_singleton`,
     `Submodule.mem_annihilator_span_singleton`, `Submodule.liftQ`,
     `TensorProduct.lid`, `TensorProduct.map_tmul`, and the tensor-product
     quotient equivalences.  The intended construction chooses `r` from a
     witness `x = b * r` and sends `(x, s + I)` to `r * s + I`; proving this
     independent of the chosen witness requires transporting
     `b * (r-r') = 0` through the annihilator hypothesis into `I`.  I could
     not package that choice as the required curried linear map and then build
     its inverse tensor equivalence, needed to certify the nonzero kernel
     witness in the final clause, within pass 1. -/
  sorry
