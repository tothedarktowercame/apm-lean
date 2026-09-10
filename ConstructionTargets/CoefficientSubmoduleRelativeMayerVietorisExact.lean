import ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal

noncomputable section
namespace ConstructionTargets.CoefficientSubmoduleRelativeMayerVietorisExact

open ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal

variable (R : Type) [CommRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

noncomputable def leftToSupQuotient (P Q : Submodule R M) :
    M ⧸ P →ₗ[R] M ⧸ (P ⊔ Q) :=
  P.liftQ (P ⊔ Q).mkQ (by rw [Submodule.ker_mkQ]; exact le_sup_left)

noncomputable def rightToSupQuotient (P Q : Submodule R M) :
    M ⧸ Q →ₗ[R] M ⧸ (P ⊔ Q) :=
  Q.liftQ (P ⊔ Q).mkQ (by rw [Submodule.ker_mkQ]; exact le_sup_right)

noncomputable def piecesToSupQuotient (P Q : Submodule R M) :
    (M ⧸ P) × (M ⧸ Q) →ₗ[R] M ⧸ (P ⊔ Q) :=
  (leftToSupQuotient R P Q).coprod (-rightToSupQuotient R P Q)

@[simp] theorem piecesToSupQuotient_mk (P Q : Submodule R M) (x y : M) :
    piecesToSupQuotient R P Q
      (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
        Submodule.Quotient.mk (x - y) := by
  simp [piecesToSupQuotient, leftToSupQuotient, rightToSupQuotient,
    sub_eq_add_neg]

theorem infQuotientDiagonal_piecesToSupQuotient_exact
    (P Q : Submodule R M) :
    Function.Exact (infQuotientDiagonal R P Q)
      (piecesToSupQuotient R P Q) := by
  rintro ⟨xp, yq⟩
  induction xp using Submodule.Quotient.induction_on with | _ x => ?_
  induction yq using Submodule.Quotient.induction_on with | _ y => ?_
  constructor
  · intro h
    rw [piecesToSupQuotient_mk, ← Submodule.Quotient.mk_zero,
      Submodule.Quotient.eq] at h
    have hs : x - y ∈ P ⊔ Q := by simpa using h
    rcases Submodule.mem_sup.mp hs with ⟨p, hp, q, hq, hpq⟩
    refine ⟨Submodule.Quotient.mk (x - p), ?_⟩
    apply Prod.ext
    · apply (Submodule.Quotient.eq P).2
      simpa using hp
    · apply (Submodule.Quotient.eq Q).2
      have : x - p = y + q := by
        calc
          x - p = (x - y) - p + y := by abel
          _ = (p + q) - p + y := by rw [hpq]
          _ = y + q := by abel
      rw [this]
      simpa using hq
  · rintro ⟨z, hz⟩
    rw [← hz]
    induction z using Submodule.Quotient.induction_on with | _ z => ?_
    simp [infQuotientDiagonal_mk, piecesToSupQuotient_mk]

#print axioms infQuotientDiagonal_piecesToSupQuotient_exact
end ConstructionTargets.CoefficientSubmoduleRelativeMayerVietorisExact
