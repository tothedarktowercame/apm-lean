import ConstructionTargets.SimplicialChainModel

/-! # Rational Lefschetz fixed-point theorem (wired through `SimplicialChainMaps`)

`LefschetzCompactPolyhedron` states the oriented chain model
`exists_carrier_avoiding_oriented_chain_model` as a `sorry`. Its proof lives in
`SimplicialChainMaps`, which imports `LefschetzCompactPolyhedron`, so the
original file cannot call it. This module restates the three theorems downstream
of the chain model, word for word, and proves them through
`SimplicialChainMaps.exists_carrier_avoiding_oriented_chain_model`. Consumers
should use `LefschetzFixedPoint.fixedPointOfNonzeroLefschetz`. It has the same
statement as the `LefschetzCompactPolyhedron` version, and its axioms show what
remains open in the `SimplicialChainMaps` chain (claude-14, 2026-10-29). -/

open Set CategoryTheory
open ConstructionTargets.RationalLefschetz

noncomputable section

namespace ConstructionTargets.LefschetzFixedPoint

open ConstructionTargets.LefschetzCompactPolyhedron

theorem exists_faceAvoiding_simplicial_trace_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (havoid : FaceAvoiding K e g) :
    ∃ M : FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧
      (∀ k, M.homologyTrace k =
        LinearMap.trace ℚ (Homology X k) (induced g k).hom) := by
  obtain ⟨δ, hδ, hmargin⟩ :=
    faceAvoiding_uniform_carrier_margin K hK e g havoid
  obtain ⟨M, hchain, hmodel⟩ :=
    SimplicialChainMaps.exists_carrier_avoiding_oriented_chain_model K hK e g δ hδ hmargin
  exact ⟨M, hchain, homologyTrace_eq_of_models M g hmodel⟩

/-- A face-avoiding map on a finite polyhedron has Lefschetz number zero. -/
theorem lefschetzNumber_eq_zero_of_faceAvoiding
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X)) {L : ℚ}
    (havoid : FaceAvoiding K e g) (hL : HasLefschetzNumber g L) : L = 0 := by
  obtain ⟨M, hchain, htrace⟩ :=
    exists_faceAvoiding_simplicial_trace_model K hK e g havoid
  rw [lefschetzNumber_eq_model_homology_trace g hL M htrace,
    hopf_trace_formula M]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hchain k, mul_zero]

/-- Rational Lefschetz fixed-point theorem for a finite polyhedron. -/
theorem fixedPointOfNonzeroLefschetz
    {X : Type} [TopologicalSpace X] (hX : IsFinitePolyhedron X)
    (f : C(X, X)) {L : ℚ} (hL : HasLefschetzNumber f L) (hne : L ≠ 0) :
    ∃ x, f x = x := by
  by_contra hfixed
  push_neg at hfixed
  obtain ⟨n, K, hK, ⟨e⟩⟩ := hX
  obtain ⟨ε, hε, hsep⟩ := fixedPointFree_uniform_separation K hK e f hfixed
  obtain ⟨K', hK', hspace, hfine⟩ := exists_fine_subdivision K hK hε
  let e' : X ≃ₜ K'.space := e.trans (Homeomorph.setCongr hspace.symm)
  have havoid : FaceAvoiding K' e' f :=
    faceAvoiding_of_fine K' e' f hfine (fun x => hsep x)
  exact hne (lefschetzNumber_eq_zero_of_faceAvoiding K' hK' e' f havoid hL)

end ConstructionTargets.LefschetzFixedPoint
