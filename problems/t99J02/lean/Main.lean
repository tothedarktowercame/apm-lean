import ConstructionTargets.GenusTwoSurfacePiOne
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.CollaredConnectedSumHomology

/-!
# APM t99J02: the double torus

The printed phrase “double torus” is made precise as the classified polygon
surface `Surface true 2`.  Its CW structure is encoded by the repository's
actual standard signed octagon quotient: all polygon vertices are identified,
its eight sides form four edge orbits, and the quotient of the single polygon
is homeomorphic to `X` (so it supplies the single 2-cell).  The requested
connected-sum description uses the genuine collared connected-sum quotient,
with both summands the concrete torus `Surface true 1`, rather than merely
recording genus arithmetic.

“Using the CW decomposition”, “using van Kampen”, and “using
Mayer--Vietoris” prescribe proof methods.  The statement records their
mathematical outputs: the integral singular homology groups (twice, once for
each requested computation) and the fundamental group presentation.  The
presentation's relator is the explicit product `[a₁,b₁][a₂,b₂]` defined in
`GenusTwoSurfacePiOne`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.CollaredConnectedSumHomology

/-- The standard CW, connected-sum, homology, and fundamental-group
descriptions of the closed orientable surface of genus two. -/
theorem apm_t99j02 :
    let X := Surface true 2
    let P := standardPairingData true 2 (by norm_num)
    let H := fun (k : ℕ) =>
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))
    -- One vertex, four 1-cells, and the one polygonal 2-cell.
    (P.edgeCount = 8 ∧
      Nat.card (PairingOrbit P.pair) = 4 ∧
      (∀ i j : Fin P.edgeCount,
        Relation.EqvGen P.Rel (polygonVertex P.edgeCount i)
          (polygonVertex P.edgeCount j)) ∧
      Nonempty (P.Space ≃ₜ X)) ∧
    -- The cellular computation of integral homology.
    (Nonempty (H 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
      Nonempty (H 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 3 ≤ k → IsZero (H k))) ∧
    -- X is the connected sum of two concrete tori.
    (∃ c₁ c₂ : BallCollar 2 (Surface true 1),
      Nonempty (ConnectedSum c₁ c₂ ≃ₜ X)) ∧
    -- The van Kampen presentation, at every basepoint.
    (∀ x : X, Nonempty
      (FundamentalGroup X x ≃*
        apm_t92J05_genusTwoGroup)) ∧
    -- The Mayer--Vietoris computation of integral homology.
    (Nonempty (H 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
      Nonempty (H 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 3 ≤ k → IsZero (H k))) := by
  sorry
