import ConstructionTargets.ProductSimplexShuffleParity
import ConstructionTargets.SingularSubdivision

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexAffineRealization

universe u
open SSet
open ConstructionTargets.ProductSimplexMaximalPaths
open ConstructionTargets.SingularSubdivision

/-- The pair of topological standard-simplex vertices encoded by a path vertex. -/
def gridVertex {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (i : Fin (p + q + 1)) :
    stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1)) :=
  (standardSimplexVertices p (SSet.prodStdSimplex.objEquiv z.1 i).1,
   standardSimplexVertices q (SSet.prodStdSimplex.objEquiv z.1 i).2)

/-- Affine realization of an ordered family of vertices in a product of simplices. -/
def productAffine {n p q : ℕ}
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)),
      stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1))) :=
  ContinuousMap.prodMk
    (affineSimplex (fun i => (v i).1))
    (affineSimplex (fun i => (v i).2))

/-- The production singular simplex realized by a maximal lattice path. -/
def pathRealization {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    C(stdSimplex ℝ (Fin (p + q + 1)),
      stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1))) :=
  productAffine (gridVertex z)

@[simp] theorem productAffine_standardVertex {n p q : ℕ}
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1)))
    (i : Fin (n + 1)) :
    productAffine v (standardSimplexVertices n i) = v i := by
  apply Prod.ext
  · ext j
    simp [productAffine, affineSimplex_apply, standardSimplexVertices, Pi.single_apply]
  · ext j
    simp [productAffine, affineSimplex_apply, standardSimplexVertices, Pi.single_apply]

@[simp] theorem pathRealization_standardVertex {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (i : Fin (p + q + 1)) :
    pathRealization z (standardSimplexVertices (p + q) i) = gridVertex z i := by
  exact productAffine_standardVertex (gridVertex z) i

@[simp] theorem affineSimplex_standardVertex' {n : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (n + 1) → stdSimplex ℝ ι) (i : Fin (n + 1)) :
    affineSimplex v (standardSimplexVertices n i) = v i := by
  ext j
  simp [affineSimplex_apply, standardSimplexVertices, Pi.single_apply]

/-- Restricting an affine product simplex to a face deletes the same ordered vertex. -/
theorem productAffine_comp_face {n p q : ℕ}
    (v : Fin (n + 2) → stdSimplex ℝ (Fin (p + 1)) × stdSimplex ℝ (Fin (q + 1)))
    (i : Fin (n + 2)) :
    (productAffine v).comp (faceAffine n i) =
      productAffine (v ∘ i.succAbove) := by
  apply ContinuousMap.ext
  intro x
  apply Prod.ext
  · change affineSimplex (fun j => (v j).1) (faceAffine n i x) = _
    have h := affineSimplex_comp_affineSimplex (fun j => (v j).1)
      (fun j => standardSimplexVertices (n + 1) (i.succAbove j))
    have hx := congrArg (fun f => f x) h
    simpa [faceAffine, Function.comp_def] using hx
  · change affineSimplex (fun j => (v j).2) (faceAffine n i x) = _
    have h := affineSimplex_comp_affineSimplex (fun j => (v j).2)
      (fun j => standardSimplexVertices (n + 1) (i.succAbove j))
    have hx := congrArg (fun f => f x) h
    simpa [faceAffine, Function.comp_def] using hx


end ConstructionTargets.ProductSimplexAffineRealization
