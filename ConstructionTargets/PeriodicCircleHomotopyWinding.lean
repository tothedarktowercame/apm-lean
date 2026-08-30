import ConstructionTargets.CircleExponentialPathLift

/-!
# Winding invariance under a free homotopy of circle loops

The homotopy need not fix the common basepoint.  We first lift its moving
basepoint and then lift the whole square.  The difference between the two
lifted path endpoints is continuous in the homotopy parameter and has constant
circle exponential, so covering-space uniqueness makes that difference
constant.
-/

open scoped unitInterval

namespace ConstructionTargets.PeriodicCircleHomotopyWinding

open ConstructionTargets.CircleWindingUniqueness

/-- The path traced by the left edge of a square homotopy. -/
noncomputable def leftEdge (H : C(I × I, Circle)) : C(I, Circle) :=
  H.comp ((ContinuousMap.const I (0 : I)).prodMk (ContinuousMap.id I))

/-- Lift the moving basepoint of a free homotopy, starting at `a`. -/
noncomputable def liftedLeftEdge (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath (leftEdge H) a h0

/-- Lift the full homotopy square from its already lifted left edge. -/
noncomputable def liftedSquare (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a) : C(I × I, ℝ) :=
  Circle.isCoveringMap_exp.liftHomotopy H (liftedLeftEdge H a h0) fun s ↦ by
    exact (congr_fun
      (Circle.isCoveringMap_exp.liftPath_lifts (leftEdge H) a h0) s).symm

/-- The lifted square projects to the given homotopy. -/
theorem exp_liftedSquare (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a) (p : I × I) :
    Circle.exp (liftedSquare H a h0 p) = H p :=
  congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H
    (liftedLeftEdge H a h0) _) p

/-- The left edge of the lifted square is the chosen moving-basepoint lift. -/
theorem liftedSquare_zero (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a) (s : I) :
    liftedSquare H a h0 (0, s) = liftedLeftEdge H a h0 s :=
  Circle.isCoveringMap_exp.liftHomotopy_zero H (liftedLeftEdge H a h0) _ s

/-- The real endpoint displacement of the lifted loop at homotopy time `s`. -/
noncomputable def endpointDisplacement (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a) (s : I) : ℝ :=
  liftedSquare H a h0 (1, s) - liftedSquare H a h0 (0, s)

/-- For a free homotopy through loops, the lifted endpoint displacement is
constant.  This is the covering-space form of homotopy invariance of winding. -/
theorem endpointDisplacement_eq (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a)
    (hloop : ∀ s : I, H (1, s) = H (0, s)) (s s' : I) :
    endpointDisplacement H a h0 s = endpointDisplacement H a h0 s' := by
  apply Circle.isCoveringMap_exp.const_of_comp
      (((liftedSquare H a h0).continuous.comp
          ((ContinuousMap.const I (1 : I)).prodMk (ContinuousMap.id I)).continuous).sub
        ((liftedSquare H a h0).continuous.comp
          ((ContinuousMap.const I (0 : I)).prodMk (ContinuousMap.id I)).continuous))
  · intro u v
    rw [Circle.exp_sub, Circle.exp_sub]
    change Circle.exp (liftedSquare H a h0 (1, u)) /
        Circle.exp (liftedSquare H a h0 (0, u)) =
      Circle.exp (liftedSquare H a h0 (1, v)) /
        Circle.exp (liftedSquare H a h0 (0, v))
    rw [exp_liftedSquare H a h0, exp_liftedSquare H a h0,
      exp_liftedSquare H a h0, exp_liftedSquare H a h0,
      hloop u, hloop v]
    simp

/-- Every loop slice of the lifted square has a unique integral endpoint
displacement. -/
theorem existsUnique_endpointWinding_at (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a)
    (hloop : ∀ s : I, H (1, s) = H (0, s)) (s : I) :
    ∃! n : ℤ, IsEndpointWinding (liftedSquare H a h0 (1, s))
      (liftedSquare H a h0 (0, s)) n := by
  apply (exp_eq_iff_existsUnique_endpointWinding _ _).mp
  rw [exp_liftedSquare H a h0, exp_liftedSquare H a h0]
  exact hloop s

/-- An endpoint winding integer at one end of a free loop homotopy is the same
endpoint winding integer at the other end. -/
theorem endpointWinding_transport (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a)
    (hloop : ∀ s : I, H (1, s) = H (0, s)) (n : ℤ)
    (hn : IsEndpointWinding (liftedSquare H a h0 (1, 0))
      (liftedSquare H a h0 (0, 0)) n) :
    IsEndpointWinding (liftedSquare H a h0 (1, 1))
      (liftedSquare H a h0 (0, 1)) n := by
  unfold IsEndpointWinding at hn ⊢
  have hd := endpointDisplacement_eq H a h0 hloop 0 1
  unfold endpointDisplacement at hd
  linarith

/-- Consequently, the unique endpoint winding extracted at the two ends of a
free homotopy through loops is the same integer. -/
theorem uniqueEndpointWinding_agrees (H : C(I × I, Circle)) (a : ℝ)
    (h0 : H (0, 0) = Circle.exp a)
    (hloop : ∀ s : I, H (1, s) = H (0, s))
    {m n : ℤ}
    (hm : IsEndpointWinding (liftedSquare H a h0 (1, 0))
      (liftedSquare H a h0 (0, 0)) m)
    (hn : IsEndpointWinding (liftedSquare H a h0 (1, 1))
      (liftedSquare H a h0 (0, 1)) n) :
    m = n :=
  endpointWinding_unique (endpointWinding_transport H a h0 hloop m hm) hn

#print axioms exp_liftedSquare
#print axioms endpointDisplacement_eq
#print axioms existsUnique_endpointWinding_at
#print axioms endpointWinding_transport
#print axioms uniqueEndpointWinding_agrees

end ConstructionTargets.PeriodicCircleHomotopyWinding
