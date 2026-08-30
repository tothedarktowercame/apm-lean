import ConstructionTargets.SimplyConnectedOpenCover

/-!
# Simply connected spheres and products

Generic closure of simple connectivity under products, and the sharp
Euclidean-sphere result in dimensions at least two.
-/

noncomputable section

namespace ConstructionTargets.SimplyConnectedSphereProducts

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A product of simply connected spaces is simply connected. -/
theorem simplyConnectedSpace_prod [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] : SimplyConnectedSpace (X × Y) := by
  letI : PathConnectedSpace (X × Y) :=
    { nonempty := Nonempty.map2 (fun x y ↦ (x, y)) inferInstance inferInstance
      joined := fun x y ↦ ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
        (PathConnectedSpace.somePath x.2 y.2)⟩ }
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · infer_instance
  · intro x y p q
    apply Path.Homotopic.Quotient.eq.mp
    calc
      Path.Homotopic.Quotient.mk p =
          Path.Homotopic.prod
            (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk p))
            (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk p)) :=
        (Path.Homotopic.prod_projLeft_projRight _).symm
      _ = Path.Homotopic.prod
            (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk q))
            (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk q)) := by
        exact congrArg₂ Path.Homotopic.prod
          (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      _ = Path.Homotopic.Quotient.mk q :=
        Path.Homotopic.prod_projLeft_projRight _

/-- The unit sphere in `ℝ^(n+1)` is simply connected exactly in the range
needed here: sphere dimension at least two. -/
theorem euclideanSphere_simplyConnected (n : Nat) (hn : 2 ≤ n) :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv0 : v ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x 0) h
    simpa [v] using h0
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp [Module.finrank_fin_fun]⟩
  have hfin : Module.finrank ℝ (ℝ ∙ v)ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton hv0
  apply simplyConnectedSpace_sphere_of_pole v hv
  rw [← Module.finrank_eq_rank, hfin]
  exact_mod_cast hn

#print axioms simplyConnectedSpace_prod
#print axioms euclideanSphere_simplyConnected

end ConstructionTargets.SimplyConnectedSphereProducts
