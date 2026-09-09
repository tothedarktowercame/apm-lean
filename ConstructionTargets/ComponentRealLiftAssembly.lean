import ConstructionTargets.ClassicalLocalPathConnectivity
noncomputable section
open Set Topology ContinuousMap
namespace ConstructionTargets.ComponentRealLiftAssembly
variable {X : Type} [TopologicalSpace X]
abbrev componentFiber (c : ConnectedComponents X) := {x : X // (x : ConnectedComponents X) = c}

def componentDecomposition [LocallyConnectedSpace X] :
    (Σ c : ConnectedComponents X, componentFiber c) ≃ₜ X :=
  (Equiv.sigmaFiberEquiv (fun x : X => (x : ConnectedComponents X))).toHomeomorphOfContinuousOpen
    (continuous_sigma (fun _ => continuous_subtype_val))
    (isOpenMap_sigma.mpr (fun c =>
      (isOpen_discrete ({c} : Set (ConnectedComponents X))).preimage
        ConnectedComponents.continuous_coe |>.isOpenMap_subtype_val))

def assembledLift [LocallyConnectedSpace X]
    (F : ∀ c : ConnectedComponents X, C(componentFiber c, ℝ)) : C(X,ℝ) :=
  (⟨fun u => F u.1 u.2, continuous_sigma (fun c => (F c).continuous)⟩ :
    C((Σ c : ConnectedComponents X, componentFiber c), ℝ)).comp
    ⟨(componentDecomposition (X := X)).symm, (componentDecomposition (X := X)).symm.continuous⟩

theorem assembledLift_apply [LocallyConnectedSpace X]
    (F : ∀ c : ConnectedComponents X, C(componentFiber c, ℝ)) (x : X) :
    assembledLift F x = F (x : ConnectedComponents X) ⟨x,rfl⟩ := rfl

theorem exists_global_lift [LocallyConnectedSpace X] (f : C(X,Circle))
    (h : ∀ c : ConnectedComponents X, ∃ F : C(componentFiber c, ℝ),
      ∀ x, Circle.exp (F x) = f x.val) :
    ∃ F : C(X,ℝ), ∀ x, Circle.exp (F x) = f x := by
  choose F hF using h
  exact ⟨assembledLift F, fun x => hF (x : ConnectedComponents X) ⟨x,rfl⟩⟩

theorem nullhomotopic_of_component_lifts [LocallyConnectedSpace X] (f : C(X,Circle))
    (h : ∀ c : ConnectedComponents X, ∃ F : C(componentFiber c, ℝ),
      ∀ x, Circle.exp (F x) = f x.val) :
    ContinuousMap.Homotopic f (ContinuousMap.const X 1) := by
  obtain ⟨F,hF⟩ := exists_global_lift f h
  refine ⟨{ toFun := fun tx => Circle.exp ((1-(tx.1 : ℝ))*F tx.2)
            continuous_toFun := by fun_prop
            map_zero_left := by intro x; simpa using hF x
            map_one_left := by intro x; simp }⟩

def componentInclusion (c : ConnectedComponents X) : C(componentFiber c, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem component_loop_naturality (f : C(X,Circle)) (c : ConnectedComponents X)
    (x : componentFiber c) (p : FundamentalGroup (componentFiber c) x) :
    FundamentalGroup.map (f.comp (componentInclusion c)) x p =
      FundamentalGroup.map f x.val (FundamentalGroup.map (componentInclusion c) x p) := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply Quotient.sound
    exact ⟨Path.Homotopy.refl _⟩

theorem componentFiber_eq (x : X) :
    {y : X | (y : ConnectedComponents X) = (x : ConnectedComponents X)} = connectedComponent x :=
  connectedComponents_preimage_singleton

theorem componentFiber_pathConnected (hX : LocallyContractibleSpace X)
    (c : ConnectedComponents X) : PathConnectedSpace (componentFiber c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change PathConnectedSpace {y : X | (y : ConnectedComponents X) = (x : ConnectedComponents X)}
  rw [componentFiber_eq]
  exact ClassicalLocalPathConnectivity.component_pathConnected hX x

theorem component_loop_trivial (f : C(X,Circle)) (c : ConnectedComponents X)
    (x : componentFiber c)
    (h : ∀ p : FundamentalGroup X x.val, FundamentalGroup.map f x.val p = 1)
    (p : FundamentalGroup (componentFiber c) x) :
    FundamentalGroup.map (f.comp (componentInclusion c)) x p = 1 := by
  rw [component_loop_naturality]
  exact h _

theorem classical_component_lifts_nullhomotopic (hX : LocallyContractibleSpace X)
    (f : C(X,Circle))
    (h : ∀ c : ConnectedComponents X, ∃ F : C(componentFiber c, ℝ),
      ∀ x, Circle.exp (F x) = f x.val) :
    ContinuousMap.Homotopic f (ContinuousMap.const X 1) := by
  letI := ClassicalLocalPathConnectivity.locPathConnected_of_classical hX
  exact nullhomotopic_of_component_lifts f h

theorem empty_domain_lift [IsEmpty X] (f : C(X,Circle)) :
    ∃ F : C(X,ℝ), ∀ x, Circle.exp (F x) = f x :=
  ⟨ContinuousMap.const X 0, fun x => isEmptyElim x⟩

end ConstructionTargets.ComponentRealLiftAssembly
#print axioms ConstructionTargets.ComponentRealLiftAssembly.exists_global_lift
#print axioms ConstructionTargets.ComponentRealLiftAssembly.component_loop_naturality
#print axioms ConstructionTargets.ComponentRealLiftAssembly.nullhomotopic_of_component_lifts

#print axioms ConstructionTargets.ComponentRealLiftAssembly.componentDecomposition
#print axioms ConstructionTargets.ComponentRealLiftAssembly.componentFiber_eq
#print axioms ConstructionTargets.ComponentRealLiftAssembly.componentFiber_pathConnected
#print axioms ConstructionTargets.ComponentRealLiftAssembly.component_loop_trivial
#print axioms ConstructionTargets.ComponentRealLiftAssembly.classical_component_lifts_nullhomotopic
#print axioms ConstructionTargets.ComponentRealLiftAssembly.empty_domain_lift
