import Mathlib
import ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

open scoped Manifold ContDiff Topology
noncomputable section

namespace ConstructionTargets.T98A06Closure

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def SmoothVectorField {X : Type} [TopologicalSpace X] {n : ℕ}
    [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
    (v : ∀ x : X, TangentSpace (𝓡 n) x) : Prop :=
  ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x => (v x : TangentBundle (𝓡 n) X))

def HasLocalSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∀ x₀ : X, ∃ U ∈ 𝓝 x₀, ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞
      (fun x => (w x : TangentBundle (𝓡 n) X)) U ∧
    ∀ x ∈ U, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

def HasSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    SmoothVectorField w ∧ ∀ x, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

/-- The pointwise linear-algebra input to the local submersion theorem: in
finite-dimensional manifold coordinates, every surjective derivative admits
a continuous linear right inverse. -/
theorem surjective_continuousLinearMap_has_rightInverse {n m : ℕ}
    (L : E n →L[ℝ] E m) (hL : Function.Surjective L) :
    ∃ R : E m →L[ℝ] E n,
      L.comp R = ContinuousLinearMap.id ℝ (E m) := by
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  refine ⟨LinearMap.toContinuousLinearMap R, ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  exact LinearMap.congr_fun hR y

#print axioms surjective_continuousLinearMap_has_rightInverse

/-- Algebraic correction used in the local submersion theorem: if `A ∘ R`
is invertible, correcting `R` by that inverse gives an exact right inverse of
`A`. -/
theorem rightInverse_of_comp_continuousLinearEquiv {n m : ℕ}
    (A : E n →L[ℝ] E m) (R : E m →L[ℝ] E n)
    (u : E m ≃L[ℝ] E m)
    (hu : A.comp R = u.toContinuousLinearMap) :
    A.comp (R.comp u.symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ (E m) := by
  apply ContinuousLinearMap.ext
  intro y
  change A (R (u.symm y)) = y
  rw [show A (R (u.symm y)) = u (u.symm y) by
    exact DFunLike.congr_fun hu (u.symm y)]
  exact u.apply_symm_apply y

#print axioms rightInverse_of_comp_continuousLinearEquiv

/-- A smoothly varying family of linear maps has a smoothly varying right
inverse wherever one fixed pointwise right inverse makes the composite
invertible.  This is the fixed-coordinate analytic step used after choosing
tangent-bundle charts in the local submersion construction. -/
theorem contDiff_rightInverse_of_comp_isInvertible
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {n m : ℕ} (A : Z → E n →L[ℝ] E m) (R : E m →L[ℝ] E n)
    (hA : ContDiff ℝ ∞ A)
    (hinv : ∀ z, ((A z).comp R).IsInvertible) :
    ∃ Q : Z → E m →L[ℝ] E n, ContDiff ℝ ∞ Q ∧
      ∀ z, (A z).comp (Q z) = ContinuousLinearMap.id ℝ (E m) := by
  let B : Z → E m →L[ℝ] E m := fun z => (A z).comp R
  let Q : Z → E m →L[ℝ] E n := fun z =>
    R.comp (ContinuousLinearMap.inverse (B z))
  refine ⟨Q, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    have hB : ContDiffAt ℝ ∞ B z :=
      hA.contDiffAt.clm_comp contDiffAt_const
    have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (B z) :=
      (hinv z).contDiffAt_map_inverse
    have hiB : ContDiffAt ℝ ∞ (fun z => ContinuousLinearMap.inverse (B z)) z :=
      hi.comp z hB
    exact contDiffAt_const.clm_comp hiB
  · intro z
    change (A z).comp (R.comp (ContinuousLinearMap.inverse (B z))) = _
    rw [← ContinuousLinearMap.comp_assoc]
    change (B z).comp (ContinuousLinearMap.inverse (B z)) = _
    exact (hinv z).self_comp_inverse

#print axioms contDiff_rightInverse_of_comp_isInvertible

/-- Applying the smoothly varying right inverse to a smooth target-coordinate
vector gives the source-coordinate lift used in a submersion chart. -/
theorem contDiff_lift_of_comp_isInvertible
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {n m : ℕ} (A : Z → E n →L[ℝ] E m) (b : Z → E m)
    (R : E m →L[ℝ] E n)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hinv : ∀ z, ((A z).comp R).IsInvertible) :
    ∃ w : Z → E n, ContDiff ℝ ∞ w ∧ ∀ z, A z (w z) = b z := by
  obtain ⟨Q, hQ, hAQ⟩ :=
    contDiff_rightInverse_of_comp_isInvertible A R hA hinv
  refine ⟨fun z ↦ Q z (b z), hQ.clm_apply hb, ?_⟩
  intro z
  exact DFunLike.congr_fun (hAQ z) (b z)

#print axioms contDiff_lift_of_comp_isInvertible

/-- Smooth fixed-trivialization coordinates determine a smooth tangent
section on any set contained in that trivialization's source. -/
theorem contMDiffOn_tangentSection_of_trivialization_coordinates
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
    (x₀ : X) (U : Set X) (w : ∀ x : X, TangentSpace (𝓡 n) x)
    (hU : U ⊆ (trivializationAt (E n) (TangentSpace (𝓡 n)) x₀).baseSet)
    (hcoord : ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (fun x ↦ ((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
        (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2) U) :
    ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞
      (fun x ↦ (w x : TangentBundle (𝓡 n) X)) U := by
  intro x hx
  exact (Bundle.Trivialization.contMDiffWithinAt_section
    (e := trivializationAt (E n) (TangentSpace (𝓡 n)) x₀) U (hU hx)).2
      (hcoord x hx)

#print axioms contMDiffOn_tangentSection_of_trivialization_coordinates

/-- A coordinate solution is the required manifold-derivative lift once the
coordinate family is identified with `mfderiv`.  Injectivity is supplied by
the target tangent trivialization at the image point. -/
theorem mfderiv_eq_of_trivialization_coordinates
    {n m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y)
    (w : ∀ x : X, TangentSpace (𝓡 n) x)
    (A : X → E n →L[ℝ] E m) (x₀ : X) (y₀ : Y) (x : X)
    (hy : f x ∈ (trivializationAt (E m) (TangentSpace (𝓡 m)) y₀).baseSet)
    (hA : ((trivializationAt (E m) (TangentSpace (𝓡 m)) y₀)
      (⟨f x, mfderiv (𝓡 n) (𝓡 m) f x (w x)⟩ :
        TangentBundle (𝓡 m) Y)).2 =
      A x (((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
        (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2))
    (hsolve : A x (((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
        (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2) =
      ((trivializationAt (E m) (TangentSpace (𝓡 m)) y₀)
        (⟨f x, v (f x)⟩ : TangentBundle (𝓡 m) Y)).2) :
    mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x) := by
  apply ((trivializationAt (E m) (TangentSpace (𝓡 m)) y₀).linearEquivAt
    ℝ (f x) hy).injective
  simpa only [Bundle.Trivialization.linearEquivAt_apply] using hA.trans hsolve

#print axioms mfderiv_eq_of_trivialization_coordinates

/-- Neighborhoodwise solutions in fixed tangent-trivialization coordinates
assemble into the local smooth lift datum used by partition-of-unity gluing. -/
theorem hasLocalSmoothLift_of_trivialization_coordinates
    {n m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y)
    (hcoord : ∀ x₀ : X, ∃ U ∈ 𝓝 x₀,
      ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
      ∃ A : X → E n →L[ℝ] E m, ∃ y₀ : Y,
        U ⊆ (trivializationAt (E n) (TangentSpace (𝓡 n)) x₀).baseSet ∧
        (∀ x ∈ U,
          f x ∈ (trivializationAt (E m) (TangentSpace (𝓡 m)) y₀).baseSet) ∧
        ContMDiffOn (𝓡 n) (𝓡 n) ∞
          (fun x ↦ ((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
            (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2) U ∧
        (∀ x ∈ U,
          ((trivializationAt (E m) (TangentSpace (𝓡 m)) y₀)
            (⟨f x, mfderiv (𝓡 n) (𝓡 m) f x (w x)⟩ :
              TangentBundle (𝓡 m) Y)).2 =
            A x (((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
              (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2)) ∧
        (∀ x ∈ U,
          A x (((trivializationAt (E n) (TangentSpace (𝓡 n)) x₀)
            (⟨x, w x⟩ : TangentBundle (𝓡 n) X)).2) =
            ((trivializationAt (E m) (TangentSpace (𝓡 m)) y₀)
              (⟨f x, v (f x)⟩ : TangentBundle (𝓡 m) Y)).2)) :
    HasLocalSmoothLift (n := n) (m := m) f v := by
  intro x₀
  obtain ⟨U, hU, w, A, y₀, hsource, htarget, hsmooth, hA, hsolve⟩ := hcoord x₀
  refine ⟨U, hU, w,
    contMDiffOn_tangentSection_of_trivialization_coordinates x₀ U w hsource hsmooth, ?_⟩
  intro x hx
  exact mfderiv_eq_of_trivialization_coordinates f v w A x₀ y₀ x
    (htarget x hx) (hA x hx) (hsolve x hx)

#print axioms hasLocalSmoothLift_of_trivialization_coordinates

theorem t98A06_global_vectorField_lift
    (hlocal : ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasLocalSmoothLift (n := n) (m := m) f v) :
    ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasSmoothLift (n := n) (m := m) f v := by
  intro n m X Y _ _ _ _ _ _ _ _ _ _ f hf hsurj v hv
  let t : ∀ x : X, Set (TangentSpace (modelWithCornersSelf ℝ (E n)) x) :=
    fun x ↦ {u | mfderiv (modelWithCornersSelf ℝ (E n))
      (modelWithCornersSelf ℝ (E m)) f x u = v (f x)}
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    exact (convex_singleton (v (f x)) : Convex ℝ {v (f x)}).linear_preimage
      (mfderiv (modelWithCornersSelf ℝ (E n))
        (modelWithCornersSelf ℝ (E m)) f x).toLinearMap
  have hloc : ∀ x₀ : X, ∃ U ∈ nhds x₀,
      ∃ w : ∀ x : X, TangentSpace (modelWithCornersSelf ℝ (E n)) x,
        ContMDiffOn (modelWithCornersSelf ℝ (E n))
          (modelWithCornersSelf ℝ (E n)).tangent ∞
          (fun x ↦ (w x : TangentBundle (modelWithCornersSelf ℝ (E n)) X)) U ∧
        ∀ x ∈ U, w x ∈ t x := by
    simpa [t] using hlocal n m X Y f hf hsurj v hv
  letI : LocallyCompactSpace X :=
    Manifold.locallyCompact_of_finiteDimensional (modelWithCornersSelf ℝ (E n))
  letI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨w, hw⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (modelWithCornersSelf ℝ (E n))
      (fun x : X ↦ TangentSpace (modelWithCornersSelf ℝ (E n)) x) t ht hloc
  refine ⟨fun x ↦ w x, w.contMDiff, ?_⟩
  intro x
  exact hw x

#print axioms t98A06_global_vectorField_lift

end ConstructionTargets.T98A06Closure
