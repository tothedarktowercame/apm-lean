import Mathlib
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # APM t99J04 — inverse function theorem and compact local diffeomorphisms -/

open scoped Manifold

noncomputable section

abbrev apm_t99J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_t99J04_coordinateMap {n : ℕ} {X : Type} (f : Fin n → X → ℝ) :
    X → apm_t99J04_Euclidean n :=
  fun p ↦ WithLp.toLp 2 (fun i ↦ f i p)

lemma apm_t99J04_dualCoordinates_bijective
    {n : ℕ} (hn : 0 < n) {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hfin : Module.finrank ℝ V = n)
    (phi : Fin n → Module.Dual ℝ V) (hli : LinearIndependent ℝ phi) :
    Function.Bijective (fun v : V ↦ fun i ↦ phi i v) := by
  let L : V →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi phi
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hcard : Fintype.card (Fin n) =
      Module.finrank ℝ (Module.Dual ℝ V) := by
    rw [Fintype.card_fin, Subspace.dual_finrank_eq, hfin]
  let b : Module.Basis (Fin n) ℝ (Module.Dual ℝ V) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = phi i := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    ext v
    simp only [Submodule.mem_bot, LinearMap.mem_ker, L]
    constructor
    · intro hv
      apply (Module.forall_dual_apply_eq_zero_iff ℝ v).mp
      intro psi
      rw [← b.sum_repr psi, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      rw [hb i]
      have hi0 : phi i v = 0 := congrFun hv i
      simp [hi0]
    · rintro rfl
      simp
  have hdim : Module.finrank ℝ V = Module.finrank ℝ (Fin n → ℝ) := by
    rw [hfin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact ⟨hLinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLinj⟩

lemma apm_t99J04_surjective_of_isLocalDiffeomorph
    {E E' X Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace E' Y] (f : X → Y)
    (hf : IsLocalDiffeomorph (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := hf.isOpen_range
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf.contMDiff.continuous).isClosed
  have hrange : Set.range f = Set.univ :=
    (show IsClopen (Set.range f) from ⟨hclosed, hopen⟩).eq_univ
      (Set.range_nonempty f)
  exact Set.range_eq_univ.mp hrange

lemma apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT
    {E E' X Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [CompleteSpace E']
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) (⊤ : ℕ∞) X]
    [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace E' Y] [IsManifold (𝓘(ℝ, E')) (⊤ : ℕ∞) Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x))
    (hlocalIFT : ∀ x,
      ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f x →
      Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x) →
      IsLocalDiffeomorphAt (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f x) :
    Function.Surjective f := by
  apply apm_t99J04_surjective_of_isLocalDiffeomorph (E := E) (E' := E') f
  intro x
  exact hlocalIFT x hf.contMDiffAt (hbij x)

/-- LIBRARY: the missing boundaryless finite-dimensional manifold inverse
function theorem. -/
theorem apm_t99J04_bridge_local_inverse_function
    {E E' X Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [CompleteSpace E']
    [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓘(ℝ, E)) (⊤ : ℕ∞) X]
    [TopologicalSpace Y] [ChartedSpace E' Y]
    [IsManifold (𝓘(ℝ, E')) (⊤ : ℕ∞) Y]
    (f : X → Y) (x : X)
    (hf : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f x)
    (hbij : Function.Bijective
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x)) :
    IsLocalDiffeomorphAt (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f x := by
  sorry

-- BEGIN SEAT AREA
theorem apm_t99J04_coordinateMap_contMDiff
    (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t99J04_Euclidean n) X]
    [IsManifold (𝓘(ℝ, apm_t99J04_Euclidean n)) (⊤ : ℕ∞) X]
    (f : Fin n → X → ℝ)
    (hf : ∀ i,
      ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (f i)) :
    ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n))
      𝓘(ℝ, apm_t99J04_Euclidean n) (⊤ : ℕ∞)
      (apm_t99J04_coordinateMap f) := by
  have hpi : ContMDiff (modelWithCornersSelf ℝ (apm_t99J04_Euclidean n))
      (modelWithCornersSelf ℝ (Fin n → ℝ)) (⊤ : ℕ∞) (fun p i ↦ f i p) :=
    contMDiff_pi_space.2 hf
  have hlp : ContMDiff (modelWithCornersSelf ℝ (Fin n → ℝ))
      (modelWithCornersSelf ℝ (apm_t99J04_Euclidean n)) (⊤ : ℕ∞)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm :=
    ContinuousLinearMap.contMDiff
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  exact hlp.comp hpi
-- END SEAT AREA

theorem apm_t99J04_bridge_coordinateMap_mfderiv_bijective
    (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t99J04_Euclidean n) X]
    [IsManifold (𝓘(ℝ, apm_t99J04_Euclidean n)) (⊤ : ℕ∞) X]
    (x : X) (f : Fin n → X → ℝ)
    (hf : ∀ i,
      ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (f i))
    (hcoord : ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n))
      𝓘(ℝ, apm_t99J04_Euclidean n) (⊤ : ℕ∞)
      (apm_t99J04_coordinateMap f))
    (hli : LinearIndependent ℝ
      (fun i : Fin n ↦
        (NormedSpace.fromTangentSpace (f i x)).toContinuousLinearMap ∘L
          mfderiv (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (f i) x)) :
    Function.Bijective
      (mfderiv (𝓘(ℝ, apm_t99J04_Euclidean n))
        𝓘(ℝ, apm_t99J04_Euclidean n) (apm_t99J04_coordinateMap f) x) := by
  sorry

theorem apm_t99j04 :
    (∀ (n : ℕ) (X : Type) [TopologicalSpace X]
      [ChartedSpace (apm_t99J04_Euclidean n) X]
      [IsManifold (𝓘(ℝ, apm_t99J04_Euclidean n)) (⊤ : ℕ∞) X]
      (x : X) (f : Fin n → X → ℝ),
      (∀ i, ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (f i)) →
      LinearIndependent ℝ
        (fun i : Fin n ↦
          (NormedSpace.fromTangentSpace (f i x)).toContinuousLinearMap ∘L
            mfderiv (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (f i) x) →
      IsLocalDiffeomorphAt (𝓘(ℝ, apm_t99J04_Euclidean n))
        𝓘(ℝ, apm_t99J04_Euclidean n) (⊤ : ℕ∞) (apm_t99J04_coordinateMap f) x) ∧
    (∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [CompleteSpace E']
      (X Y : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [Nonempty X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) (⊤ : ℕ∞) X]
      [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
      [ChartedSpace E' Y] [IsManifold (𝓘(ℝ, E')) (⊤ : ℕ∞) Y]
      (f : X → Y),
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) (⊤ : ℕ∞) f →
      (∀ x, Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x)) →
      Function.Surjective f) := by
  constructor
  · intro n X _ _ _ x f hf hli
    have hsmooth := apm_t99J04_coordinateMap_contMDiff n X f hf
    exact apm_t99J04_bridge_local_inverse_function _ _ hsmooth.contMDiffAt
      (apm_t99J04_bridge_coordinateMap_mfderiv_bijective n X x f hf hsmooth hli)
  · intro E E' _ _ _ _ _ _ _ _ X Y _ _ _ _ _ _ _ _ _ _ _ f hf hbij
    exact apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT f hf hbij
      (fun x hx hb ↦ apm_t99J04_bridge_local_inverse_function f x hx hb)

#print axioms apm_t99j04
