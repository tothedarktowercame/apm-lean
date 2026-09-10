import ConstructionTargets.CoefficientIteratedHomotopy
noncomputable section
namespace ConstructionTargets.CoefficientSmallComparison
open CategoryTheory CategoryTheory.Limits
open CoefficientSmallH0
variable (R : Type) [CommRing R]
variable {X α : Type} [TopologicalSpace X] (U : α → Set X)

def elementHom {M : ModuleCat R} (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
@[simp] theorem elementHom_one {M : ModuleCat R} (x : M) : elementHom R x 1 = x := by
  simp [elementHom]

theorem cycle_lift (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (q : C.X (n+1)) (hq : C.d (n+1) n q = 0) :
    ∃ x : C.cycles (n+1), C.iCycles (n+1) x = q := by
  have h : elementHom R q ≫ C.d (n+1) n = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change C.d (n+1) n (r • q) = 0
    simp [hq]
  refine ⟨C.liftCycles (elementHom R q) n (by simp) h 1, ?_⟩
  have he := ConcreteCategory.congr_hom (C.liftCycles_i (elementHom R q) n (by simp) h) 1
  exact he.trans (elementHom_one R q)

theorem exists_boundary (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (x : C.cycles n) (h : C.homologyπ n x = 0) :
    ∃ b : C.X (n+1), C.d (n+1) n b = C.iCycles n x := by
  let S := ShortComplex.mk (C.toCycles (n+1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n+1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel (n+1) n (by simp))
  obtain ⟨b,hb⟩ := (S.moduleCat_exact_iff.mp hS) x h
  change C.toCycles (n+1) n b = x at hb
  refine ⟨b, ?_⟩
  have hi := ConcreteCategory.congr_hom (C.toCycles_i (n+1) n) b
  simpa only [CategoryTheory.comp_apply, hb] using hi.symm

theorem surjective_succ (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap (inc R U) (n+1)) := by
  intro y
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective ((L R (X := X)).homologyπ (n+1))).mp inferInstance y
  let S := CoefficientEventualSmallness.subdivisionIterate R (X := X)
  obtain ⟨k,hk⟩ := CoefficientEventualSmallness.actual_chain_eventual R U (n+1)
    ((L R).iCycles (n+1) x) ho hc
  obtain ⟨q,hq⟩ := hk k le_rfl
  have hdq : (K R U).d (n+1) n q = 0 := by
    apply (ModuleCat.mono_iff_injective ((inc R U).f n)).mp inferInstance
    have hcomm := ConcreteCategory.congr_hom ((inc R U).comm (n+1) n) q
    have hs := ConcreteCategory.congr_hom ((S k).comm (n+1) n) ((L R).iCycles (n+1) x)
    have hz := ConcreteCategory.congr_hom ((L R (X := X)).iCycles_d (n+1) n) x
    simp only [CategoryTheory.comp_apply] at hcomm hs hz
    rw [map_zero, ← hcomm, hq]
    change (L R).d (n+1) n ((S k).f (n+1) _) = 0
    rw [hs, hz]
    simp
  obtain ⟨w,hw⟩ := cycle_lift R (K R U) n q hdq
  have hcy : HomologicalComplex.cyclesMap (inc R U) (n+1) w =
      HomologicalComplex.cyclesMap (S k) (n+1) x := by
    apply (ModuleCat.mono_iff_injective ((L R (X := X)).iCycles (n+1))).mp inferInstance
    have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (inc R U) (n+1)) w
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (S k) (n+1)) x
    simp only [CategoryTheory.comp_apply] at h1 h2
    rw [h1, hw, hq]
    exact h2.symm
  refine ⟨(K R U).homologyπ (n+1) w, ?_⟩
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inc R U) (n+1)) w
  have h2 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (S k) (n+1)) x
  simp only [CategoryTheory.comp_apply] at h1 h2
  rw [h1, hcy, ← h2]
  change HomologicalComplex.homologyMap (CoefficientEventualSmallness.subdivisionIterate R k) (n+1) _ = _
  rw [CoefficientIteratedHomotopy.absolute_homology_identity]
  exact hx

theorem injective_all (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap (inc R U) n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective ((K R U).homologyπ n)).mp inferInstance y
  let xp := HomologicalComplex.cyclesMap (inc R U) n x
  have hxp : (L R (X := X)).homologyπ n xp = 0 := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inc R U) n) x
    simpa only [CategoryTheory.comp_apply, xp, hx, hy] using h.symm
  obtain ⟨b,hb⟩ := exists_boundary R (L R (X := X)) n xp hxp
  obtain ⟨k,hk⟩ := CoefficientEventualSmallness.actual_chain_eventual R U (n+1) b ho hc
  obtain ⟨q,hq⟩ := hk k le_rfl
  let S := CoefficientEventualSmallness.subdivisionIterate R (X := X) k
  let T := CoefficientIteratedHomotopy.smallIterate R U k
  have hqd : (K R U).d (n+1) n q = T.f n ((K R U).iCycles n x) := by
    apply (ModuleCat.mono_iff_injective ((inc R U).f n)).mp inferInstance
    have hi := ConcreteCategory.congr_hom ((inc R U).comm (n+1) n) q
    have hs := ConcreteCategory.congr_hom (S.comm (n+1) n) b
    have hcy := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (inc R U) n) x
    have ht := ConcreteCategory.congr_hom (congrArg (fun f => f.f n)
      (CoefficientIteratedHomotopy.iterate_inclusion R U k)) ((K R U).iCycles n x)
    change (inc R U).f n (T.f n _) = S.f n ((inc R U).f n _) at ht
    simp only [CategoryTheory.comp_apply] at hi hs hcy
    rw [← hi, hq]
    change (L R).d (n+1) n (S.f (n+1) b) = _
    rw [hs, hb]
    change S.f n ((L R).iCycles n (HomologicalComplex.cyclesMap (inc R U) n x)) = _
    rw [hcy]
    exact ht.symm
  have hqx : (K R U).toCycles (n+1) n q = HomologicalComplex.cyclesMap T n x := by
    apply (ModuleCat.mono_iff_injective ((K R U).iCycles n)).mp inferInstance
    have h1 := ConcreteCategory.congr_hom ((K R U).toCycles_i (n+1) n) q
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i T n) x
    simp only [CategoryTheory.comp_apply] at h1 h2
    rw [h1, hqd]
    exact h2.symm
  have hz := ConcreteCategory.congr_hom ((K R U).toCycles_comp_homologyπ (n+1) n) q
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality T n) x
  simp only [CategoryTheory.comp_apply] at hz hn
  rw [hqx, ← hn] at hz
  change HomologicalComplex.homologyMap (CoefficientIteratedHomotopy.smallIterate R U k) n
    ((K R U).homologyπ n x) = _ at hz
  rw [CoefficientIteratedHomotopy.small_homology_identity] at hz
  simpa only [CategoryTheory.id_apply, hx] using hz

theorem inclusion_isIso (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (inc R U) n) := by
  cases n with
  | zero => exact CoefficientSmallH0.h0_isIso R U ho hc
  | succ n =>
    letI : Mono (HomologicalComplex.homologyMap (inc R U) (n+1)) :=
      (ModuleCat.mono_iff_injective _).mpr (injective_all R U ho hc (n+1))
    letI : Epi (HomologicalComplex.homologyMap (inc R U) (n+1)) :=
      (ModuleCat.epi_iff_surjective _).mpr (surjective_succ R U ho hc n)
    exact isIso_of_mono_of_epi _

/-- All spaces, coefficient rings and cover index types are Type 0. -/
def homologyIso (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (K R U).homology n ≅ (L R (X := X)).homology n := by
  letI := inclusion_isIso R U ho hc n
  exact asIso (HomologicalComplex.homologyMap (inc R U) n)

theorem homologyIso_hom (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (homologyIso R U ho hc n).hom = HomologicalComplex.homologyMap (inc R U) n := rfl

theorem inverse_left (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (homologyIso R U ho hc n).inv ≫ HomologicalComplex.homologyMap (inc R U) n = 𝟙 _ :=
  (homologyIso R U ho hc n).inv_hom_id

theorem inverse_right (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    HomologicalComplex.homologyMap (inc R U) n ≫ (homologyIso R U ho hc n).inv = 𝟙 _ :=
  (homologyIso R U ho hc n).hom_inv_id

def integral_interval (n : ℕ) := homologyIso ℤ CoefficientSmallPath.intervalCover
  CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers n

def rational_interval (n : ℕ) := homologyIso ℚ CoefficientSmallPath.intervalCover
  CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers n

#print axioms surjective_succ
#print axioms injective_all
#print axioms inclusion_isIso
#print axioms homologyIso_hom
#print axioms inverse_left
#print axioms inverse_right
#print axioms integral_interval
#print axioms rational_interval
end ConstructionTargets.CoefficientSmallComparison
