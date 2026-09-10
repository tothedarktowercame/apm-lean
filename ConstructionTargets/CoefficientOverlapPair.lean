import ConstructionTargets.CoefficientChartLocal
noncomputable section
namespace ConstructionTargets.CoefficientOverlapPair
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal CoefficientChartPair
variable (R : Type) [CommRing R]
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
abbrev E := EuclideanSpace ℝ (Fin (m+2))
def common (a b : M) : Set M := (chartAt (E m) a).source ∩ (chartAt (E m) b).source
theorem common_open (a b : M) : IsOpen (common m a b) :=
  (chartAt (E m) a).open_source.inter (chartAt (E m) b).open_source

def restricted (a : M) (U : Set M) := (chartAt (E m) a).restr U
theorem restricted_source (a : M) (U : Set M) (hU : IsOpen U)
    (h : U ⊆ (chartAt (E m) a).source) : (restricted m a U).source = U := by
  rw [restricted, OpenPartialHomeomorph.restr_source' _ _ hU]
  exact Set.inter_eq_right.mpr h

def coordinates (a : M) (U : Set M) (hU : IsOpen U) (h : U ⊆ (chartAt (E m) a).source) :=
  (Homeomorph.setCongr (restricted_source m a U hU h).symm).trans
    (restricted m a U).toHomeomorphSourceTarget

def image (a : M) (U : Set M) (x : M) : Set (E m) :=
  {z | z + chartAt (E m) a x ∈ (restricted m a U).target}
theorem image_open (a : M) (U : Set M) (x : M) : IsOpen (image m a U x) :=
  (restricted m a U).open_target.preimage (continuous_id.add continuous_const)
def translate (a : M) (U : Set M) (x : M) : (restricted m a U).target ≃ₜ image m a U x where
  toFun y := ⟨y.val - chartAt (E m) a x, by simp [image, y.property]⟩
  invFun z := ⟨z.val + chartAt (E m) a x, z.property⟩
  left_inv y := by ext; simp
  right_inv z := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def pointed (a : M) (U : Set M) (hU : IsOpen U) (h : U ⊆ (chartAt (E m) a).source) (x : M) :=
  (coordinates m a U hU h).trans (translate m a U x)
theorem pointed_value (a : M) (U : Set M) (hU : IsOpen U) (h : U ⊆ (chartAt (E m) a).source)
    (x : M) (y : U) : (pointed m a U hU h x y).val = chartAt (E m) a y.val - chartAt (E m) a x := rfl

def left (a b x : M) := pointed m a (common m a b) (common_open m a b) Set.inter_subset_left x
def right (a b x : M) := pointed m b (common m a b) (common_open m a b) Set.inter_subset_right x
def transition (a b x : M) := (left m a b x).symm.trans (right m a b x)

theorem left_zero (a b x : M) (hx : x ∈ common m a b) : (left m a b x ⟨x,hx⟩).val = 0 := sub_self _
theorem right_zero (a b x : M) (hx : x ∈ common m a b) : (right m a b x ⟨x,hx⟩).val = 0 := sub_self _
theorem transition_square (a b x : M) (y : common m a b) :
    transition m a b x (left m a b x y) = right m a b x y :=
  congrArg (right m a b x) ((left m a b x).symm_apply_apply y)

def pair (a b x : M) (hx : x ∈ common m a b) :=
  pairIso R (transition m a b x) (left m a b x ⟨x,hx⟩)

theorem left_image_zero (a b x : M) (hx : x ∈ common m a b) :
    0 ∈ image m a (common m a b) x := (left_zero m a b x hx) ▸ (left m a b x ⟨x,hx⟩).property
theorem right_image_zero (a b x : M) (hx : x ∈ common m a b) :
    0 ∈ image m b (common m a b) x := (right_zero m a b x hx) ▸ (right m a b x ⟨x,hx⟩).property

theorem transition_value (a b x : M) (z : image m a (common m a b) x) :
    (transition m a b x z).val =
      chartAt (E m) b ((chartAt (E m) a).symm (z.val + chartAt (E m) a x)) - chartAt (E m) b x := rfl

theorem left_deleted (a b x : M) (hx : x ∈ common m a b) :
    deleted (left m a b x ⟨x,hx⟩) = localDeleted (image m a (common m a b) x) 0 := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, left_zero]
theorem right_deleted (a b x : M) (hx : x ∈ common m a b) :
    deleted (transition m a b x (left m a b x ⟨x,hx⟩)) =
      localDeleted (image m b (common m a b) x) 0 := by
  rw [transition_square]
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, right_zero]

def leftAmbient (a b x : M) : C(image m a (common m a b) x,M) :=
  (inclusion (common m a b)).comp (homeoMap (left m a b x).symm)
def rightAmbient (a b x : M) : C(image m b (common m a b) x,M) :=
  (inclusion (common m a b)).comp (homeoMap (right m a b x).symm)
theorem ambient_square (a b x : M) :
    (rightAmbient m a b x).comp (homeoMap (transition m a b x)) = leftAmbient m a b x := by
  ext z
  exact congrArg Subtype.val ((right m a b x).symm_apply_apply ((left m a b x).symm z))
theorem ambient_chain_square (a b x : M) :
    absoluteMap R (homeoMap (transition m a b x)) ≫ absoluteMap R (rightAmbient m a b x) =
      absoluteMap R (leftAmbient m a b x) := by
  simp only [absoluteMap, ← Functor.map_comp]
  exact congrArg (fun f => (chains R).map (TopCat.toSSet.map (TopCat.ofHom f))) (ambient_square m a b x)

theorem projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (left m a b x ⟨x,hx⟩)))).f n ≫
      (pair R m a b x hx).hom.f n =
    (absoluteMap R (homeoMap (transition m a b x))).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (transition m a b x (left m a b x ⟨x,hx⟩))))).f n :=
  CoefficientRadialPair.projection_degree R (deleted (left m a b x ⟨x,hx⟩))
    (deleted (transition m a b x (left m a b x ⟨x,hx⟩))) (homeoMap (transition m a b x))
    (fun _ hy h => hy ((transition m a b x).injective h)) n

theorem pair_inverse_left (a b x : M) (hx : x ∈ common m a b) :
    (pair R m a b x hx).inv ≫ (pair R m a b x hx).hom = 𝟙 _ := (pair R m a b x hx).inv_hom_id
theorem pair_inverse_right (a b x : M) (hx : x ∈ common m a b) :
    (pair R m a b x hx).hom ≫ (pair R m a b x hx).inv = 𝟙 _ := (pair R m a b x hx).hom_inv_id

def integral_overlap (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := pair ℤ m a b x hx
def rational_overlap (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := pair ℚ m a b x hx
theorem inverse_projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (transition m a b x (left m a b x ⟨x,hx⟩))))).f n ≫
      (pair R m a b x hx).inv.f n =
    (absoluteMap R (homeoMap (transition m a b x).symm)).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (left m a b x ⟨x,hx⟩)))).f n :=
  CoefficientRadialPair.projection_degree R
    (deleted (transition m a b x (left m a b x ⟨x,hx⟩))) (deleted (left m a b x ⟨x,hx⟩))
    (homeoMap (transition m a b x).symm) (fun y hy h => hy (by
      change (transition m a b x).symm y = left m a b x ⟨x,hx⟩ at h
      exact ((transition m a b x).apply_symm_apply y).symm.trans (congrArg (transition m a b x) h))) n

def homology (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (pair R m a b x hx)
theorem homology_forward (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (homology R m a b x hx n).hom = HomologicalComplex.homologyMap (pair R m a b x hx).hom n := rfl
#print axioms inverse_projection
#print axioms homology_forward
#print axioms common_open
#print axioms restricted_source
#print axioms pointed_value
#print axioms image_open
#print axioms transition_value
#print axioms transition_square
#print axioms left_image_zero
#print axioms right_image_zero
#print axioms left_deleted
#print axioms right_deleted
#print axioms ambient_square
#print axioms ambient_chain_square
#print axioms projection
#print axioms pair_inverse_left
#print axioms pair_inverse_right
#print axioms integral_overlap
#print axioms rational_overlap
end ConstructionTargets.CoefficientOverlapPair
