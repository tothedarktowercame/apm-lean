import ConstructionTargets.GeometricSimplicialSubdivision
import ConstructionTargets.CoefficientSimplicialChainFinsuppRange
import ConstructionTargets.CoefficientSingularSubdivision
import ConstructionTargets.CoefficientBarycentricNaturality
import ConstructionTargets.CoefficientAffineNaturality
import ConstructionTargets.RationalLefschetz

/-! Concrete, staged ordered-face chain blueprint. -/
open Set CategoryTheory
noncomputable section
namespace ConstructionTargets.OrientedSimplicialChains

open SingularSubdivision

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The genuine degree-`k` basis: faces with `k+1` vertices.  Their canonical
orientation is the increasing order inherited from the ambient lexicographic order. -/
def FaceIndex {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  {s : Finset (Euc n) // s ∈ K.faces ∧ s.card = k + 1}

abbrev FaceModule {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  FaceIndex K k →₀ ℚ

abbrev FaceModuleCat {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :=
  ModuleCat.of ℚ (FaceModule K k)

/-- Generator-level specification of the signed deletion differential. -/
def IsSignedDeletion {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k) : Prop :=
  ∀ k (s : FaceIndex K (k + 1)), ∃ z : FaceModule K k,
    d k (Finsupp.single s 1) = z ∧ ∀ t, z t = ∑ v ∈ s.1,
      if s.1.erase v = t.1 then (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v) else 0

/-- Generator-level specification of canonical affine realization.  It pins
down the map and rules out the arbitrary-comparison defect of the old model. -/
def IsAffineComparison {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k) : Prop :=
  ∀ k (s : FaceIndex K k), ∃ σ : SingularSimplex (TopCat.of K.space) k,
    cmp k (Finsupp.single s 1) = (CoefficientH0.singularGenerator ℚ _ k σ) 1 ∧
    Set.range (continuousMapOfSingularSimplex k σ) =
      (fun x : K.space => (x : Euc n)) ⁻¹' convexHull ℝ (s.1 : Set (Euc n))

/-! Stage 1: raw data and independent obligations. -/

theorem signedDeletion_exists {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∃ d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k,
      IsSignedDeletion o K d := by
  let b : ∀ k, FaceIndex K (k + 1) → FaceModule K k := fun k s =>
    ∑ v : s.1, Finsupp.single
      (⟨s.1.erase v.1,
        K.down_closed s.2.1 (Finset.erase_subset v.1 s.1) (by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have hc := Finset.card_erase_of_mem v.2
          rw [h, Finset.card_empty, s.2.2] at hc
          omega),
        by
          rw [Finset.card_erase_of_mem v.2, s.2.2]
          omega⟩ : FaceIndex K k)
      ((-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1))
  let d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k := fun k =>
    ModuleCat.ofHom (Finsupp.linearCombination ℚ (b k))
  refine ⟨d, ?_⟩
  intro k s
  refine ⟨b k s, ?_, ?_⟩
  · simp [d]
  · intro t
    simp only [b]
    change Finsupp.applyAddHom t _ = _
    rw [map_sum]
    change (∑ v : s.1, Finsupp.single
      (⟨s.1.erase v.1,
        K.down_closed s.2.1 (Finset.erase_subset v.1 s.1) (by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have hc := Finset.card_erase_of_mem v.2
          rw [h, Finset.card_empty, s.2.2] at hc
          omega),
        by rw [Finset.card_erase_of_mem v.2, s.2.2]; omega⟩ : FaceIndex K k)
      ((-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1)) t) = _
    simp_rw [Finsupp.single_apply]
    rw [← Finset.sum_attach s.1]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Subtype.ext_iff]

theorem signedDeletion_sq_zero_aux_generator_aux_idxOf_erase
    {α : Type*} [DecidableEq α] (l : List α) (a b : α)
    (hn : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    (l.erase a).idxOf b =
      if l.idxOf a < l.idxOf b then l.idxOf b - 1 else l.idxOf b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      simp only [List.nodup_cons] at hn
      by_cases hax : a = x
      · subst a
        have hbx : b ≠ x := Ne.symm hab
        have hpos : 0 < (x :: l).idxOf b := by
          simp [List.idxOf_cons_ne, hab, hbx]
        simp [List.idxOf_cons_ne, hab, hbx, hpos]
      · have hax' : x ≠ a := Ne.symm hax
        have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left hax
        by_cases hbx : b = x
        · subst b
          simp [hax, hax', hn.1, List.idxOf_cons_ne]
        · have hbx' : x ≠ b := Ne.symm hbx
          have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left hbx
          simp only [List.erase_cons]
          simp [hax']
          rw [List.idxOf_cons_ne (l.erase a) hbx']
          simp only [List.idxOf_cons_ne l hax', List.idxOf_cons_ne l hbx']
          rw [ih hn.2 hal hbl]
          split_ifs <;> omega

theorem signedDeletion_sq_zero_aux_generator_aux_sign_cancel
    {α : Type*} [DecidableEq α] (l : List α) (a b : α)
    (hn : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    (-1 : ℚ) ^ l.idxOf a * (-1 : ℚ) ^ (l.erase a).idxOf b +
      (-1 : ℚ) ^ l.idxOf b * (-1 : ℚ) ^ (l.erase b).idxOf a = 0 := by
  rw [signedDeletion_sq_zero_aux_generator_aux_idxOf_erase l a b hn ha hb hab,
    signedDeletion_sq_zero_aux_generator_aux_idxOf_erase l b a hn hb ha hab.symm]
  have hidx : l.idxOf a ≠ l.idxOf b := by
    intro h
    apply hab
    have hi := congrArg (fun i => l[i]?) h
    have hla := List.getElem?_idxOf ha
    have hlb := List.getElem?_idxOf hb
    exact Option.some.inj (hla.symm.trans (hi.trans hlb))
  rcases lt_or_gt_of_ne hidx with hlt | hgt
  · rw [if_pos hlt, if_neg (not_lt_of_ge hlt.le)]
    have hp : 0 < l.idxOf b := lt_of_le_of_lt (Nat.zero_le _) hlt
    rw [← pow_add, ← pow_add]
    have he : l.idxOf b + l.idxOf a = l.idxOf a + (l.idxOf b - 1) + 1 := by omega
    rw [he, pow_succ]
    ring
  · rw [if_neg (not_lt_of_ge hgt.le), if_pos hgt]
    have hp : 0 < l.idxOf a := lt_of_le_of_lt (Nat.zero_le _) hgt
    rw [← pow_add, ← pow_add]
    have he : l.idxOf a + l.idxOf b = l.idxOf b + (l.idxOf a - 1) + 1 := by omega
    rw [he, pow_succ]
    ring

def signedDeletion_sq_zero_aux_generator_aux_erase {n k : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) : FaceIndex K k :=
  ⟨s.1.erase v,
    K.down_closed s.2.1 (Finset.erase_subset _ _) (by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv, s.2.2]
      omega),
    by rw [Finset.card_erase_of_mem hv, s.2.2]; omega⟩

theorem signedDeletion_sq_zero_aux_generator_aux_boundary {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (s : FaceIndex K (k + 1)) :
    d k (Finsupp.single s 1) =
      ∑ v ∈ s.1.attach, (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1) •
        Finsupp.single (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1 := by
  rcases hd k s with ⟨z, hz, hformula⟩
  rw [hz]
  ext t
  rw [hformula]
  rw [← Finset.sum_attach s.1]
  change _ = Finsupp.applyAddHom t
    (∑ v ∈ s.1.attach, (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1) •
      Finsupp.single (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : s.1.erase v.1 = t.1
  · have ht : signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2 = t :=
      Subtype.ext h
    simp [h, ht]
  · have ht : signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2 ≠ t := by
      intro he
      exact h (congrArg Subtype.val he)
    simp [h, ht]

theorem signedDeletion_sq_zero_aux_generator {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (k : ℕ) (s : FaceIndex K (k + 2)) :
    d k (d (k + 1) (Finsupp.single s 1)) = 0 := by
  sorry

theorem signedDeletion_sq_zero {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) : ∀ k, d (k + 1) ≫ d k = 0 := by
  intro k
  ext x t
  change d k (d (k + 1) (Finsupp.single x 1)) t = 0
  rw [signedDeletion_sq_zero_aux_generator o K d hd k x]
  rfl

theorem faceModule_finiteDimensional {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∀ k, FiniteDimensional ℚ (FaceModule K k) := by
  intro k
  letI : Finite K.faces := hK
  letI : Finite (FaceIndex K k) :=
    Finite.of_injective
      (fun s : FaceIndex K k => (⟨s.1, s.2.1⟩ : K.faces))
      (by
        intro s t h
        exact Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  infer_instance

theorem faceModule_zero_above {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite) :
    ∃ b, ∀ k, b < k → Subsingleton (FaceModule K k) := by
  classical
  let F : Finset (Finset (Euc n)) := hK.toFinset
  let U : Finset (Euc n) := F.biUnion id
  refine ⟨U.card, fun k hk => ?_⟩
  have hempty : IsEmpty (FaceIndex K k) :=
    ⟨fun s => by
      have hsF : s.1 ∈ F := by
        simpa [F] using s.2.1
      have hsub : s.1 ⊆ U := by
        intro x hx
        simp only [U, Finset.mem_biUnion]
        exact ⟨s.1, hsF, hx⟩
      have hcard : s.1.card ≤ U.card := Finset.card_le_card hsub
      have heq : s.1.card = k + 1 := s.2.2
      omega⟩
  letI := hempty
  infer_instance

/-! Concrete affine comparison (claude-14, 2026-10-28, after lemma-3 returned it
unstarted): defs with no proof obligations left open, three Prop leaves. -/

/-- The vertices of a face in increasing `o`-order. -/
noncomputable def faceVertices {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) : Fin (k + 1) → Euc n :=
  fun i => (s.1.sort o.le).get ⟨i, by rw [Finset.length_sort, s.2.2]; exact i.2⟩

lemma faceVertices_mem {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) (i : Fin (k + 1)) :
    faceVertices o s i ∈ s.1 := by
  have := List.get_mem (s.1.sort o.le) ⟨i, by rw [Finset.length_sort, s.2.2]; exact i.2⟩
  simpa [faceVertices] using (Finset.mem_sort o.le).1 this

/-- The affine simplex of a face. -/
noncomputable def faceMap {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) :
    C(stdSimplex ℝ (Fin (k + 1)), K.space) where
  toFun x := ⟨∑ i, x i • faceVertices o s i, by
    apply Geometry.SimplicialComplex.convexHull_subset_space s.2.1
    apply (convex_convexHull ℝ _).sum_mem (fun i _ => stdSimplex.zero_le x i)
      (by simpa using x.2.2)
    intro i _
    exact subset_convexHull ℝ _ (faceVertices_mem o s i)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_finset_sum _ fun i _ =>
      (((continuous_apply i).comp continuous_subtype_val)).smul continuous_const

/-- The singular simplex of a face. -/
noncomputable def faceSimplex {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) :
    SingularSimplex (TopCat.of K.space) k :=
  singularSimplexOfContinuousMap _ k (faceMap o s)

/-- The comparison: linear extension of `s ↦ [faceSimplex s]`. -/
noncomputable def affineCmp {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) :
    FaceModuleCat K k ⟶ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k :=
  ModuleCat.ofHom (Finsupp.lsum ℚ (fun s : FaceIndex K k =>
    (CoefficientH0.singularGenerator ℚ (TopCat.of K.space) k (faceSimplex o s)).hom))

/-- (AC1) The comparison sends a basis face to its singular simplex. -/
theorem affineCmp_single {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (k : ℕ) (s : FaceIndex K k) :
    affineCmp o K k (Finsupp.single s 1) =
      (CoefficientH0.singularGenerator ℚ _ k (faceSimplex o s)) 1 := by
  change (Finsupp.lsum ℚ (fun s : FaceIndex K k =>
    (CoefficientH0.singularGenerator ℚ (TopCat.of K.space) k
      (faceSimplex o s)).hom)) (Finsupp.single s 1) = _
  rw [Finsupp.lsum_single]

/-- (AC2) The affine simplex of a face has image exactly the face's hull. -/
theorem faceSimplex_range_aux {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) :
    Set.range (continuousMapOfSingularSimplex k (faceSimplex o s)) =
      (fun x : K.space => (x : Euc n)) ⁻¹' convexHull ℝ (s.1 : Set (Euc n)) := by
  classical
  simp only [faceSimplex, continuousMapOfSingularSimplex_ofContinuousMap]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => stdSimplex.zero_le w i) (by simpa using w.2.2)
      (fun i _ => subset_convexHull ℝ _ (faceVertices_mem o s i))
  · intro hx
    let e : Fin (k + 1) ≃ s.1 := (s.1.orderIsoOfFin s.2.2).toEquiv
    rw [Finset.convexHull_eq] at hx
    rcases hx with ⟨w, hw₀, hw₁, hwx⟩
    let u : Fin (k + 1) → ℝ := fun i => w (e i : Euc n)
    have hu : u ∈ stdSimplex ℝ (Fin (k + 1)) := by
      refine ⟨fun i => hw₀ _ (e i).2, ?_⟩
      rw [show ∑ i, u i = ∑ y : s.1, w y by
        exact Equiv.sum_comp e (fun y : s.1 => w y)]
      rw [← Finset.sum_attach] at hw₁
      exact hw₁
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    have hv (i : Fin (k + 1)) : faceVertices o s i = (e i : Euc n) := by
      set_option maxHeartbeats 5000000 in
        change (s.1.sort o.le).get _ = s.1.orderEmbOfFin s.2.2 i
        exact (Finset.orderEmbOfFin_apply s.1 s.2.2 i).symm
    rw [s.1.centerMass_eq_of_sum_1 (w := w) (z := id) hw₁] at hwx
    change (∑ i, u i • faceVertices o s i) = (x : Euc n)
    rw [show ∑ i, u i • faceVertices o s i =
        ∑ y : s.1, w y.1 • y.1 by
      simpa only [u, hv] using
        (Equiv.sum_comp e (fun y : s.1 => w y.1 • y.1))]
    rw [← Finset.sum_attach] at hwx
    exact hwx

theorem faceSimplex_range {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K k) :
    Set.range (continuousMapOfSingularSimplex k (faceSimplex o s)) =
      (fun x : K.space => (x : Euc n)) ⁻¹' convexHull ℝ (s.1 : Set (Euc n)) := by
  exact faceSimplex_range_aux o s

-- BEGIN SEAT AREA
theorem affineCmp_comm_aux_vertices {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K (k + 1))
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    faceVertices o
        (signedDeletion_sq_zero_aux_generator_aux_erase K s
          (faceVertices o s i) (faceVertices_mem o s i)) j =
      faceVertices o s (i.succAbove j) := by
  classical
  letI : LinearOrder (Euc n) := o
  let l := s.1.sort o.le
  have hli : i.1 < l.length := by simp [l, s.2.2]; omega
  have herase :
      (s.1.erase (l.get ⟨i, hli⟩)).sort o.le = l.erase (l.get ⟨i, hli⟩) := by
    apply List.Perm.eq_of_pairwise' (r := o.le)
    · exact Finset.pairwise_sort _ _
    · exact (Finset.pairwise_sort s.1 o.le).erase _
    · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
      ((Finset.sort_nodup s.1 o.le).erase _)]
      intro x
      rw [(Finset.sort_nodup s.1 o.le).mem_erase_iff]
      simp [Finset.mem_sort, l]
  have hnodup : l.Nodup := Finset.sort_nodup _ _
  simp only [faceVertices, signedDeletion_sq_zero_aux_generator_aux_erase]
  change ((s.1.erase (l.get ⟨i, hli⟩)).sort o.le).get _ = l.get _
  have hopt : ((s.1.erase (l.get ⟨i, hli⟩)).sort o.le)[j.1]? =
      l[(i.succAbove j).1]? := by
    rw [herase, hnodup.erase_get, List.getElem?_eraseIdx]
    split_ifs with h
    · congr 1
      exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt i j h).symm
    · congr 1
      exact congrArg Fin.val
        (Fin.succAbove_of_le_castSucc i j (Nat.le_of_not_gt h)).symm
  exact Option.some.inj
    ((List.getElem?_eq_getElem (by
        rw [Finset.length_sort, Finset.card_erase_of_mem]
        · rw [s.2.2]
          omega
        · exact (Finset.mem_sort o.le).1 (List.get_mem l ⟨i, hli⟩))).symm.trans
      (hopt.trans (List.getElem?_eq_getElem (by simp [l, s.2.2]; omega))))
-- END SEAT AREA

theorem affineCmp_comm_aux_face {n k : ℕ} (o : LinearOrder (Euc n))
    {K : Geometry.SimplicialComplex ℝ (Euc n)} (s : FaceIndex K (k + 1))
    (i : Fin (k + 2)) :
    (TopCat.toSSet.obj (TopCat.of K.space)).δ i (faceSimplex o s) =
      faceSimplex o
        (signedDeletion_sq_zero_aux_generator_aux_erase K s
          (faceVertices o s i) (faceVertices_mem o s i)) := by
  sorry

/-- Reindex the singular boundary (`singularGenerator_boundary`) against the
signed-deletion formula `hd`, given the face compatibility. -/
theorem affineCmp_comm_aux_sum {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hface : ∀ (k : ℕ) (s : FaceIndex K (k + 1)) (i : Fin (k + 2)),
      (TopCat.toSSet.obj (TopCat.of K.space)).δ i (faceSimplex o s) =
        faceSimplex o (signedDeletion_sq_zero_aux_generator_aux_erase K s (faceVertices o s i) (faceVertices_mem o s i)))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (k : ℕ) :
    affineCmp o K (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ affineCmp o K k := by
  sorry

/-- (AC3) The comparison is a chain map: the `i`-th singular face of
`faceSimplex s` is `faceSimplex (s.erase (i-th vertex))`
(`singularSimplexOfContinuousMap_face`, `affineSimplex` of the face inclusion),
so `singularGenerator_boundary` matches the signed-deletion formula `hd`. -/
theorem affineCmp_comm {n : ℕ} (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (k : ℕ) :
    affineCmp o K (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ affineCmp o K k := by
  exact affineCmp_comm_aux_sum o K (fun k s i => affineCmp_comm_aux_face o s i) d hd k

theorem affineComparison_exists_and_commutes {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) :
    ∃ cmp : ∀ k, FaceModuleCat K k ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k,
      IsAffineComparison K cmp ∧ ∀ k,
        cmp (k + 1) ≫ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
          d k ≫ cmp k := by
  exact ⟨affineCmp o K, fun k s => ⟨faceSimplex o s, affineCmp_single o K k s,
    faceSimplex_range o s⟩, affineCmp_comm o K d hd⟩

/-! Stage 2.  `ChainComplex.of` occurs only with the stage-one square-zero
conclusion supplied explicitly, so these declarations acquire no hidden axiom. -/

theorem orderedFace_singular_quasiIso {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (hchain : ∀ k, cmp (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp k) :
    ∀ k, Function.Bijective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (k + 2) (k + 1) k) cmp hchain) k).hom := by
  sorry

end ConstructionTargets.OrientedSimplicialChains
