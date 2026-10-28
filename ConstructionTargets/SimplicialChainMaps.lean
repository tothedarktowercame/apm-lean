import ConstructionTargets.OrientedSimplicialChains
import ConstructionTargets.GeometricSimplicialSubdivision
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.SimplicialSingularComparison

/-! Concrete chain maps used in the finite-polyhedron Lefschetz argument. -/
open Set CategoryTheory
open ConstructionTargets.OrientedSimplicialChains
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.SimplicialChainMaps

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev GSC (n : ℕ) := Geometry.SimplicialComplex ℝ (Euc n)

/-- The parity of the inversions created by applying `h` to the increasing
vertices of `s`.  This definition is meaningful even when `h` has collisions;
the vertex-chain specification uses it only in the injective case. -/
/- claude-14 fix 2026-10-28 (from lemma-3's sign leaf): the inversion test used
`>` on `Euc m`, which resolves to the POINTWISE partial order of EuclideanSpace,
not `om`; pointwise-incomparable images were never counted, so this was not the
sign of the sorting permutation. It now compares with `om` explicitly. -/
def sortingSign {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (s : Finset (Euc n)) (h : Euc n → Euc m) : ℚ :=
  (-1 : ℚ) ^ ((Finset.univ.filter fun ij : Fin s.card × Fin s.card =>
    ij.1 < ij.2 ∧
      @LT.lt (Euc m) om.toLT (h ((s.1.sort on.le).getD ij.2 0))
        (h ((s.1.sort on.le).getD ij.1 0))).card)

/-- Generator formula for the ordered-face map of a simplicial vertex map.
It is zero on a collapsed face and otherwise is the image face with sorting sign. -/
def IsVertexChainMap {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k) : Prop :=
  ∀ k (s : FaceIndex K k),
    if hinj : (s.1.image h).card = k + 1 then
      ∃ t : FaceIndex L k, t.1 = s.1.image h ∧
        hm k (Finsupp.single s 1) = Finsupp.single t (sortingSign on om s.1 h)
    else hm k (Finsupp.single s 1) = 0

/-- A face of `K'` is carried by an old face when all its vertices lie in it. -/
def IsCarriedBy {n : ℕ} (K K' : GSC n) (u : Finset (Euc n)) (s : Finset (Euc n)) : Prop :=
  u ∈ K'.faces ∧ s ∈ K.faces ∧ (u : Set (Euc n)) ⊆ s

/-- Generator-level subdivision formula: coefficients are signed flag simplices,
and every occurring simplex is carried by the source face.  `IsFlagSimplex`
records the strict chain of old faces whose barycenters form `u`. -/
def IsFlagSimplex {n : ℕ} (K K' : GSC n) (s u : Finset (Euc n)) : Prop :=
  ∃ c : Finset (Finset (Euc n)),
    GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
    (∀ t ∈ c, (t : Set (Euc n)) ⊆ s) ∧ u = c.image GeometricSimplicialSubdivision.barycenter

/-- The vertex introduced at a member of a flag.  The `getD` makes the formula
total off genuine maximal flags; on a flag contributing to a `k`-simplex the
difference is a singleton. -/
def flagNewVertex {n : ℕ} (o : LinearOrder (Euc n))
    (c : Finset (Finset (Euc n))) (t : Finset (Euc n)) : Euc n :=
  ((t \ c.biUnion (fun u => if u ⊂ t then u else ∅)).1.sort o.le).getD 0 0

/-- Closed orientation formula for a flag: order the faces by inclusion and
take the inversion parity of the successive newly introduced old vertices. -/
def flagSign {n : ℕ} (o : LinearOrder (Euc n))
    (c : Finset (Finset (Euc n))) : ℚ :=
  (-1 : ℚ) ^ ((c ×ˢ c).filter fun tu =>
    tu.1 ⊂ tu.2 ∧ flagNewVertex o c tu.1 > flagNewVertex o c tu.2).card

def IsSubdivisionChainMap {n : ℕ} (o : LinearOrder (Euc n)) (K K' : GSC n)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k) : Prop := by
  classical
  exact ∀ k (s : FaceIndex K k), ∃ z : FaceModule K' k,
    sd k (Finsupp.single s 1) = z ∧
    ∀ u, z u = ∑ c ∈ s.1.powerset.powerset,
      if GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
          u.1 = c.image GeometricSimplicialSubdivision.barycenter then
        flagSign o c else 0

/-- The canonical barycentric step, with all three construction proofs fixed. -/
def barycentricStep {n : ℕ} (K : GSC n) : GSC n :=
  GeometricSimplicialSubdivision.barycentricSubdivision K
    (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent K)
    (GeometricSimplicialSubdivision.barycentricFaces_isLowerSet K)
    (GeometricSimplicialSubdivision.barycentricFaces_inter_subset K)

def homeomorphMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : C(X,Y) := ⟨e, e.continuous⟩

/-- Carrier avoidance: every face `u` of the subdivision lying GEOMETRICALLY in a
face `s` of `K` (its vertices in `convexHull s`) is sent by `h` to vertices off
`s`.  (claude-14 fix 2026-10-28, from lemma-1's report: the earlier
`(u : Set _) ⊆ s` compared vertex sets, but subdivision vertices are barycenters,
not vertices of `s`, so it almost never applied.) -/
def CarrierAvoidingVertexMap {n : ℕ} (K K' : GSC n) (h : Euc n → Euc n) : Prop :=
  ∀ s ∈ K.faces, ∀ u ∈ K'.faces, (u : Set (Euc n)) ⊆ convexHull ℝ (s : Set (Euc n)) →
    Disjoint (u.image h : Set (Euc n)) s

theorem vertexChainMap_exists {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K L h) :
    ∃ hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k,
      IsVertexChainMap on om K L h hm := by
  classical
  let b : ∀ k, FaceIndex K k → FaceModule L k := fun k s =>
    if hinj : (s.1.image h).card = k + 1 then
      Finsupp.single
        (⟨s.1.image h, hh.2 s.1 s.2.1, hinj⟩ : FaceIndex L k)
        (sortingSign on om s.1 h)
    else 0
  let hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k := fun k =>
    ModuleCat.ofHom (Finsupp.linearCombination ℚ (b k))
  refine ⟨hm, ?_⟩
  intro k s
  split_ifs with hinj
  · refine ⟨⟨s.1.image h, hh.2 s.1 s.2.1, hinj⟩, rfl, ?_⟩
    simp [hm, b, hinj]
  · simp [hm, b, hinj]

lemma vertexChainMap_commutes_aux_ext {n m k : ℕ}
    (K : GSC n) (L : GSC m)
    (f g : FaceModuleCat K (k + 1) ⟶ FaceModuleCat L k)
    (hfg : ∀ s : FaceIndex K (k + 1),
      f (Finsupp.single s 1) = g (Finsupp.single s 1)) : f = g := by
  ext s a
  exact congrArg (fun x => x a) (hfg s)

lemma vertexChainMap_commutes_aux_generator_aux_boundaryK {n k : ℕ}
    (on : LinearOrder (Euc n)) (K : GSC n)
    (dK : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hdK : IsSignedDeletion on K dK) (s : FaceIndex K (k + 1)) :
    dK k (Finsupp.single s 1) =
      ∑ v ∈ s.1.attach, (-1 : ℚ) ^ ((s.1.sort on.le).idxOf v.1) •
        Finsupp.single
          (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1 := by
  exact signedDeletion_sq_zero_aux_generator_aux_boundary on K dK hdK s

lemma vertexChainMap_commutes_aux_generator_aux_boundaryL {m k : ℕ}
    (om : LinearOrder (Euc m)) (L : GSC m)
    (dL : ∀ k, FaceModuleCat L (k + 1) ⟶ FaceModuleCat L k)
    (hdL : IsSignedDeletion om L dL) (t : FaceIndex L (k + 1)) :
    dL k (Finsupp.single t 1) =
      ∑ v ∈ t.1.attach, (-1 : ℚ) ^ ((t.1.sort om.le).idxOf v.1) •
        Finsupp.single
          (signedDeletion_sq_zero_aux_generator_aux_erase L t v.1 v.2) 1 := by
  exact signedDeletion_sq_zero_aux_generator_aux_boundary om L dL hdL t

lemma vertexChainMap_commutes_aux_generator_aux_injective_aux_injOn {n m : ℕ}
    {k : ℕ} (K : GSC n) (s : FaceIndex K (k + 1)) (h : Euc n → Euc m)
    (hinj : (s.1.image h).card = k + 2) : Set.InjOn h s.1 := by
  apply Finset.injOn_of_card_image_eq
  rw [hinj, s.2.2]

lemma vertexChainMap_commutes_aux_generator_aux_injective_aux_image_erase {n m : ℕ}
    {k : ℕ} (K : GSC n) (s : FaceIndex K (k + 1)) (h : Euc n → Euc m)
    (hinj : (s.1.image h).card = k + 2) (v : Euc n) (hv : v ∈ s.1) :
    (s.1.erase v).image h = (s.1.image h).erase (h v) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxv, hxs⟩, rfl⟩
    refine ⟨?_, x, hxs, rfl⟩
    intro heq
    exact hxv (vertexChainMap_commutes_aux_generator_aux_injective_aux_injOn K s h hinj
      hxs hv heq)
  · rintro ⟨hzv, x, hxs, rfl⟩
    refine ⟨x, ⟨?_, hxs⟩, rfl⟩
    rintro rfl
    exact hzv rfl

open scoped Classical in
/-- Inversions of `h` on `a`, counted on elements: pairs `x <_on y` with `h y <_om h x`. -/
noncomputable def elemInv {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) : ℕ :=
  ((a ×ˢ a).filter (fun p => @LT.lt (Euc n) on.toLT p.1 p.2 ∧ @LT.lt (Euc m) om.toLT (h p.2) (h p.1))).card

/-- (P0) Index form = element form: the sorted list is an order isomorphism
`Fin a.card ≃o a`. -/
theorem sortingSign_eq_elemInv {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) :
    sortingSign on om a h = (-1 : ℚ) ^ elemInv on om a h := by
  classical
  letI := on
  letI := om
  let e : Fin a.card ≃o a := a.orderIsoOfFin rfl
  have hget (i : Fin a.card) :
      (a.1.sort on.le).getD i 0 = (e i : Euc n) := by
    calc
      _ = (a.1.sort on.le)[i] := List.getD_eq_getElem _ _ (by simpa using i.2)
      _ = (e i : Euc n) := (a.orderEmbOfFin_apply rfl i).symm
  let source := Finset.univ.filter (fun ij : Fin a.card × Fin a.card =>
        ij.1 < ij.2 ∧
          @LT.lt (Euc m) om.toLT (h ((a.1.sort on.le).getD ij.2 0))
            (h ((a.1.sort on.le).getD ij.1 0)))
  let target := (a ×ˢ a).filter (fun p =>
        @LT.lt (Euc n) on.toLT p.1 p.2 ∧
          @LT.lt (Euc m) om.toLT (h p.2) (h p.1))
  have hc : source.card = target.card := by
    apply Finset.card_bij
        (fun ij _ => ((e ij.1 : Euc n), (e ij.2 : Euc n)))
    · intro ij hij
      simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      rw [hget, hget] at hij
      simp only [Finset.mem_filter, Finset.mem_product, (e ij.1).2, (e ij.2).2,
        true_and, target]
      exact ⟨e.lt_iff_lt.mpr hij.1, hij.2⟩
    · intro ij₁ hij₁ ij₂ hij₂ heq
      apply Prod.ext
      · exact e.injective (Subtype.ext (congrArg Prod.fst heq))
      · exact e.injective (Subtype.ext (congrArg Prod.snd heq))
    · intro p hp
      simp only [target, Finset.mem_filter, Finset.mem_product] at hp
      let i : Fin a.card := e.symm ⟨p.1, hp.1.1⟩
      let j : Fin a.card := e.symm ⟨p.2, hp.1.2⟩
      have hi : (e i : Euc n) = p.1 := by simp [i]
      have hj : (e j : Euc n) = p.2 := by simp [j]
      refine ⟨(i, j), ?_, ?_⟩
      · simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact e.lt_iff_lt.mp (by simpa [i, j] using hp.2.1)
        · rw [hget, hget, hi, hj]
          exact hp.2.2
      · simp [i, j]
  simp only [sortingSign, elemInv]
  exact congrArg ((-1 : ℚ) ^ ·) (by simpa [source, target] using hc)

open scoped Classical in
/-- (P1) Removing `v` removes exactly the inversions involving `v`. -/
theorem elemInv_erase {n m : ℕ} (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) (v : Euc n) (hv : v ∈ a) :
    elemInv on om a h = elemInv on om (a.erase v) h +
      ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT u v ∧ @LT.lt (Euc m) om.toLT (h v) (h u))).card +
      ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT v u ∧ @LT.lt (Euc m) om.toLT (h u) (h v))).card := by
  classical
  rw [← Finset.insert_erase hv]
  simp only [elemInv]
  rw [← Finset.card_disjSum, ← Finset.card_disjSum]
  apply Finset.card_bij
    (fun p _ =>
      if p.1 = v then Sum.inr p.2
      else if p.2 = v then Sum.inl (Sum.inr p.1)
      else Sum.inl (Sum.inl p))
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_erase, Finset.mem_disjSum]
    aesop
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert] at hp₁ hp₂
    split_ifs at heq <;> simp_all [Prod.ext_iff]
  · intro q hq
    simp only [Finset.mem_disjSum, Finset.mem_filter, Finset.mem_product,
      Finset.mem_erase] at hq
    rcases q with (q | q)
    · rcases q with (q | q)
      · refine ⟨q, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert]
          grind
        · rcases hq with ⟨x, y, hxy, rfl⟩ <;> simp_all
      · refine ⟨(q, v), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert]
          grind
        · simp_all
    · refine ⟨(v, q), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert]
        grind
      · simp_all

open scoped Classical in
/-- (P2) Position in the sorted list = number of smaller elements. -/
theorem sort_idxOf_eq_card_lt_aux {α : Type*} [DecidableEq α] (o : LinearOrder α)
    (l : List α) (v : α) (hv : v ∈ l) (hs : l.Pairwise o.le) (hn : l.Nodup) :
    l.idxOf v = (l.toFinset.filter (fun x => o.lt x v)).card := by
  letI := o
  induction l with
  | nil => simp at hv
  | cons x l ih =>
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · have hnot : ∀ y ∈ l, ¬y < v := by
          intro y hy hyx
          exact (not_lt_of_ge (hs.rel_head_tail hy)) hyx
        have hf : l.toFinset.filter (fun y => y < v) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro y hy
          simp only [Finset.mem_filter, List.mem_toFinset] at hy
          exact hnot y hy.1 hy.2
        rw [List.idxOf_cons_self, List.toFinset_cons, Finset.filter_insert]
        simp [hf]
      · have hxl : x ≤ v := hs.rel_head_tail hv
        have hxv : x < v := lt_of_le_of_ne hxl (hn.rel_head_tail hv)
        rw [List.idxOf_cons_ne l (ne_of_lt hxv)]
        simp only [List.toFinset_cons, Finset.filter_insert, hxv, if_true]
        rw [Finset.card_insert_of_notMem]
        · simp [ih hv hs.tail hn.tail]
        · intro hx
          simp only [Finset.mem_filter, List.mem_toFinset] at hx
          exact (hn.rel_head_tail hx.1) rfl

theorem sort_idxOf_eq_card_lt {n : ℕ} (on : LinearOrder (Euc n))
    (a : Finset (Euc n)) (v : Euc n) (hv : v ∈ a) :
    (a.sort on.le).idxOf v = (a.filter (fun u => @LT.lt (Euc n) on.toLT u v)).card := by
  simpa using sort_idxOf_eq_card_lt_aux on (a.sort on.le) v (by simpa using hv)
    (a.pairwise_sort on.le) (a.sort_nodup on.le)

open scoped Classical in
/-- (P3) The same for the image, through the injective `h`. -/
theorem image_sort_idxOf_eq_card_lt_aux {α : Type*} [DecidableEq α] (o : LinearOrder α)
    (l : List α) (v : α) (hv : v ∈ l) (hs : l.Pairwise o.le) (hn : l.Nodup) :
    l.idxOf v = (l.toFinset.filter (fun x => @LT.lt α o.toLT x v)).card := by
  letI := o
  induction l with
  | nil => simp at hv
  | cons x l ih =>
      cases hs with
      | cons hrel hs =>
       cases hn with
       | cons hnotmem hn =>
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · have hnot : ∀ y ∈ l, ¬y < v := by
          intro y hy hyx
          exact (not_lt_of_ge (hrel y hy)) hyx
        simp only [List.idxOf_cons_self, List.toFinset_cons, Finset.filter_insert,
          lt_self_iff_false, if_false]
        exact (Finset.card_eq_zero.mpr (by
          rw [Finset.filter_eq_empty_iff]
          intro y hy
          exact hnot y (by simpa using hy))).symm
      · have hxl : x ≤ v := hrel v hv
        have hxv : x < v := lt_of_le_of_ne hxl (by
          intro h
          subst x
          exact (hnotmem v hv) rfl)
        rw [List.idxOf_cons_ne l (ne_of_lt hxv)]
        simp only [List.toFinset_cons, Finset.filter_insert, hxv, if_true]
        rw [Finset.card_insert_of_notMem]
        · simp [ih hv hs hn]
        · intro hx
          rw [Finset.mem_filter] at hx
          exact hnotmem x (by simpa using hx.1) rfl

theorem image_sort_idxOf_eq_card_lt {n m : ℕ} (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) (hinj : Set.InjOn h a)
    (v : Euc n) (hv : v ∈ a) :
    ((a.image h).sort om.le).idxOf (h v) = (a.filter (fun u => @LT.lt (Euc m) om.toLT (h u) (h v))).card := by
  letI := om
  rw [image_sort_idxOf_eq_card_lt_aux om ((a.image h).sort om.le) (h v)
    (by simpa using ⟨v, hv, rfl⟩) ((a.image h).pairwise_sort (· ≤ ·))
    (Finset.sort_nodup _ _)]
  rw [Finset.sort_toFinset]
  have heq : ((a.image h).filter (fun z => z < h v)) =
      (a.filter (fun u => h u < h v)).image h := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, huv⟩
      exact ⟨u, ⟨hu, huv⟩, rfl⟩
    · rintro ⟨u, ⟨hu, huv⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, huv⟩
  rw [heq, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy

open scoped Classical in
/-- (P4) The parity count: with `A = #{u <_on v}`, `B = #{h u <_om h v}`,
`X = #{both}`, the two `P1` counts are `A - X` and `B - X` (injectivity makes the
`om`-comparison of `h u, h v` total for `u ≠ v`), so the sign changes by
`(-1)^(A+B)`. -/
theorem vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity_aux_count {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) (hinj : Set.InjOn h a)
    (v : Euc n) (hv : v ∈ a) :
    (-1 : ℚ) ^ (a.filter (fun u => @LT.lt (Euc n) on.toLT u v)).card * (-1 : ℚ) ^ elemInv on om (a.erase v) h =
      (-1 : ℚ) ^ elemInv on om a h * (-1 : ℚ) ^ (a.filter (fun u => @LT.lt (Euc m) om.toLT (h u) (h v))).card := by
  sorry

/-- The parity identity behind naturality of oriented deletion.  This is the
Laplace-minor sign rule for the permutation which reorders `h '' s`. -/
lemma vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (a : Finset (Euc n)) (h : Euc n → Euc m) (hinj : Set.InjOn h a)
    (v : Euc n) (hv : v ∈ a) :
    (-1 : ℚ) ^ ((a.sort on.le).idxOf v) * sortingSign on om (a.erase v) h =
      sortingSign on om a h *
        (-1 : ℚ) ^ (((a.image h).sort om.le).idxOf (h v)) := by
  classical
  rw [sortingSign_eq_elemInv, sortingSign_eq_elemInv, sort_idxOf_eq_card_lt on a v hv,
    image_sort_idxOf_eq_card_lt om a h hinj v hv]
  convert vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity_aux_count on om a h hinj v hv using 3

lemma vertexChainMap_commutes_aux_generator_aux_injective_aux_sign {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    {k : ℕ} (K : GSC n) (s : FaceIndex K (k + 1)) (h : Euc n → Euc m)
    (hinj : (s.1.image h).card = k + 2) (v : Euc n) (hv : v ∈ s.1) :
    (-1 : ℚ) ^ ((s.1.sort on.le).idxOf v) *
        sortingSign on om (s.1.erase v) h =
      sortingSign on om s.1 h *
        (-1 : ℚ) ^ (((s.1.image h).sort om.le).idxOf (h v)) := by
  apply vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity
  · exact vertexChainMap_commutes_aux_generator_aux_injective_aux_injOn K s h hinj
  · exact hv

theorem vertexChainMap_commutes_aux_generator_aux_injective {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK) (hdL : IsSignedDeletion om L dL)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1))
    (hinj : (s.1.image h).card = k + 2) :
    dL k (hm (k + 1) (Finsupp.single s 1)) =
      hm k (dK k (Finsupp.single s 1)) := by
  sorry

lemma vertexChainMap_commutes_aux_generator_aux_collapse_aux_image_card {n m k : ℕ}
    (K : GSC n) (h : Euc n → Euc m) (s : FaceIndex K (k + 1))
    (hcol : (s.1.image h).card ≠ k + 2) :
    (s.1.image h).card ≤ k + 1 := by
  have hle : (s.1.image h).card ≤ k + 2 := by
    simpa [s.2.2] using Finset.card_image_le (f := h) (s := s.1)
  omega

/-- (C-A) At least two collisions: every one-vertex deletion still collapses,
so every term of `dK s` maps to `0`. -/
theorem vertexChainMap_commutes_aux_generator_aux_collapse_aux_many {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1))
    (hcard : (s.1.image h).card ≤ k) :
    hm k (dK k (Finsupp.single s 1)) = 0 := by
  rw [vertexChainMap_commutes_aux_generator_aux_boundaryK on K dK hdK s,
    map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [map_smul]
  have himage : ((s.1.erase v.1).image h).card ≤ k := by
    apply le_trans (Finset.card_le_card ?_) hcard
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.erase_subset _ _ hx, rfl⟩
  have hzero :
      hm k (Finsupp.single
        (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1) = 0 := by
    have hspec := hhm k
      (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2)
    rw [dif_neg] at hspec
    · exact hspec
    · intro heq
      change ((s.1.erase v.1).image h).card = k + 1 at heq
      rw [heq] at himage
      omega
  rw [hzero, smul_zero]

/-- (C-B) Exactly one collision `h v = h w`, `v ≠ w`: only deleting `v` or `w`
gives an injective image, the same face, with opposite signs. -/
theorem vertexChainMap_commutes_aux_generator_aux_collapse_aux_one {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1))
    (hcard : (s.1.image h).card = k + 1) :
    hm k (dK k (Finsupp.single s 1)) = 0 := by
  sorry

/-- (VG2) `h` collapses `s`: the left side is `0`; on the right the deleted
faces with injective image come in pairs (delete either of two vertices with the
same image) whose terms cancel, and all others map to `0`. -/
theorem vertexChainMap_commutes_aux_generator_aux_collapse {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK) (hdL : IsSignedDeletion om L dL)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1))
    (hcol : (s.1.image h).card ≠ k + 2) :
    dL k (hm (k + 1) (Finsupp.single s 1)) =
      hm k (dK k (Finsupp.single s 1)) := by
  have hl : hm (k + 1) (Finsupp.single s 1) = 0 := by
    have := hhm (k + 1) s
    rw [dif_neg hcol] at this
    exact this
  rw [hl, map_zero]
  have hle := vertexChainMap_commutes_aux_generator_aux_collapse_aux_image_card K h s hcol
  rcases Nat.lt_or_ge (s.1.image h).card (k + 1) with hlt | hge
  · exact (vertexChainMap_commutes_aux_generator_aux_collapse_aux_many on om K L h dK hm
      hdK hhm k s (by omega)).symm
  · exact (vertexChainMap_commutes_aux_generator_aux_collapse_aux_one on om K L h dK hm
      hdK hhm k s (by omega)).symm

lemma vertexChainMap_commutes_aux_generator {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK) (hdL : IsSignedDeletion om L dL)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1)) :
    dL k (hm (k + 1) (Finsupp.single s 1)) =
      hm k (dK k (Finsupp.single s 1)) := by
  by_cases hinj : (s.1.image h).card = k + 2
  · exact vertexChainMap_commutes_aux_generator_aux_injective on om K L h dK dL hm
      hdK hdL hhm k s hinj
  · exact vertexChainMap_commutes_aux_generator_aux_collapse on om K L h dK dL hm
      hdK hdL hhm k s hinj

theorem vertexChainMap_commutes {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK) (hdL : IsSignedDeletion om L dL)
    (hhm : IsVertexChainMap on om K L h hm) :
    ∀ k, hm (k+1) ≫ dL k = dK k ≫ hm k := by
  intro k
  apply vertexChainMap_commutes_aux_ext
  intro s
  exact vertexChainMap_commutes_aux_generator on om K L h dK dL hm hdK hdL hhm k s

theorem barycentricSubdivisionChainMap_exists {n : ℕ} (o : LinearOrder (Euc n))
    (K : GSC n) (hi hd hx) :
    ∃ sd : ∀ k, FaceModuleCat K k ⟶
        FaceModuleCat (GeometricSimplicialSubdivision.barycentricSubdivision K hi hd hx) k,
      IsSubdivisionChainMap o K
        (GeometricSimplicialSubdivision.barycentricSubdivision K hi hd hx) sd := by
  classical
  let K' := GeometricSimplicialSubdivision.barycentricSubdivision K hi hd hx
  let b : ∀ k, FaceIndex K k → FaceModule K' k := fun k s =>
    ∑ c ∈ s.1.powerset.powerset,
      if hc : GeometricSimplicialSubdivision.IsStrictFaceChain K c then
        if hcard : (c.image GeometricSimplicialSubdivision.barycenter).card = k + 1 then
          Finsupp.single
            (⟨c.image GeometricSimplicialSubdivision.barycenter,
              ⟨⟨c, hc, rfl⟩, by
                intro h
                rw [Set.mem_singleton_iff] at h
                rw [h] at hcard
                simp at hcard⟩, hcard⟩ : FaceIndex K' k)
            (flagSign o c)
        else 0
      else 0
  let sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k := fun k =>
    ModuleCat.ofHom (Finsupp.linearCombination ℚ (b k))
  refine ⟨sd, ?_⟩
  intro k s
  refine ⟨b k s, ?_, ?_⟩
  · simp [sd]
  · intro u
    simp only [b]
    change Finsupp.applyAddHom u _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c hcsub
    by_cases hc : GeometricSimplicialSubdivision.IsStrictFaceChain K c
    · by_cases hcard : (c.image GeometricSimplicialSubdivision.barycenter).card = k + 1
      · simp [hc, hcard, Finsupp.single_apply]
        apply if_congr
        · constructor
          · intro h
            exact (congrArg Subtype.val h).symm
          · intro h
            exact Subtype.ext h.symm
        · rfl
        · rfl
      · have hne : ¬u.1 = c.image GeometricSimplicialSubdivision.barycenter := by
          intro heq
          apply hcard
          rw [← heq]
          exact u.2.2
        simp [hc, hcard, hne]
    · simp [hc]

theorem subdivisionChainMap_commutes {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat K' (k+1) ⟶ FaceModuleCat K' k)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hdK : IsSignedDeletion o K dK) (hdK' : IsSignedDeletion o K' dK')
    (hsd : IsSubdivisionChainMap o K K' sd) :
    ∀ k, sd (k+1) ≫ dK' k = dK k ≫ sd k := by
  sorry

theorem vertexChainMap_affineComparison_square {n m : ℕ} (on : LinearOrder (Euc n))
    (om : LinearOrder (Euc m)) (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K L h)
    (f : C(K.space, L.space))
    (hf : ∀ s ∈ K.faces, ∀ x : K.space, (x : Euc n) ∈ convexHull ℝ (s : Set _) →
      (f x : Euc m) ∈ convexHull ℝ (s.image h : Set _))
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hhm : IsVertexChainMap on om K L h hm)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dL : ∀ k, FaceModuleCat L (k+1) ⟶ FaceModuleCat L k)
    (hddK : ∀ k, dK (k+1) ≫ dK k = 0) (hddL : ∀ k, dL (k+1) ≫ dL k = 0)
    (hmH : ChainComplex.of _ dK hddK ⟶ ChainComplex.of _ dL hddL)
    (hmH_f : ∀ k, hmH.f k = hm k)
    (cmpK : ∀ k, FaceModuleCat K k ⟶ (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (cmpL : ∀ k, FaceModuleCat L k ⟶ (CoefficientH0.SingularChains ℚ (TopCat.of L.space)).X k)
    (hcmpK : IsAffineComparison K cmpK) (hcmpL : IsAffineComparison L cmpL)
    (cmpKH : ChainComplex.of _ dK hddK ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpLH : ChainComplex.of _ dL hddL ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of L.space))
    (cmpKH_f : ∀ k, cmpKH.f k = cmpK k) (cmpLH_f : ∀ k, cmpLH.f k = cmpL k) :
    ∀ k,
      HomologicalComplex.homologyMap hmH k ≫ HomologicalComplex.homologyMap cmpLH k =
      HomologicalComplex.homologyMap cmpKH k ≫ induced f k := by
  sorry

theorem subdivision_affineComparison_square {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (hspace : K.space = K'.space)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hsd : IsSubdivisionChainMap o K K' sd)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat K' (k+1) ⟶ FaceModuleCat K' k)
    (hddK : ∀ k, dK (k+1) ≫ dK k = 0) (hddK' : ∀ k, dK' (k+1) ≫ dK' k = 0)
    (sdH : ChainComplex.of _ dK hddK ⟶ ChainComplex.of _ dK' hddK')
    (sdH_f : ∀ k, sdH.f k = sd k)
    (cmpK : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (cmpK' : ∀ k, FaceModuleCat K' k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K'.space)).X k)
    (hcmpK : IsAffineComparison K cmpK) (hcmpK' : IsAffineComparison K' cmpK')
    (cmpKH : ChainComplex.of _ dK hddK ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpK'H : ChainComplex.of _ dK' hddK' ⟶
      CoefficientH0.SingularChains ℚ (TopCat.of K'.space))
    (cmpKH_f : ∀ k, cmpKH.f k = cmpK k) (cmpK'H_f : ∀ k, cmpK'H.f k = cmpK' k) :
    ∀ k,
      HomologicalComplex.homologyMap sdH k ≫ HomologicalComplex.homologyMap cmpK'H k =
      HomologicalComplex.homologyMap cmpKH k ≫
        induced (Homeomorph.setCongr hspace) k := by
  sorry

lemma composite_zero_diagonal_aux_barycenter_mem {n : ℕ}
    (t s : Finset (Euc n)) (ht : t.Nonempty) (hts : t ⊆ s) :
    GeometricSimplicialSubdivision.barycenter t ∈ convexHull ℝ (s : Set (Euc n)) := by
  apply convexHull_mono (by simpa using hts)
  apply Finset.centerMass_id_mem_convexHull
  · intro x hx
    positivity
  · simpa using (Finset.card_pos.mpr ht : 0 < t.card)

lemma composite_zero_diagonal_aux_vertex {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (h : Euc n → Euc n)
    (hm : ∀ k, FaceModuleCat K' k ⟶ FaceModuleCat K k)
    (hhm : IsVertexChainMap o o K' K h hm)
    (havoid : CarrierAvoidingVertexMap K K' h) (k : ℕ)
    (s : FaceIndex K k) (u : FaceIndex K' k)
    (hu : (u.1 : Set (Euc n)) ⊆ convexHull ℝ (s.1 : Set (Euc n))) :
    (hm k (Finsupp.single u 1)) s = 0 := by
  classical
  have hdis : Disjoint (u.1.image h : Set (Euc n)) s.1 :=
    havoid s.1 s.2.1 u.1 u.2.1 hu
  by_cases hinj : (u.1.image h).card = k + 1
  · have hv := hhm k u
    simp only [dif_pos hinj] at hv
    obtain ⟨t, ht, heq⟩ := hv
    rw [heq, Finsupp.single_apply]
    simp only [ite_eq_right_iff]
    intro hts
    subst t
    have hsne : s.1.Nonempty := K.nonempty_of_mem_faces s.2.1
    obtain ⟨x, hx⟩ := hsne
    have hxim : x ∈ u.1.image h := by
      rw [← ht]
      exact hx
    exact (Set.disjoint_left.1 hdis hxim hx).elim
  · have hz := hhm k u
    simp only [dif_neg hinj] at hz
    rw [hz]
    rfl

theorem composite_zero_diagonal {n : ℕ} (o : LinearOrder (Euc n)) (K K' : GSC n)
    (h : Euc n → Euc n) (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hm : ∀ k, FaceModuleCat K' k ⟶ FaceModuleCat K k)
    (hsd : IsSubdivisionChainMap o K K' sd)
    (hhm : IsVertexChainMap o o K' K h hm)
    (havoid : CarrierAvoidingVertexMap K K' h) :
    ∀ k (s : FaceIndex K k), (hm k (sd k (Finsupp.single s 1))) s = 0 := by
  classical
  intro k s
  obtain ⟨z, hsdz, hz⟩ := hsd k s
  rw [hsdz]
  rw [← Finsupp.sum_single z]
  change Finsupp.applyAddHom s
    (hm k (∑ u ∈ z.support, Finsupp.single u (z u))) = 0
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro u hu
  rw [← Finsupp.smul_single_one, map_smul]
  change z u * (hm k (Finsupp.single u 1)) s = 0
  rw [composite_zero_diagonal_aux_vertex o K K' h hm hhm havoid k s u]
  simp only [mul_zero]
  intro x hx
  have hzu : z u ≠ 0 := Finsupp.mem_support_iff.mp hu
  rw [hz u] at hzu
  have hex : ∃ c ∈ s.1.powerset.powerset,
      GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
        u.1 = c.image GeometricSimplicialSubdivision.barycenter := by
    by_contra hn
    push_neg at hn
    apply hzu
    apply Finset.sum_eq_zero
    intro c hc
    split_ifs with hi
    · exact (hn c hc hi.1 hi.2).elim
    · rfl
  obtain ⟨c, hcps, hcond⟩ := hex
  have hcsub : ∀ t ∈ c, t ⊆ s.1 := by
    intro t ht
    exact Finset.mem_powerset.1 ((Finset.mem_powerset.1 hcps) ht)
  have hxu : x ∈ c.image GeometricSimplicialSubdivision.barycenter := by
    simpa [hcond.2] using hx
  obtain ⟨t, htc, rfl⟩ := Finset.mem_image.1 hxu
  apply composite_zero_diagonal_aux_barycenter_mem t s.1
  · exact K.nonempty_of_mem_faces (hcond.1.1 t htc)
  · exact hcsub t htc

/-- LIBRARY: geometric preparation retaining the fact that the fine complex is
an iterated barycentric subdivision, together with a carrier-avoiding simplicial
approximation homotopic to `g`. -/
theorem exists_fine_iterated_approximation
    {X : Type} [TopologicalSpace X] {n : ℕ} (K : GSC n) (hK : K.faces.Finite)
    (e : X ≃ₜ K.space) (g : C(X,X)) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X, (e x : Euc n) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _), δ ≤ dist (e (g x) : Euc n) y) :
    ∃ p m : ℕ, ∃ hL : ((barycentricStep^[p]) K).space = K.space,
      ((barycentricStep^[p]) K).faces.Finite ∧
      ∃ hspace : ((barycentricStep^[m]) ((barycentricStep^[p]) K)).space =
          ((barycentricStep^[p]) K).space,
        ((barycentricStep^[m]) ((barycentricStep^[p]) K)).faces.Finite ∧
      ∃ h : Euc n → Euc n,
        GeometricSimplicialSubdivision.IsSimplicialVertexMap
          ((barycentricStep^[m]) ((barycentricStep^[p]) K)) ((barycentricStep^[p]) K) h ∧
        CarrierAvoidingVertexMap ((barycentricStep^[p]) K)
          ((barycentricStep^[m]) ((barycentricStep^[p]) K)) h ∧
        ∀ v ∈ ((barycentricStep^[m]) ((barycentricStep^[p]) K)).vertices,
          (fun x : ((barycentricStep^[m]) ((barycentricStep^[p]) K)).space =>
            (e.trans (Homeomorph.setCongr hL.symm)) (g ((e.trans
              (Homeomorph.setCongr hL.symm)).symm (Homeomorph.setCongr hspace x)))) ''
              ((Subtype.val : _ → Euc n) ⁻¹'
                GeometricSimplicialSubdivision.openStar
                  ((barycentricStep^[m]) ((barycentricStep^[p]) K)) v) ⊆
            (Subtype.val : ((barycentricStep^[p]) K).space → Euc n) ⁻¹'
              GeometricSimplicialSubdivision.openStar ((barycentricStep^[p]) K) (h v) := by
  sorry

/-- LIBRARY: assemble explicit commuting subdivision and vertex maps, their
comparison squares and quasi-isomorphism into the packaged finite chain model. -/
theorem oriented_model_of_explicit_maps
    {X : Type} [TopologicalSpace X] {n : ℕ} (K K' : GSC n)
    (m : ℕ) (hiter : K' = (barycentricStep^[m]) K)
    (hK : K.faces.Finite) (hK' : K'.faces.Finite) (hspace : K'.space = K.space)
    (e : X ≃ₜ K.space) (g : C(X,X)) (h : Euc n → Euc n)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K' K h)
    (havoid : CarrierAvoidingVertexMap K K' h)
    (f : C(K'.space, K.space))
    (hf : ∀ s ∈ K'.faces, ∀ x : K'.space,
      (x : Euc n) ∈ convexHull ℝ (s : Set _) →
      (f x : Euc n) ∈ convexHull ℝ (s.image h : Set _))
    (hhom : ContinuousMap.Homotopic
      ((homeomorphMap e).comp
        (g.comp ((homeomorphMap e.symm).comp
          (homeomorphMap (Homeomorph.setCongr hspace : K'.space ≃ₜ K.space))))) f) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧ LefschetzCompactPolyhedron.HomologyModels M g := by
  sorry

/-- Adapter with exactly the statement consumed by `LefschetzCompactPolyhedron`. -/
theorem exists_carrier_avoiding_oriented_chain_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X,
      (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _),
        δ ≤ dist (e (g x) : EuclideanSpace ℝ (Fin n)) y) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧
        LefschetzCompactPolyhedron.HomologyModels M g := by
  obtain ⟨p, m, hL, hLfin, hspace, hK', h, hh, hav, hstar⟩ :=
    exists_fine_iterated_approximation K hK e g δ hδ hmargin
  let L := (barycentricStep^[p]) K
  let K' := (barycentricStep^[m]) L
  let eL : X ≃ₜ L.space := e.trans (Homeomorph.setCongr hL.symm)
  obtain ⟨f, _hvertex, hf⟩ :=
    GeometricSimplicialSubdivision.exists_inducedContinuousMap K' hK' L h hh
  exact oriented_model_of_explicit_maps L K' m rfl hLfin hK' hspace eL g h hh hav f hf
    (GeometricSimplicialSubdivision.inducedMap_homotopic_of_star_condition
      K' L _ f h hstar hf)
end ConstructionTargets.SimplicialChainMaps

#print axioms ConstructionTargets.SimplicialChainMaps.exists_carrier_avoiding_oriented_chain_model
