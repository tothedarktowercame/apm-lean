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

/-- Closed orientation formula for a flag `s₀ ⊂ ⋯ ⊂ s_k` (claude-14 fix
2026-10-28, from lemma-2's counterexample): the coefficient of the `o`-sorted
subdivided face is the product of
* the inversion parity, under `o`, of the newly introduced old vertices in
  inclusion order (the sign of `sd` on the `o`-ordered simplex), and
* the inversion parity, under `o`, of the barycenters in inclusion order
  (reordering `[b₀,…,b_k]` into the `o`-sorted basis of the subdivision).
The earlier form had only the first factor and compared with the POINTWISE `>`
of EuclideanSpace instead of `o`.  Check: edge `[0,1]`, `o` reversed, `m = 1/2`:
both flags get `+1`, matching `sd[1,0] = [m,0] - [m,1]`. -/
def flagSign {n : ℕ} (o : LinearOrder (Euc n))
    (c : Finset (Finset (Euc n))) : ℚ :=
  (-1 : ℚ) ^ ((c ×ˢ c).filter fun tu =>
    tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o c tu.2) (flagNewVertex o c tu.1)).card *
  (-1 : ℚ) ^ ((c ×ˢ c).filter fun tu =>
    tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (GeometricSimplicialSubdivision.barycenter tu.2)
      (GeometricSimplicialSubdivision.barycenter tu.1)).card

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
  classical
  let A := a.filter (fun u => @LT.lt (Euc n) on.toLT u v)
  let B := a.filter (fun u => @LT.lt (Euc m) om.toLT (h u) (h v))
  let X := a.filter (fun u =>
    @LT.lt (Euc n) on.toLT u v ∧ @LT.lt (Euc m) om.toLT (h u) (h v))
  let Y := a.filter (fun u =>
    @LT.lt (Euc n) on.toLT u v ∧ @LT.lt (Euc m) om.toLT (h v) (h u))
  let Z := a.filter (fun u =>
    @LT.lt (Euc n) on.toLT v u ∧ @LT.lt (Euc m) om.toLT (h u) (h v))
  have himage_ne (u : Euc n) (hu : u ∈ a) (huv : u ≠ v) : h u ≠ h v := by
    exact fun huv' => huv (hinj hu hv huv')
  have hA : A.card = X.card + Y.card := by
    have hdis : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro u huX huY
      simp only [X, Y, Finset.mem_filter] at huX huY
      exact (not_lt_of_ge (le_of_lt huX.2.2)) huY.2.2
    rw [← Finset.card_union_of_disjoint hdis]
    congr 1
    ext u
    simp only [A, X, Y, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hne : h u ≠ h v := himage_ne u hu.1 (ne_of_lt hu.2)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hu.1, hu.2, hlt⟩
      · exact Or.inr ⟨hu.1, hu.2, hgt⟩
    · aesop
  have hB : B.card = X.card + Z.card := by
    have hdis : Disjoint X Z := by
      rw [Finset.disjoint_left]
      intro u huX huZ
      simp only [X, Z, Finset.mem_filter] at huX huZ
      exact (not_lt_of_ge (le_of_lt huX.2.1)) huZ.2.1
    rw [← Finset.card_union_of_disjoint hdis]
    congr 1
    ext u
    simp only [B, X, Z, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hne : u ≠ v := by
        intro huv
        subst u
        exact (lt_irrefl (h v)) hu.2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hu.1, hlt, hu.2⟩
      · exact Or.inr ⟨hu.1, hgt, hu.2⟩
    · aesop
  have hY :
      ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT u v ∧
        @LT.lt (Euc m) om.toLT (h v) (h u))).card = Y.card := by
    congr 1
    ext u
    simp only [Y, Finset.mem_filter, Finset.mem_erase]
    aesop
  have hZ :
      ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT v u ∧
        @LT.lt (Euc m) om.toLT (h u) (h v))).card = Z.card := by
    congr 1
    ext u
    simp only [Z, Finset.mem_filter, Finset.mem_erase]
    aesop
  have hInv : elemInv on om a h = elemInv on om (a.erase v) h + Y.card + Z.card := by
    rw [elemInv_erase on om a h v hv, hY, hZ]
  change (-1 : ℚ) ^ A.card * (-1 : ℚ) ^ elemInv on om (a.erase v) h =
    (-1 : ℚ) ^ elemInv on om a h * (-1 : ℚ) ^ B.card
  rw [← pow_add, ← pow_add, hA, hB, hInv]
  ring_nf
  rw [pow_mul]
  rcases neg_one_pow_eq_or ℚ Z.card with hz | hz <;> simp [hz]

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
  classical
  have hinj' : (s.1.image h).card = (k + 1) + 1 := by omega
  have hs := hhm (k + 1) s
  rw [dif_pos hinj'] at hs
  obtain ⟨t, ht, hmt⟩ := hs
  rw [hmt, show Finsupp.single t (sortingSign on om s.1 h) =
      (sortingSign on om s.1 h) • Finsupp.single t 1 by ext; simp,
    map_smul, vertexChainMap_commutes_aux_generator_aux_boundaryL om L dL hdL t,
    vertexChainMap_commutes_aux_generator_aux_boundaryK on K dK hdK s]
  simp only [map_sum, map_smul]
  simp only [Finset.smul_sum, smul_smul]
  symm
  apply Finset.sum_bij (fun v _ => ⟨h v.1, by simpa [ht] using Finset.mem_image_of_mem h v.2⟩)
  · intro v hv
    exact Finset.mem_attach _ _
  · intro a ha b hb hab
    apply Subtype.ext
    apply (vertexChainMap_commutes_aux_generator_aux_injective_aux_injOn K s h hinj)
    · exact a.2
    · exact b.2
    · exact congrArg Subtype.val hab
  · intro w hw
    have hw' : w.1 ∈ s.1.image h := by rw [← ht]; exact w.2
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hw'
    exact ⟨⟨v, hv⟩, Finset.mem_attach _ _, Subtype.ext heq⟩
  · intro v hv
    have himg := vertexChainMap_commutes_aux_generator_aux_injective_aux_image_erase
      K s h hinj v.1 v.2
    have hcard : ((s.1.erase v.1).image h).card = k + 1 := by
      rw [himg, Finset.card_erase_of_mem (Finset.mem_image_of_mem h v.2), hinj]
      omega
    let sv := signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2
    have hsv := hhm k sv
    rw [dif_pos (by simpa [sv] using hcard)] at hsv
    obtain ⟨u, hu, hmu⟩ := hsv
    have hut : u = signedDeletion_sq_zero_aux_generator_aux_erase L t (h v.1) (by
        simpa [ht] using Finset.mem_image_of_mem h v.2) := by
      apply Subtype.ext
      change u.1 = t.1.erase (h v.1)
      rw [hu]
      simp only [sv, signedDeletion_sq_zero_aux_generator_aux_erase]
      rw [himg, ht]
    subst u
    rw [hmu]
    rw [show Finsupp.single
        (signedDeletion_sq_zero_aux_generator_aux_erase L t (h v.1) (by
          simpa [ht] using Finset.mem_image_of_mem h v.2))
        (sortingSign on om sv.1 h) =
        (sortingSign on om sv.1 h) • Finsupp.single
          (signedDeletion_sq_zero_aux_generator_aux_erase L t (h v.1) (by
            simpa [ht] using Finset.mem_image_of_mem h v.2)) 1 by ext; simp]
    rw [smul_smul]
    congr 1
    simpa [ht, sv, signedDeletion_sq_zero_aux_generator_aux_erase] using
      (vertexChainMap_commutes_aux_generator_aux_injective_aux_sign
      on om K s h hinj v.1 v.2)

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

/-- (B2) The two surviving deletions of a single collision have opposite signs:
`h '' (s.erase v)` and `h '' (s.erase w)` are the same sequence except that the
common value `h v = h w` moves across the `b - 1 - a` vertices strictly between
`v` (position `a`) and `w` (position `b`); each crossing flips one inversion. -/
lemma vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sign_aux_pos
    {n : ℕ} (on : LinearOrder (Euc n)) (a : Finset (Euc n))
    {v w : Euc n} (hv : v ∈ a) (hw : w ∈ a) (hvw : v ≠ w) :
    (-1 : ℚ) ^ ((a.sort on.le).idxOf v) *
        (-1 : ℚ) ^ (((a.erase v).sort on.le).idxOf w) =
      -((-1 : ℚ) ^ ((a.sort on.le).idxOf w) *
        (-1 : ℚ) ^ (((a.erase w).sort on.le).idxOf v)) := by
  classical
  rw [sort_idxOf_eq_card_lt on a v hv, sort_idxOf_eq_card_lt on a w hw,
    sort_idxOf_eq_card_lt on (a.erase v) w (by simp [hw, hvw.symm]),
    sort_idxOf_eq_card_lt on (a.erase w) v (by simp [hv, hvw])]
  rcases lt_or_gt_of_ne hvw with hvw' | hwv'
  · have h₁ :
        ((a.erase w).filter (fun u => @LT.lt (Euc n) on.toLT u v)) =
          a.filter (fun u => @LT.lt (Euc n) on.toLT u v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hua⟩, huv⟩
        exact ⟨hua, huv⟩
      · intro hu
        refine ⟨⟨?_, hu.1⟩, hu.2⟩
        intro huw
        subst u
        exact (not_lt_of_ge (le_of_lt hvw')) hu.2
    have h₂ :
        a.filter (fun u => @LT.lt (Euc n) on.toLT u w) =
          insert v ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT u w)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      by_cases huv : u = v
      · simp [huv, hv, hvw']
      · simp [huv]
    rw [h₁, h₂, Finset.card_insert_of_notMem]
    · simp [pow_succ, mul_comm]
    · simp
  · have h₁ :
        ((a.erase v).filter (fun u => @LT.lt (Euc n) on.toLT u w)) =
          a.filter (fun u => @LT.lt (Euc n) on.toLT u w) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hua⟩, huw⟩
        exact ⟨hua, huw⟩
      · intro hu
        refine ⟨⟨?_, hu.1⟩, hu.2⟩
        intro huv
        subst u
        exact (not_lt_of_ge (le_of_lt hwv')) hu.2
    have h₂ :
        a.filter (fun u => @LT.lt (Euc n) on.toLT u v) =
          insert w ((a.erase w).filter (fun u => @LT.lt (Euc n) on.toLT u v)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      by_cases huw : u = w
      · simp [huw, hw, hwv']
      · simp [huw]
    rw [h₁, h₂, Finset.card_insert_of_notMem]
    · simp [pow_succ, mul_comm]
    · simp

theorem vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sign {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    {k : ℕ} (K : GSC n) (h : Euc n → Euc m) (s : FaceIndex K (k + 1))
    (hcard : (s.1.image h).card = k + 1)
    {v w : Euc n} (hv : v ∈ s.1) (hw : w ∈ s.1) (hvw : v ≠ w) (hh : h v = h w) :
    (-1 : ℚ) ^ ((s.1.sort on.le).idxOf v) * sortingSign on om (s.1.erase v) h =
      -((-1 : ℚ) ^ ((s.1.sort on.le).idxOf w) * sortingSign on om (s.1.erase w) h) := by
  classical
  have himage_v : (s.1.erase v).image h = s.1.image h := by
    ext z
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst x
        exact ⟨w, ⟨hvw.symm, hw⟩, hh.symm⟩
      · exact ⟨x, ⟨hxv, hx⟩, rfl⟩
  have himage_w : (s.1.erase w).image h = s.1.image h := by
    ext z
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hxw : x = w
      · subst x
        exact ⟨v, ⟨hvw, hv⟩, hh⟩
      · exact ⟨x, ⟨hxw, hx⟩, rfl⟩
  have hinj_v : Set.InjOn h (s.1.erase v) := by
    apply Finset.injOn_of_card_image_eq
    rw [himage_v, hcard, Finset.card_erase_of_mem hv, s.2.2]
    omega
  have hinj_w : Set.InjOn h (s.1.erase w) := by
    apply Finset.injOn_of_card_image_eq
    rw [himage_w, hcard, Finset.card_erase_of_mem hw, s.2.2]
    omega
  have hvw_v := vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity
    on om (s.1.erase v) h hinj_v w (by simp [hw, hvw.symm])
  have hvw_w := vertexChainMap_commutes_aux_generator_aux_injective_aux_sign_aux_parity
    on om (s.1.erase w) h hinj_w v (by simp [hv, hvw])
  have herase : (s.1.erase v).erase w = (s.1.erase w).erase v := by
    ext x
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hxw, hxv, hxs⟩
      exact ⟨hxv, hxw, hxs⟩
    · rintro ⟨hxv, hxw, hxs⟩
      exact ⟨hxw, hxv, hxs⟩
  rw [herase, himage_v] at hvw_v
  rw [himage_w, hh] at hvw_w
  rw [sortingSign_eq_elemInv] at hvw_v hvw_w
  have hpos := vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sign_aux_pos
    on s.1 hv hw hvw
  rcases neg_one_pow_eq_or ℚ ((s.1.sort on.le).idxOf v) with h1 | h1 <;>
  rcases neg_one_pow_eq_or ℚ ((s.1.sort on.le).idxOf w) with h2 | h2 <;>
  rcases neg_one_pow_eq_or ℚ (((s.1.erase v).sort on.le).idxOf w) with h3 | h3 <;>
  rcases neg_one_pow_eq_or ℚ (((s.1.erase w).sort on.le).idxOf v) with h4 | h4 <;>
  rcases neg_one_pow_eq_or ℚ (elemInv on om ((s.1.erase w).erase v) h) with h5 | h5 <;>
  rcases neg_one_pow_eq_or ℚ (((s.1.image h).sort om.le).idxOf (h w)) with h6 | h6 <;>
  simp only [h1, h2, h3, h4, h5, h6] at hpos hvw_v hvw_w ⊢ <;>
    norm_num at hpos <;> norm_num at hvw_v hvw_w ⊢ <;> linarith


/-- (B-sum) Given (B2): expand `dK s` (`_aux_boundaryK`); deletions other than
`v, w` still collapse and map to `0`; the two remaining terms are the same face
with opposite coefficients. -/
theorem vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sum {n m : ℕ}
    (on : LinearOrder (Euc n)) (om : LinearOrder (Euc m))
    (K : GSC n) (L : GSC m) (h : Euc n → Euc m)
    (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (hm : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat L k)
    (hdK : IsSignedDeletion on K dK)
    (hhm : IsVertexChainMap on om K L h hm) (k : ℕ)
    (s : FaceIndex K (k + 1))
    (hcard : (s.1.image h).card = k + 1)
    (hB2 : ∀ {v w : Euc n}, v ∈ s.1 → w ∈ s.1 → v ≠ w → h v = h w →
      (-1 : ℚ) ^ ((s.1.sort on.le).idxOf v) * sortingSign on om (s.1.erase v) h =
        -((-1 : ℚ) ^ ((s.1.sort on.le).idxOf w) * sortingSign on om (s.1.erase w) h)) :
    hm k (dK k (Finsupp.single s 1)) = 0 := by
  classical
  have hlt : (s.1.image h).card < s.1.card := by
    rw [hcard, s.2.2]
    omega
  obtain ⟨v, hv, w, hw, hvw, hcollapse⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt hlt
  have himage_v : (s.1.erase v).image h = s.1.image h := by
    apply Finset.Subset.antisymm (Finset.image_mono h (Finset.erase_subset _ _))
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases hxv : x = v
    · subst x
      exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hvw.symm, hw⟩,
        hcollapse.symm⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩, rfl⟩
  have himage_w : (s.1.erase w).image h = s.1.image h := by
    apply Finset.Subset.antisymm (Finset.image_mono h (Finset.erase_subset _ _))
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases hxw : x = w
    · subst x
      exact Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hv⟩,
        hcollapse⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxw, hx⟩, rfl⟩
  let ev := signedDeletion_sq_zero_aux_generator_aux_erase K s v hv
  let ew := signedDeletion_sq_zero_aux_generator_aux_erase K s w hw
  have hev_image : ev.1.image h = s.1.image h := himage_v
  have hew_image : ew.1.image h = s.1.image h := himage_w
  have hcard_ev : (ev.1.image h).card = k + 1 := by rw [hev_image, hcard]
  have hcard_ew : (ew.1.image h).card = k + 1 := by rw [hew_image, hcard]
  have hspecv := hhm k ev
  rw [dif_pos hcard_ev] at hspecv
  obtain ⟨tv, htv, hmapv⟩ := hspecv
  have hspecw := hhm k ew
  rw [dif_pos hcard_ew] at hspecw
  obtain ⟨tw, htw, hmapw⟩ := hspecw
  have htvw : tv = tw := by
    apply Subtype.ext
    rw [htv, htw, hev_image, hew_image]
  have hzero (u : Euc n) (hu : u ∈ s.1) (huv : u ≠ v) (huw : u ≠ w) :
      hm k (Finsupp.single
        (signedDeletion_sq_zero_aux_generator_aux_erase K s u hu) 1) = 0 := by
    have hc : ((s.1.erase u).image h).card ≠ k + 1 := by
      intro hc
      have hcard_erase : (s.1.erase u).card = k + 1 := by
        rw [Finset.card_erase_of_mem hu, s.2.2]
        omega
      have hinj : Set.InjOn h (s.1.erase u) :=
        Finset.injOn_of_card_image_eq (hc.trans hcard_erase.symm)
      exact hvw (hinj (Finset.mem_erase.mpr ⟨huv.symm, hv⟩)
        (Finset.mem_erase.mpr ⟨huw.symm, hw⟩) hcollapse)
    have hspec := hhm k
      (signedDeletion_sq_zero_aux_generator_aux_erase K s u hu)
    change (if hinj : ((s.1.erase u).image h).card = k + 1 then _ else _) at hspec
    rw [dif_neg hc] at hspec
    exact hspec
  rw [vertexChainMap_commutes_aux_generator_aux_boundaryK on K dK hdK s, map_sum]
  let vv : {x // x ∈ s.1} := ⟨v, hv⟩
  let ww : {x // x ∈ s.1} := ⟨w, hw⟩
  have hvv : vv ≠ ww := by
    intro heq
    exact hvw (congrArg Subtype.val heq)
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_attach _ vv)]
  have hwwmem : ww ∈ s.1.attach \ {vv} := by
    simp only [Finset.mem_sdiff, Finset.mem_attach, Finset.mem_singleton]
    exact ⟨trivial, hvv.symm⟩
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hwwmem]
  have hrest : ∑ u ∈ (s.1.attach \ {vv}) \ {ww},
      hm k (((-1 : ℚ) ^ ((s.1.sort on.le).idxOf u.1)) •
        Finsupp.single (signedDeletion_sq_zero_aux_generator_aux_erase K s u.1 u.2) 1) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rcases Finset.mem_sdiff.mp hu with ⟨hu, huw⟩
    rcases Finset.mem_sdiff.mp hu with ⟨_, huv⟩
    rw [map_smul, hzero u.1 u.2]
    · exact smul_zero _
    · intro heq
      apply huv
      exact Finset.mem_singleton.mpr (Subtype.ext heq)
    · intro heq
      apply huw
      exact Finset.mem_singleton.mpr (Subtype.ext heq)
  rw [hrest, add_zero, map_smul, map_smul]
  change _ • hm k (Finsupp.single ev 1) + _ • hm k (Finsupp.single ew 1) = 0
  rw [hmapv, hmapw, htvw]
  have hs := hB2 hv hw hvw hcollapse
  change (-1 : ℚ) ^ ((s.1.sort on.le).idxOf v) * sortingSign on om ev.1 h =
    -((-1 : ℚ) ^ ((s.1.sort on.le).idxOf w) * sortingSign on om ew.1 h) at hs
  ext z
  by_cases hz : z = tw
  · subst z
    simpa [vv, ww] using (eq_neg_iff_add_eq_zero.mp hs)
  · simp [hz]

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
  exact vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sum on om K L h dK hm hdK hhm k s hcard
    (fun hv hw hvw hh => vertexChainMap_commutes_aux_generator_aux_collapse_aux_one_aux_sign on om K h s hcard hv hw hvw hh)

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

/- claude-14 fix 2026-10-28 (lemma-2's counterexample): `K'` must be the
barycentric subdivision; for an arbitrary `K'` (e.g. only the vertices `a, b, m`
of a subdivided edge, no edges) the coefficient condition is vacuous in degree 1
and `sd` is not a chain map. -/
theorem subdivisionChainMap_commutes_aux_signedDeletion_unique {n : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (d e : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (he : IsSignedDeletion o K e) : d = e := by
  funext k
  ext s t
  obtain ⟨z, hz, hza⟩ := hd k s
  obtain ⟨w, hw, hwa⟩ := he k s
  change d k (Finsupp.single s 1) t = e k (Finsupp.single s 1) t
  rw [hz, hw, hza, hwa]

theorem subdivisionChainMap_commutes_aux_subdivision_unique {n : ℕ}
    (o : LinearOrder (Euc n)) (K K' : GSC n)
    (sd se : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hsd : IsSubdivisionChainMap o K K' sd)
    (hse : IsSubdivisionChainMap o K K' se) : sd = se := by
  funext k
  ext s u
  obtain ⟨z, hz, hza⟩ := hsd k s
  obtain ⟨w, hw, hwa⟩ := hse k s
  change sd k (Finsupp.single s 1) u = se k (Finsupp.single s 1) u
  rw [hz, hw, hza, hwa]

/-- The ordered cone on a subdivided face.  Its value is zero unless adjoining
`b` again gives a face; the exponent is the position at which `b` is inserted
in the order `o`. -/
def subdivisionCone {n : ℕ} (o : LinearOrder (Euc n)) (K' : GSC n)
    (b : Euc n) (k : ℕ) : FaceModuleCat K' k ⟶ FaceModuleCat K' (k + 1) := by
  classical
  let c : FaceIndex K' k → FaceModule K' (k + 1) := fun u =>
    if hb : b ∉ u.1 ∧ insert b u.1 ∈ K'.faces then
      Finsupp.single
        (⟨insert b u.1, hb.2, by rw [Finset.card_insert_of_notMem hb.1, u.2.2]⟩ :
          FaceIndex K' (k + 1))
        ((-1 : ℚ) ^ (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card)
    else 0
  exact ModuleCat.ofHom (Finsupp.linearCombination ℚ c)

/-- Every generator occurring in `x` can be coned to `b`. -/
def ConeAdmissible {n k : ℕ} (K' : GSC n) (b : Euc n)
    (x : FaceModule K' k) : Prop :=
  ∀ u : FaceIndex K' k, x u ≠ 0 → b ∉ u.1 ∧ insert b u.1 ∈ K'.faces

lemma subdivisionChainMap_commutes_aux_cone_boundary_aux_single_aux_sign
    {α : Type*} [DecidableEq α] (o : LinearOrder α) (a : Finset α) (b p : α)
    (hb : b ∉ a) (hp : p ∈ a) :
    (-1 : ℚ) ^ (a.filter fun q => @LT.lt α o.toLT q b).card *
        (-1 : ℚ) ^ ((insert b a).filter fun q => @LT.lt α o.toLT q p).card =
      -((-1 : ℚ) ^ (a.filter fun q => @LT.lt α o.toLT q p).card *
        (-1 : ℚ) ^ ((a.erase p).filter fun q => @LT.lt α o.toLT q b).card) := by
  letI := o
  by_cases hpb : p < b
  · have hbp : ¬ b < p := not_lt_of_ge hpb.le
    simp [Finset.filter_insert, Finset.filter_erase, hb, hp, hpb, hbp,
      Finset.card_erase_of_mem]
    have hcpos : 0 < (a.filter fun q => q < b).card :=
      Finset.card_pos.mpr ⟨p, by simp [hp, hpb]⟩
    have he : (a.filter fun q => q < b).card =
        (a.filter fun q => q < b).card - 1 + 1 := by omega
    rw [he, pow_succ]
    have he2 : (a.filter fun q => q < b).card - 1 + 1 - 1 =
        (a.filter fun q => q < b).card - 1 := by omega
    rw [he2]
    ring
  · have hbp : b < p := lt_of_le_of_ne (le_of_not_gt hpb) (by
      intro h
      subst p
      exact hb hp)
    simp [Finset.filter_insert, Finset.filter_erase, hb, hp, hpb, hbp,
      Finset.card_erase_of_mem, pow_succ]
    ring

/-- Positive-degree cone-boundary identity.  This is the local sign
calculation: deletion of `b` gives `x`, while deleting a vertex of `u` has the
opposite sign from coning that deletion.
Route (claude-14): with `s = insert b u` and `c_u = #{q ∈ u | q <_o b}`, split
`∑ c ∈ s.attach` as the `b`-term plus `∑ p ∈ u` (`Finset.sum_insert`, after
transporting `attach`).  `b`-term: `s.erase b = u` and `idx_s b = #{q ∈ s | q <_o b} = c_u`
(`sort_idxOf_eq_card_lt`), so the sign `(-1)^(c_u + idx_s b) = 1`.  `p`-term:
`s.erase p = insert b (u.erase p)`; `idx_s p = idx_u p + [b <_o p]` and
`c_u = c_{u.erase p} + [p <_o b]` (both from `sort_idxOf_eq_card_lt` and
`Finset.filter_insert`/`filter_erase`), so the exponents differ by `1`
(`p ≠ b`, `o` total); the cone condition for `u.erase p` holds by `K'.down_closed`. -/
lemma subdivisionChainMap_commutes_aux_cone_boundary_aux_single {n k : ℕ}
    (o : LinearOrder (Euc n)) (K' : GSC n)
    (dK' : ∀ j, FaceModuleCat K' (j + 1) ⟶ FaceModuleCat K' j)
    (hdK' : IsSignedDeletion o K' dK') (b : Euc n)
    (u : FaceIndex K' (k + 1))
    (hu : b ∉ u.1 ∧ insert b u.1 ∈ K'.faces) :
    dK' (k + 1) (subdivisionCone o K' b (k + 1) (Finsupp.single u 1)) =
      Finsupp.single u 1 -
        subdivisionCone o K' b k (dK' k (Finsupp.single u 1)) := by
  classical
  let s : FaceIndex K' (k + 2) :=
    ⟨insert b u.1, hu.2, by rw [Finset.card_insert_of_notMem hu.1, u.2.2]⟩
  have hcone : subdivisionCone o K' b (k + 1) (Finsupp.single u 1) =
      ((-1 : ℚ) ^ (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card) •
        Finsupp.single s 1 := by
    simp [subdivisionCone, hu, s, Finsupp.smul_single]
  rw [hcone, map_smul, signedDeletion_sq_zero_aux_generator_aux_boundary o K' dK' hdK' s,
    signedDeletion_sq_zero_aux_generator_aux_boundary o K' dK' hdK' u, map_sum]
  have hs1 : (s.1 : Finset (Euc n)) = insert b u.1 := rfl
  have hbnot : (⟨b, Finset.mem_insert_self b u.1⟩ : {x // x ∈ insert b u.1}) ∉
      (u.1.attach).image fun x => (⟨x.1, Finset.mem_insert_of_mem x.2⟩ : {x // x ∈ insert b u.1}) := by
    simp only [Finset.mem_image, Finset.mem_attach, true_and, not_exists]
    intro x hx
    have h := congrArg Subtype.val hx
    simp only at h
    exact hu.1 (h ▸ x.2)
  simp only [hs1]
  rw [Finset.attach_insert, Finset.sum_insert hbnot, Finset.sum_image (fun x _ y _ h =>
    Subtype.ext (by simpa using congrArg Subtype.val h))]
  set c : ℚ := (-1 : ℚ) ^ (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card with hc
  have hcc : c * c = 1 := by rw [hc, ← pow_add, ← two_mul, pow_mul]; norm_num
  have heb : signedDeletion_sq_zero_aux_generator_aux_erase K' s b
      (Finset.mem_insert_self b u.1) = u := Subtype.ext (Finset.erase_insert hu.1)
  have hidxb : List.idxOf b ((insert b u.1).sort o.le) =
      (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card := by
    rw [sort_idxOf_eq_card_lt o _ b (Finset.mem_insert_self b u.1), Finset.filter_insert,
      if_neg (@lt_irrefl _ o.toPreorder b)]
  simp only [Subtype.coe_mk]
  rw [hidxb, heb, smul_add, smul_smul, hcc, one_smul, Finset.smul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hxb : x.1 ≠ b := fun h => hu.1 (h ▸ x.2)
  have he : b ∉ (u.1.erase x.1) ∧ insert b (u.1.erase x.1) ∈ K'.faces :=
    ⟨fun h => hu.1 (Finset.mem_of_mem_erase h),
      K'.down_closed hu.2 (Finset.insert_subset_insert _ (Finset.erase_subset _ _))
        (Finset.insert_nonempty _ _)⟩
  have hconex : subdivisionCone o K' b k
      (Finsupp.single (signedDeletion_sq_zero_aux_generator_aux_erase K' u x.1 x.2) 1) =
      ((-1 : ℚ) ^ ((u.1.erase x.1).filter fun q => @LT.lt (Euc n) o.toLT q b).card) •
        Finsupp.single (⟨insert b (u.1.erase x.1), he.2, by
          rw [Finset.card_insert_of_notMem he.1, Finset.card_erase_of_mem x.2, u.2.2]; omega⟩ :
            FaceIndex K' (k + 1)) 1 := by
    simp [subdivisionCone, signedDeletion_sq_zero_aux_generator_aux_erase, he]
    exact (Finsupp.smul_single_one _ _).symm
  rw [map_smul, hconex, smul_smul]
  erw [smul_smul]
  rw [← neg_smul]
  have hex : signedDeletion_sq_zero_aux_generator_aux_erase K' s x.1
      (Finset.mem_insert_of_mem x.2) = ⟨insert b (u.1.erase x.1), he.2, by
          rw [Finset.card_insert_of_notMem he.1, Finset.card_erase_of_mem x.2, u.2.2]; omega⟩ :=
    Subtype.ext (Finset.erase_insert_of_ne hxb.symm)
  rw [hex]
  congr 1
  rw [sort_idxOf_eq_card_lt o _ x.1 (Finset.mem_insert_of_mem x.2),
    sort_idxOf_eq_card_lt o _ x.1 x.2]
  exact subdivisionChainMap_commutes_aux_cone_boundary_aux_single_aux_sign o u.1 b x.1 hu.1 x.2

theorem subdivisionChainMap_commutes_aux_cone_boundary {n k : ℕ}
    (o : LinearOrder (Euc n)) (K' : GSC n)
    (dK' : ∀ j, FaceModuleCat K' (j + 1) ⟶ FaceModuleCat K' j)
    (hdK' : IsSignedDeletion o K' dK') (b : Euc n)
    (x : FaceModule K' (k + 1)) (hx : ConeAdmissible K' b x) :
    dK' (k + 1) (subdivisionCone o K' b (k + 1) x) =
      x - subdivisionCone o K' b k (dK' k x) := by
  classical
  rw [← Finsupp.sum_single x]
  change dK' (k + 1) (subdivisionCone o K' b (k + 1)
      (∑ u ∈ x.support, Finsupp.single u (x u))) =
    (∑ u ∈ x.support, Finsupp.single u (x u)) -
      subdivisionCone o K' b k
        (dK' k (∑ u ∈ x.support, Finsupp.single u (x u)))
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul]
  rw [map_smul, ← smul_sub]
  rw [subdivisionChainMap_commutes_aux_cone_boundary_aux_single o K' dK' hdK' b u
    (hx u (Finsupp.mem_support_iff.mp hu))]

/-- Degree-zero cone-boundary identity, with the augmentation term at the cone
vertex made explicit. -/
lemma subdivisionChainMap_commutes_aux_cone_boundary_zero_aux_single {n : ℕ}
    (o : LinearOrder (Euc n)) (K' : GSC n)
    (dK' : ∀ j, FaceModuleCat K' (j + 1) ⟶ FaceModuleCat K' j)
    (hdK' : IsSignedDeletion o K' dK') (b : Euc n)
    (hb : ({b} : Finset (Euc n)) ∈ K'.faces) (u : FaceIndex K' 0)
    (hu : b ∉ u.1 ∧ insert b u.1 ∈ K'.faces) (a : ℚ) :
    dK' 0 (subdivisionCone o K' b 0 (Finsupp.single u a)) =
      Finsupp.single u a - a •
        Finsupp.single (⟨{b}, hb, by simp⟩ : FaceIndex K' 0) 1 := by
  classical
  letI : LinearOrder (Euc n) := o
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp u.2.2
  have hvb : v ≠ b := by
    rintro rfl; exact hu.1 (by rw [hv]; exact Finset.mem_singleton_self _)
  let s : FaceIndex K' 1 :=
    ⟨insert b u.1, hu.2, by rw [Finset.card_insert_of_notMem hu.1, u.2.2]⟩
  have hcone : subdivisionCone o K' b 0 (Finsupp.single u a) =
      (a * (-1 : ℚ) ^ (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card) •
        Finsupp.single s 1 := by
    simp [subdivisionCone, hu, s, Finsupp.smul_single, mul_comm]
  rw [hcone, map_smul]
  erw [Finsupp.smul_single_one]
  obtain ⟨z, hz, hzt⟩ := hdK' 0 s
  rw [hz]
  ext t
  rw [Finsupp.smul_apply, hzt t]
  simp only [s, hv]
  rw [Finset.sum_pair hvb.symm]
  have e1 : ({b, v} : Finset (Euc n)).erase b = {v} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩; exact absurd h2 h1; exact h2
    · rintro rfl; exact ⟨hvb, Or.inr rfl⟩
  have e2 : ({b, v} : Finset (Euc n)).erase v = {b} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩; exact h2; exact absurd h2 h1
    · rintro rfl; exact ⟨hvb.symm, Or.inl rfl⟩
  rw [e1, e2, sort_idxOf_eq_card_lt o _ b (by simp), sort_idxOf_eq_card_lt o _ v (by simp)]
  have hut : (u = t) ↔ ({v} : Finset (Euc n)) = t.1 := by rw [← hv]; exact Subtype.ext_iff
  have hbt : ((⟨{b}, hb, by simp⟩ : FaceIndex K' 0) = t) ↔ ({b} : Finset (Euc n)) = t.1 :=
    Subtype.ext_iff
  simp only [Finsupp.sub_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
  have hvneb : ({v} : Finset (Euc n)) ≠ {b} := by simpa using hvb
  rcases lt_or_gt_of_ne hvb with hlt | hgt
  · have c1 : (({b, v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q b).card = 1 := by
      rw [Finset.card_eq_one]; refine ⟨v, ?_⟩; ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩; exact absurd h (lt_irrefl _); rfl
      · rintro rfl; exact ⟨Or.inr rfl, hlt⟩
    have c2 : (({b, v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q v).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact not_lt_of_gt hlt
      · exact lt_irrefl _
    have c3 : (({v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q b).card = 1 := by
      rw [Finset.filter_singleton, if_pos hlt]; rfl
    rw [c1, c2, c3]
    by_cases h1 : ({v} : Finset (Euc n)) = t.1
    · have h2 : ({b} : Finset (Euc n)) ≠ t.1 := fun h => hvneb (h1.trans h.symm)
      simp only [h1, if_true, h2, if_false]
      erw [Finsupp.single_apply, if_neg ((hbt.not).mpr h2)]
      norm_num
      exact fun h => absurd (hut.mpr h1) h
    · by_cases h2 : ({b} : Finset (Euc n)) = t.1
      · simp only [h1, if_false, h2, if_true]
        erw [Finsupp.single_apply]
        rw [if_neg ((hut.not).mpr h1)]
        split_ifs with hh
        · norm_num
        · exact absurd (Subtype.ext (by rfl)) hh
      · simp only [h1, if_false, h2]
        erw [Finsupp.single_apply, if_neg ((hbt.not).mpr h2)]
        norm_num
        exact fun h => absurd h ((hut.not).mpr h1)
  · have c1 : (({b, v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact lt_irrefl _
      · exact not_lt_of_gt hgt
    have c2 : (({b, v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q v).card = 1 := by
      rw [Finset.card_eq_one]; refine ⟨b, ?_⟩; ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩; rfl; exact absurd h (lt_irrefl _)
      · rintro rfl; exact ⟨Or.inl rfl, hgt⟩
    have c3 : (({v} : Finset (Euc n)).filter fun q => @LT.lt (Euc n) o.toLT q b).card = 0 := by
      rw [Finset.filter_singleton, if_neg (not_lt_of_gt hgt)]; rfl
    rw [c1, c2, c3]
    by_cases h1 : ({v} : Finset (Euc n)) = t.1
    · have h2 : ({b} : Finset (Euc n)) ≠ t.1 := fun h => hvneb (h1.trans h.symm)
      simp only [h1, if_true, h2, if_false]
      erw [Finsupp.single_apply, if_neg ((hbt.not).mpr h2)]
      norm_num
      exact fun h => absurd (hut.mpr h1) h
    · by_cases h2 : ({b} : Finset (Euc n)) = t.1
      · simp only [h1, if_false, h2, if_true]
        erw [Finsupp.single_apply]
        rw [if_neg ((hut.not).mpr h1)]
        split_ifs with hh
        · norm_num
        · exact absurd (Subtype.ext (by rfl)) hh
      · simp only [h1, if_false, h2]
        erw [Finsupp.single_apply, if_neg ((hbt.not).mpr h2)]
        norm_num
        exact fun h => absurd h ((hut.not).mpr h1)
/-
  classical
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp u.2.2
  have hvb : v ≠ b := by simpa [hv, Finset.mem_singleton, eq_comm] using hu.1
  rw [show Finsupp.single u a = a • Finsupp.single u 1 by
    ext; simp [Finsupp.single_apply]]
  rw [map_smul, map_smul]
  simp only [subdivisionCone]
  change a • dK' 0 ((Finsupp.linearCombination ℚ fun w : FaceIndex K' 0 =>
      if hw : b ∉ w.1 ∧ insert b w.1 ∈ K'.faces then
        Finsupp.single
          (⟨insert b w.1, hw.2,
            by rw [Finset.card_insert_of_notMem hw.1, w.2.2]⟩ : FaceIndex K' 1)
          ((-1 : ℚ) ^ (w.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card)
      else 0) (Finsupp.single u 1)) = _
  rw [Finsupp.linearCombination_single]
  rw [dif_pos hu]
  simp only [one_smul]
  let s : FaceIndex K' 1 :=
    ⟨insert b u.1, hu.2, by rw [Finset.card_insert_of_notMem hu.1, u.2.2]⟩
  let e : ℚ := (-1 : ℚ) ^
    (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card
  change a • dK' 0 (Finsupp.single s e) = _
  rw [show Finsupp.single s e = e • Finsupp.single s 1 by
    ext; simp [Finsupp.single_apply]]
  rw [map_smul]
  obtain ⟨z, hz, hformula⟩ := hdK' 0 s
  rw [hz]
  ext t
  change a * (e * z t) = _
  rw [hformula]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp t.2.2
  have hut : u = t ↔ v = w := by
    constructor
    · intro h; simpa [hv, hw] using congrArg Subtype.val h
    · intro h; subst w; exact Subtype.ext (hv.trans hw.symm)
  have hbt : (⟨{b}, hb, by simp⟩ : FaceIndex K' 0) = t ↔ b = w := by
    constructor
    · intro h; simpa [hw] using congrArg Subtype.val h
    · intro h; subst w; exact Subtype.ext hw.symm
  have herasev : ({b, v} : Finset (Euc n)).erase v = {b} := by
    ext q; simp [hvb, hvb.symm]
  have heraseb : ({b, v} : Finset (Euc n)).erase b = {v} := by
    ext q; simp [hvb, hvb.symm]
  rcases lt_or_gt_of_ne hvb with hvlt | hblt
  · have hsort : ({b, v} : Finset (Euc n)).sort o.le = [v, b] := by
      rw [Finset.pair_comm]
      exact Finset.sort_insert o.le (by simp [le_of_lt hvlt]) (by simp [hvb])
    by_cases hwv : w = v
    · subst w; simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt,
        Finsupp.single_apply, hvb, hvb.symm, hvlt]
    by_cases hwb : w = b
    · subst w; simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt,
        Finsupp.single_apply, hvb, hvb.symm, hvlt]
    simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt, Finsupp.single_apply, hvb, hvb.symm,
      hvlt, hwv, hwb]
  · have hsort : ({b, v} : Finset (Euc n)).sort o.le = [b, v] := by
      exact Finset.sort_insert o.le (by simp [le_of_lt hblt]) (by simp [hvb])
    by_cases hwv : w = v
    · subst w; simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt,
        Finsupp.single_apply, hvb, hvb.symm, hblt]
    by_cases hwb : w = b
    · subst w; simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt,
        Finsupp.single_apply, hvb, hvb.symm, hblt]
    simp [s, e, hv, hw, hsort, herasev, heraseb, hut, hbt, Finsupp.single_apply, hvb, hvb.symm,
      hblt, hwv, hwb]
-/

theorem subdivisionChainMap_commutes_aux_cone_boundary_zero {n : ℕ}
    (o : LinearOrder (Euc n)) (K' : GSC n)
    (dK' : ∀ j, FaceModuleCat K' (j + 1) ⟶ FaceModuleCat K' j)
    (hdK' : IsSignedDeletion o K' dK') (b : Euc n)
    (hb : ({b} : Finset (Euc n)) ∈ K'.faces) (x : FaceModule K' 0)
    (hx : ConeAdmissible K' b x) :
    dK' 0 (subdivisionCone o K' b 0 x) =
      x - (x.sum fun _ a => a) •
        Finsupp.single (⟨{b}, hb, by simp⟩ : FaceIndex K' 0) 1 := by
  sorry
/-
  classical
  rw [← Finsupp.sum_single x]
  change dK' 0 (subdivisionCone o K' b 0
      (∑ u ∈ x.support, Finsupp.single u (x u))) = _
  simp only [map_sum]
  have hsum :
      (∑ u ∈ x.support,
        dK' 0 (subdivisionCone o K' b 0 (Finsupp.single u (x u)))) =
      ∑ u ∈ x.support, (Finsupp.single u (x u) - (x u) •
        Finsupp.single (⟨{b}, hb, by simp⟩ : FaceIndex K' 0) 1) := by
    apply Finset.sum_congr rfl
    intro u hu
    exact subdivisionChainMap_commutes_aux_cone_boundary_zero_aux_single
      o K' dK' hdK' b hb u (hx u (Finsupp.mem_support_iff.mp hu)) (x u)
  rw [hsum]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_smul]
-/

/-- Subdivision chains of proper facets can be coned to the barycenter of the
ambient face. -/
theorem subdivisionChainMap_commutes_aux_facet_admissible {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (sd : ∀ j, FaceModuleCat K j ⟶ FaceModuleCat (barycentricStep K) j)
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (s : FaceIndex K (k + 1)) (v : Euc n) (hv : v ∈ s.1) :
    ConeAdmissible (barycentricStep K) (GeometricSimplicialSubdivision.barycenter s.1)
      (sd k (Finsupp.single
        (signedDeletion_sq_zero_aux_generator_aux_erase K s v hv) 1)) := by
  classical
  let r := signedDeletion_sq_zero_aux_generator_aux_erase K s v hv
  obtain ⟨z, hz, hcoeff⟩ := hsd k r
  rw [hz]
  intro u hu
  have hzu : z u ≠ 0 := hu
  rw [hcoeff u] at hzu
  have hex : ∃ c ∈ r.1.powerset.powerset,
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
  obtain ⟨c, hcps, hc, huimage⟩ := hex
  have hcsub : ∀ t ∈ c, t ⊆ s.1.erase v := by
    intro t ht
    exact Finset.mem_powerset.1 ((Finset.mem_powerset.1 hcps) ht)
  have htsub : ∀ t ∈ c, t ⊂ s.1 := by
    intro t ht
    refine Finset.ssubset_iff_subset_ne.2 ⟨(hcsub t ht).trans (Finset.erase_subset _ _), ?_⟩
    intro heq
    have hvt : v ∈ t := by rw [heq]; exact hv
    have := (hcsub t ht) hvt
    simpa using this
  have hbnot : GeometricSimplicialSubdivision.barycenter s.1 ∉ u.1 := by
    rw [huimage]
    intro hb
    obtain ⟨t, htc, hbt⟩ := Finset.mem_image.1 hb
    have htne : t.Nonempty := K.nonempty_of_mem_faces (hc.1 t htc)
    have hmem := GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_mem_span
      htne (show t ⊆ t from fun _ h => h)
    apply GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_not_mem_span
      K s.2.1 (htsub t htc)
    simpa [hbt] using hmem
  refine ⟨hbnot, ?_⟩
  change insert (GeometricSimplicialSubdivision.barycenter s.1) u.1 ∈
    (GeometricSimplicialSubdivision.barycentricSubdivision K
      (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent K)
      (GeometricSimplicialSubdivision.barycentricFaces_isLowerSet K)
      (GeometricSimplicialSubdivision.barycentricFaces_inter_subset K)).faces
  change insert (GeometricSimplicialSubdivision.barycenter s.1) u.1 ∈
    GeometricSimplicialSubdivision.barycentricFaces K \ {∅}
  constructor
  · refine ⟨insert s.1 c, ?_, ?_⟩
    · constructor
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | htc
        · exact s.2.1
        · exact hc.1 t htc
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | hac <;>
          rcases Finset.mem_insert.1 hb with rfl | hbc
        · exact (hab rfl).elim
        · exact Or.inr (htsub b hbc)
        · exact Or.inl (htsub a hac)
        · exact hc.2 a hac b hbc hab
    · rw [Finset.image_insert, ← huimage]
  · simp

/-- Distinct members of a strict face chain have distinct barycenters (the
larger face's barycenter is off the affine span of the smaller one). -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_bary_injOn {n : ℕ}
    (K : GSC n) (c : Finset (Finset (Euc n)))
    (hc : GeometricSimplicialSubdivision.IsStrictFaceChain K c) :
    Set.InjOn GeometricSimplicialSubdivision.barycenter (c : Set (Finset (Euc n))) := by
  intro s hs t ht hst
  have hi := (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain
    K c hc).injective
  have heq : (⟨s, hs⟩ : c) = ⟨t, ht⟩ := hi hst
  exact congrArg Subtype.val heq

/-- A strict face chain of `k + 2` faces inside a `(k+1)`-face `s` is maximal: it
contains `s`, and the rest lies in the facet opposite the new vertex of `s`. -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_top_aux_card_inj {n : ℕ}
    (K : GSC n) (c : Finset (Finset (Euc n)))
    (hc : GeometricSimplicialSubdivision.IsStrictFaceChain K c) :
    Set.InjOn Finset.card (c : Set (Finset (Euc n))) := by
  intro a ha b hb hab
  by_contra hne
  rcases hc.2 a ha b hb hne with h | h
  · exact (Finset.card_lt_card h).ne hab
  · exact (Finset.card_lt_card h).ne' hab

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_top {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (c : Finset (Finset (Euc n)))
    (hc : GeometricSimplicialSubdivision.IsStrictFaceChain K c)
    (hcs : c ⊆ s.1.powerset) (hcard : c.card = k + 2) :
    s.1 ∈ c ∧ flagNewVertex o c s.1 ∈ s.1 ∧
      c.erase s.1 ⊆ (s.1.erase (flagNewVertex o c s.1)).powerset := by
  have hscard : s.1.card = k + 2 := s.2.2
  have hcinj := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_top_aux_card_inj K c hc
  have himage : (c.image Finset.card).card = k + 2 := by
    rw [Finset.card_image_iff.mpr hcinj, hcard]
  have htop : s.1 ∈ c := by
    by_contra hs
    have hsub : c.image Finset.card ⊆ Finset.Icc 1 (k + 1) := by
      intro m hm
      obtain ⟨t, htc, rfl⟩ := Finset.mem_image.1 hm
      have htne : t.Nonempty := K.nonempty_of_mem_faces (hc.1 t htc)
      have htle := Finset.card_le_card (Finset.mem_powerset.1 (hcs htc))
      have htlt : t.card < s.1.card := lt_of_le_of_ne htle (fun h => by
        have heq := Finset.eq_of_subset_of_card_le
          (Finset.mem_powerset.1 (hcs htc)) h.symm.le
        exact hs (heq ▸ htc))
      rw [hscard] at htlt
      simp only [Finset.mem_Icc]
      constructor
      · exact Finset.card_pos.2 htne
      · exact Nat.lt_succ_iff.1 (by simpa [Nat.add_assoc] using htlt)
    have hbad : k + 2 ≤ k + 1 := by
      simpa [himage, Nat.card_Icc] using Finset.card_le_card hsub
    omega
  let d := c.erase s.1
  have hdcard : d.card = k + 1 := by
    dsimp [d]
    rw [Finset.card_erase_of_mem htop, hcard]
    omega
  have hdsub : d.image Finset.card ⊆ Finset.Icc 1 (k + 1) := by
    intro m hm
    obtain ⟨t, htd, rfl⟩ := Finset.mem_image.1 hm
    have htc : t ∈ c := (Finset.mem_erase.1 htd).2
    have htne : t.Nonempty := K.nonempty_of_mem_faces (hc.1 t htc)
    have htss : t ⊂ s.1 := by
      rcases hc.2 t htc s.1 htop (Finset.mem_erase.1 htd).1 with h | h
      · exact h
      · exact (h.not_subset (Finset.mem_powerset.1 (hcs htc))).elim
    simp only [Finset.mem_Icc]
    constructor
    · exact Finset.card_pos.2 htne
    · have := Finset.card_lt_card htss
      omega
  have hdinj : Set.InjOn Finset.card (d : Set (Finset (Euc n))) :=
    hcinj.mono (Finset.erase_subset _ _)
  have hdimagecard : (d.image Finset.card).card = k + 1 := by
    rw [Finset.card_image_iff.mpr hdinj, hdcard]
  have hdeq : d.image Finset.card = Finset.Icc 1 (k + 1) := by
    apply Finset.eq_of_subset_of_card_le hdsub
    rw [Nat.card_Icc, hdimagecard]
    omega
  have hex : ∃ t ∈ d, t.card = k + 1 := by
    have hm : k + 1 ∈ d.image Finset.card := by
      rw [hdeq]
      simp
    simpa using Finset.mem_image.1 hm
  obtain ⟨t, htd, htcard⟩ := hex
  have htc : t ∈ c := (Finset.mem_erase.1 htd).2
  have htss : t ⊂ s.1 := by
    rcases hc.2 t htc s.1 htop (Finset.mem_erase.1 htd).1 with h | h
    · exact h
    · exact (h.not_subset (Finset.mem_powerset.1 (hcs htc))).elim
  have hall : ∀ u ∈ c, u ⊂ s.1 → u ⊆ t := by
    intro u huc hus
    by_cases hut : u = t
    · simpa [hut]
    rcases hc.2 u huc t htc hut with h | h
    · exact h.subset
    · have := Finset.card_lt_card h
      have huscard := Finset.card_lt_card hus
      omega
  have hUnion : c.biUnion (fun u => if u ⊂ s.1 then u else ∅) = t := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨u, huc, hxu⟩ := Finset.mem_biUnion.1 hx
      split at hxu
      · exact hall u huc ‹u ⊂ s.1› hxu
      · simp at hxu
    · intro x hxt
      apply Finset.mem_biUnion.2
      exact ⟨t, htc, by simp [htss, hxt]⟩
  have hdiffcard : (s.1 \ t).card = 1 := by
    rw [Finset.card_sdiff_of_subset htss.subset, hscard, htcard]
    omega
  obtain ⟨v, hv⟩ : ∃ v, s.1 \ t = {v} := Finset.card_eq_one.1 hdiffcard
  have hvmem : v ∈ s.1 \ t := by rw [hv]; simp
  have hflag : flagNewVertex o c s.1 = v := by
    rw [flagNewVertex, hUnion, hv]
    simp
  refine ⟨htop, ?_, ?_⟩
  · rw [hflag]
    exact (Finset.mem_sdiff.1 hvmem).1
  · rw [hflag]
    intro u hud
    apply Finset.mem_powerset.2
    have huc := (Finset.mem_erase.1 hud).2
    have hus : u ⊂ s.1 := by
      rcases hc.2 u huc s.1 htop (Finset.mem_erase.1 hud).1 with h | h
      · exact h
      · exact (h.not_subset (Finset.mem_powerset.1 (hcs huc))).elim
    have hut := hall u huc hus
    intro x hxu
    have hxs : x ∈ s.1 := hus.subset hxu
    have hxv : x ≠ v := by
      by_contra hx
      have hxmem : x ∈ s.1 \ t := by simpa [hx] using hvmem
      exact (Finset.mem_sdiff.1 hxmem).2 (hut hxu)
    exact Finset.mem_erase.2 ⟨hxv, hxs⟩

/-- Converse of `_aux_top`: topping a maximal chain of the facet `s.erase v`
with `s` gives a strict face chain whose new vertex at `s` is `v`. -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_insert {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    GeometricSimplicialSubdivision.IsStrictFaceChain K (insert s.1 c') ∧ s.1 ∉ c' ∧
      flagNewVertex o (insert s.1 c') s.1 = v := by
  classical
  have hsscard : s.1.card = k + 2 := s.2.2
  have hercard : (s.1.erase v).card = k + 1 := by
    rw [Finset.card_erase_of_mem hv, hsscard]
    omega
  have hinj : Set.InjOn Finset.card (c' : Set (Finset (Euc n))) := by
    intro a ha b hb hab
    by_contra hne
    rcases hc'.2 a ha b hb hne with h | h
    · exact (Nat.ne_of_lt (Finset.card_lt_card h)) hab
    · exact (Nat.ne_of_lt (Finset.card_lt_card h)) hab.symm
  have htop : s.1.erase v ∈ c' := by
    by_contra hnot
    have himsub : c'.image Finset.card ⊆ Finset.Icc 1 k := by
      intro m hm
      obtain ⟨t, htc, rfl⟩ := Finset.mem_image.1 hm
      have htne := GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_nonempty
        K c' hc' t htc
      have htsub := Finset.mem_powerset.1 (hcs htc)
      have htnefacet : t ≠ s.1.erase v := by exact fun h => hnot (h ▸ htc)
      have hproper : t ⊂ s.1.erase v := Finset.ssubset_iff_subset_ne.2 ⟨htsub, htnefacet⟩
      apply Finset.mem_Icc.2
      constructor
      · exact Finset.one_le_card.2 htne
      · have := Finset.card_lt_card hproper
        omega
    have himcard : (c'.image Finset.card).card = k + 1 := by
      rw [Finset.card_image_iff.mpr hinj]
      exact hcard
    have hle := Finset.card_le_card himsub
    rw [Nat.card_Icc] at hle
    omega
  have hproperfacet : s.1.erase v ⊂ s.1 := by
    exact Finset.ssubset_iff_subset_ne.2 ⟨Finset.erase_subset _ _, fun h => by
      have hh := congrArg (fun z : Finset (Euc n) => v ∈ z) h
      simp [hv] at hh⟩
  have hchain : GeometricSimplicialSubdivision.IsStrictFaceChain K (insert s.1 c') := by
    constructor
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact s.2.1
      · exact hc'.1 t ht
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with rfl | ha <;>
        rcases Finset.mem_insert.1 hb with rfl | hb
      · exact (hab rfl).elim
      · right
        exact (Finset.ssubset_of_subset_of_ssubset
          (Finset.mem_powerset.1 (hcs hb)) hproperfacet)
      · left
        exact (Finset.ssubset_of_subset_of_ssubset
          (Finset.mem_powerset.1 (hcs ha)) hproperfacet)
      · exact hc'.2 a ha b hb hab
  have hsnot : s.1 ∉ c' := by
    intro hs
    have := Finset.mem_powerset.1 (hcs hs)
    exact hproperfacet.not_subset this
  refine ⟨hchain, hsnot, ?_⟩
  have hUnion : (insert s.1 c').biUnion (fun u => if u ⊂ s.1 then u else ∅) =
      s.1.erase v := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hx
      rcases Finset.mem_insert.1 hu with rfl | hu
      · have hirr : ¬ s.1 ⊂ s.1 := fun h => h.ne rfl
        rw [if_neg hirr] at hxu
        simp at hxu
      · have husub := Finset.mem_powerset.1 (hcs hu)
        have huprop := Finset.ssubset_of_subset_of_ssubset husub hproperfacet
        simp [huprop] at hxu
        exact husub hxu
    · intro x hx
      apply Finset.mem_biUnion.2
      refine ⟨s.1.erase v, Finset.mem_insert_of_mem htop, ?_⟩
      simp [hproperfacet, hx]
  simp [flagNewVertex, hUnion, Finset.sdiff_erase, hv]

/-- Sign recursion: topping a maximal chain `c'` of `s.erase v` with `s`
multiplies `flagSign` by the deletion sign of `v` and the cone insertion sign
of `barycenter s`.  (New pairs `(t, s)`: `v` precedes the new vertices of the
`(k+1) - idx v` larger vertices; `barycenter s` precedes the `(k+1) - #lt`
larger barycenters; `2(k+1)` cancels.) -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_proper {n k : ℕ}
    (K : GSC n) (s : FaceIndex K (k + 1)) (v : Euc n)
    (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hcs : c' ⊆ (s.1.erase v).powerset) (t : Finset (Euc n)) (ht : t ∈ c') :
    t ⊂ s.1 := by
  refine Finset.ssubset_iff_subset_ne.2
    ⟨(Finset.mem_powerset.1 (hcs ht)).trans (Finset.erase_subset _ _), ?_⟩
  intro heq
  have hsub := Finset.mem_powerset.1 (hcs ht)
  have : v ∈ s.1.erase v := hsub (heq ▸ hv)
  simpa using this

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hcs : c' ⊆ (s.1.erase v).powerset) (t : Finset (Euc n)) (ht : t ∈ c') :
    flagNewVertex o (insert s.1 c') t = flagNewVertex o c' t := by
  classical
  have hp := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_proper
    K s v hv c' hcs t ht
  simp [flagNewVertex, Finset.biUnion_insert, hp.asymm]

/-- First factor of `flagSign`: topping with `s` adds the pairs `(t, s)` with
`v` below the new vertex of `t`.  The new vertices of the maximal chain `c'` are
exactly `s.erase v`, once each, so there are `(k+1) - idx v` such pairs. -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_newVertices
    {n k : ℕ} (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    Set.BijOn (flagNewVertex o c') c' (s.1.erase v) := by
  classical
  let U := s.1.erase v
  have hUcard : U.card = k + 1 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hv, s.2.2]
    omega
  have hcinj : Set.InjOn Finset.card (c' : Set (Finset (Euc n))) :=
    subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_top_aux_card_inj K c' hc'
  have himsub : c'.image Finset.card ⊆ Finset.Icc 1 (k + 1) := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · exact Finset.one_le_card.2
        (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_nonempty
          K c' hc' t ht)
    · simpa [← hUcard] using
        Finset.card_le_card (Finset.mem_powerset.1 (hcs ht))
  have himcard : (c'.image Finset.card).card = k + 1 := by
    rw [Finset.card_image_iff.mpr hcinj, hcard]
  have himeq : c'.image Finset.card = Finset.Icc 1 (k + 1) := by
    apply Finset.eq_of_subset_of_card_le himsub
    rw [Nat.card_Icc, himcard]
    omega
  have hnew : ∀ t ∈ c',
      flagNewVertex o c' t ∈ t ∧
        ∀ u ∈ c', u ⊂ t → flagNewVertex o c' t ∉ u := by
    intro t ht
    have htne :=
      GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_nonempty
        K c' hc' t ht
    let B := c'.biUnion (fun u => if u ⊂ t then u else ∅)
    have hBsub : B ⊆ t := by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hx
      split at hxu
      · exact (Finset.ssubset_iff_subset_ne.1 ‹u ⊂ t›).1 hxu
      · simp at hxu
    have hBcard : B.card = t.card - 1 := by
      by_cases hone : t.card = 1
      · have hBempty : B = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.1
          intro hBn
          obtain ⟨x, hx⟩ := hBn
          obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hx
          split at hxu
          · have hupos : 0 < u.card := Finset.card_pos.2
                (GeometricSimplicialSubdivision.barycentricFaces_affineIndependent_aux_chain_nonempty
                  K c' hc' u hu)
            have hult := Finset.card_lt_card ‹u ⊂ t›
            omega
          · simp at hxu
        simp [hBempty, hone]
      · have htwo : 2 ≤ t.card := by
          have := Finset.card_pos.2 htne
          omega
        have htupper : t.card ≤ k + 1 := by
          simpa [← hUcard] using
            Finset.card_le_card (Finset.mem_powerset.1 (hcs ht))
        have hpredmem : t.card - 1 ∈ c'.image Finset.card := by
          rw [himeq]
          simp only [Finset.mem_Icc]
          omega
        obtain ⟨p, hp, hpcard⟩ := Finset.mem_image.1 hpredmem
        have hpt : p ⊂ t := by
          by_cases hptne : p = t
          · subst p
            omega
          rcases hc'.2 p hp t ht hptne with h | h
          · exact h
          · have := Finset.card_lt_card h
            omega
        have hBeq : B = p := by
          apply Finset.Subset.antisymm
          · intro x hx
            obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hx
            split at hxu
            · by_cases hup : u = p
              · simpa [hup] using hxu
              rcases hc'.2 u hu p hp hup with h | h
              · exact h.subset hxu
              · have hutcard := Finset.card_lt_card ‹u ⊂ t›
                have hpucard := Finset.card_lt_card h
                omega
            · simp at hxu
          · intro x hxp
            apply Finset.mem_biUnion.2
            exact ⟨p, hp, by simp [hpt, hxp]⟩
        rw [hBeq, hpcard]
    have hdiffcard : (t \ B).card = 1 := by
      rw [Finset.card_sdiff_of_subset hBsub, hBcard]
      have := Finset.card_pos.2 htne
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hdiffcard
    have hflag : flagNewVertex o c' t = x := by
      rw [flagNewVertex]
      change ((t \ B).1.sort o.le).getD 0 0 = x
      rw [hx]
      simp
    have hxmem : x ∈ t \ B := by simp [hx]
    refine ⟨hflag.symm ▸ (Finset.mem_sdiff.1 hxmem).1, ?_⟩
    intro u hu hut hxu
    rw [hflag] at hxu
    have hxB : x ∈ B := Finset.mem_biUnion.2 ⟨u, hu, by simp [hut, hxu]⟩
    exact (Finset.mem_sdiff.1 hxmem).2 hxB
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact Finset.mem_powerset.1 (hcs ht) (hnew t ht).1
  · intro a ha b hb hab
    by_contra hne
    rcases hc'.2 a ha b hb hne with h | h
    · exact (hnew b hb).2 a ha h (hab ▸ (hnew a ha).1)
    · exact (hnew a ha).2 b hb h (hab.symm ▸ (hnew b hb).1)
  · intro x hx
    have hmap : Set.MapsTo (flagNewVertex o c') (c' : Set _) (U : Set _) := by
      intro t ht
      exact Finset.mem_powerset.1 (hcs ht) (hnew t ht).1
    have hcardU : (U : Set (Euc n)).ncard = k + 1 := by simp [hUcard]
    have hcardc : (c' : Set (Finset (Euc n))).ncard = k + 1 := by simp [hcard]
    have himcardset : ((flagNewVertex o c') '' (c' : Set _)).ncard = k + 1 := by
      rw [Set.ncard_image_of_injOn]
      · exact hcardc
      · intro a ha b hb hab
        by_contra hne
        rcases hc'.2 a ha b hb hne with h | h
        · exact (hnew b hb).2 a ha h (hab ▸ (hnew a ha).1)
        · exact (hnew a ha).2 b hb h (hab.symm ▸ (hnew b hb).1)
    have heq : (flagNewVertex o c') '' (c' : Set _) = (U : Set _) := by
      apply Set.eq_of_subset_of_ncard_le
      · exact hmap.image_subset
      · rw [himcardset, hcardU]
      · exact Set.toFinite _
    rw [← heq] at hx
    exact hx

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_rank
    {n : ℕ} (o : LinearOrder (Euc n)) (a : Finset (Euc n)) (v : Euc n) (hv : v ∈ a) :
    (a.filter fun x => @LT.lt (Euc n) o.toLT v x).card + (a.sort o.le).idxOf v =
      a.card - 1 := by
  letI : LinearOrder (Euc n) := o
  rw [sort_idxOf_eq_card_lt o a v hv]
  have h := (a.erase v).card_filter_add_card_filter_not
    (fun x => @LT.lt (Euc n) o.toLT v x)
  rw [Finset.card_erase_of_mem hv] at h
  rw [← h]
  congr 1
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxa, hxlt⟩
      exact ⟨⟨hxlt.ne', hxa⟩, hxlt⟩
    · rintro ⟨⟨_, hxa⟩, hxlt⟩
      exact ⟨hxa, hxlt⟩
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxa, hxlt⟩
      exact ⟨⟨hxlt.ne, hxa⟩, hxlt.asymm⟩
    · rintro ⟨⟨hxne, hxa⟩, hnot⟩
      refine ⟨hxa, ?_⟩
      rcases lt_trichotomy x v with hxlt | hxeq | hxgt
      · exact hxlt
      · exact (hxne hxeq).elim
      · exact (hnot hxgt).elim

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_insertCount
    {n k : ℕ} (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    ((insert s.1 c' ×ˢ insert s.1 c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o (insert s.1 c') tu.2)
          (flagNewVertex o (insert s.1 c') tu.1)).card =
      ((c' ×ˢ c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o c' tu.2)
          (flagNewVertex o c' tu.1)).card +
      ((s.1.erase v).filter fun x => @LT.lt (Euc n) o.toLT v x).card := by
  classical
  obtain ⟨_, hsnot, htop⟩ :=
    subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_insert
      o K s v hv c' hc' hcs hcard
  let B := (c' ×ˢ c').filter fun tu =>
    tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o c' tu.2)
      (flagNewVertex o c' tu.1)
  let C := c'.filter fun t =>
    @LT.lt (Euc n) o.toLT v (flagNewVertex o c' t)
  have hdecomp :
      ((insert s.1 c' ×ˢ insert s.1 c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o (insert s.1 c') tu.2)
          (flagNewVertex o (insert s.1 c') tu.1)) = B ∪ (C ×ˢ {s.1}) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, B, C]
    constructor
    · rintro ⟨⟨ha | ha, hb | hb⟩, hab, hlt⟩
      · subst a; subst b; exact (hab.ne rfl).elim
      · subst a
        exact hab.not_subset
          (subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_proper
            K s v hv c' hcs b hb).subset |>.elim
      · right
        subst b
        rw [htop] at hlt
        rw [subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
          o K s v hv c' hcs a ha] at hlt
        exact ⟨⟨ha, hlt⟩, rfl⟩
      · left
        rw [subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
          o K s v hv c' hcs a ha,
          subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
            o K s v hv c' hcs b hb] at hlt
        exact ⟨⟨ha, hb⟩, hab, hlt⟩
    · rintro (⟨⟨ha, hb⟩, hab, hlt⟩ | ⟨⟨ha, hlt⟩, rfl⟩)
      · refine ⟨⟨Or.inr ha, Or.inr hb⟩, hab, ?_⟩
        simpa only [
          subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
            o K s v hv c' hcs a ha,
          subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
            o K s v hv c' hcs b hb] using hlt
      · refine ⟨⟨Or.inr ha, Or.inl rfl⟩,
          subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_proper
            K s v hv c' hcs a ha, ?_⟩
        simpa only [htop,
          subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_newVertex
            o K s v hv c' hcs a ha] using hlt
  rw [hdecomp, Finset.card_union_of_disjoint]
  · simp only [Finset.card_product, Finset.card_singleton, mul_one, B]
    congr 1
    have hbij :=
      subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_newVertices
        o K s v hv c' hc' hcs hcard
    apply Finset.card_bij (fun t _ => flagNewVertex o c' t)
    · intro t ht
      simp only [C, Finset.mem_filter] at ht
      simp only [Finset.mem_filter]
      exact ⟨hbij.1 ht.1, ht.2⟩
    · intro a ha b hb hab
      simp only [C, Finset.mem_filter] at ha hb
      exact hbij.2.1 ha.1 hb.1 hab
    · intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨t, ht, heq⟩ := hbij.2.2 hx.1
      refine ⟨t, ?_, heq⟩
      simp only [C, Finset.mem_filter]
      exact ⟨ht, heq ▸ hx.2⟩
  · rw [Finset.disjoint_left]
    intro ⟨a, b⟩ hab hac
    simp only [B, Finset.mem_filter, Finset.mem_product] at hab
    simp only [Finset.mem_product, Finset.mem_singleton] at hac
    rcases hac with ⟨_, rfl⟩
    exact hsnot hab.1.2

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    ((insert s.1 c' ×ˢ insert s.1 c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o (insert s.1 c') tu.2)
          (flagNewVertex o (insert s.1 c') tu.1)).card + (s.1.sort o.le).idxOf v =
      ((c' ×ˢ c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o c' tu.2)
          (flagNewVertex o c' tu.1)).card + (k + 1) := by
  rw [subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_insertCount
    o K s v hv c' hc' hcs hcard]
  have hr := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first_aux_rank
    o s.1 v hv
  have hc : (s.1.erase v).card = k + 1 := by
    rw [Finset.card_erase_of_mem hv, s.2.2]
    omega
  have hf :
      ((s.1.erase v).filter fun x => @LT.lt (Euc n) o.toLT v x).card =
        (s.1.filter fun x => @LT.lt (Euc n) o.toLT v x).card := by
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    aesop
  rw [hf]
  have hs : s.1.card = k + 2 := s.2.2
  omega

/-- Second factor of `flagSign`: topping with `s` adds the pairs `(t, s)` with
`barycenter s` below `barycenter t`; with the `#lt` barycenters below it (no
ties, by `_aux_bary_injOn` and `_aux_insert`) they account for all `k + 1`
faces of `c'`. -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_second {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    ((insert s.1 c' ×ˢ insert s.1 c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (GeometricSimplicialSubdivision.barycenter tu.2)
          (GeometricSimplicialSubdivision.barycenter tu.1)).card +
        ((c'.image GeometricSimplicialSubdivision.barycenter).filter fun q =>
          @LT.lt (Euc n) o.toLT q (GeometricSimplicialSubdivision.barycenter s.1)).card =
      ((c' ×ˢ c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (GeometricSimplicialSubdivision.barycenter tu.2)
          (GeometricSimplicialSubdivision.barycenter tu.1)).card + (k + 1) := by
  classical
  let b : Finset (Euc n) → Euc n := GeometricSimplicialSubdivision.barycenter
  let P : (Finset (Euc n) × Finset (Euc n)) → Prop := fun tu =>
    tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (b tu.2) (b tu.1)
  have hins := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_insert
    o K s v hv c' hc' hcs hcard
  have hchain := hins.1
  have hsnot := hins.2.1
  have hproper : ∀ t ∈ c', t ⊂ s.1 := by
    intro t ht
    exact subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_proper
      K s v hv c' hcs t ht
  have hbne : ∀ t ∈ c', b t ≠ b s.1 := by
    intro t ht heq
    have hi := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_bary_injOn
      K (insert s.1 c') hchain
    have := hi (Finset.mem_insert_of_mem ht) (Finset.mem_insert_self _ _) heq
    exact hsnot (this ▸ ht)
  have hprod :
      ((insert s.1 c' ×ˢ insert s.1 c').filter P) =
        ((c' ×ˢ c').filter P) ∪
          ((c'.filter fun t => @LT.lt (Euc n) o.toLT (b s.1) (b t)) ×ˢ {s.1}) := by
    ext ⟨a, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨rfl | ha, rfl | hd⟩, had⟩
      · exact (had.1.ne rfl).elim
      · exact (had.1.not_subset (hproper d hd).subset).elim
      · exact Or.inr ⟨⟨ha, had.2⟩, rfl⟩
      · exact Or.inl ⟨⟨ha, hd⟩, had⟩
    · rintro (⟨⟨ha, hd⟩, had⟩ | ⟨⟨ha, had⟩, rfl⟩)
      · exact ⟨⟨Or.inr ha, Or.inr hd⟩, had⟩
      · exact ⟨⟨Or.inr ha, Or.inl rfl⟩, hproper a ha, had⟩
  have hdisj : Disjoint ((c' ×ˢ c').filter P)
      ((c'.filter fun t => @LT.lt (Euc n) o.toLT (b s.1) (b t)) ×ˢ {s.1}) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hy
    have hsecond : x.2 = s.1 := Finset.mem_singleton.1 (Finset.mem_product.1 hy).2
    have hmem : x.2 ∈ c' := (Finset.mem_product.1 (Finset.mem_filter.1 hx).1).2
    exact hsnot (hsecond ▸ hmem)
  have himage :
      ((c'.image b).filter fun q => @LT.lt (Euc n) o.toLT q (b s.1)).card =
        (c'.filter fun t => @LT.lt (Euc n) o.toLT (b t) (b s.1)).card := by
    have heq :
        (c'.image b).filter (fun q => @LT.lt (Euc n) o.toLT q (b s.1)) =
          (c'.filter fun t => @LT.lt (Euc n) o.toLT (b t) (b s.1)).image b := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
        exact ⟨a, ⟨ha, hlt⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, hlt⟩
    have hi : Set.InjOn b
        (↑(c'.filter fun t => @LT.lt (Euc n) o.toLT (b t) (b s.1)) :
          Set (Finset (Euc n))) := by
      intro a ha d hd had
      exact subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_bary_injOn
        K c' hc' (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hd).1 had
    rw [heq, Finset.card_image_iff.mpr hi]
  have hsplit :
      (c'.filter fun t => @LT.lt (Euc n) o.toLT (b s.1) (b t)).card +
        (c'.filter fun t => @LT.lt (Euc n) o.toLT (b t) (b s.1)).card = c'.card := by
    have heq : (c'.filter fun t => @LT.lt (Euc n) o.toLT (b s.1) (b t)) =
        c'.filter (fun t => ¬ @LT.lt (Euc n) o.toLT (b t) (b s.1)) := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, not_lt_of_ge hlt.le⟩
      · rintro ⟨ht, hnot⟩
        exact ⟨ht, lt_of_le_of_ne (le_of_not_gt hnot) (hbne t ht).symm⟩
    rw [heq, add_comm, Finset.card_filter_add_card_filter_not]
  change ((insert s.1 c' ×ˢ insert s.1 c').filter P).card +
      ((c'.image b).filter fun q => @LT.lt (Euc n) o.toLT q (b s.1)).card =
    ((c' ×ˢ c').filter P).card + (k + 1)
  rw [hprod, Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_singleton, mul_one, himage]
  omega

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_pow (A i A' m : ℕ) (h : A + i = A' + m) :
    (-1 : ℚ) ^ A = (-1) ^ A' * (-1) ^ m * (-1) ^ i := by
  have hi : (-1 : ℚ) ^ i * (-1) ^ i = 1 := by
    rw [← mul_pow]; norm_num
  have : (-1 : ℚ) ^ A * (-1) ^ i = (-1) ^ A' * (-1) ^ m := by
    rw [← pow_add, h, pow_add]
  calc (-1 : ℚ) ^ A = (-1) ^ A * ((-1) ^ i * (-1) ^ i) := by rw [hi, mul_one]
    _ = _ := by rw [← mul_assoc, this]

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n) (s : FaceIndex K (k + 1))
    (v : Euc n) (hv : v ∈ s.1) (c' : Finset (Finset (Euc n)))
    (hc' : GeometricSimplicialSubdivision.IsStrictFaceChain K c')
    (hcs : c' ⊆ (s.1.erase v).powerset) (hcard : c'.card = k + 1) :
    flagSign o (insert s.1 c') =
      (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v) *
        (-1 : ℚ) ^ ((c'.image GeometricSimplicialSubdivision.barycenter).filter fun q =>
          @LT.lt (Euc n) o.toLT q (GeometricSimplicialSubdivision.barycenter s.1)).card *
        flagSign o c' := by
  have h1 := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_pow _ _ _ _
    (subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_first o K s v hv c' hc' hcs hcard)
  have h2 := subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_pow _ _ _ _
    (subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sign_aux_second o K s v hv c' hc' hcs hcard)
  have hm : (-1 : ℚ) ^ (k + 1) * (-1) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  unfold flagSign
  rw [h1, h2]
  linear_combination
    ((-1 : ℚ) ^ ((s.1.sort o.le).idxOf v) *
      (-1) ^ ((c'.image GeometricSimplicialSubdivision.barycenter).filter fun q =>
          @LT.lt (Euc n) o.toLT q (GeometricSimplicialSubdivision.barycenter s.1)).card *
      (-1) ^ ((c' ×ˢ c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (flagNewVertex o c' tu.2)
          (flagNewVertex o c' tu.1)).card *
      (-1) ^ ((c' ×ˢ c').filter fun tu =>
        tu.1 ⊂ tu.2 ∧ @LT.lt (Euc n) o.toLT (GeometricSimplicialSubdivision.barycenter tu.2)
          (GeometricSimplicialSubdivision.barycenter tu.1)).card) * hm

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_sd_coeff {n j : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (sd : ∀ i, FaceModuleCat K i ⟶ FaceModuleCat (barycentricStep K) i)
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (r : FaceIndex K j) (w : FaceIndex (barycentricStep K) j) : by
    classical
    exact sd j (Finsupp.single r 1) w =
      ∑ c ∈ r.1.powerset.powerset,
        if GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
            w.1 = c.image GeometricSimplicialSubdivision.barycenter then
          flagSign o c else 0 := by
  classical
  obtain ⟨z, hz, hcoeff⟩ := hsd j r
  rw [hz, hcoeff]

/-- Coefficient of a cone at a face containing the apex: only the face with
the apex erased contributes. -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_mem {n k : ℕ} (o : LinearOrder (Euc n)) (K' : GSC n)
    (b : Euc n) (x : FaceModuleCat K' k) (U : FaceIndex K' (k + 1)) (w : FaceIndex K' k)
    (hb : b ∈ U.1) (hw : w.1 = U.1.erase b) :
    subdivisionCone o K' b k x U =
      (-1 : ℚ) ^ (w.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card * x w := by
  sorry

/-- A cone vanishes on faces not containing the apex. -/
-- BEGIN SEAT AREA
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_cone_apply_not_mem {n k : ℕ} (o : LinearOrder (Euc n)) (K' : GSC n)
    (b : Euc n) (x : FaceModuleCat K' k) (U : FaceIndex K' (k + 1)) (hb : b ∉ U.1) :
    subdivisionCone o K' b k x U = 0 := by
  classical
  simp only [subdivisionCone]
  change (Finsupp.linearCombination ℚ (fun u : FaceIndex K' k =>
    if hu : b ∉ u.1 ∧ insert b u.1 ∈ K'.faces then
      Finsupp.single
        (⟨insert b u.1, hu.2,
          by rw [Finset.card_insert_of_notMem hu.1, u.2.2]⟩ : FaceIndex K' (k + 1))
        ((-1 : ℚ) ^ (u.1.filter fun q => @LT.lt (Euc n) o.toLT q b).card)
    else 0)) x U = 0
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum_apply, Finsupp.sum]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro u hu
  split_ifs with hcone
  · simp only [Finsupp.coe_smul, Pi.smul_apply]
    rw [Finsupp.single_apply]
    split_ifs with heq
    · exfalso
      apply hb
      rw [← congrArg Subtype.val heq]
      exact Finset.mem_insert_self b u.1
    · simp
  · rw [smul_zero]
    rfl
-- END SEAT AREA

/-- Reindexing: strict chains of `s` with barycenter image `u` (necessarily
maximal, hence topped by `s`) correspond to pairs `(v, c')` with `c'` a chain of
`s.erase v` and `c = insert s c'` (`_aux_top`, `_aux_insert`, `_aux_bary_injOn`). -/
lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff_aux_reindex {n k : ℕ} (o : LinearOrder (Euc n)) (K : GSC n)
    (s : FaceIndex K (k + 1)) (u : Finset (Euc n)) (hu : u.card = k + 2) : by
    classical
    exact
    (∑ c ∈ s.1.powerset.powerset,
      if GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
          u = c.image GeometricSimplicialSubdivision.barycenter then
        flagSign o c else 0) =
      ∑ v ∈ s.1.attach, ∑ c' ∈ (s.1.erase v.1).powerset.powerset,
        if GeometricSimplicialSubdivision.IsStrictFaceChain K c' ∧
            u = insert (GeometricSimplicialSubdivision.barycenter s.1)
              (c'.image GeometricSimplicialSubdivision.barycenter) then
          flagSign o (insert s.1 c') else 0 := by
  sorry

lemma subdivisionChainMap_commutes_aux_cone_formula_aux_coeff {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (sd : ∀ j, FaceModuleCat K j ⟶ FaceModuleCat (barycentricStep K) j)
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (s : FaceIndex K (k + 1)) (u : FaceIndex (barycentricStep K) (k + 1)) : by
    classical
    exact
    (∑ c ∈ s.1.powerset.powerset,
      if GeometricSimplicialSubdivision.IsStrictFaceChain K c ∧
          u.1 = c.image GeometricSimplicialSubdivision.barycenter then
        flagSign o c else 0) =
      (∑ v ∈ s.1.attach,
        (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1) •
          subdivisionCone o (barycentricStep K)
            (GeometricSimplicialSubdivision.barycenter s.1) k
            (sd k (Finsupp.single
              (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1))) u := by
  sorry

/-- Recursive cone formula for the canonical flag subdivision of a non-vertex
face. -/
theorem subdivisionChainMap_commutes_aux_cone_formula {n k : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (sd : ∀ j, FaceModuleCat K j ⟶ FaceModuleCat (barycentricStep K) j)
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (s : FaceIndex K (k + 1)) :
    sd (k + 1) (Finsupp.single s 1) =
      ∑ v ∈ s.1.attach,
        (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1) •
          subdivisionCone o (barycentricStep K)
            (GeometricSimplicialSubdivision.barycenter s.1) k
            (sd k (Finsupp.single
              (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1)) := by
  classical
  ext u
  obtain ⟨z, hz, hcoeff⟩ := hsd (k + 1) s
  rw [hz, hcoeff]
  exact subdivisionChainMap_commutes_aux_cone_formula_aux_coeff o K sd hsd s u

/-- Formal induction assembling the cone formula and cone-boundary identities.
The sign-bearing geometric facts are supplied explicitly so this lemma is
independent of their proofs. -/
lemma subdivisionChainMap_commutes_aux_induction_aux_augmentation {n : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat (barycentricStep K) k)
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (r : FaceIndex K 0) :
    (sd 0 (Finsupp.single r 1)).sum (fun _ a => a) = 1 := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp r.2.2
  obtain ⟨z, hz, hcoeff⟩ := hsd 0 r
  rw [hz]
  have hrface : ({x} : Finset (Euc n)) ∈ K.faces := by simpa [hx] using r.2.1
  let u : FaceIndex (barycentricStep K) 0 :=
    ⟨{GeometricSimplicialSubdivision.barycenter ({x} : Finset (Euc n))}, by
      constructor
      · refine ⟨{{x}}, ?_, by simp⟩
        constructor
        · simpa using hrface
        · simp
      · simp,
      by simp⟩
  have hp₁ : ({x} : Finset (Euc n)).powerset = {∅, {x}} := by
    ext a
    simp [Finset.subset_singleton_iff]
  have hp₂ : ({∅, {x}} : Finset (Finset (Euc n))).powerset =
      {∅, {∅}, {{x}}, {∅, {x}}} := by
    ext c
    simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hempty : (∅ : Finset (Euc n)) ∉ K.faces := by
    intro h
    exact (K.nonempty_of_mem_faces h).ne_empty rfl
  have hself : ¬ ({x} : Finset (Euc n)) ⊂ {x} := by
    intro h
    exact h.ne rfl
  have hzsingle : z = Finsupp.single u 1 := by
    ext v
    have hvempty : v.1 ≠ ∅ := by
      intro h
      have := v.2.2
      simp [h] at this
    rw [hcoeff]
    rw [hx, hp₁, hp₂]
    rw [Finset.sum_eq_single {{x}}]
    · by_cases hv : v.1 = u.1
      · have : v = u := Subtype.ext hv
        subst v
        simp [u, hrface, GeometricSimplicialSubdivision.IsStrictFaceChain,
          flagSign, flagNewVertex, hself, Finset.filter_singleton]
      · have hv' : v ≠ u := fun h => hv (congrArg Subtype.val h)
        simp [u, hv, hv', hrface, GeometricSimplicialSubdivision.IsStrictFaceChain,
          flagSign, flagNewVertex, hself, Finset.filter_singleton]
    · intro c hc hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try contradiction
      all_goals simp [hvempty, hempty,
        GeometricSimplicialSubdivision.IsStrictFaceChain]
    · simp
  rw [hzsingle]
  simp

lemma subdivisionChainMap_commutes_aux_induction_aux_edge_sign_sum {n : ℕ}
    (o : LinearOrder (Euc n)) (s : Finset (Euc n)) (hs : s.card = 2) :
    ∑ v ∈ s.attach, (-1 : ℚ) ^ ((s.sort o.le).idxOf v.1) = 0 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  have ha : a ∈ ({a, b} : Finset (Euc n)) := by simp
  have hb : b ∈ ({a, b} : Finset (Euc n)) := by simp
  have hatt : ({a, b} : Finset (Euc n)).attach = {⟨a, ha⟩, ⟨b, hb⟩} := by
    ext x
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro _
      rcases Finset.mem_insert.mp x.2 with hxa | hxb
      · exact Or.inl (Subtype.ext hxa)
      · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hxb))
    · intro _
      trivial
  rw [hatt]
  rcases @lt_or_gt_of_ne (Euc n) o a b hab with hablt | hbalt
  · have hsort : ({a, b} : Finset (Euc n)).sort o.le = [a, b] := by
      simpa using Finset.sort_insert (s := {b}) (a := a) o.le
        (fun x hx => by
          rw [Finset.mem_singleton.mp hx]
          exact le_of_lt hablt)
        (by simpa only [Finset.mem_singleton] using hab)
    simp [hsort, hab, hab.symm]
  · have hsort : ({a, b} : Finset (Euc n)).sort o.le = [b, a] := by
      rw [Finset.pair_comm]
      simpa using Finset.sort_insert (s := {a}) (a := b) o.le
        (fun x hx => by
          rw [Finset.mem_singleton.mp hx]
          exact le_of_lt hbalt)
        (by simpa only [Finset.mem_singleton] using hab.symm)
    simp [hsort, hab, hab.symm]

/- Note (claude-14): lemma-3's 99-line assembly attempt (does not compile; the
positive-degree residual must be handled as ONE summed expression — apply the
induction hypothesis inside the sum, then linearity and `dK ≫ dK = 0`; it cannot
be killed termwise) is saved at
~/notes/packets/lemmas/partials/subdivisionChainMap_commutes_aux_induction.attempt-lemma3.lean -/
theorem subdivisionChainMap_commutes_aux_induction {n : ℕ}
    (o : LinearOrder (Euc n)) (K : GSC n)
    (dK : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat (barycentricStep K) (k + 1) ⟶
      FaceModuleCat (barycentricStep K) k)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat (barycentricStep K) k)
    (hdK : IsSignedDeletion o K dK)
    (hdK' : IsSignedDeletion o (barycentricStep K) dK')
    (hsd : IsSubdivisionChainMap o K (barycentricStep K) sd)
    (hCB : ∀ k (b : Euc n) (x : FaceModule (barycentricStep K) (k + 1)),
      ConeAdmissible (barycentricStep K) b x →
      dK' (k + 1) (subdivisionCone o (barycentricStep K) b (k + 1) x) =
        x - subdivisionCone o (barycentricStep K) b k (dK' k x))
    (hCB0 : ∀ (b : Euc n) (hb : ({b} : Finset (Euc n)) ∈ (barycentricStep K).faces)
        (x : FaceModule (barycentricStep K) 0),
      ConeAdmissible (barycentricStep K) b x →
      dK' 0 (subdivisionCone o (barycentricStep K) b 0 x) =
        x - (x.sum fun _ a => a) •
          Finsupp.single (⟨{b}, hb, by simp⟩ : FaceIndex (barycentricStep K) 0) 1)
    (hCF : ∀ k (s : FaceIndex K (k + 1)),
      sd (k + 1) (Finsupp.single s 1) =
        ∑ v ∈ s.1.attach,
          (-1 : ℚ) ^ ((s.1.sort o.le).idxOf v.1) •
            subdivisionCone o (barycentricStep K)
              (GeometricSimplicialSubdivision.barycenter s.1) k
              (sd k (Finsupp.single
                (signedDeletion_sq_zero_aux_generator_aux_erase K s v.1 v.2) 1)))
    (hAdm : ∀ k (s : FaceIndex K (k + 1)) (v : Euc n) (hv : v ∈ s.1),
      ConeAdmissible (barycentricStep K)
        (GeometricSimplicialSubdivision.barycenter s.1)
        (sd k (Finsupp.single
          (signedDeletion_sq_zero_aux_generator_aux_erase K s v hv) 1))) :
    ∀ k, sd (k + 1) ≫ dK' k = dK k ≫ sd k := by
  sorry

theorem subdivisionChainMap_commutes {n : ℕ} (o : LinearOrder (Euc n))
    (K K' : GSC n) (dK : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (dK' : ∀ k, FaceModuleCat K' (k+1) ⟶ FaceModuleCat K' k)
    (sd : ∀ k, FaceModuleCat K k ⟶ FaceModuleCat K' k)
    (hdK : IsSignedDeletion o K dK) (hdK' : IsSignedDeletion o K' dK')
    (hK' : K' = barycentricStep K)
    (hsd : IsSubdivisionChainMap o K K' sd) :
    ∀ k, sd (k+1) ≫ dK' k = dK k ≫ sd k := by
  subst K'
  apply subdivisionChainMap_commutes_aux_induction o K dK dK' sd hdK hdK' hsd
  · intro k
    exact subdivisionChainMap_commutes_aux_cone_boundary o (barycentricStep K) dK' hdK'
  · exact subdivisionChainMap_commutes_aux_cone_boundary_zero o (barycentricStep K) dK' hdK'
  · intro k
    exact subdivisionChainMap_commutes_aux_cone_formula o K sd hsd
  · intro k
    exact subdivisionChainMap_commutes_aux_facet_admissible o K sd hsd

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
