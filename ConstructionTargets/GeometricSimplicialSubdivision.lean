import Mathlib

/-! # Geometric barycentric subdivision and simplicial approximation interfaces -/

open Set

noncomputable section
namespace ConstructionTargets.GeometricSimplicialSubdivision

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The barycenter of a nonempty finite set (the empty value is harmless). -/
def barycenter {n : ℕ} (s : Finset (Euc n)) : Euc n :=
  s.centerMass (fun _ => (1 : ℝ)) id

/-- A finite collection of old faces, linearly ordered by strict inclusion. -/
def IsStrictFaceChain {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) : Prop :=
  (∀ s ∈ c, s ∈ K.faces) ∧ ∀ s ∈ c, ∀ t ∈ c, s ≠ t → s ⊂ t ∨ t ⊂ s

/-- Vertex sets prescribed for the barycentric subdivision. -/
def barycentricFaces {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    Set (Finset (Euc n)) :=
  {u | ∃ c : Finset (Finset (Euc n)), IsStrictFaceChain K c ∧
      u = c.image barycenter}

lemma barycentricFaces_affineIndependent_aux_barycenter_formula {n : ℕ}
    (s : Finset (Euc n)) :
    barycenter s = (s.card : ℝ)⁻¹ • ∑ x ∈ s, x := by
  simp [barycenter, Finset.centerMass]

lemma barycentricFaces_affineIndependent_aux_chain_nonempty {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c) :
    ∀ s ∈ c, s.Nonempty := by
  intro s hs
  exact K.nonempty_of_mem_faces (hc.1 s hs)

lemma barycentricFaces_affineIndependent_aux_chain_subset_of_card_le {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    {s t : Finset (Euc n)} (hs : s ∈ c) (ht : t ∈ c) (hst : s.card ≤ t.card) :
    s ⊆ t := by
  by_cases h : s = t
  · simpa [h]
  rcases hc.2 s hs t ht h with hsub | hsub
  · exact hsub.subset
  · exact False.elim (Nat.not_lt_of_ge hst (Finset.card_lt_card hsub))

/-- (C1) For faces `s ⊊ t` of `K`, the barycenter of `t` is not in the affine
span of `s`: its barycentric weight on a vertex of `t \ s` is positive, and the
vertices of `t` are affinely independent (`K.indep`). -/
theorem barycentricFaces_affineIndependent_aux_chain_not_mem_span {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) {s t : Finset (Euc n)}
    (ht : t ∈ K.faces) (hst : s ⊂ t) :
    barycenter t ∉ affineSpan ℝ (s : Set (Euc n)) := by
  classical
  obtain ⟨v, hvt, hvs⟩ := Finset.exists_of_ssubset hst
  intro hm
  let i : t := ⟨v, hvt⟩
  letI : Nonempty t := ⟨i⟩
  let u : Set t := {x | (x : Euc n) ∈ s}
  have himage : ((fun x : t => (x : Euc n)) '' u) = (s : Set (Euc n)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hst.subset hx⟩, hx, rfl⟩
  have hnonempty : t.Nonempty := K.nonempty_of_mem_faces ht
  have hattach : t.attach.Nonempty := by simp [hnonempty]
  have hsum : ∑ x ∈ t.attach, t.attach.centroidWeights ℝ x = 1 :=
    t.attach.sum_centroidWeights_eq_one_of_nonempty ℝ hattach
  have hbary : barycenter t = t.attach.affineCombination ℝ
      (fun x : t => (x : Euc n)) (t.attach.centroidWeights ℝ) := by
    rw [barycentricFaces_affineIndependent_aux_barycenter_formula]
    rw [t.attach.affineCombination_eq_linear_combination _ _ hsum]
    simp only [Finset.centroidWeights_apply, Finset.card_attach, Finset.sum_attach]
    rw [Finset.smul_sum]
  have hz := (K.indep ht).eq_zero_of_affineCombination_mem_affineSpan
    hsum (s := u) (i := i) (by simpa [← himage, ← hbary] using hm)
    (by simp [i]) (by simpa [u, i] using hvs)
  have hcard : (t.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hnonempty)
  exact hcard (inv_eq_zero.mp (by simpa using hz))

/-- (C2) The barycenter of a nonempty `s ⊆ t` lies in the affine span of `t`. -/
theorem barycentricFaces_affineIndependent_aux_chain_mem_span {n : ℕ}
    {s t : Finset (Euc n)} (hs : s.Nonempty) (hst : s ⊆ t) :
    barycenter s ∈ affineSpan ℝ (t : Set (Euc n)) := by
  have hb : barycenter s ∈ convexHull ℝ (s : Set (Euc n)) := by
    apply Finset.centerMass_id_mem_convexHull
    · intro x hx
      positivity
    · simpa using (Finset.card_pos.mpr hs : 0 < s.card)
  exact affineSpan_mono ℝ (by simpa using hst) (convexHull_subset_affineSpan _ hb)

/-- (C3) Induction on the chain: remove its largest face `t`; the remaining
barycenters are independent (induction) and lie in the affine span of the next
largest face `s ⊊ t` (C2), which does not contain `barycenter t` (C1);
`AffineIndependent` is preserved by adjoining a point outside the span. -/
theorem barycentricFaces_affineIndependent_aux_chain_induction {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hC1 : ∀ {s t : Finset (Euc n)}, t ∈ K.faces → s ⊂ t →
      barycenter t ∉ affineSpan ℝ (s : Set (Euc n)))
    (hC2 : ∀ {s t : Finset (Euc n)}, s.Nonempty → s ⊆ t →
      barycenter s ∈ affineSpan ℝ (t : Set (Euc n)))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c) :
    AffineIndependent ℝ (fun s : c => barycenter (s : Finset (Euc n))) := by
  classical
  refine Finset.induction_on_max_value Finset.card c ?_ ?_ hc
  · intro
    exact affineIndependent_of_subsingleton ℝ _
  · intro a c ha hmax ih hc
    all_goals
      have hca : a ∈ K.faces := hc.1 a (Finset.mem_insert_self a c)
      have hcc : IsStrictFaceChain K c := by
        refine ⟨fun s hs => hc.1 s (Finset.mem_insert_of_mem hs), ?_⟩
        intro s hs t ht hst
        exact hc.2 s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht) hst
      have hind : AffineIndependent ℝ
          (fun s : c => barycenter (s : Finset (Euc n))) := ih hcc
      by_cases hce : c = ∅
      · subst c
        rw [Finset.insert_empty]
        exact affineIndependent_of_subsingleton ℝ _
      · have hcne : c.Nonempty := Finset.nonempty_iff_ne_empty.mpr hce
        obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image c Finset.card hcne
        let i : (insert a c : Finset (Finset (Euc n))) :=
          ⟨a, Finset.mem_insert_self a c⟩
        apply AffineIndependent.affineIndependent_of_notMem_span (i := i)
        · let e : {x : (insert a c : Finset (Finset (Euc n))) // x ≠ i} ≃ c :=
            { toFun := fun x => ⟨x.1.1, by
                have hx := x.1.2
                simp only [Finset.mem_insert] at hx
                rcases hx with hxa | hxc
                · exfalso
                  apply x.2
                  apply Subtype.ext
                  exact hxa
                · exact hxc⟩
              invFun := fun x => ⟨⟨x.1, Finset.mem_insert_of_mem x.2⟩, by
                intro h
                have := congrArg Subtype.val h
                change x.1 = a at this
                exact ha (this ▸ x.2)⟩
              left_inv := by intro x; exact Subtype.ext (Subtype.ext rfl)
              right_inv := by intro x; exact Subtype.ext rfl }
          convert (affineIndependent_equiv e).2 hind using 1
        · intro hmem
          have hba : b ⊂ a := by
            have hba' := hc.2 b (Finset.mem_insert_of_mem hb) a
              (Finset.mem_insert_self a c) (by exact fun h => ha (h ▸ hb))
            rcases hba' with hba' | hab'
            · exact hba'
            · exact False.elim (Nat.not_lt_of_ge (hmax b hb) (Finset.card_lt_card hab'))
          apply hC1 hca hba
          refine (affineSpan_le.2 ?_) hmem
          rintro y ⟨x, hx, rfl⟩
          have hxc : x.1 ∈ c := by
            have hxin := x.2
            simp only [Finset.mem_insert] at hxin
            rcases hxin with hxa | hxc
            · exfalso
              apply hx
              apply Subtype.ext
              exact hxa
            · exact hxc
          apply hC2 (barycentricFaces_affineIndependent_aux_chain_nonempty K c hcc x.1 hxc)
          exact barycentricFaces_affineIndependent_aux_chain_subset_of_card_le K c hcc hxc hb
            (hbmax x.1 hxc)

/-- (A1) Along a strict chain `s₀ ⊂ s₁ ⊂ ⋯` of faces of `K`, the barycenters are
affinely independent: all lie in the top face, whose vertices are independent
(`K.indep`), and `barycenter sᵢ` has positive weight on a vertex of
`sᵢ \ sᵢ₋₁` that every earlier barycenter lacks (triangular coordinates). -/
theorem barycentricFaces_affineIndependent_aux_chain {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c) :
    AffineIndependent ℝ (fun s : c => barycenter (s : Finset (Euc n))) := by
  exact barycentricFaces_affineIndependent_aux_chain_induction K
    (fun ht hst => barycentricFaces_affineIndependent_aux_chain_not_mem_span K ht hst)
    (fun hs hst => barycentricFaces_affineIndependent_aux_chain_mem_span hs hst) c hc

/-- (A2) Transfer from the chain-indexed family to the image finset
(an affinely independent family is injective; `AffineIndependent.range`). -/
theorem barycentricFaces_affineIndependent_aux_transfer {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hchain : ∀ c : Finset (Finset (Euc n)), IsStrictFaceChain K c →
      AffineIndependent ℝ (fun s : c => barycenter (s : Finset (Euc n)))) :
    ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n) := by
  rintro u ⟨c, hc, rfl⟩
  have heq : Set.range (fun s : c => barycenter (s : Finset (Euc n))) =
      (c.image barycenter : Set (Euc n)) := by
    ext x
    simp
  change AffineIndependent ℝ
    (fun x : (c.image barycenter : Set (Euc n)) => (x : Euc n))
  rw [← heq]
  exact (hchain c hc).range

/-- Barycenters of a strict chain of nonempty faces are affinely independent. -/
theorem barycentricFaces_affineIndependent {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n) := by
  exact barycentricFaces_affineIndependent_aux_transfer K
    (fun c hc => barycentricFaces_affineIndependent_aux_chain K c hc)

/-- Subsets of barycenter sets of strict chains are again such sets. -/
theorem barycentricFaces_isLowerSet {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    IsLowerSet (barycentricFaces K) := by
  intro u v hv hu
  obtain ⟨c, hc, rfl⟩ := hu
  refine ⟨c.filter (fun s ↦ barycenter s ∈ v), ?_, ?_⟩
  · constructor
    · intro s hs
      exact hc.1 s (Finset.mem_filter.mp hs).1
    · intro s hs t ht hst
      exact hc.2 s (Finset.mem_filter.mp hs).1 t
        (Finset.mem_filter.mp ht).1 hst
  · ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      have hx' : x ∈ c.image barycenter := hv hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx'
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hx⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact (Finset.mem_filter.mp hs).2

/-- (I1) A point of the hull of finitely many barycenters is a positive-weight
combination of the barycenters of some sub-collection (drop the zero weights;
if two faces share a barycenter keep one). -/
theorem barycentricFaces_inter_subset_aux_positive_subchain {n : ℕ}
    (c : Finset (Finset (Euc n))) (x : Euc n)
    (hx : x ∈ convexHull ℝ ((c.image barycenter : Finset (Euc n)) : Set (Euc n))) :
    ∃ c₀ ⊆ c, ∃ w : Finset (Euc n) → ℝ, (∀ s ∈ c₀, 0 < w s) ∧
      ∑ s ∈ c₀, w s = 1 ∧ ∑ s ∈ c₀, w s • barycenter s = x := by
  classical
  obtain ⟨a, ha0, ha1, hax⟩ := (Finset.mem_convexHull').mp hx
  let d := (c.image barycenter).filter (fun y ↦ 0 < a y)
  have hdmem : ∀ y ∈ d, y ∈ c.image barycenter := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  let r : (y : Euc n) → y ∈ d → Finset (Euc n) := fun y hy ↦
    Classical.choose (Finset.mem_image.mp (hdmem y hy))
  have hr_mem (y : Euc n) (hy : y ∈ d) : r y hy ∈ c := by
    exact (Classical.choose_spec (Finset.mem_image.mp (hdmem y hy))).1
  have hr_eq (y : Euc n) (hy : y ∈ d) : barycenter (r y hy) = y := by
    exact (Classical.choose_spec (Finset.mem_image.mp (hdmem y hy))).2
  let c₀ := d.attach.image (fun y ↦ r y.1 y.2)
  refine ⟨c₀, ?_, fun s ↦ a (barycenter s), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
    exact hr_mem y.1 y.2
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
    change 0 < a (barycenter (r y.1 y.2))
    rw [hr_eq y.1 y.2]
    exact (Finset.mem_filter.mp y.2).2
  · rw [Finset.sum_image]
    · simp_rw [hr_eq]
      rw [Finset.sum_attach]
      calc
        ∑ y ∈ d, a y = ∑ y ∈ c.image barycenter, a y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hyd
          have hnpos : ¬ 0 < a y := by
            intro hp
            exact hyd (Finset.mem_filter.mpr ⟨hy, hp⟩)
          exact le_antisymm (not_lt.mp hnpos) (ha0 y hy)
        _ = 1 := ha1
    · intro y hy z hz heq
      apply Subtype.ext
      simpa only [hr_eq] using congrArg barycenter heq
  · rw [Finset.sum_image]
    · simp_rw [hr_eq]
      change ∑ y ∈ d.attach, a y.1 • y.1 = x
      calc
        ∑ y ∈ d.attach, a y.1 • y.1 = ∑ y ∈ d, a y • y :=
          Finset.sum_attach d (fun y ↦ a y • y)
        ∑ y ∈ d, a y • y = ∑ y ∈ c.image barycenter, a y • y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hyd
          have hnpos : ¬ 0 < a y := by
            intro hp
            exact hyd (Finset.mem_filter.mpr ⟨hy, hp⟩)
          have hz : a y = 0 := le_antisymm (not_lt.mp hnpos) (ha0 y hy)
          simp [hz]
        _ = x := hax
    · intro y hy z hz heq
      apply Subtype.ext
      simpa only [hr_eq] using congrArg barycenter heq

lemma barycentricFaces_inter_subset_aux_chain_unique_aux_nonempty
    {n : ℕ} (c : Finset (Finset (Euc n))) (w : Finset (Euc n) → ℝ)
    (hs : ∑ s ∈ c, w s = 1) : c.Nonempty := by
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty.mp hc] at hs
  simp at hs

lemma barycentricFaces_inter_subset_aux_chain_unique_aux_top
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    (hne : c.Nonempty) :
    ∃ t ∈ c, ∀ s ∈ c, s ⊆ t := by
  classical
  obtain ⟨t, ht, hcard⟩ := Finset.exists_max_image c Finset.card hne
  refine ⟨t, ht, ?_⟩
  intro s hs
  by_cases hst : s = t
  · simpa [hst]
  · rcases hc.2 s hs t ht hst with hsub | hsup
    · exact hsub.subset
    · exact False.elim ((Nat.not_lt_of_ge (hcard s hs)) (Finset.card_lt_card hsup))

/-- (U2) A positive-weight combination of the barycenters of a strict chain lies
in the closed hull of the chain's top face `t` and in no facet `t.erase v`
(every vertex of `t` gets positive barycentric weight from `barycenter t`). -/
theorem barycentricFaces_inter_subset_aux_chain_unique_aux_relint {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    (t : Finset (Euc n)) (ht : t ∈ c) (htop : ∀ s ∈ c, s ⊆ t)
    (w : Finset (Euc n) → ℝ) (hw : ∀ s ∈ c, 0 < w s) (hs : ∑ s ∈ c, w s = 1) :
    ∑ s ∈ c, w s • barycenter s ∈ convexHull ℝ (t : Set (Euc n)) ∧
      ∀ v ∈ t, ∑ s ∈ c, w s • barycenter s ∉
        convexHull ℝ ((t.erase v : Finset (Euc n)) : Set (Euc n)) := by
  classical
  let a : Euc n → ℝ := fun v =>
    ∑ s ∈ c, if v ∈ s then w s / (s.card : ℝ) else 0
  have hne : ∀ s ∈ c, s.Nonempty :=
    barycentricFaces_affineIndependent_aux_chain_nonempty K c hc
  have hcard : ∀ s ∈ c, (s.card : ℝ) ≠ 0 := by
    intro s hs
    exact_mod_cast (Finset.card_ne_zero.mpr (hne s hs))
  have ha0 : ∀ v ∈ t, 0 ≤ a v := by
    intro v hv
    apply Finset.sum_nonneg
    intro s hs
    split_ifs
    · exact div_nonneg (le_of_lt (hw s hs)) (Nat.cast_nonneg _)
    · exact le_rfl
  have hasum : ∑ v ∈ t, a v = 1 := by
    simp only [a, Finset.sum_ite_irrel, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    calc
      ∑ s ∈ c, ∑ v ∈ t, (if v ∈ s then w s / (s.card : ℝ) else 0) =
          ∑ s ∈ c, ∑ v ∈ s, w s / (s.card : ℝ) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [← Finset.sum_subset (htop s hs)]
            · simp
            · intro v hvt hvs
              simp [hvs]
      _ = ∑ s ∈ c, w s := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp [hcard s hs]
      _ = 1 := hs
  have haeq : ∑ v ∈ t, a v • v = ∑ s ∈ c, w s • barycenter s := by
    simp only [a]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    calc
      ∑ s ∈ c, ∑ v ∈ t, (if v ∈ s then w s / (s.card : ℝ) else 0) • v =
          ∑ s ∈ c, ∑ v ∈ s, (w s / (s.card : ℝ)) • v := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [← Finset.sum_subset (htop s hs)]
            · simp
            · intro v hvt hvs
              simp [hvs]
      _ = ∑ s ∈ c, w s • barycenter s := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [barycentricFaces_affineIndependent_aux_barycenter_formula,
              smul_smul, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            rw [div_eq_mul_inv, mul_comm]
  constructor
  · rw [← haeq]
    exact Finset.mem_convexHull'.2 ⟨a, ha0, hasum, rfl⟩
  · intro v hv hmem
    have hspan : (∑ s ∈ c, w s • barycenter s) ∈
        affineSpan ℝ ((fun x : t => (x : Euc n)) '' {x | (x : Euc n) ∈ t.erase v}) := by
      have hsub : ((t.erase v : Finset (Euc n)) : Set (Euc n)) =
          (fun x : t => (x : Euc n)) '' {x | (x : Euc n) ∈ t.erase v} := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, (Finset.erase_subset v t) hx⟩, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact hx
      rw [← hsub]
      exact convexHull_subset_affineSpan _ hmem
    have hatt : ∑ i ∈ t.attach, a (i : Euc n) • (i : Euc n) =
        ∑ x ∈ t, a x • x := by
      refine Finset.sum_bij (fun i _ => (i : Euc n)) ?_ ?_ ?_ ?_
      · intro i hi
        exact i.property
      · intro i hi j hj hij
        exact Subtype.ext hij
      · intro x hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
      · intro i hi
        rfl
    have hz := (K.indep (hc.1 t ht)).eq_zero_of_affineCombination_mem_affineSpan
      (fs := t.attach) (w := fun x : t => a x) (s := {x | (x : Euc n) ∈ t.erase v})
      (by simpa only [Finset.sum_attach] using hasum) (by
        rw [Finset.affineCombination_eq_linear_combination]
        · rw [hatt, haeq]
          exact hspan
        · simpa only [Finset.sum_attach] using hasum) (i := ⟨v, hv⟩) (by simp) (by simp)
    have hpos : 0 < a v := by
      have hterm : 0 < w t / (t.card : ℝ) :=
        div_pos (hw t ht) (by exact_mod_cast (Finset.card_pos.mpr (hne t ht)))
      have hle : w t / (t.card : ℝ) ≤ a v := by
        change w t / (t.card : ℝ) ≤
          ∑ s ∈ c, (if v ∈ s then w s / (s.card : ℝ) else 0)
        simpa only [if_pos hv] using (Finset.single_le_sum (f := fun s =>
            if v ∈ s then w s / (s.card : ℝ) else 0) (fun s hs => by
          change 0 ≤ (if v ∈ s then w s / (s.card : ℝ) else 0)
          split_ifs
          · exact div_nonneg (le_of_lt (hw s hs)) (Nat.cast_nonneg _)
          · exact le_rfl) ht)
      exact lt_of_lt_of_le hterm hle
    exact (ne_of_gt hpos) hz

/-- (U1) Two faces of `K` whose relative interiors share a point are equal
(intersection axiom: the point lies in the hull of `t₀ ∩ t₁`, a face of both,
which must then be all of each). -/
theorem barycentricFaces_inter_subset_aux_chain_unique_aux_carrier {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) {t₀ t₁ : Finset (Euc n)}
    (ht₀ : t₀ ∈ K.faces) (ht₁ : t₁ ∈ K.faces) (x : Euc n)
    (hx₀ : x ∈ convexHull ℝ (t₀ : Set (Euc n)))
    (hx₁ : x ∈ convexHull ℝ (t₁ : Set (Euc n)))
    (hi₀ : ∀ v ∈ t₀, x ∉ convexHull ℝ ((t₀.erase v : Finset (Euc n)) : Set (Euc n)))
    (hi₁ : ∀ v ∈ t₁, x ∉ convexHull ℝ ((t₁.erase v : Finset (Euc n)) : Set (Euc n))) :
    t₀ = t₁ := by
  apply Finset.Subset.antisymm
  · intro v hv₀
    by_contra hv₁
    apply hi₀ v hv₀
    have hx : x ∈ convexHull ℝ ((t₀ ∩ t₁ : Finset (Euc n)) : Set (Euc n)) := by
      simpa only [Finset.coe_inter] using
        (K.convexHull_inter_convexHull ht₀ ht₁ ▸ ⟨hx₀, hx₁⟩)
    exact convexHull_mono (by
      intro y hy
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hy.1, fun hyv ↦ hv₁ (hyv ▸ hy.2)⟩) hx
  · intro v hv₁
    by_contra hv₀
    apply hi₁ v hv₁
    have hx : x ∈ convexHull ℝ ((t₀ ∩ t₁ : Finset (Euc n)) : Set (Euc n)) := by
      simpa only [Finset.coe_inter] using
        (K.convexHull_inter_convexHull ht₀ ht₁ ▸ ⟨hx₀, hx₁⟩)
    exact convexHull_mono (by
      intro y hy
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hy.2, fun hyv ↦ hv₀ (hyv ▸ hy.1)⟩) hx

def barycentricFaces_inter_subset_aux_chain_unique_aux_within_q {n : ℕ}
    (c : Finset (Finset (Euc n))) (w : Finset (Euc n) → ℝ) (v : Euc n) : ℝ :=
  ∑ s ∈ c with v ∈ s, w s * (s.card : ℝ)⁻¹

lemma barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_sum {n : ℕ}
    (c : Finset (Finset (Euc n))) (t : Finset (Euc n))
    (hne : ∀ s ∈ c, s.Nonempty) (hsub : ∀ s ∈ c, s ⊆ t)
    (w : Finset (Euc n) → ℝ) :
    ∑ v ∈ t, barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w v =
      ∑ s ∈ c, w s := by
  classical
  simp only [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_filter]
  have hf : t.filter (fun v ↦ v ∈ s) = s := by
    ext v
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hv ↦ hsub s hs hv)
  rw [hf]
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (hne s hs))
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- (W1) Equal points give equal vertex coefficients on `t`: both sides expand
to `∑ v ∈ t, q v • v` (barycenter formula) with weights summing to `1`, and
the vertices of `t` are affinely independent (`K.indep`). -/
lemma barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_eq_aux_expand {n : ℕ}
    (c : Finset (Finset (Euc n))) (t : Finset (Euc n))
    (hsub : ∀ s ∈ c, s ⊆ t) (w : Finset (Euc n) → ℝ) :
    ∑ v ∈ t, barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w v • v =
      ∑ s ∈ c, w s • barycenter s := by
  classical
  simp only [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q]
  simp_rw [Finset.sum_filter, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show (∑ x ∈ t, (if x ∈ s then w s * (s.card : ℝ)⁻¹ else 0) • x) =
      ∑ x ∈ t, if x ∈ s then (w s * (s.card : ℝ)⁻¹) • x else 0 by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxs : x ∈ s <;> simp [hxs]]
  rw [← Finset.sum_filter]
  have hf : t.filter (fun v ↦ v ∈ s) = s := by
    ext v
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hv ↦ hsub s hs hv)
  rw [hf, barycentricFaces_affineIndependent_aux_barycenter_formula]
  rw [← Finset.smul_sum]
  simp only [smul_smul]

theorem barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c₀ c₁ : Finset (Finset (Euc n)))
    (h₀ : IsStrictFaceChain K c₀) (h₁ : IsStrictFaceChain K c₁)
    (t : Finset (Euc n)) (ht : t ∈ K.faces)
    (hsub₀ : ∀ s ∈ c₀, s ⊆ t) (hsub₁ : ∀ s ∈ c₁, s ⊆ t)
    (w₀ w₁ : Finset (Euc n) → ℝ)
    (hs₀ : ∑ s ∈ c₀, w₀ s = 1) (hs₁ : ∑ s ∈ c₁, w₁ s = 1)
    (heq : ∑ s ∈ c₀, w₀ s • barycenter s = ∑ s ∈ c₁, w₁ s • barycenter s) :
    ∀ v ∈ t, barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c₀ w₀ v = barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c₁ w₁ v := by
  classical
  have hne₀ := barycentricFaces_affineIndependent_aux_chain_nonempty K c₀ h₀
  have hne₁ := barycentricFaces_affineIndependent_aux_chain_nonempty K c₁ h₁
  have hsum₀ : ∑ v ∈ t, barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c₀ w₀ v = 1 := by
    rw [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_sum c₀ t hne₀ hsub₀ w₀,
      hs₀]
  have hsum₁ : ∑ v ∈ t, barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c₁ w₁ v = 1 := by
    rw [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_sum c₁ t hne₁ hsub₁ w₁,
      hs₁]
  apply (K.indep ht).eq_of_sum_eq_sum_subtype
  · rw [hsum₀, hsum₁]
  · rw [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_eq_aux_expand c₀ t hsub₀ w₀,
      barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_eq_aux_expand c₁ t hsub₁ w₁]
    exact heq

/-- (W2) A positive-weight strict chain inside `t` is the family of positive
superlevel sets of its vertex coefficients: `q` is constant on each layer
`sᵢ \ sᵢ₋₁`, strictly larger on deeper layers, and `0` off the top face. -/
lemma barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_term_pos {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    (w : Finset (Euc n) → ℝ) (hw : ∀ s ∈ c, 0 < w s) :
    ∀ s ∈ c, 0 < w s * (s.card : ℝ)⁻¹ := by
  intro s hs
  exact mul_pos (hw s hs) (inv_pos.mpr (by
    exact_mod_cast (Finset.card_pos.mpr
      (barycentricFaces_affineIndependent_aux_chain_nonempty K c hc s hs))))

lemma barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_min {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    (t : Finset (Euc n)) (hsub : ∀ s ∈ c, s ⊆ t)
    (w : Finset (Euc n) → ℝ) (hw : ∀ s ∈ c, 0 < w s)
    (u : Euc n) (s : Finset (Euc n)) (hs : s ∈ c) (hu : u ∈ s)
    (hmin : ∀ r ∈ c, u ∈ r → s ⊆ r) :
    0 < barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w u ∧
      s = t.filter (fun v =>
        barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w u ≤
          barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w v) := by
  classical
  let p : Finset (Euc n) → ℝ := fun r => w r * (r.card : ℝ)⁻¹
  let A : Euc n → Finset (Finset (Euc n)) := fun v => c.filter (fun r => v ∈ r)
  have hp : ∀ r ∈ c, 0 < p r :=
    barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_term_pos K c hc w hw
  have hq (v : Euc n) :
      barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w v = ∑ r ∈ A v, p r := by
    simp [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q, A, p]
  have hsu : s ∈ A u := by simp [A, hs, hu]
  constructor
  · rw [hq]
    exact Finset.sum_pos' (fun r hr => (hp r (by
      have hr' := hr
      simp only [A, Finset.mem_filter] at hr'
      exact hr'.1)).le) ⟨s, hsu, hp s hs⟩
  · ext v
    simp only [Finset.mem_filter]
    constructor
    · intro hv
      refine ⟨hsub s hs hv, ?_⟩
      rw [hq, hq]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        simp only [A, Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, hmin r hr.1 hr.2 hv⟩
      · intro r hr₁ hr₂
        exact (hp r (by
          have hr' := hr₁
          simp only [A, Finset.mem_filter] at hr'
          exact hr'.1)).le
    · rintro ⟨hv, hle⟩
      by_contra hvs
      have hAvu : A v ⊆ A u := by
        intro r hr
        simp only [A, Finset.mem_filter] at hr ⊢
        rcases hc.2 r hr.1 s hs (fun h => hvs (h ▸ hr.2)) with hrs | hsr
        · exact False.elim (hvs (hrs.subset hr.2))
        · exact ⟨hr.1, hsr.subset hu⟩
      have hsnot : s ∉ A v := by simp [A, hs, hvs]
      have hlt : (∑ r ∈ A v, p r) < ∑ r ∈ A u, p r := by
        exact Finset.sum_lt_sum_of_subset hAvu hsu hsnot (hp s hs)
          (fun r hr _ => (hp r (by
            have hr' := hr
            simp only [A, Finset.mem_filter] at hr'
            exact hr'.1)).le)
      rw [hq, hq] at hle
      exact (not_lt_of_ge hle) hlt

theorem barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c)
    (t : Finset (Euc n)) (hsub : ∀ s ∈ c, s ⊆ t)
    (w : Finset (Euc n) → ℝ) (hw : ∀ s ∈ c, 0 < w s) :
    ∀ s : Finset (Euc n), s ∈ c ↔ ∃ u ∈ t, 0 < barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w u ∧
      s = t.filter (fun v => barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w u ≤ barycentricFaces_inter_subset_aux_chain_unique_aux_within_q c w v) := by
  classical
  intro s
  constructor
  · intro hs
    let d := c.filter (fun r => r ⊂ s)
    by_cases hd : d.Nonempty
    · obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image d Finset.card hd
      have hrs : r ⊂ s := (Finset.mem_filter.mp hr).2
      obtain ⟨u, hus, hur⟩ := (Finset.ssubset_iff_of_subset hrs.subset).mp hrs
      refine ⟨u, hsub s hs hus, ?_⟩
      apply barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_min
        K c hc t hsub w hw u s hs hus
      intro a ha hua
      by_cases has : a = s
      · simpa [has]
      rcases hc.2 a ha s hs has with hasub | hssub
      · exfalso
        apply hur
        have had : a ∈ d := Finset.mem_filter.mpr ⟨ha, hasub⟩
        rcases hc.2 a ha r (Finset.mem_filter.mp hr).1 (fun h => by
          subst h
          exact hur hua) with har | hra
        · exact har.subset hua
        · exact False.elim ((Nat.not_lt_of_ge (hrmax a had)) (Finset.card_lt_card hra))
      · exact hssub.subset
    · have hno : ∀ r ∈ c, ¬ r ⊂ s := by
        intro r hr hrs
        exact hd ⟨r, Finset.mem_filter.mpr ⟨hr, hrs⟩⟩
      obtain ⟨u, hus⟩ := barycentricFaces_affineIndependent_aux_chain_nonempty K c hc s hs
      refine ⟨u, hsub s hs hus, ?_⟩
      apply barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_min
        K c hc t hsub w hw u s hs hus
      intro r hr hur
      by_cases hrs : r = s
      · simpa [hrs]
      rcases hc.2 r hr s hs hrs with hrs | hsr
      · exact False.elim (hno r hr hrs)
      · exact hsr.subset
  · rintro ⟨u, hut, hqu, s_eq⟩
    have hAu : (c.filter (fun r => u ∈ r)).Nonempty := by
      by_contra h
      have he : c.filter (fun r => u ∈ r) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [barycentricFaces_inter_subset_aux_chain_unique_aux_within_q, he] at hqu
    obtain ⟨r, hr, hrmin⟩ := Finset.exists_min_image
      (c.filter (fun r => u ∈ r)) Finset.card hAu
    have hrc : r ∈ c := (Finset.mem_filter.mp hr).1
    have hru : u ∈ r := (Finset.mem_filter.mp hr).2
    have hminimal : ∀ a ∈ c, u ∈ a → r ⊆ a := by
      intro a ha hua
      by_cases har : a = r
      · simpa [har]
      rcases hc.2 a ha r hrc har with har | hra
      · exact False.elim ((Nat.not_lt_of_ge
          (hrmin a (Finset.mem_filter.mpr ⟨ha, hua⟩))) (Finset.card_lt_card har))
      · exact hra.subset
    have H := barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel_aux_min
      K c hc t hsub w hw u r hrc hru hminimal
    exact s_eq.trans H.2.symm ▸ hrc

/-- (U3) Inside one face `t` of `K`, a point determines the strict chain that
represents it with positive weights: its barycentric coordinate on `v ∈ t` is
`∑_{s ∋ v} w s / |s|`, a step function whose superlevel sets are the faces. -/
theorem barycentricFaces_inter_subset_aux_chain_unique_aux_within {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c₀ c₁ : Finset (Finset (Euc n)))
    (h₀ : IsStrictFaceChain K c₀) (h₁ : IsStrictFaceChain K c₁)
    (t : Finset (Euc n)) (ht : t ∈ K.faces)
    (hsub₀ : ∀ s ∈ c₀, s ⊆ t) (hsub₁ : ∀ s ∈ c₁, s ⊆ t)
    (w₀ w₁ : Finset (Euc n) → ℝ)
    (hw₀ : ∀ s ∈ c₀, 0 < w₀ s) (hw₁ : ∀ s ∈ c₁, 0 < w₁ s)
    (hs₀ : ∑ s ∈ c₀, w₀ s = 1) (hs₁ : ∑ s ∈ c₁, w₁ s = 1)
    (heq : ∑ s ∈ c₀, w₀ s • barycenter s = ∑ s ∈ c₁, w₁ s • barycenter s) :
    c₀ = c₁ := by
  classical
  have hq := barycentricFaces_inter_subset_aux_chain_unique_aux_within_q_eq K c₀ c₁ h₀ h₁
    t ht hsub₀ hsub₁ w₀ w₁ hs₀ hs₁ heq
  ext s
  rw [barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel K c₀ h₀ t
      hsub₀ w₀ hw₀ s,
    barycentricFaces_inter_subset_aux_chain_unique_aux_within_superlevel K c₁ h₁ t
      hsub₁ w₁ hw₁ s]
  constructor
  · rintro ⟨u, hu, hpos, rfl⟩
    refine ⟨u, hu, (hq u hu) ▸ hpos, Finset.filter_congr fun v hv => ?_⟩
    rw [hq u hu, hq v hv]
  · rintro ⟨u, hu, hpos, rfl⟩
    refine ⟨u, hu, (hq u hu).symm ▸ hpos, Finset.filter_congr fun v hv => ?_⟩
    rw [hq u hu, hq v hv]

/-- (I2) Uniqueness of the barycentric carrier chain: two strict chains of faces
of `K` with positive weights representing the same point are equal.  Both top
faces are the carrier of the point in `K` (positive weight on the top barycenter
puts positive barycentric weight on every vertex of the top face and none
outside it; `K`'s intersection axiom makes the carrier unique), and inside that
simplex the chain is the family of superlevel sets of the point's barycentric
coordinates. -/
theorem barycentricFaces_inter_subset_aux_chain_unique {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (c₀ c₁ : Finset (Finset (Euc n)))
    (h₀ : IsStrictFaceChain K c₀) (h₁ : IsStrictFaceChain K c₁)
    (w₀ w₁ : Finset (Euc n) → ℝ)
    (hw₀ : ∀ s ∈ c₀, 0 < w₀ s) (hw₁ : ∀ s ∈ c₁, 0 < w₁ s)
    (hs₀ : ∑ s ∈ c₀, w₀ s = 1) (hs₁ : ∑ s ∈ c₁, w₁ s = 1)
    (heq : ∑ s ∈ c₀, w₀ s • barycenter s = ∑ s ∈ c₁, w₁ s • barycenter s) :
    c₀ = c₁ := by
  obtain ⟨t₀, ht₀, htop₀⟩ := barycentricFaces_inter_subset_aux_chain_unique_aux_top K c₀ h₀
    (barycentricFaces_inter_subset_aux_chain_unique_aux_nonempty c₀ w₀ hs₀)
  obtain ⟨t₁, ht₁, htop₁⟩ := barycentricFaces_inter_subset_aux_chain_unique_aux_top K c₁ h₁
    (barycentricFaces_inter_subset_aux_chain_unique_aux_nonempty c₁ w₁ hs₁)
  obtain ⟨hx₀, hi₀⟩ := barycentricFaces_inter_subset_aux_chain_unique_aux_relint K c₀ h₀
    t₀ ht₀ htop₀ w₀ hw₀ hs₀
  obtain ⟨hx₁, hi₁⟩ := barycentricFaces_inter_subset_aux_chain_unique_aux_relint K c₁ h₁
    t₁ ht₁ htop₁ w₁ hw₁ hs₁
  rw [heq] at hx₀ hi₀
  have ht : t₀ = t₁ := barycentricFaces_inter_subset_aux_chain_unique_aux_carrier K
    (h₀.1 t₀ ht₀) (h₁.1 t₁ ht₁) _ hx₀ hx₁ hi₀ hi₁
  subst ht
  exact barycentricFaces_inter_subset_aux_chain_unique_aux_within K c₀ c₁ h₀ h₁ t₀
    (h₀.1 t₀ ht₀) htop₀ htop₁ w₀ w₁ hw₀ hw₁ hs₀ hs₁ heq

/-- (I3) A nonnegative normalized combination of barycenters lies in their hull. -/
theorem barycentricFaces_inter_subset_aux_mem_hull {n : ℕ}
    (c : Finset (Finset (Euc n))) (w : Finset (Euc n) → ℝ)
    (hw : ∀ s ∈ c, 0 ≤ w s) (hs : ∑ s ∈ c, w s = 1) :
    ∑ s ∈ c, w s • barycenter s ∈
      convexHull ℝ ((c.image barycenter : Finset (Euc n)) : Set (Euc n)) := by
  refine (convex_convexHull ℝ _).sum_mem hw hs ?_
  intro s hs
  apply subset_convexHull ℝ _
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- The common barycentric coordinates of two chain simplices are supported on
their common barycenters.  This is the hard intersection axiom. -/
theorem barycentricFaces_inter_subset {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) :
    ∀ᵉ (s ∈ barycentricFaces K) (t ∈ barycentricFaces K),
      convexHull ℝ (s : Set (Euc n)) ∩ convexHull ℝ (t : Set (Euc n)) ⊆
        convexHull ℝ (s ∩ t : Set (Euc n)) := by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ x ⟨hx, hx'⟩
  obtain ⟨c₀, hsub, w₀, hw₀, hs₀, hx₀⟩ :=
    barycentricFaces_inter_subset_aux_positive_subchain c x hx
  obtain ⟨c₁, hsub', w₁, hw₁, hs₁, hx₁⟩ :=
    barycentricFaces_inter_subset_aux_positive_subchain c' x hx'
  have hchain : ∀ {d e : Finset (Finset (Euc n))}, IsStrictFaceChain K d → e ⊆ d →
      IsStrictFaceChain K e := fun hd he =>
    ⟨fun s hs => hd.1 s (he hs), fun s hs t ht hne => hd.2 s (he hs) t (he ht) hne⟩
  have hc01 : c₀ = c₁ :=
    barycentricFaces_inter_subset_aux_chain_unique K c₀ c₁ (hchain hc hsub)
      (hchain hc' hsub') w₀ w₁ hw₀ hw₁ hs₀ hs₁ (hx₀.trans hx₁.symm)
  subst hc01
  rw [← hx₀]
  refine convexHull_mono ?_ (barycentricFaces_inter_subset_aux_mem_hull c₀ w₀
    (fun s hs => (hw₀ s hs).le) hs₀)
  intro y hy
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [Finset.coe_inter, Finset.coe_image, Set.mem_inter_iff, Set.mem_image,
    Finset.mem_coe]
  exact ⟨⟨s, hsub hs, rfl⟩, ⟨s, hsub' hs, rfl⟩⟩

/-- Assemble the three independent face facts into Mathlib's geometric complex. -/
def barycentricSubdivision {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (hi : ∀ u ∈ barycentricFaces K, AffineIndependent ℝ ((↑) : u → Euc n))
    (hd : IsLowerSet (barycentricFaces K))
    (hx : ∀ᵉ (s ∈ barycentricFaces K) (t ∈ barycentricFaces K),
      convexHull ℝ (s : Set (Euc n)) ∩ convexHull ℝ (t : Set (Euc n)) ⊆
        convexHull ℝ (s ∩ t : Set (Euc n))) :
    Geometry.SimplicialComplex ℝ (Euc n) :=
  Geometry.SimplicialComplex.ofErase (barycentricFaces K) hi hd hx

/-- Subdivision preserves finiteness of the face set. -/
theorem barycentricSubdivision_finite {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (hi hd hx) :
    (barycentricSubdivision K hi hd hx).faces.Finite := by
  classical
  have hchains : {c : Finset (Finset (Euc n)) | (c : Set (Finset (Euc n))) ⊆ K.faces}.Finite := by
    exact Set.Finite.preimage_embedding
      (Finset.coeEmb : Finset (Finset (Euc n)) ↪o Set (Finset (Euc n))).toEmbedding
      hK.finite_subsets
  have himages : ((fun c : Finset (Finset (Euc n)) => c.image barycenter) ''
      {c | (c : Set (Finset (Euc n))) ⊆ K.faces}).Finite := hchains.image _
  apply himages.subset
  intro u hu
  have hu' : u ∈ barycentricFaces K := by
    exact hu.1
  obtain ⟨c, hc, rfl⟩ := hu'
  exact ⟨c, (fun s hs => hc.1 s hs), rfl⟩

/-- Every old simplex is the union of the chain simplices, and conversely. -/
theorem barycentricSubdivision_space {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hi hd hx) :
    (barycentricSubdivision K hi hd hx).space = K.space := by
  sorry

/-- (M1) Hatcher's estimate: a point of a simplex is within
`(m-1)/m · diam` of its barycenter, `m` the number of vertices (the distance to
the barycenter is convex, so its maximum is at a vertex `v`, and
`v - barycenter t = (1/m) ∑_{w} (v - w)` has at most `m - 1` nonzero terms). -/
theorem barycentricSubdivision_mesh_aux_barycenter_dist {n : ℕ}
    (t : Finset (Euc n)) (ht : t.Nonempty) (p : Euc n)
    (hp : p ∈ convexHull ℝ (t : Set (Euc n))) :
    dist p (barycenter t) ≤ ((t.card - 1 : ℝ) / t.card) *
      Metric.diam (convexHull ℝ (t : Set (Euc n))) := by
  classical
  let D := Metric.diam (convexHull ℝ (t : Set (Euc n)))
  have hbounded : Bornology.IsBounded (convexHull ℝ (t : Set (Euc n))) :=
    isBounded_convexHull.mpr t.finite_toSet.isBounded
  have hvertex (v : Euc n) (hv : v ∈ t) :
      dist v (barycenter t) ≤ ((t.card - 1 : ℝ) / t.card) * D := by
    have hcard : (t.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr ht)
    have hvh : v ∈ convexHull ℝ (t : Set (Euc n)) :=
      (subset_convexHull ℝ (t : Set (Euc n))) (by simpa using hv)
    have hpair (w : Euc n) (hw : w ∈ t.erase v) : dist v w ≤ D := by
      apply Metric.dist_le_diam_of_mem hbounded hvh
      exact (subset_convexHull ℝ (t : Set (Euc n)))
        (by simpa using (Finset.mem_of_mem_erase hw))
    rw [dist_eq_norm, barycentricFaces_affineIndependent_aux_barycenter_formula]
    have hid : v - (t.card : ℝ)⁻¹ • ∑ x ∈ t, x =
        (t.card : ℝ)⁻¹ • ∑ x ∈ t.erase v, (v - x) := by
      rw [← Finset.sum_erase_add _ _ hv]
      simp only [smul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem hv]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht))]
      have hinv : (t.card : ℝ)⁻¹ * ((t.card : ℝ) - 1) =
          1 - (t.card : ℝ)⁻¹ := by field_simp
      rw [smul_sub, smul_smul]
      norm_num only [Nat.cast_one]
      rw [hinv, sub_smul]
      module
    rw [hid, norm_smul, norm_inv, norm_natCast]
    calc
      (t.card : ℝ)⁻¹ * ‖∑ x ∈ t.erase v, (v - x)‖
          ≤ (t.card : ℝ)⁻¹ * ∑ x ∈ t.erase v, ‖v - x‖ := by
              gcongr
              exact norm_sum_le _ _
      _ ≤ (t.card : ℝ)⁻¹ * ((t.erase v).card * D) := by
              gcongr
              calc
                ∑ x ∈ t.erase v, ‖v - x‖ = ∑ x ∈ t.erase v, dist v x := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [dist_eq_norm]
                _ ≤ ∑ _x ∈ t.erase v, D := Finset.sum_le_sum fun x hx => hpair x hx
                _ = (t.erase v).card * D := by simp
      _ = ((t.card - 1 : ℝ) / t.card) * D := by
              rw [Finset.card_erase_of_mem hv]
              push_cast
              field_simp
              rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht))]
              ring
  obtain ⟨v, hv, hvmax⟩ :=
    (convexOn_univ_dist (barycenter t)).exists_ge_of_mem_convexHull
      (by simp) hp
  exact hvmax.trans (hvertex v hv)

/-- (M2) Pairwise bound for chain barycenters: two faces of a chain are nested,
the smaller barycenter lies in the hull of the larger face `t`, apply (M1),
then `(|t|-1)/|t| ≤ d/(d+1)` and `diam t ≤ sSup` (finite set, so bounded). -/
theorem barycentricSubdivision_mesh_aux_chain_bound {n d : ℕ}
    (hM1 : ∀ (t : Finset (Euc n)), t.Nonempty → ∀ p ∈ convexHull ℝ (t : Set (Euc n)),
      dist p (barycenter t) ≤ ((t.card - 1 : ℝ) / t.card) *
        Metric.diam (convexHull ℝ (t : Set (Euc n))))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (c : Finset (Finset (Euc n))) (hc : IsStrictFaceChain K c) :
    ∀ x ∈ c.image barycenter, ∀ y ∈ c.image barycenter,
      dist x y ≤ (d / (d + 1 : ℝ)) *
        sSup {r : ℝ | ∃ s ∈ K.faces,
          r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
  sorry

/-- Hatcher's mesh estimate for one barycentric subdivision. -/
theorem barycentricSubdivision_mesh {n d : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ d + 1) (hi hd hx) :
    ∀ u ∈ (barycentricSubdivision K hi hd hx).faces,
      Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
        (d / (d + 1 : ℝ)) *
          sSup {r : ℝ | ∃ s ∈ K.faces,
            r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
  classical
  intro u hu
  have hu' : u ∈ barycentricFaces K := hu.1
  obtain ⟨c, hc, rfl⟩ := hu'
  rw [convexHull_diam]
  let M : ℝ := sSup {r : ℝ | ∃ s ∈ K.faces,
    r = Metric.diam (convexHull ℝ (s : Set (Euc n)))}
  have hM : 0 ≤ M := by
    apply Real.sSup_nonneg
    intro r hr
    obtain ⟨s, hs, rfl⟩ := hr
    exact Metric.diam_nonneg
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (div_nonneg (Nat.cast_nonneg d) (by positivity)) hM)
  intro x hx y hy
  exact barycentricSubdivision_mesh_aux_chain_bound
    (fun t ht p hp => barycentricSubdivision_mesh_aux_barycenter_dist t ht p hp)
    K hK hdim c hc x hx y hy

/-- Iterating any finite, space-preserving subdivision with the barycentric
mesh contraction produces a prescribed mesh. -/
lemma exists_fine_of_barycentric_step_aux_iterate {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (step : ∀ L : Geometry.SimplicialComplex ℝ (Euc n), L.faces.Finite →
      ∃ L' : Geometry.SimplicialComplex ℝ (Euc n), L'.faces.Finite ∧
        L'.space = L.space ∧
        ∀ u ∈ L'.faces,
          Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
            (n / (n + 1 : ℝ)) *
              sSup {r : ℝ | ∃ s ∈ L.faces,
                r = Metric.diam (convexHull ℝ (s : Set (Euc n)))}) :
    ∀ m : ℕ, ∃ L : Geometry.SimplicialComplex ℝ (Euc n),
      L.faces.Finite ∧ L.space = K.space ∧
      ∀ u ∈ L.faces,
        Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
          (n / (n + 1 : ℝ)) ^ m *
            sSup {r : ℝ | ∃ s ∈ K.faces,
              r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
  intro m
  have hM0 : 0 ≤ sSup {r : ℝ | ∃ s ∈ K.faces,
      r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
    by_cases hneK : K.faces.Nonempty
    · obtain ⟨s, hs⟩ := hneK
      refine Metric.diam_nonneg.trans (le_csSup ?_ ⟨s, hs, rfl⟩)
      apply (hK.image (fun t : Finset (Euc n) ↦
          Metric.diam (convexHull ℝ (t : Set (Euc n))))).bddAbove.mono
      intro r hr
      obtain ⟨t, ht, rfl⟩ := hr
      exact ⟨t, ht, rfl⟩
    · simp [Set.not_nonempty_iff_eq_empty.mp hneK]
  induction m with
  | zero =>
      refine ⟨K, hK, rfl, ?_⟩
      intro u hu
      simp only [pow_zero, one_mul]
      apply le_csSup
      · apply (hK.image (fun s : Finset (Euc n) ↦
            Metric.diam (convexHull ℝ (s : Set (Euc n))))).bddAbove.mono
        intro r hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact ⟨s, hs, rfl⟩
      · exact ⟨u, hu, rfl⟩
  | succ m ih =>
      obtain ⟨L, hL, hspace, hmesh⟩ := ih
      obtain ⟨L', hL', hspace', hstep⟩ := step L hL
      refine ⟨L', hL', hspace'.trans hspace, ?_⟩
      intro u hu
      refine (hstep u hu).trans ?_
      have hsup : sSup {r : ℝ | ∃ s ∈ L.faces,
          r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} ≤
          (n / (n + 1 : ℝ)) ^ m *
            sSup {r : ℝ | ∃ s ∈ K.faces,
              r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
        by_cases hne : {r : ℝ | ∃ s ∈ L.faces,
            r = Metric.diam (convexHull ℝ (s : Set (Euc n)))}.Nonempty
        · apply csSup_le hne
          intro r hr
          obtain ⟨s, hs, rfl⟩ := hr
          exact hmesh s hs
        · rw [Set.not_nonempty_iff_eq_empty.mp hne]
          rw [Real.sSup_empty]
          exact mul_nonneg (by positivity) hM0
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hsup (by positivity : 0 ≤ n / (n + 1 : ℝ)))

theorem exists_fine_of_barycentric_step {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (step : ∀ L : Geometry.SimplicialComplex ℝ (Euc n), L.faces.Finite →
      ∃ L' : Geometry.SimplicialComplex ℝ (Euc n), L'.faces.Finite ∧
        L'.space = L.space ∧
        ∀ u ∈ L'.faces,
          Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
            (n / (n + 1 : ℝ)) *
              sSup {r : ℝ | ∃ s ∈ L.faces,
                r = Metric.diam (convexHull ℝ (s : Set (Euc n)))})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ (Euc n),
      K'.faces.Finite ∧ K'.space = K.space ∧
      ∀ s ∈ K'.faces,
        Metric.diam (convexHull ℝ (↑s : Set (Euc n))) < ε := by
  let M := sSup {r : ℝ | ∃ s ∈ K.faces,
    r = Metric.diam (convexHull ℝ (s : Set (Euc n)))}
  let q : ℝ := n / (n + 1 : ℝ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
    norm_num
  have hlim : Filter.Tendsto (fun m : ℕ ↦ q ^ m * M) Filter.atTop (nhds 0) :=
    by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const M
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q ^ m * M < ε := by
    have hevent : ∀ᶠ m : ℕ in Filter.atTop, q ^ m * M < ε :=
      (tendsto_order.1 hlim).2 ε hε
    exact hevent.exists
  obtain ⟨L, hL, hspace, hmesh⟩ :=
    exists_fine_of_barycentric_step_aux_iterate K hK step m
  refine ⟨L, hL, hspace, ?_⟩
  intro s hs
  exact (hmesh s hs).trans_lt (by simpa [q, M] using hm)

/-- Every finite geometric simplicial complex admits an arbitrarily fine
finite subdivision with unchanged realization. -/
theorem exists_fine_subdivision {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K'.faces.Finite ∧ K'.space = K.space ∧
      ∀ s ∈ K'.faces, Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) < ε := by
  have step : ∀ L : Geometry.SimplicialComplex ℝ (Euc n), L.faces.Finite →
      ∃ L' : Geometry.SimplicialComplex ℝ (Euc n), L'.faces.Finite ∧
        L'.space = L.space ∧
        ∀ u ∈ L'.faces,
          Metric.diam (convexHull ℝ (u : Set (Euc n))) ≤
            (n / (n + 1 : ℝ)) *
              sSup {r : ℝ | ∃ s ∈ L.faces,
                r = Metric.diam (convexHull ℝ (s : Set (Euc n)))} := by
    intro L hL
    let hi := barycentricFaces_affineIndependent L
    let hd := barycentricFaces_isLowerSet L
    let hx := barycentricFaces_inter_subset L
    refine ⟨barycentricSubdivision L hi hd hx,
      barycentricSubdivision_finite L hL hi hd hx,
      barycentricSubdivision_space L hi hd hx, ?_⟩
    apply barycentricSubdivision_mesh L hL
    intro s hs
    have hspan := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : s → Euc n)))
    have hcard := (L.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right hspan 1)
    simpa using hcard
  exact exists_fine_of_barycentric_step K hK step hε

/-! ## Simplicial approximation interfaces -/

/-- A vertex map which sends every face to a face. -/
def IsSimplicialVertexMap {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (h : Euc n → Euc m) : Prop :=
  (∀ v ∈ K.vertices, h v ∈ L.vertices) ∧
    ∀ s ∈ K.faces, s.image h ∈ L.faces

/-- The (relative) open star expressed using positive barycentric support. -/
def openStar {n : ℕ} (K : Geometry.SimplicialComplex ℝ (Euc n))
    (v : Euc n) : Set (Euc n) :=
  {x | ∃ s ∈ K.faces, v ∈ s ∧ x ∈ convexHull ℝ (s : Set (Euc n)) ∧
      x ∉ convexHull ℝ ((s.erase v : Finset (Euc n)) : Set (Euc n))}

/-- A simplicial vertex map has a continuous affine realization. -/
theorem exists_inducedContinuousMap {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (h : Euc n → Euc m)
    (hh : IsSimplicialVertexMap K L h) :
    ∃ f : C(K.space, L.space),
      (∀ v (hv : v ∈ K.vertices), f ⟨v, Geometry.SimplicialComplex.vertices_subset_space hv⟩ =
        ⟨h v, Geometry.SimplicialComplex.vertices_subset_space (hh.1 v hv)⟩) ∧
      ∀ s ∈ K.faces, ∀ x : K.space,
        (x : Euc n) ∈ convexHull ℝ (s : Set (Euc n)) →
        (f x : Euc m) ∈ convexHull ℝ (s.image h : Set (Euc m)) := by
  sorry

/-- The star condition makes the affine realization straight-line homotopic
to the original map. -/
lemma inducedMap_homotopic_of_star_condition_aux_source_carrier {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (x : K.space) :
    ∃ s ∈ K.faces,
      (x : Euc n) ∈ convexHull ℝ (s : Set (Euc n)) ∧
      ∀ v ∈ s,
        (x : Euc n) ∉ convexHull ℝ ((s.erase v : Finset (Euc n)) : Set (Euc n)) := by
  classical
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.2
  let t : Finset (Euc n) := Caratheodory.minCardFinsetOfMemConvexHull hxs
  have hts : (t : Set (Euc n)) ⊆ (s : Set (Euc n)) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hxs
  have hxt : (x : Euc n) ∈ convexHull ℝ (t : Set (Euc n)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hxs
  have htne : t.Nonempty :=
    Caratheodory.minCardFinsetOfMemConvexHull_nonempty hxs
  have htface : t ∈ K.faces := K.down_closed hs (by simpa using hts) htne
  refine ⟨t, htface, hxt, ?_⟩
  intro v hv herase
  have hcard := Caratheodory.minCardFinsetOfMemConvexHull_card_le_card hxs
    (Set.Subset.trans (by simpa using Finset.erase_subset v t) hts) herase
  change t.card ≤ (t.erase v).card at hcard
  rw [Finset.card_erase_of_mem hv] at hcard
  have htpos : 0 < t.card := Finset.card_pos.mpr htne
  omega

lemma inducedMap_homotopic_of_star_condition_aux_target_carrier {m : ℕ}
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (y : L.space)
    (s : Finset (Euc m))
    (hy : ∀ v ∈ s, (y : Euc m) ∈ openStar L v) :
    ∃ t ∈ L.faces, s ⊆ t ∧ (y : Euc m) ∈ convexHull ℝ (t : Set (Euc m)) := by
  sorry

theorem inducedMap_homotopic_of_star_condition {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m))
    (g f : C(K.space, L.space)) (h : Euc n → Euc m)
    (hstar : ∀ v ∈ K.vertices,
      g '' ((Subtype.val : K.space → Euc n) ⁻¹' openStar K v) ⊆
        (Subtype.val : L.space → Euc m) ⁻¹' openStar L (h v))
    (haff : ∀ s ∈ K.faces, ∀ x : K.space,
      (x : Euc n) ∈ convexHull ℝ (s : Set (Euc n)) →
      (f x : Euc m) ∈ convexHull ℝ (s.image h : Set (Euc m))) :
    ContinuousMap.Homotopic g f := by
  have hcarrier : ∀ x : K.space, ∃ t ∈ L.faces,
      (g x : Euc m) ∈ convexHull ℝ (t : Set (Euc m)) ∧
      (f x : Euc m) ∈ convexHull ℝ (t : Set (Euc m)) := by
    intro x
    obtain ⟨s, hs, hxs, hxmin⟩ :=
      inducedMap_homotopic_of_star_condition_aux_source_carrier K x
    have hgstar : ∀ w ∈ s.image h, (g x : Euc m) ∈ openStar L w := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      apply hstar v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
      have hxstar : (x : Euc n) ∈ openStar K v := ⟨s, hs, hv, hxs, hxmin v hv⟩
      exact ⟨x, hxstar, rfl⟩
    obtain ⟨t, ht, hst, hgt⟩ :=
      inducedMap_homotopic_of_star_condition_aux_target_carrier L (g x) (s.image h) hgstar
    refine ⟨t, ht, hgt, ?_⟩
    exact convexHull_mono hst (haff s hs x hxs)
  let F : C(Set.Icc (0 : ℝ) 1 × K.space, L.space) :=
    { toFun := fun z =>
        ⟨(1 - (z.1 : ℝ)) • (g z.2 : Euc m) + (z.1 : ℝ) • (f z.2 : Euc m), by
          obtain ⟨t, ht, hgt, hft⟩ := hcarrier z.2
          apply Geometry.SimplicialComplex.convexHull_subset_space ht
          exact (convex_convexHull ℝ (t : Set (Euc m))) hgt hft
            (by linarith [z.1.2.2]) z.1.2.1 (by ring)⟩
      continuous_toFun := by fun_prop }
  refine ⟨{
    toContinuousMap := F
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    simp [F]
  · intro x
    apply Subtype.ext
    simp [F]

/-- Lebesgue-number simplicial approximation: sufficiently small stars admit
a vertex choice satisfying the star condition. -/
lemma exists_vertexMap_of_mesh_lt_lebesgue_aux_barycenter_mem_openStar {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) {s : Finset (Euc n)}
    (hs : s ∈ K.faces) {v : Euc n} (hv : v ∈ s) :
    barycenter s ∈ openStar K v := by
  classical
  refine ⟨s, hs, hv, ?_, ?_⟩
  · apply Finset.centerMass_id_mem_convexHull
    · intro x hx
      positivity
    · simpa using (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs) : 0 < s.card)
  · exact fun h =>
      barycentricFaces_affineIndependent_aux_chain_not_mem_span K hs
        (Finset.erase_ssubset hv) (by
          have hc : convexHull ℝ ((s.erase v : Finset (Euc n)) : Set (Euc n)) ⊆
              affineSpan ℝ ((s.erase v : Finset (Euc n)) : Set (Euc n)) :=
            convexHull_subset_affineSpan ((s.erase v : Finset (Euc n)) : Set (Euc n))
          exact hc h)

lemma exists_vertexMap_of_mesh_lt_lebesgue_aux_common_openStars {m : ℕ}
    (L : Geometry.SimplicialComplex ℝ (Euc m))
    (u : Finset (Euc m)) (hu : u.Nonempty) {x : Euc m}
    (hx : ∀ w ∈ u, x ∈ openStar L w) : u ∈ L.faces := by
  classical
  have hu' := hu
  obtain ⟨w₀, hw₀⟩ := hu
  obtain ⟨t, ht, hw₀t, hxt, -⟩ := hx w₀ hw₀
  apply L.down_closed ht
  · intro w hw
    obtain ⟨r, hr, hwr, hxr, hxerase⟩ := hx w hw
    by_contra hwt
    apply hxerase
    have hxi : x ∈ convexHull ℝ ((r ∩ t : Finset (Euc m)) : Set (Euc m)) := by
      simpa only [Finset.coe_inter] using
        (L.convexHull_inter_convexHull hr ht ▸ ⟨hxr, hxt⟩)
    exact convexHull_mono (by
      intro y hy
      have hyr : y ∈ r := (Finset.mem_inter.mp hy).1
      have hyt : y ∈ t := (Finset.mem_inter.mp hy).2
      exact Finset.mem_erase.mpr ⟨fun hyw => hwt (hyw ▸ hyt), hyr⟩) hxi
  · exact hu'

set_option maxHeartbeats 800000 in
theorem exists_vertexMap_of_mesh_lt_lebesgue {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (L : Geometry.SimplicialComplex ℝ (Euc m)) (g : C(K.space, L.space))
    (δ : ℝ) (hδ : 0 < δ)
    (hlebesgue : ∀ x : K.space, ∃ w ∈ L.vertices,
      Metric.ball x δ ⊆ g ⁻¹' ((Subtype.val : L.space → Euc m) ⁻¹' openStar L w))
    (hmesh : ∀ s ∈ K.faces,
      Metric.diam (convexHull ℝ (s : Set (Euc n))) < δ / 2) :
    ∃ h : Euc n → Euc m, IsSimplicialVertexMap K L h ∧
      ∀ v ∈ K.vertices,
        g '' ((Subtype.val : K.space → Euc n) ⁻¹' openStar K v) ⊆
          (Subtype.val : L.space → Euc m) ⁻¹' openStar L (h v) := by
  classical
  have hchoice : ∀ v : Euc n, ∃ w : Euc m, ∀ hv : v ∈ K.vertices,
      w ∈ L.vertices ∧
        Metric.ball (⟨v, Geometry.SimplicialComplex.vertices_subset_space hv⟩ : K.space) δ ⊆
          g ⁻¹' ((Subtype.val : L.space → Euc m) ⁻¹' openStar L w) := by
    intro v
    by_cases hv : v ∈ K.vertices
    · obtain ⟨w, hw, hb⟩ :=
        hlebesgue (⟨v, Geometry.SimplicialComplex.vertices_subset_space hv⟩ : K.space)
      exact ⟨w, fun hv' => ⟨hw, by simpa only using hb⟩⟩
    · exact ⟨0, fun hv' => (hv hv').elim⟩
  choose h hh using hchoice
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    exact (hh v hv).1
  · intro s hs
    have hbHull : barycenter s ∈ convexHull ℝ (s : Set (Euc n)) := by
      apply Finset.centerMass_id_mem_convexHull
      · intro y hy
        positivity
      · simpa using (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs) : 0 < s.card)
    let b : K.space := ⟨barycenter s, K.convexHull_subset_space hs hbHull⟩
    apply exists_vertexMap_of_mesh_lt_lebesgue_aux_common_openStars L
      (s.image h) (Finset.image_nonempty.mpr (K.nonempty_of_mem_faces hs))
      (x := (g b : Euc m))
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have hvvertex : v ∈ K.vertices :=
        K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hbball : b ∈ Metric.ball (⟨v,
          Geometry.SimplicialComplex.vertices_subset_space hvvertex⟩ : K.space) δ := by
        rw [Metric.mem_ball]
        change dist (barycenter s) v < δ
        exact (Metric.dist_le_diam_of_mem
          (isBounded_convexHull.mpr s.finite_toSet.isBounded)
          hbHull
          (subset_convexHull ℝ (s : Set (Euc n)) hv)).trans_lt
          ((hmesh s hs).trans (by linarith))
      exact (hh v hvvertex).2 hbball
  · intro v hv y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply (hh v hv).2
    rw [Metric.mem_ball]
    change dist (x : Euc n) v < δ
    obtain ⟨s, hs, hvs, hxs, -⟩ := hx
    exact (Metric.dist_le_diam_of_mem
      (isBounded_convexHull.mpr s.finite_toSet.isBounded) hxs
      (subset_convexHull ℝ (s : Set (Euc n)) hvs)).trans_lt
      ((hmesh s hs).trans (by linarith))

end ConstructionTargets.GeometricSimplicialSubdivision

#print axioms ConstructionTargets.GeometricSimplicialSubdivision.exists_fine_subdivision
