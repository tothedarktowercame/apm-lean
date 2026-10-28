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
  sorry

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
-- BEGIN SEAT AREA
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
-- END SEAT AREA

/-- Every old simplex is the union of the chain simplices, and conversely. -/
theorem barycentricSubdivision_space {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hi hd hx) :
    (barycentricSubdivision K hi hd hx).space = K.space := by
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
  sorry

/-- Iterating any finite, space-preserving subdivision with the barycentric
mesh contraction produces a prescribed mesh. -/
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
  sorry

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
  sorry

/-- Lebesgue-number simplicial approximation: sufficiently small stars admit
a vertex choice satisfying the star condition. -/
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
  sorry

end ConstructionTargets.GeometricSimplicialSubdivision

#print axioms ConstructionTargets.GeometricSimplicialSubdivision.exists_fine_subdivision
