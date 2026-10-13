import Mathlib
import ConstructionTargets.NestedEmbeddingTransition
import ConstructionTargets.t91J06Closure

/-! # Blueprint for APM t91J06

The registered theorem is true.  The old unregistered glue helper is not used:
without an embedding hypothesis it is false.  The corrected gluing lemma below
retains `hf`.
-/

open Set

noncomputable section

abbrev apm_t91J06_I := Set.Icc (0 : ℝ) 1

/-- The points of the unit interval lying in its real-line interior. -/
def apm_t91J06_Iinterior : Set apm_t91J06_I :=
  {x | x.1 ∈ Ioo (0 : ℝ) 1}

def apm_t91J06_stage {X : Type*} (f : ℕ → apm_t91J06_I → X) (n : ℕ) : Set X :=
  f n '' univ

lemma apm_t91J06_stage_compact
    {X : Type*} [TopologicalSpace X] (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n)) (n : ℕ) :
    IsCompact (apm_t91J06_stage f n) := by
  exact isCompact_univ.image (hf n).continuous

lemma apm_t91J06_stage_mono
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) :
    Monotone (apm_t91J06_stage f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rcases hnested n hx with ⟨y, hy, rfl⟩
  exact ⟨y, mem_univ y, rfl⟩

lemma apm_t91J06_exists_mem_stage
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ apm_t91J06_stage f n := by
  have hx : x ∈ (⋃ n, f n '' (univ : Set apm_t91J06_I)) := by
    rw [hcover]
    exact mem_univ x
  simpa only [mem_iUnion] using hx

lemma apm_t91J06_exists_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨n, hn⟩ := apm_t91J06_exists_mem_stage f hcover x
  exact ⟨n + 1, hnested n hn⟩

lemma apm_t91J06_exists_pair_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x y : X) :
    ∃ n, x ∈ f n '' apm_t91J06_Iinterior ∧
      y ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨nx, hx⟩ := apm_t91J06_exists_mem_stage f hcover x
  obtain ⟨ny, hy⟩ := apm_t91J06_exists_mem_stage f hcover y
  have hmono := apm_t91J06_stage_mono f hnested
  have hxmax : x ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_left _ _) hx
  have hymax : y ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_right _ _) hy
  exact ⟨max nx ny + 1, hnested (max nx ny) hxmax,
    hnested (max nx ny) hymax⟩

/-- LIBRARY: extend arbitrary prescribed coordinates across an interval
embedded strictly inside the unit interval.  The independent orientations of
`t` and `q` account for all four cases. -/
theorem apm_t91J06_extend_interval_embedding_coordinates
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (hi : Function.Injective t)
    (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)) :
    ∃ Q : apm_t91J06_I ≃ₜ
        Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ),
      ∀ x, (Q (t x) : ℝ) = (q x : ℝ) := by
  sorry

/-- Recursively choose coordinates on all compact stages.  The extension
contract is an explicit parameter so this lemma can be developed in parallel
with the library lemma above. -/
noncomputable def apm_t91J06_compatible_stage_coordinates_aux_stageHomeo
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X) (hf : ∀ n, Topology.IsEmbedding (f n))
    (n : ℕ) : ↥(apm_t91J06_stage f n) ≃ₜ apm_t91J06_I :=
  (Homeomorph.setCongr (by simp [apm_t91J06_stage])).trans
    (hf n).toHomeomorph.symm

theorem apm_t91J06_compatible_stage_coordinates
    (hExtend : ∀ (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I),
      Continuous t → Function.Injective t →
      Set.range t ⊆ apm_t91J06_Iinterior →
      ∀ q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
        ∃ Q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ),
          ∀ x, (Q (t x) : ℝ) = (q x : ℝ))
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior) :
    ∃ g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
        Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
      ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
        ((g (n + 1))
            ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ) := by
  let hsub : ∀ n, Set.range (f n) ⊆ Set.range (f (n + 1)) := fun n => by
    simpa only [image_univ] using
      (hnested n).trans (image_subset_range (f (n + 1)) apm_t91J06_Iinterior)
  let t : ∀ n, apm_t91J06_I → apm_t91J06_I := fun n =>
    ConstructionTargets.NestedEmbeddingTransition.transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n)
  have ht_cont : ∀ n, Continuous (t n) := fun n => by
    exact ConstructionTargets.NestedEmbeddingTransition.continuous_transition
      (f n) (f (n + 1)) (hf n).continuous (hf (n + 1)) (hsub n)
  have ht_inj : ∀ n, Function.Injective (t n) := fun n => by
    exact ConstructionTargets.NestedEmbeddingTransition.injective_transition
      (f n) (f (n + 1)) (hf n).injective (hf (n + 1)) (hsub n)
  have ht_int : ∀ n, Set.range (t n) ⊆ apm_t91J06_Iinterior := fun n => by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ConstructionTargets.NestedEmbeddingTransition.transition_mem_of_range_subset_image
      (f n) (f (n + 1)) (hf (n + 1)) apm_t91J06_Iinterior
      (by simpa only [image_univ] using hnested n) x
  let q : ∀ n : ℕ, apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) :=
    fun (n : ℕ) => Nat.rec (motive := fun k : ℕ =>
        apm_t91J06_I ≃ₜ Set.Icc (-(k + 1 : ℝ)) (k + 1 : ℝ))
      (by
        exact (Homeomorph.setCongr (show apm_t91J06_I = Set.Icc (0 : ℝ) 1 from rfl)).trans
          ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans
            (Homeomorph.setCongr (by norm_num))))
      (fun k qk => by
        let w := hExtend k (t k) (ht_cont k) (ht_inj k) (ht_int k) qk
        exact (Classical.choose w).trans (Homeomorph.setCongr (by
          congr 1 <;> norm_num [Nat.cast_succ] <;> ring)) ) n
  have hq : ∀ n x, ((q (n + 1)) (t n x) : ℝ) = ((q n) x : ℝ) := by
    intro n x
    simp only [q]
    exact Classical.choose_spec
      (hExtend n (t n) (ht_cont n) (ht_inj n) (ht_int n) (q n)) x
  refine ⟨fun n =>
    (apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n).trans (q n), ?_⟩
  intro n x hx
  have hxnext : x ∈ apm_t91J06_stage f (n + 1) :=
    apm_t91J06_stage_mono f hnested (Nat.le_succ n) hx
  change ((q (n + 1))
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
        ⟨x, hxnext⟩) : ℝ) =
    ((q n) ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n)
      ⟨x, hx⟩) : ℝ)
  have heq : t n
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩) =
      (apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
        ⟨x, hxnext⟩ := by
    apply (hf (n + 1)).injective
    change f (n + 1) (t n _) = f (n + 1) _
    rw [show t n = ConstructionTargets.NestedEmbeddingTransition.transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n) from rfl]
    rw [ConstructionTargets.NestedEmbeddingTransition.g_transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n)
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩)]
    have hn : f n
        ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩) = x := by
      exact congrArg Subtype.val ((hf n).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr (by simp [apm_t91J06_stage])) ⟨x, hx⟩))
    have hn1 : f (n + 1)
        ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
          ⟨x, hxnext⟩) = x := by
      exact congrArg Subtype.val ((hf (n + 1)).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr (by simp [apm_t91J06_stage])) ⟨x, hxnext⟩))
    exact hn.trans hn1.symm
  rw [← heq]
  exact hq n _

/-- Glue compatible stage coordinates.  Unlike the false helper in the
source file, this statement retains `hf`, which is needed to obtain local
inverse charts and hence continuity of the inverse. -/
theorem apm_t91J06_glue_with_embeddings
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C)
    (g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (hcompat : ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
      ((g (n + 1))
          ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ)) :
    Nonempty (X ≃ₜ ℝ) := by
  sorry

theorem apm_t91j06
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C) :
    Nonempty (X ≃ₜ ℝ) := by
  obtain ⟨g, hg⟩ := apm_t91J06_compatible_stage_coordinates
    apm_t91J06_extend_interval_embedding_coordinates f hf hnested
  exact apm_t91J06_glue_with_embeddings f hf hnested hcover hweak g hg

#print axioms apm_t91j06
