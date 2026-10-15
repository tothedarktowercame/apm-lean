import Mathlib
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
import ConstructionTargets.FundamentalGroupoidTwoOpenDescent
import ConstructionTargets.TwoOpenDescentReconstruction
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.CircleMetricFundamentalGroup
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.Surfaces
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PointWedgeVanKampen

/-! # Two-open van Kampen: attaching one cell (banked from the t92J05 blueprint, claude-14, 2026-10-15)

For an open cover `X = U ∪ V` with `U`, `V`, `U ∩ V` path connected and `V` simply connected,
the left inclusion induces `π₁(U, x) ↠ π₁(X, x)` with kernel the normal closure of the image of
`π₁(U ∩ V, x)` (`apm_t92J05_twoOpen_simplyConnectedRight_kernel`), hence
`π₁(X, x) ≃* π₁(U, x) ⧸ normalClosure (image of π₁(U ∩ V))` (`apm_t92J05_twoOpen_attach_one_cell`).
Proved from the two-open fundamental-groupoid pseudopushout and path subdivision.  `X : Type`. -/

open CategoryTheory Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization
noncomputable section

/-! ### A generic one-relator van Kampen interface -/

/-- Inclusion of the left member of a two-open cover into the ambient space. -/
def apm_t92J05_twoOpen_leftInclusion
    {X : Type} [TopologicalSpace X] (U : Set X) : ContinuousMap U X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of the overlap into the left member of a two-open cover. -/
def apm_t92J05_twoOpen_overlapToLeft
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    ContinuousMap (U ∩ V : Set X) U :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- **LIBRARY (groupoid-to-based van Kampen).**  With the right-hand open
member simply connected, inclusion of the left member is onto on `π₁`, and
its kernel is precisely the normal closure of the overlap image.  This is the
based-group consequence to extract from the banked fundamental-groupoid
pseudopushout. -/
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le_ker
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (a : K →* G) (h : ∀ k, f (a k) = 1) :
    Subgroup.normalClosure (a.range : Set G) ≤ MonoidHom.ker f := by
  letI : (MonoidHom.ker f).Normal := f.normal_ker
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨k, rfl⟩
  exact h k

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_overlap_killed
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (x : (U ∩ V : Set X))
    (g : FundamentalGroup (U ∩ V : Set X) x) :
    FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U)
      (⟨x.1, x.2.1⟩ : U)
      (FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x g) = 1 := by
  let overlapToRight : ContinuousMap (U ∩ V : Set X) V :=
    ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  let rightInclusion : ContinuousMap V X :=
    ⟨Subtype.val, continuous_subtype_val⟩
  letI : Subsingleton (FundamentalGroup V (overlapToRight x)) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have hright : FundamentalGroup.map overlapToRight x g = 1 := by
    apply Subsingleton.elim
  have hleft_comp :
      FundamentalGroup.map
          (apm_t92J05_twoOpen_leftInclusion U)
          (⟨x.1, x.2.1⟩ : U)
          (FundamentalGroup.map
            (apm_t92J05_twoOpen_overlapToLeft U V) x g) =
        FundamentalGroup.map
          ((apm_t92J05_twoOpen_leftInclusion U).comp
            (apm_t92J05_twoOpen_overlapToLeft U V)) x g := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  have hright_comp :
      FundamentalGroup.map rightInclusion (overlapToRight x)
          (FundamentalGroup.map overlapToRight x g) =
        FundamentalGroup.map (rightInclusion.comp overlapToRight) x g := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  rw [hleft_comp]
  change FundamentalGroup.map (rightInclusion.comp overlapToRight) x g = 1
  rw [← hright_comp, hright, map_one]
  rfl

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Subgroup.normalClosure (overlapMap.range : Set
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))) ≤
      MonoidHom.ker leftMap := by
  dsimp only
  apply apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le_ker
  exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_overlap_killed U V x

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_right_loop
    {X : Type} [TopologicalSpace X] (V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (v : V)
    (r : Path v v) :
    FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap V X) v
        (Path.Homotopic.Quotient.mk r) = 1 := by
  letI : Subsingleton (FundamentalGroup V v) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have hr : (Path.Homotopic.Quotient.mk r : FundamentalGroup V v) =
      (1 : FundamentalGroup V v) :=
    Subsingleton.elim _ _
  simpa [hr]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_connector
    {X : Type} [TopologicalSpace X] (U : Set X) [PathConnectedSpace U]
    (u₀ u₁ : U) : Nonempty (Path u₀ u₁) := by
  exact PathConnectedSpace.joined u₀ u₁

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (c : (U ∩ V : Set X)) {z : X} (i j : Bool)
    (hzi : z ∈ twoChart U V i) (hzj : z ∈ twoChart U V j) :
    ∃ a : Path z c.1,
      ∀ t, a t ∈ twoChart U V i ∩ twoChart U V j := by
  cases i <;> cases j
  · let zV : V := ⟨z, by simpa [twoChart] using hzi⟩
    let cV : V := ⟨c.1, c.2.2⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zV cV
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    simpa [twoChart] using
      (show (a t).1 ∈ V ∩ V from ⟨(a t).2, (a t).2⟩)
  · let zI : (U ∩ V : Set X) :=
      ⟨z, ⟨by simpa [twoChart] using hzj,
        by simpa [twoChart] using hzi⟩⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zI c
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    change (a t).1 ∈ V ∩ U
    exact ⟨(a t).2.2, (a t).2.1⟩
  · let zI : (U ∩ V : Set X) :=
      ⟨z, ⟨by simpa [twoChart] using hzi,
        by simpa [twoChart] using hzj⟩⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zI c
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    change (a t).1 ∈ U ∩ V
    exact (a t).2
  · let zU : U := ⟨z, by simpa [twoChart] using hzi⟩
    let cU : U := ⟨c.1, c.2.1⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zU cU
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    simpa [twoChart] using
      (show (a t).1 ∈ U ∩ U from ⟨(a t).2, (a t).2⟩)

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_telescoping
    {C : Type*} [Category C] {n : ℕ}
    (A B : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ)
    (g : (i : Fin n) → B i.castSucc ⟶ B i.succ)
    (e : (i : Fin (n + 1)) → B i ≅ A i)
    (h : ∀ i, g i = (e i.castSucc).hom ≫ f i ≫ (e i.succ).inv) :
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g =
      (e 0).hom ≫
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A f ≫
        (e (Fin.last n)).inv := by
  induction n with
  | zero =>
      simp only [
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_zero]
      simp
  | succ n ih =>
      rw [
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ,
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ]
      have hp := ih (A := A ∘ Fin.castSucc) (B := B ∘ Fin.castSucc)
        (f := fun i ↦ f i.castSucc) (g := fun i ↦ g i.castSucc)
        (e := fun i ↦ e i.castSucc) (fun i ↦ h i.castSucc)
      rw [hp, h (Fin.last n)]
      simp only [Function.comp_apply, Category.assoc]
      rw [Iso.inv_hom_id_assoc]
      simpa only [Category.assoc, Fin.castSucc_zero, Fin.succ_last]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_product_range
    {G H : Type*} [Group G] [Group H] (f : G →* H) (l : List H)
    (h : ∀ z ∈ l, z = 1 ∨ z ∈ f.range) : l.prod ∈ f.range := by
  induction l with
  | nil =>
      exact ⟨1, map_one f⟩
  | cons z l ih =>
      have hz := h z (by simp)
      obtain ⟨gz, hgz⟩ : ∃ gz : G, f gz = z := by
        rcases hz with rfl | ⟨gz, rfl⟩
        · exact ⟨1, map_one f⟩
        · exact ⟨gz, rfl⟩
      obtain ⟨gl, hgl⟩ := ih (fun w hw ↦ h w (by simp [hw]))
      refine ⟨gz * gl, ?_⟩
      simp only [map_mul, List.prod_cons, hgz, hgl]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_piece
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [SimplyConnectedSpace V] (x : (U ∩ V : Set X))
    {z w : X} (b : Bool) (a : Path z x.1) (r : Path z w) (d : Path w x.1)
    (ha : ∀ t, a t ∈ twoChart U V b)
    (hr : ∀ t, r t ∈ twoChart U V b)
    (hd : ∀ t, d t ∈ twoChart U V b) :
    let ℓ : Path x.1 x.1 := a.symm.trans (r.trans d)
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    Path.Homotopic.Quotient.mk ℓ = (1 : FundamentalGroup X x.1) ∨
      Path.Homotopic.Quotient.mk ℓ ∈ leftMap.range := by
  dsimp only
  cases b
  · left
    let aV : Path (⟨z, by simpa [twoChart] using ha 0⟩ : V)
        (⟨x.1, x.2.2⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false a (by simpa [twoChart] using ha)
    let rV : Path (⟨z, by simpa [twoChart] using hr 0⟩ : V)
        (⟨w, by simpa [twoChart] using hr 1⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false r (by simpa [twoChart] using hr)
    let dV : Path (⟨w, by simpa [twoChart] using hd 0⟩ : V)
        (⟨x.1, x.2.2⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false d (by simpa [twoChart] using hd)
    let ℓV : Path (⟨x.1, x.2.2⟩ : V) (⟨x.1, x.2.2⟩ : V) :=
      aV.symm.trans (rV.trans dV)
    have h :=
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_right_loop
        V (⟨x.1, x.2.2⟩ : V) ℓV
    rw [← h]
    apply congrArg Path.Homotopic.Quotient.mk
    change a.symm.trans (r.trans d) =
      (aV.symm.trans (rV.trans dV)).map continuous_subtype_val
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    have haV : aV.map continuous_subtype_val = a := by
      apply Path.ext; rfl
    have hrV : rV.map continuous_subtype_val = r := by
      apply Path.ext; rfl
    have hdV : dV.map continuous_subtype_val = d := by
      apply Path.ext; rfl
    rw [haV, hrV, hdV]
  · right
    let aU : Path (⟨z, by simpa [twoChart] using ha 0⟩ : U)
        (⟨x.1, x.2.1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true a (by simpa [twoChart] using ha)
    let rU : Path (⟨z, by simpa [twoChart] using hr 0⟩ : U)
        (⟨w, by simpa [twoChart] using hr 1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true r (by simpa [twoChart] using hr)
    let dU : Path (⟨w, by simpa [twoChart] using hd 0⟩ : U)
        (⟨x.1, x.2.1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true d (by simpa [twoChart] using hd)
    refine ⟨Path.Homotopic.Quotient.mk (aU.symm.trans (rU.trans dU)), ?_⟩
    apply congrArg Path.Homotopic.Quotient.mk
    change (aU.symm.trans (rU.trans dU)).map continuous_subtype_val =
      a.symm.trans (r.trans d)
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    have haU : aU.map continuous_subtype_val = a := by
      apply Path.ext; rfl
    have hrU : rU.map continuous_subtype_val = r := by
      apply Path.ext; rfl
    have hdU : dU.map continuous_subtype_val = d := by
      apply Path.ext; rfl
    rw [haU, hrU, hdU]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_composeFin_range
    {X : Type*} [TopologicalSpace X] (y : X) {n : ℕ}
    (f : Fin n → FundamentalGroup X y) (K : Subgroup (FundamentalGroup X y))
    (hf : ∀ i, f i ∈ K) :
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
      (fun _ : Fin (n + 1) ↦ FundamentalGroupoid.mk y) f ∈ K := by
  induction n with
  | zero =>
      rw [ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_zero]
      exact K.one_mem
  | succ n ih =>
      rw [ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ]
      exact K.mul_mem (hf (Fin.last n))
        (ih (fun i ↦ f i.castSucc) (fun i ↦ hf i.castSucc))

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) (p : Path x.1 x.1) :
    ∃ q : FundamentalGroup U (⟨x.1, x.2.1⟩ : U),
      FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
          (⟨x.1, x.2.1⟩ : U) q = Path.Homotopic.Quotient.mk p := by
  classical
  let S := Classical.choice
    (ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.exists_pathTwoOpenSubdivision
      p hU hV hcover)
  let mid : (i : Fin S.n) → Path (S.point i.castSucc.succ) x.1 := fun i ↦
    Classical.choose
      (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
        U V x (S.side i.castSucc) (S.side i.succ)
        (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
        (by
          convert S.piece_mem i.succ 0 using 1 <;>
            try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
            convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))
  let a : (i : Fin (S.n + 2)) → Path (S.point i) x.1 :=
    Fin.cases ((Path.refl x.1).cast S.point_zero rfl)
      (fun j ↦ Fin.lastCases
        (by convert (Path.refl x.1).cast S.point_last rfl)
        (fun i ↦ mid i) j)
  have ha : ∀ (k : Fin (S.n + 1)) t,
      a k.castSucc t ∈ twoChart U V (S.side k) := by
    intro k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · intro t
      have hx : x.1 ∈ twoChart U V (S.side 0) := by
        cases h : S.side 0 <;> simp [twoChart, h, x.2.1, x.2.2]
      simpa [a] using hx
    · intro t
      have hm := (Classical.choose_spec
        (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
          U V x (z := S.point i.castSucc.succ) (S.side i.castSucc) (S.side i.succ)
          (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
          (by
            convert S.piece_mem i.succ 0 using 1 <;>
              try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
              convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))) t
      exact (by simpa [a, mid] using hm.2)
  let B : Fin (S.n + 2) → FundamentalGroupoid X := fun k ↦ ⟨S.point k⟩
  let A : Fin (S.n + 2) → FundamentalGroupoid X := fun _ ↦ ⟨x.1⟩
  let g : (k : Fin (S.n + 1)) → B k.castSucc ⟶ B k.succ := fun k ↦
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (S.piece k))
  let e : (k : Fin (S.n + 2)) → B k ≅ A k := fun k ↦
    asIso (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (a k)))
  let f : (k : Fin (S.n + 1)) → A k.castSucc ⟶ A k.succ := fun k ↦
    (e k.castSucc).inv ≫ g k ≫ (e k.succ).hom
  have htel :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_telescoping
      A B f g e (by intro k; simp [f])
  have hf_piece : ∀ k, f k = Path.Homotopic.Quotient.mk
      ((a k.castSucc).symm.trans ((S.piece k).trans (a k.succ))) := by
    intro k
    simp only [f, e, g, A, B, asIso_inv, asIso_hom]
    have hi : inv (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (a k.castSucc))) =
        FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (a k.castSucc).symm) := by
      rw [← Groupoid.inv_eq_inv]
      rfl
    rw [hi]
    change Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (a k.castSucc).symm)
        (Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (S.piece k))
          (Path.Homotopic.Quotient.mk (a k.succ))) = _
    rw [← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_trans]
  have hd : ∀ (k : Fin (S.n + 1)) t,
      a k.succ t ∈ twoChart U V (S.side k) := by
    intro k
    refine Fin.lastCases ?_ (fun i ↦ ?_) k
    · intro t
      have hx : x.1 ∈ twoChart U V (S.side (Fin.last S.n)) := by
        cases h : S.side (Fin.last S.n) <;>
          simp [twoChart, h, x.2.1, x.2.2]
      simpa only [a, Fin.cases_succ, Fin.lastCases_last,
        Path.cast, Path.refl] using hx
    · intro t
      have hm := (Classical.choose_spec
        (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
          U V x (z := S.point i.castSucc.succ) (S.side i.castSucc) (S.side i.succ)
          (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
          (by
            convert S.piece_mem i.succ 0 using 1 <;>
              try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
              convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))) t
      exact (by simpa [a, mid] using hm.1)
  have hf : ∀ k, f k = 1 ∨ f k ∈
      (FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
        (⟨x.1, x.2.1⟩ : U)).range := by
    intro k
    rw [hf_piece]
    exact
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_piece
        U V x (S.side k) (a k.castSucc) (S.piece k) (a k.succ)
        (ha k) (S.piece_mem k) (hd k)
  have hprod :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_composeFin_range
      x.1 f
      (FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
        (⟨x.1, x.2.1⟩ : U)).range (fun k ↦ by
          rcases hf k with h | h
          · rw [h]
            exact Subgroup.one_mem _
          · exact h)
  obtain ⟨q, hq⟩ := hprod
  refine ⟨q, ?_⟩
  rw [hq]
  calc
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A f =
        (e 0).inv ≫
          ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g ≫
          (e (Fin.last (S.n + 1))).hom := by rw [htel]; simp
    _ = Path.Homotopic.Quotient.mk p := by
      have he0 : (e 0).inv =
          eqToHom (congrArg FundamentalGroupoid.mk S.point_zero).symm := by
        have h0 :=
          ConstructionTargets.TwoOpenDescentReconstruction.fromPath_cast_unbracket
            (Path.refl x.1) S.point_zero rfl
        have h0' : eqToHom (congrArg FundamentalGroupoid.mk S.point_zero).symm ≫
            FundamentalGroupoid.fromPath
              (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_zero rfl)) = 𝟙 _ := by
          simpa using h0
        simp only [e, a, A, B, Fin.cases_zero, asIso_inv]
        rw [← cancel_mono (FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_zero rfl)))]
        rw [h0']
        simp
      have helast : (e (Fin.last (S.n + 1))).hom =
          eqToHom (congrArg FundamentalGroupoid.mk S.point_last) := by
        have hl :=
          ConstructionTargets.TwoOpenDescentReconstruction.fromPath_cast_unbracket
            (Path.refl x.1) S.point_last rfl
        have hl' : eqToHom (congrArg FundamentalGroupoid.mk S.point_last).symm ≫
            FundamentalGroupoid.fromPath
              (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_last rfl)) = 𝟙 _ := by
          simpa using hl
        have halast : a (Fin.last (S.n + 1)) =
            (Path.refl x.1).cast S.point_last rfl := by
          apply Path.ext
          funext t
          conv_lhs => rw [← Fin.succ_last]
          simp only [a, Fin.cases_succ, Fin.lastCases_last]
          simp [Path.cast, Path.refl]
          rfl
        simp only [e, A, B, asIso_hom]
        rw [halast]
        rw [← cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk S.point_last).symm)]
        rw [hl']
        simp
      rw [he0, helast]
      have hev :=
        ConstructionTargets.TwoOpenDescentReconstruction.canonical_evaluate
          (U := U) (V := V) (𝟭 (FundamentalGroupoid X)) p S
      let D := ConstructionTargets.TwoOpenDescentReconstruction.canonicalTwoOpenDescentDatum
        (U := U) (V := V) (𝟭 (FundamentalGroupoid X))
      have hfold :
          ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g =
            ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
              (D.obj ∘ S.point) (D.mappedPiece S) := by
        congr 1
        funext k
        rw [ConstructionTargets.TwoOpenDescentReconstruction.canonical_mappedPiece]
        simp [B, g, D]
      rw [hfold]
      simpa [B, g,
        D,
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.evaluate]
        using hev
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    Function.Surjective (FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)) := by
  intro g
  induction g using Quotient.inductionOn with
  | h p =>
      obtain ⟨q, hq⟩ :=
        apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization
          U V hU hV hcover x p
      exact ⟨q, hq⟩
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_of_factor
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (a : K →* G)
    (r : H →* (G ⧸ Subgroup.normalClosure (a.range : Set G)))
    (hfactor : r.comp f =
      QuotientGroup.mk' (Subgroup.normalClosure (a.range : Set G))) :
    MonoidHom.ker f ≤ Subgroup.normalClosure (a.range : Set G) := by
  intro g hg
  have hq : QuotientGroup.mk' (Subgroup.normalClosure (a.range : Set G)) g = 1 := by
    rw [← hfactor]
    change r (f g) = 1
    rw [hg, map_one]
  exact (QuotientGroup.eq_one_iff g).mp hq

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X))
    (Z : FundamentalGroupoid U) :
    FundamentalGroupoid.mk (apm_t92J05_twoOpen_overlapToLeft U V x) ≅ Z :=
  asIso (Path.Homotopic.Quotient.mk
    (PathConnectedSpace.somePath
      (apm_t92J05_twoOpen_overlapToLeft U V x) Z.as))

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid V ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  exact (Functor.const _).obj (SingleObj.star _)

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftFunctor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid U ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector U V x
  let N := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
      (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  exact
    { obj := fun _ => SingleObj.star _
      map := fun {a b} p => QuotientGroup.mk' N
        ((c a).hom ≫ p ≫ (c b).inv)
      map_id := by
        intro a
        change QuotientGroup.mk' N ((c a).hom ≫ 𝟙 a ≫ (c a).inv) = 1
        rw [show (c a).hom ≫ 𝟙 a ≫ (c a).inv = 𝟙 _ by simp]
        exact map_one _
      map_comp := by
        intro a b d p q
        let A : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c a).hom ≫ p ≫ (c b).inv
        let B : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c b).hom ≫ q ≫ (c d).inv
        have h : (c a).hom ≫ (p ≫ q) ≫ (c d).inv = B * A := by
          change (c a).hom ≫ (p ≫ q) ≫ (c d).inv =
            ((c a).hom ≫ p ≫ (c b).inv) ≫
              ((c b).hom ≫ q ≫ (c d).inv)
          simp [Category.assoc]
        change QuotientGroup.mk' N ((c a).hom ≫ (p ≫ q) ≫ (c d).inv) =
          QuotientGroup.mk' N B * QuotientGroup.mk' N A
        rw [h, map_mul] }

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] (x : (U ∩ V : Set X))
    (Z : FundamentalGroupoid (U ∩ V : Set X)) :
    FundamentalGroupoid.mk x ≅ Z :=
  asIso (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x Z.as))

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) (Z : FundamentalGroupoid U) :
    FundamentalGroupoid.mk (apm_t92J05_twoOpen_overlapToLeft U V x) ≅ Z := by
  classical
  exact if h : Z.as.1 ∈ V then
    (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso
      (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector
        U V x (FundamentalGroupoid.mk ⟨Z.as.1, Z.as.2, h⟩))
  else
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector
      U V x Z

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid U ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector U V x
  let N := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
      (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  exact
    { obj := fun _ => SingleObj.star _
      map := fun {a b} p => QuotientGroup.mk' N ((c a).hom ≫ p ≫ (c b).inv)
      map_id := by
        intro a
        change QuotientGroup.mk' N ((c a).hom ≫ 𝟙 a ≫ (c a).inv) = 1
        rw [show (c a).hom ≫ 𝟙 a ≫ (c a).inv = 𝟙 _ by simp]
        exact map_one _
      map_comp := by
        intro a b d p q
        let A : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c a).hom ≫ p ≫ (c b).inv
        let B : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c b).hom ≫ q ≫ (c d).inv
        have h : (c a).hom ≫ (p ≫ q) ≫ (c d).inv = B * A := by
          change (c a).hom ≫ (p ≫ q) ≫ (c d).inv =
            ((c a).hom ≫ p ≫ (c b).inv) ≫ ((c b).hom ≫ q ≫ (c d).inv)
          simp [Category.assoc]
        change QuotientGroup.mk' N ((c a).hom ≫ (p ≫ q) ≫ (c d).inv) =
          QuotientGroup.mk' N B * QuotientGroup.mk' N A
        rw [h, map_mul] }

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X))
    {a b : FundamentalGroupoid (U ∩ V : Set X)} (p : a ⟶ b) :
    (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V) ⋙
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
        U V x).map p = 𝟙 _ := by
  classical
  let d := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector U V x
  let loop : FundamentalGroup (U ∩ V : Set X) x :=
    (d a).hom ≫ p ≫ (d b).inv
  change QuotientGroup.mk' _ _ = 1
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.subset_normalClosure
  refine ⟨loop, ?_⟩
  change FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x loop = _
  rw [show
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_overlapToLeft U V)).obj a) =
      (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso (d a) by
        unfold apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
        rw [dif_pos (show
          ((FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).obj a).as.1 ∈ V
          from a.as.2.2)]
        rfl,
    show
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_overlapToLeft U V)).obj b) =
      (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso (d b) by
        unfold apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
        rw [dif_pos (show
          ((FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).obj b).as.1 ∈ V
          from b.as.2.2)]
        rfl]
  let F := FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)
  change F.map loop = F.map (d a).hom ≫ F.map p ≫ F.map (d b).inv
  dsimp [loop]
  rw [F.map_comp, F.map_comp]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom
    {G : Type} [Group G] (a b : SingleObj G) (h : a = b) :
    (eqToHom h : a ⟶ b) = 𝟙 _ := by
  cases a
  cases b
  cases h
  rfl

set_option maxHeartbeats 800000 in
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    ∃ r : FundamentalGroup X x.1 →*
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
          Subgroup.normalClosure (overlapMap.range : Set
            (FundamentalGroup U
              (apm_t92J05_twoOpen_overlapToLeft U V x)))),
      r.comp leftMap = QuotientGroup.mk'
        (Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U
              (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  classical
  dsimp only
  let Q := FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
    Subgroup.normalClosure
      ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  let L :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor U V x
  let R :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial U V x
  let D : @ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum
      X _ U V (SingleObj Q) _ :=
    { obj := fun _ => SingleObj.star Q
      functor := by intro b; cases b; exact R; exact L
      obj_eq := by intro b z; cases b <;> rfl
      overlap_eq := by
        intro a b p hpU hpV
        rw [apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom]
        simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, one_mul, mul_one]
        change (1 : Q) = L.map _
        symm
        let q : Path (⟨a, by simpa using hpU 0, by simpa using hpV 0⟩ : (U ∩ V : Set X))
            (⟨b, by simpa using hpU 1, by simpa using hpV 1⟩ : (U ∩ V : Set X)) :=
          { toFun := fun t => ⟨p t, hpU t, hpV t⟩
            continuous_toFun := p.continuous.subtype_mk _
            source' := Subtype.ext p.source
            target' := Subtype.ext p.target }
        exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
          U V x (Path.Homotopic.Quotient.mk q) }
  let F := ConstructionTargets.TwoOpenDescentFunctor.twoOpenDescentFunctor hU hV hcover D
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x (FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U))
  let k : Q := QuotientGroup.mk' _ c.hom
  let s : FundamentalGroup X x.1 →* Q := F.mapEnd _
  let r : FundamentalGroup X x.1 →* Q :=
    { toFun := fun g => k * s g * k⁻¹
      map_one' := by rw [map_one]; group
      map_mul' := by intro a b; rw [map_mul]; group }
  refine ⟨r, ?_⟩
  ext g
  change k * F.map ((FundamentalGroupoid.map
    (apm_t92J05_twoOpen_leftInclusion U)).map g) * k⁻¹ = _
  let z := FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U)
  have hn := (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
    hU hV hcover D true).hom.naturality g
  have hn' : L.map g = F.map ((FundamentalGroupoid.map
      (apm_t92J05_twoOpen_leftInclusion U)).map g) := by
    have hn0 : (D.functor true).map g =
        (ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor
          hU hV hcover D true).map g := by
      simp only [ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso,
        ConstructionTargets.TwoOpenDescentRestriction.restrictionAppIso,
        NatIso.ofComponents_hom_app, eqToIso.hom] at hn
      calc
        (D.functor true).map g = (D.functor true).map g ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = 𝟙 _ ≫ (ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor
              hU hV hcover D true).map g := hn
        _ = _ := Category.id_comp _
    have hncover : L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) := by
      simpa [D, L, F,
        ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor] using hn0
    have hi : ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
        (U := U) (V := V) true = apm_t92J05_twoOpen_leftInclusion U := rfl
    simpa [hi] using hncover
  rw [← hn']
  let N : Subgroup (FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x)) := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  letI : N.Normal := inferInstance
  change FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) at g
  have hL : L.map g = k⁻¹ * QuotientGroup.mk' N g * k := by
    have hLraw : L.map g = QuotientGroup.mk' N (c.hom ≫ g ≫ c.inv) := rfl
    rw [hLraw]
    let cg : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) := c.hom
    have hk : k = QuotientGroup.mk' N cg := rfl
    rw [hk]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    dsimp [cg]
    change c.hom ≫ g ≫ c.inv = c.hom ≫ g ≫ Groupoid.inv c.hom
    rw [Groupoid.inv_eq_inv]
    have hc : CategoryTheory.inv c.hom = c.inv :=
      IsIso.inv_eq_of_hom_inv_id c.hom_inv_id
    exact congrArg (fun q => c.hom ≫ g ≫ q) hc.symm
  change k * L.map g * k⁻¹ = QuotientGroup.mk' N g
  rw [hL]
  group
/-
  classical
  dsimp only
  let Q := FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
    Subgroup.normalClosure
      ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  let L :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
      U V x
  let R :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial
      U V x
  let D : @ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum
      X _ U V (SingleObj Q) _ :=
    { obj := fun _ => SingleObj.star Q
      functor := by
        intro b
        cases b
        · exact R
        · exact L
      obj_eq := by intro b z; cases b <;> rfl
      overlap_eq := by
        intro a b p hpU hpV
        rw [apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom]
        simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, one_mul, mul_one]
        change (1 : Q) = L.map _
        symm
        let q : Path (⟨a, by simpa using hpU 0, by simpa using hpV 0⟩ : (U ∩ V : Set X))
            (⟨b, by simpa using hpU 1, by simpa using hpV 1⟩ : (U ∩ V : Set X)) :=
          { toFun := fun t => ⟨p t, hpU t, hpV t⟩
            continuous_toFun := p.continuous.subtype_mk _
            source' := Subtype.ext p.source
            target' := Subtype.ext p.target }
        have hk :=
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
            U V x (Path.Homotopic.Quotient.mk q)
        exact hk }
  let F := ConstructionTargets.TwoOpenDescentFunctor.twoOpenDescentFunctor
    hU hV hcover D
  let c :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x (FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U))
  let k : Q := QuotientGroup.mk' _ c.hom
  let s : FundamentalGroup X x.1 →* Q := F.mapEnd _
  let r : FundamentalGroup X x.1 →* Q :=
    { toFun := fun g => k * s g * k⁻¹
      map_one' := by rw [map_one]; group
      map_mul' := by intro a b; rw [map_mul]; group }
  refine ⟨r, ?_⟩
  ext g
  change k * F.map ((FundamentalGroupoid.map
    (apm_t92J05_twoOpen_leftInclusion U)).map g) * k⁻¹ = _
  let z := FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U)
  have hn := (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
    hU hV hcover D true).hom.naturality g
  have hn' : L.map g =
      F.map ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_leftInclusion U)).map g) := by
    have heta : (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
      hU hV hcover D true).hom.app z = (1 : Q) := by
      rfl
    rw [heta] at hn
    have hncover : L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) := by
      have hn0 := hn
      simp [D, L, F,
        ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor,
        SingleObj.comp_as_mul] at hn0
      change (1 : Q) * L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) * 1 at hn0
      simpa using hn0
    have hi : ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
        (U := U) (V := V) true = apm_t92J05_twoOpen_leftInclusion U := rfl
    simpa [hi] using hncover
  rw [← hn']
  let N : Subgroup (FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x)) := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range :
      Set (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  letI : N.Normal := inferInstance
  have hz : z = FundamentalGroupoid.mk
      (apm_t92J05_twoOpen_overlapToLeft U V x) := by rfl
  subst z
  have hL : L.map g = k⁻¹ * QuotientGroup.mk' N g * k := by
    dsimp [L, k, c,
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor]
    change QuotientGroup.mk' N (c.hom ≫ g ≫ c.inv) = _
    rw [show c.hom ≫ g ≫ c.inv = c.inv * g * c.hom by rfl]
    simp [map_mul]
  rw [hL]
  change k * (k⁻¹ * QuotientGroup.mk' N g * k) * k⁻¹ =
    QuotientGroup.mk' N g
  group
-/
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    MonoidHom.ker (FundamentalGroup.map
        (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)) ≤
      Subgroup.normalClosure
        ((FundamentalGroup.map
          (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
            (FundamentalGroup U
              (apm_t92J05_twoOpen_overlapToLeft U V x))) := by
  obtain ⟨r, hr⟩ :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor
      U V hU hV hcover x
  exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_of_factor
    _ _ r hr
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Function.Surjective leftMap ∧
      MonoidHom.ker leftMap =
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))) := by
  dsimp only
  refine ⟨apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective
    U V hU hV hcover x, ?_⟩
  apply le_antisymm
  · exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le
      U V hU hV hcover x
  · exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le U V x
/-- **LIBRARY (pure group theory).**  A surjective homomorphism is the
quotient by its kernel; an explicitly supplied kernel computation rewrites
this as the desired normal-closure quotient. -/
lemma apm_t92J05_quotient_normalClosure_equiv_of_kernel
    {G K H : Type*} [Group G] [Group K] [Group H]
    (f : G →* H) (a : K →* G) (hsurj : Function.Surjective f)
    (hker : MonoidHom.ker f =
      Subgroup.normalClosure (a.range : Set G)) :
    Nonempty
      (H ≃* G ⧸ Subgroup.normalClosure (a.range : Set G)) := by
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-- Generic "attach one simply-connected piece" van Kampen theorem.  In the
2-cell application the overlap is an annulus, but cyclicity is not needed in
the statement: the entire overlap image is normally killed. -/
theorem apm_t92J05_twoOpen_attach_one_cell
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Nonempty
      (FundamentalGroup X x.1 ≃*
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)) ⧸
          Subgroup.normalClosure (overlapMap.range : Set
            (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let f := FundamentalGroup.map
    (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
  let a := FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x
  rcases apm_t92J05_twoOpen_simplyConnectedRight_kernel U V hU hV hcover x with
    ⟨hsurj, hker⟩
  exact apm_t92J05_quotient_normalClosure_equiv_of_kernel f a hsurj hker
