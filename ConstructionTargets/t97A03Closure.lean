import Mathlib

/-!
# Closure support for t97A03

The connected double-cover classification reduces its discrete monodromy to
the actions of the two complementary circle arcs on a two-element fiber.
-/

namespace ConstructionTargets.t97A03Closure

/-- Local homeomorphisms pull local path-connectedness back from their
target.  Covering maps are local homeomorphisms, so this supplies the missing
local hypothesis needed to upgrade a connected total space to path connected. -/
theorem IsLocalHomeomorph.locPathConnectedSpace
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] {f : Y → X} (hf : IsLocalHomeomorph f) :
    LocPathConnectedSpace Y := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro y u hu hyu
  obtain ⟨e, hye, rfl⟩ := hf y
  letI : LocPathConnectedSpace e.target := e.open_target.locPathConnectedSpace
  letI : LocPathConnectedSpace e.source :=
    e.toHomeomorphSourceTarget.isOpenEmbedding.locPathConnectedSpace
  let v : Set e.source := Subtype.val ⁻¹' u
  have hyv : (⟨y, hye⟩ : e.source) ∈ v := hyu
  let c : Set e.source := pathComponentIn v ⟨y, hye⟩
  have hcopen : IsOpen c := (hu.preimage continuous_subtype_val).pathComponentIn _
  have hcpath : IsPathConnected c := isPathConnected_pathComponentIn hyv
  have hyc : (⟨y, hye⟩ : e.source) ∈ c := mem_pathComponentIn_self hyv
  have himage_open : IsOpen (Subtype.val '' c) :=
    e.open_source.isOpenMap_subtype_val c hcopen
  have himage_mem : Subtype.val '' c ∈ nhds y :=
    himage_open.mem_nhds ⟨⟨y, hye⟩, hyc, rfl⟩
  apply Filter.mem_of_superset himage_mem
  have himage_path : IsPathConnected (Subtype.val '' c) :=
    hcpath.image continuous_subtype_val
  exact himage_path.subset_pathComponentIn
    ⟨⟨y, hye⟩, hyc, rfl⟩
    (by
      rintro _ ⟨z, hzc, rfl⟩
      simpa [v] using pathComponentIn_subset hzc)

/-- A covering over a locally path-connected base has locally path-connected
total space, obtained directly from its covering charts. -/
theorem IsCoveringMap.locPathConnectedSpace
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] {p : Y → X} (hp : IsCoveringMap p) :
    LocPathConnectedSpace Y :=
  IsLocalHomeomorph.locPathConnectedSpace hp.isLocalHomeomorph

/-- The two homeomorphism types that remain after quotienting the nontrivial
two-arc monodromy patterns by interchange of the complementary arcs. -/
inductive DoubleCoverModel
  | oneCircle
  | twoCircle
  deriving DecidableEq

/-- Every monodromy permutation of a two-point fiber is either the identity
or its unique transposition.  This supplies the finite-fiber-to-Boolean
bridge used by the two-arc classification below. -/
theorem finTwoPerm_eq_id_or_swap (e : Equiv.Perm (Fin 2)) :
    e = Equiv.refl (Fin 2) ∨ e = Equiv.swap 0 1 := by
  have h0 : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases h0 with h0 | h0
  · left
    ext i
    fin_cases i
    · simpa using congrArg Fin.val h0
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      have h1 : e 1 = 0 ∨ e 1 = 1 := by omega
      rcases h1 with h1 | h1
      · exact False.elim (hne (h1.trans h0.symm))
      · simpa using congrArg Fin.val h1
  · right
    ext i
    fin_cases i
    · simpa using congrArg Fin.val h0
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      have h1 : e 1 = 0 ∨ e 1 = 1 := by omega
      rcases h1 with h1 | h1
      · simpa using congrArg Fin.val h1
      · exact False.elim (hne (h1.trans h0.symm))

/-- Boolean normal form for an arbitrary permutation of the two-point fiber. -/
theorem finTwoPerm_bool_normalForm (e : Equiv.Perm (Fin 2)) :
    ∃ swaps : Bool,
      e = if swaps then Equiv.swap 0 1 else Equiv.refl (Fin 2) := by
  rcases finTwoPerm_eq_id_or_swap e with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- Connectedness excludes two identity arc monodromies.  Of the remaining
three Boolean patterns, exactly one swap gives the one-circle model (the two
choices differ only by interchanging arcs), while two swaps give the
two-circle model. -/
theorem twoArcMonodromy_nontrivial_classification
    (first second : Bool) (hconnected : first = true ∨ second = true) :
    (∃ swapArcs : Bool,
      (if swapArcs then (second, first) else (first, second)) = (true, false)) ∨
      (first = true ∧ second = true) := by
  cases first <;> cases second <;> simp_all

/-- Package the finite classification as a model choice while retaining the
precise normal form that the geometric realization must implement. -/
theorem twoArcMonodromy_model_exists
    (first second : Bool) (hconnected : first = true ∨ second = true) :
    ∃ model : DoubleCoverModel,
      (model = .oneCircle ∧
          ∃ swapArcs : Bool,
            (if swapArcs then (second, first) else (first, second)) =
              (true, false)) ∨
        (model = .twoCircle ∧ first = true ∧ second = true) := by
  rcases twoArcMonodromy_nontrivial_classification first second hconnected with h | h
  · exact ⟨.oneCircle, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨.twoCircle, Or.inr ⟨rfl, h⟩⟩

/-- Simultaneously replace the two lifted-arc permutations by Boolean
monodromies, transport the connectedness condition, and select the resulting
model.  The remaining classification work is therefore purely the geometric
realization of this normal form. -/
theorem twoArcPermMonodromy_model_exists
    (first second : Equiv.Perm (Fin 2))
    (hconnected : first ≠ Equiv.refl (Fin 2) ∨
      second ≠ Equiv.refl (Fin 2)) :
    ∃ firstSwaps secondSwaps model,
      first = (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      second = (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      ((model = DoubleCoverModel.oneCircle ∧
          ∃ swapArcs : Bool,
            (if swapArcs then (secondSwaps, firstSwaps)
              else (firstSwaps, secondSwaps)) = (true, false)) ∨
        (model = DoubleCoverModel.twoCircle ∧
          firstSwaps = true ∧ secondSwaps = true)) := by
  rcases finTwoPerm_bool_normalForm first with ⟨firstSwaps, hfirst⟩
  rcases finTwoPerm_bool_normalForm second with ⟨secondSwaps, hsecond⟩
  have hbool : firstSwaps = true ∨ secondSwaps = true := by
    rcases hconnected with h | h
    · left
      cases firstSwaps
      · exact False.elim (h hfirst)
      · rfl
    · right
      cases secondSwaps
      · exact False.elim (h hsecond)
      · rfl
  rcases twoArcMonodromy_model_exists firstSwaps secondSwaps hbool with
    ⟨model, hmodel⟩
  exact ⟨firstSwaps, secondSwaps, model, hfirst, hsecond, hmodel⟩

/-- If the graph generated by the two lifted arc permutations connects the
two labels of the fiber, at least one monodromy is nonidentity. -/
theorem twoArcPerm_nontrivial_of_reachable
    (first second : Equiv.Perm (Fin 2))
    (hreach : Relation.EqvGen
      (fun x y : Fin 2 ↦ first x = y ∨ second x = y) 0 1) :
    first ≠ Equiv.refl (Fin 2) ∨ second ≠ Equiv.refl (Fin 2) := by
  by_contra h
  push_neg at h
  rcases h with ⟨hfirst, hsecond⟩
  have heq : ∀ {x y : Fin 2},
      Relation.EqvGen (fun a b : Fin 2 ↦ first a = b ∨ second a = b) x y →
        x = y := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with hxy | hxy
        · simpa [hfirst] using hxy
        · simpa [hsecond] using hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  exact Fin.zero_ne_one (heq hreach)

/-- Reachability is the connected lifted-graph input needed by the discrete
model selector. -/
theorem twoArcPermMonodromy_model_exists_of_reachable
    (first second : Equiv.Perm (Fin 2))
    (hreach : Relation.EqvGen
      (fun x y : Fin 2 ↦ first x = y ∨ second x = y) 0 1) :
    ∃ firstSwaps secondSwaps model,
      first = (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      second = (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      ((model = DoubleCoverModel.oneCircle ∧
          ∃ swapArcs : Bool,
            (if swapArcs then (secondSwaps, firstSwaps)
              else (firstSwaps, secondSwaps)) = (true, false)) ∨
        (model = DoubleCoverModel.twoCircle ∧
          firstSwaps = true ∧ secondSwaps = true)) :=
  twoArcPermMonodromy_model_exists first second
    (twoArcPerm_nontrivial_of_reachable first second hreach)

/-- Combinatorial connectedness of the lifted two-arc action: no nonempty
forward-invariant subset of the fiber labels is proper. -/
def TwoArcActionConnected (first second : Equiv.Perm (Fin 2)) : Prop :=
  ∀ s : Set (Fin 2), s.Nonempty →
    (∀ x ∈ s, first x ∈ s ∧ second x ∈ s) → s = Set.univ

/-- On a two-point fiber, a nonidentity generator makes every nonempty
forward-invariant subset equal to the whole fiber. -/
theorem twoArcActionConnected_of_nontrivial
    (first second : Equiv.Perm (Fin 2))
    (h : first ≠ Equiv.refl (Fin 2) ∨ second ≠ Equiv.refl (Fin 2)) :
    TwoArcActionConnected first second := by
  intro s hs hinvariant
  rcases hs with ⟨x, hx⟩
  ext y
  simp only [Set.mem_univ, iff_true]
  rcases h with hfirst | hsecond
  · have hswap : first = Equiv.swap 0 1 :=
      (finTwoPerm_eq_id_or_swap first).resolve_left hfirst
    have hother := (hinvariant x hx).1
    rw [hswap] at hother
    fin_cases x <;> fin_cases y <;> simp_all
  · have hswap : second = Equiv.swap 0 1 :=
      (finTwoPerm_eq_id_or_swap second).resolve_left hsecond
    have hother := (hinvariant x hx).2
    rw [hswap] at hother
    fin_cases x <;> fin_cases y <;> simp_all

/-- Combinatorial connectedness makes the two labels reachable in the
equivalence closure generated by the lifted arcs. -/
theorem twoArc_reachable_of_actionConnected
    (first second : Equiv.Perm (Fin 2))
    (hconnected : TwoArcActionConnected first second) :
    Relation.EqvGen
      (fun x y : Fin 2 ↦ first x = y ∨ second x = y) 0 1 := by
  let orbit : Set (Fin 2) := {y | Relation.EqvGen
    (fun x z : Fin 2 ↦ first x = z ∨ second x = z) 0 y}
  have horbit0 : (0 : Fin 2) ∈ orbit := Relation.EqvGen.refl 0
  have hinvariant : ∀ x ∈ orbit, first x ∈ orbit ∧ second x ∈ orbit := by
    intro x hx
    change Relation.EqvGen
      (fun a b : Fin 2 ↦ first a = b ∨ second a = b) 0 x at hx
    constructor
    · change Relation.EqvGen
        (fun a b : Fin 2 ↦ first a = b ∨ second a = b) 0 (first x)
      exact Relation.EqvGen.trans 0 x (first x) hx
        (Relation.EqvGen.rel x (first x) (Or.inl rfl))
    · change Relation.EqvGen
        (fun a b : Fin 2 ↦ first a = b ∨ second a = b) 0 (second x)
      exact Relation.EqvGen.trans 0 x (second x) hx
        (Relation.EqvGen.rel x (second x) (Or.inr rfl))
  have horbit : orbit = Set.univ := hconnected orbit ⟨0, horbit0⟩ hinvariant
  have hone : (1 : Fin 2) ∈ orbit := by rw [horbit]; trivial
  exact hone

/-- Exact finite-fiber connectedness criterion for the two lifted arcs. -/
theorem twoArcActionConnected_iff_nontrivial
    (first second : Equiv.Perm (Fin 2)) :
    TwoArcActionConnected first second ↔
      first ≠ Equiv.refl (Fin 2) ∨ second ≠ Equiv.refl (Fin 2) := by
  constructor
  · intro h
    exact twoArcPerm_nontrivial_of_reachable first second
      (twoArc_reachable_of_actionConnected first second h)
  · exact twoArcActionConnected_of_nontrivial first second

/-- The exact discrete conclusion obtained once cover connectedness has been
transported to connectedness of its lifted two-arc action. -/
theorem twoArcPermMonodromy_model_exists_of_actionConnected
    (first second : Equiv.Perm (Fin 2))
    (hconnected : TwoArcActionConnected first second) :
    ∃ firstSwaps secondSwaps model,
      first = (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      second = (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
      ((model = DoubleCoverModel.oneCircle ∧
          ∃ swapArcs : Bool,
            (if swapArcs then (secondSwaps, firstSwaps)
              else (firstSwaps, secondSwaps)) = (true, false)) ∨
        (model = DoubleCoverModel.twoCircle ∧
          firstSwaps = true ∧ secondSwaps = true)) :=
  twoArcPermMonodromy_model_exists_of_reachable first second
    (twoArc_reachable_of_actionConnected first second hconnected)

/-! ## Fiber coordinates supplied by the degree-two hypothesis -/

/-- A map all of whose fibers have cardinality two is surjective. -/
theorem surjective_of_fiber_card_two
    {X Y : Type} (p : Y → X)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2) :
    Function.Surjective p := by
  intro x
  by_contra hx
  push_neg at hx
  have hempty : p ⁻¹' ({x} : Set X) = ∅ := by
    ext y
    simp [hx y]
  have h := hdegree x
  rw [hempty] at h
  simp at h

/-- The degree-two hypothesis supplies an actual `Fin 2` coordinate on each
fiber, the input needed to turn lifted arcs into permutations. -/
theorem fiber_equiv_fin_two
    {X Y : Type} (p : Y → X)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2)
    (x : X) :
    Nonempty ((p ⁻¹' ({x} : Set X)) ≃ Fin 2) := by
  have hcard0 : Nat.card (p ⁻¹' ({x} : Set X)) ≠ 0 := by
    rw [hdegree x]
    norm_num
  letI : Finite (p ⁻¹' ({x} : Set X)) := Nat.finite_of_card_ne_zero hcard0
  letI := Fintype.ofFinite (p ⁻¹' ({x} : Set X))
  exact ⟨Fintype.equivOfCardEq
    (by simpa [Nat.card_eq_fintype_card] using hdegree x)⟩

/-! ## Independence of the chosen fiber coordinate -/

/-- Relabeling a two-point fiber conjugates its monodromy, and conjugation
preserves whether that monodromy is nontrivial. -/
theorem conjugate_ne_refl_iff
    (label monodromy : Equiv.Perm (Fin 2)) :
    label.symm.trans (monodromy.trans label) ≠ Equiv.refl (Fin 2) ↔
      monodromy ≠ Equiv.refl (Fin 2) := by
  constructor
  · intro h hmono
    apply h
    subst monodromy
    ext x
    simp
  · intro h hconj
    apply h
    ext x
    have hx := congrArg (fun f : Equiv.Perm (Fin 2) ↦ f (label x)) hconj
    have hxl : label (monodromy x) = label x := by simpa using hx
    exact congrArg Fin.val (label.injective hxl)

/-- Connectedness of the lifted two-arc action is independent of the chosen
`Fin 2` coordinate on the fiber. -/
theorem twoArcActionConnected_conjugate
    (label first second : Equiv.Perm (Fin 2)) :
    TwoArcActionConnected
        (label.symm.trans (first.trans label))
        (label.symm.trans (second.trans label)) ↔
      TwoArcActionConnected first second := by
  rw [twoArcActionConnected_iff_nontrivial,
    twoArcActionConnected_iff_nontrivial,
    conjugate_ne_refl_iff, conjugate_ne_refl_iff]

/-! ## From lifted fiber transports to the two-arc action -/

/-- Express a self-equivalence of an actual two-point fiber in a chosen
`Fin 2` coordinate. -/
def labeledFiberMonodromy {F : Type} (label : F ≃ Fin 2)
    (transport : Equiv.Perm F) : Equiv.Perm (Fin 2) :=
  label.symm.trans (transport.trans label)

/-- Passing from an actual fiber transport to its labeled permutation
preserves precisely whether the transport is the identity. -/
theorem labeledFiberMonodromy_ne_refl_iff
    {F : Type} (label : F ≃ Fin 2) (transport : Equiv.Perm F) :
    labeledFiberMonodromy label transport ≠ Equiv.refl (Fin 2) ↔
      transport ≠ Equiv.refl F := by
  constructor
  · intro h htransport
    apply h
    subst transport
    ext x
    simp [labeledFiberMonodromy]
  · intro h hlabeled
    apply h
    ext x
    have hx := congrArg
      (fun f : Equiv.Perm (Fin 2) ↦ f (label x)) hlabeled
    have hxl : label (transport x) = label x := by
      simpa [labeledFiberMonodromy] using hx
    exact label.injective hxl

/-- Two lifted self-transports of a cardinal-two fiber give a connected
two-arc action exactly when at least one transport is nonidentity. -/
theorem labeledTwoTransport_actionConnected_iff
    {F : Type} (label : F ≃ Fin 2) (first second : Equiv.Perm F) :
    TwoArcActionConnected (labeledFiberMonodromy label first)
        (labeledFiberMonodromy label second) ↔
      first ≠ Equiv.refl F ∨ second ≠ Equiv.refl F := by
  rw [twoArcActionConnected_iff_nontrivial,
    labeledFiberMonodromy_ne_refl_iff,
    labeledFiberMonodromy_ne_refl_iff]

/-- A cardinal-two actual fiber together with two transports, one of them
nonidentity, canonically reaches the normalized discrete model selector after
choosing a fiber coordinate. -/
theorem twoArcModel_exists_of_fiber_transports
    {X Y : Type} (p : Y → X)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2)
    (x : X)
    (first second : Equiv.Perm (p ⁻¹' ({x} : Set X)))
    (hconnected : first ≠ Equiv.refl _ ∨ second ≠ Equiv.refl _) :
    ∃ label : (p ⁻¹' ({x} : Set X)) ≃ Fin 2,
      ∃ firstSwaps secondSwaps model,
        labeledFiberMonodromy label first =
          (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        labeledFiberMonodromy label second =
          (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        ((model = DoubleCoverModel.oneCircle ∧
            ∃ swapArcs : Bool,
              (if swapArcs then (secondSwaps, firstSwaps)
                else (firstSwaps, secondSwaps)) = (true, false)) ∨
          (model = DoubleCoverModel.twoCircle ∧
            firstSwaps = true ∧ secondSwaps = true)) := by
  rcases fiber_equiv_fin_two p hdegree x with ⟨label⟩
  have haction : TwoArcActionConnected
      (labeledFiberMonodromy label first)
      (labeledFiberMonodromy label second) :=
    (labeledTwoTransport_actionConnected_iff label first second).2 hconnected
  rcases twoArcPermMonodromy_model_exists_of_actionConnected
      (labeledFiberMonodromy label first)
      (labeledFiberMonodromy label second) haction with
    ⟨firstSwaps, secondSwaps, model, hfirst, hsecond, hmodel⟩
  exact ⟨label, firstSwaps, secondSwaps, model, hfirst, hsecond, hmodel⟩

/-! ## Covering-path transport on actual fibers -/

/-- Path lifting for a covering map, upgraded from Mathlib's bijective
monodromy function to an equivalence between the literal endpoint fibers. -/
noncomputable def coveringPathFiberEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) {x y : X}
    (γ : Path.Homotopic.Quotient x y) :
    (p ⁻¹' ({x} : Set X)) ≃ (p ⁻¹' ({y} : Set X)) :=
  Equiv.ofBijective (hp.monodromy γ) (hp.monodromy_bijective γ)

@[simp] theorem coveringPathFiberEquiv_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) {x y : X}
    (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' ({x} : Set X)) :
    coveringPathFiberEquiv p hp γ e = hp.monodromy γ e := rfl

/-- In a path-connected total space, any two points are related by covering
monodromy along the projection of an actual path upstairs.  This is the
topological transitivity input needed to obtain a moved endpoint in a
two-point fiber. -/
theorem coveringMonodromy_transitive_of_pathConnected
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (p : Y → X) (hp : IsCoveringMap p) (a b : Y) :
    ∃ γ : Path.Homotopic.Quotient (p a) (p b),
      hp.monodromy γ (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X)) =
        (⟨b, rfl⟩ : p ⁻¹' ({p b} : Set X)) := by
  obtain ⟨δ⟩ := PathConnectedSpace.joined a b
  let δq : Path.Homotopic.Quotient a b := Quotient.mk'' δ
  exact ⟨δq.map ⟨p, hp.continuous⟩, hp.monodromy_map δq⟩

/-- The form used by the supplied connected cover: once local path
connectedness of its total space is established from covering charts,
connectedness upgrades to path connectedness and hence to transitive
monodromy on endpoints. -/
theorem coveringMonodromy_transitive_of_connected_locPath
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace Y] [LocPathConnectedSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) (a b : Y) :
    ∃ γ : Path.Homotopic.Quotient (p a) (p b),
      hp.monodromy γ (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X)) =
        (⟨b, rfl⟩ : p ⁻¹' ({p b} : Set X)) := by
  letI : PathConnectedSpace Y := PathConnectedSpace.of_locPathConnectedSpace
  exact coveringMonodromy_transitive_of_pathConnected p hp a b

/-- Connected coverings of a locally path-connected base have endpoint-
transitive monodromy; the covering charts supply the local hypothesis. -/
theorem coveringMonodromy_transitive_of_connected
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [ConnectedSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) (a b : Y) :
    ∃ γ : Path.Homotopic.Quotient (p a) (p b),
      hp.monodromy γ (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X)) =
        (⟨b, rfl⟩ : p ⁻¹' ({p b} : Set X)) := by
  letI : LocPathConnectedSpace Y := IsCoveringMap.locPathConnectedSpace hp
  exact coveringMonodromy_transitive_of_connected_locPath p hp a b

/-- In a connected two-sheeted covering of a locally path-connected base,
the two distinct points over any basepoint are related by monodromy.  The
endpoint equalities expose the remaining cast needed to package this as a
literal based loop. -/
theorem exists_distinct_fiber_points_related_by_monodromy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [ConnectedSpace Y]
    (p : Y → X) (hp : IsCoveringMap p)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2) (x : X) :
    ∃ a b : Y, p a = x ∧ p b = x ∧ a ≠ b ∧
      ∃ γ : Path.Homotopic.Quotient (p a) (p b),
        hp.monodromy γ (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X)) =
          (⟨b, rfl⟩ : p ⁻¹' ({p b} : Set X)) := by
  obtain ⟨label⟩ := fiber_equiv_fin_two p hdegree x
  let a : p ⁻¹' ({x} : Set X) := label.symm 0
  let b : p ⁻¹' ({x} : Set X) := label.symm 1
  have ha : p a.1 = x := a.2
  have hb : p b.1 = x := b.2
  have hab : a ≠ b := by
    intro h
    have := congrArg label h
    simpa [a, b] using this
  refine ⟨a.1, b.1, ha, hb, ?_, ?_⟩
  · intro h
    exact hab (Subtype.ext h)
  · exact coveringMonodromy_transitive_of_connected p hp a.1 b.1

/-- Casting a constant path along an endpoint equality changes only the fiber
type: its covering monodromy preserves the underlying total-space point. -/
theorem monodromy_cast_refl_val
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) {x y : X} (h : x = y)
    (e : p ⁻¹' ({y} : Set X)) :
    (hp.monodromy ((Path.Homotopic.Quotient.refl y).cast rfl h) e).1 = e.1 := by
  change hp.liftPath _ e.1 _ 1 = e.1
  exact DFunLike.congr_fun (hp.liftPath_const e.2.symm) 1

/-- Connected degree-two covering monodromy supplies a genuinely nontrivial
loop at a point lying over the requested basepoint. -/
theorem exists_moved_covering_loop_over_connected
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [ConnectedSpace Y]
    (p : Y → X) (hp : IsCoveringMap p)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2) (x : X) :
    ∃ a : Y, p a = x ∧ ∃ γ : Path.Homotopic.Quotient (p a) (p a),
      hp.monodromy γ (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X)) ≠ ⟨a, rfl⟩ := by
  obtain ⟨a, b, ha, hb, hab, γ, hγ⟩ :=
    exists_distinct_fiber_points_related_by_monodromy p hp hdegree x
  have hba : p b = p a := hb.trans ha.symm
  let δ : Path.Homotopic.Quotient (p b) (p a) :=
    (Path.Homotopic.Quotient.refl (p b)).cast rfl hba.symm
  refine ⟨a, ha, γ.trans δ, ?_⟩
  intro heq
  have ht := hp.monodromy_trans_apply γ δ
    (⟨a, rfl⟩ : p ⁻¹' ({p a} : Set X))
  rw [hγ] at ht
  apply hab
  have hδ : (hp.monodromy δ (⟨b, rfl⟩ : p ⁻¹' ({p b} : Set X))).1 = b :=
    monodromy_cast_refl_val p hp hba.symm ⟨b, rfl⟩
  exact (congrArg Subtype.val (ht.symm.trans heq)).symm.trans hδ

/-- Transport along the constant path is the identity equivalence of the
literal fiber. -/
theorem coveringPathFiberEquiv_refl
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) (x : X) :
    coveringPathFiberEquiv p hp (.refl x) =
      Equiv.refl (p ⁻¹' ({x} : Set X)) := by
  apply Equiv.ext
  intro e
  exact congrFun hp.monodromy_refl e

/-- Fiber transport respects concatenation, with the same source-to-target
orientation as path concatenation. -/
theorem coveringPathFiberEquiv_trans
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) {x y z : X}
    (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) :
    coveringPathFiberEquiv p hp (γ.trans δ) =
      (coveringPathFiberEquiv p hp γ).trans
        (coveringPathFiberEquiv p hp δ) := by
  apply Equiv.ext
  intro e
  exact hp.monodromy_trans_apply γ δ e

/-- A fiber self-transport is nontrivial exactly when it moves an actual
point of the fiber.  This exposes the concrete endpoint witness produced by
path lifting to the finite model selector. -/
theorem fiberTransport_ne_refl_iff_exists_moved
    {F : Type} (transport : Equiv.Perm F) :
    transport ≠ Equiv.refl F ↔ ∃ e : F, transport e ≠ e := by
  constructor
  · contrapose!
    intro h
    ext e
    exact h e
  · rintro ⟨e, he⟩ h
    apply he
    simp [h]

/-- If one of two lifted loops moves a literal fiber point, their covering
monodromies select one of the two normalized double-cover models. -/
theorem twoArcModel_exists_of_moved_covering_loop
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2)
    (x : X) (firstLoop secondLoop : Path.Homotopic.Quotient x x)
    (hmoved : (∃ e, coveringPathFiberEquiv p hp firstLoop e ≠ e) ∨
      ∃ e, coveringPathFiberEquiv p hp secondLoop e ≠ e) :
    ∃ label : (p ⁻¹' ({x} : Set X)) ≃ Fin 2,
      ∃ firstSwaps secondSwaps model,
        labeledFiberMonodromy label (coveringPathFiberEquiv p hp firstLoop) =
          (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        labeledFiberMonodromy label (coveringPathFiberEquiv p hp secondLoop) =
          (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        ((model = DoubleCoverModel.oneCircle ∧
            ∃ swapArcs : Bool,
              (if swapArcs then (secondSwaps, firstSwaps)
                else (firstSwaps, secondSwaps)) = (true, false)) ∨
          (model = DoubleCoverModel.twoCircle ∧
            firstSwaps = true ∧ secondSwaps = true)) := by
  apply twoArcModel_exists_of_fiber_transports p hdegree x
    (coveringPathFiberEquiv p hp firstLoop)
    (coveringPathFiberEquiv p hp secondLoop)
  rcases hmoved with hfirst | hsecond
  · exact Or.inl ((fiberTransport_ne_refl_iff_exists_moved _).2 hfirst)
  · exact Or.inr ((fiberTransport_ne_refl_iff_exists_moved _).2 hsecond)

/-- Evaluation of a word in the two fixed complementary-arc transports. -/
def twoArcTransportWord {F : Type} (first second : Equiv.Perm F) :
    List Bool → Equiv.Perm F
  | [] => Equiv.refl F
  | b :: word =>
      (if b then first else second).trans (twoArcTransportWord first second word)

theorem twoArcTransportWord_eq_refl
    {F : Type} (first second : Equiv.Perm F)
    (hfirst : first = Equiv.refl F) (hsecond : second = Equiv.refl F) :
    ∀ word, twoArcTransportWord first second word = Equiv.refl F := by
  subst first
  subst second
  intro word
  induction word with
  | nil => rfl
  | cons b word ih => cases b <;> simp [twoArcTransportWord, ih]

/-- If a nontrivial transport is a word in the two fixed arc transports,
then at least one of those actual arc transports is nonidentity. -/
theorem twoArcTransport_nontrivial_of_generated
    {F : Type} (first second transport : Equiv.Perm F)
    (hgenerated : ∃ word, transport = twoArcTransportWord first second word)
    (hne : transport ≠ Equiv.refl F) :
    first ≠ Equiv.refl F ∨ second ≠ Equiv.refl F := by
  by_contra h
  push_neg at h
  rcases h with ⟨hfirst, hsecond⟩
  rcases hgenerated with ⟨word, rfl⟩
  exact hne (twoArcTransportWord_eq_refl first second hfirst hsecond word)

/-- Two loop classes in the base now supply the actual fiber transports used
by the normalized model selector. -/
theorem twoArcModel_exists_of_covering_loops
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p)
    (hdegree : ∀ x : X, Nat.card (p ⁻¹' ({x} : Set X)) = 2)
    (x : X) (firstLoop secondLoop : Path.Homotopic.Quotient x x)
    (hconnected : coveringPathFiberEquiv p hp firstLoop ≠ Equiv.refl _ ∨
      coveringPathFiberEquiv p hp secondLoop ≠ Equiv.refl _) :
    ∃ label : (p ⁻¹' ({x} : Set X)) ≃ Fin 2,
      ∃ firstSwaps secondSwaps model,
        labeledFiberMonodromy label (coveringPathFiberEquiv p hp firstLoop) =
          (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        labeledFiberMonodromy label (coveringPathFiberEquiv p hp secondLoop) =
          (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        ((model = DoubleCoverModel.oneCircle ∧
            ∃ swapArcs : Bool,
              (if swapArcs then (secondSwaps, firstSwaps)
                else (firstSwaps, secondSwaps)) = (true, false)) ∨
          (model = DoubleCoverModel.twoCircle ∧
            firstSwaps = true ∧ secondSwaps = true)) :=
  twoArcModel_exists_of_fiber_transports p hdegree x
    (coveringPathFiberEquiv p hp firstLoop)
    (coveringPathFiberEquiv p hp secondLoop) hconnected

#print axioms twoArcMonodromy_nontrivial_classification
#print axioms twoArcMonodromy_model_exists
#print axioms finTwoPerm_eq_id_or_swap
#print axioms finTwoPerm_bool_normalForm
#print axioms twoArcPermMonodromy_model_exists
#print axioms twoArcPerm_nontrivial_of_reachable
#print axioms twoArcPermMonodromy_model_exists_of_reachable
#print axioms twoArc_reachable_of_actionConnected
#print axioms twoArcActionConnected_iff_nontrivial
#print axioms twoArcPermMonodromy_model_exists_of_actionConnected
#print axioms surjective_of_fiber_card_two
#print axioms fiber_equiv_fin_two
#print axioms conjugate_ne_refl_iff
#print axioms twoArcActionConnected_conjugate
#print axioms labeledFiberMonodromy_ne_refl_iff
#print axioms labeledTwoTransport_actionConnected_iff
#print axioms twoArcModel_exists_of_fiber_transports
#print axioms coveringPathFiberEquiv_apply
#print axioms coveringMonodromy_transitive_of_pathConnected
#print axioms coveringMonodromy_transitive_of_connected_locPath
#print axioms IsLocalHomeomorph.locPathConnectedSpace
#print axioms IsCoveringMap.locPathConnectedSpace
#print axioms coveringMonodromy_transitive_of_connected
#print axioms exists_distinct_fiber_points_related_by_monodromy
#print axioms monodromy_cast_refl_val
#print axioms exists_moved_covering_loop_over_connected
#print axioms coveringPathFiberEquiv_refl
#print axioms coveringPathFiberEquiv_trans
#print axioms twoArcModel_exists_of_covering_loops
#print axioms fiberTransport_ne_refl_iff_exists_moved
#print axioms twoArcModel_exists_of_moved_covering_loop
#print axioms twoArcTransportWord_eq_refl
#print axioms twoArcTransport_nontrivial_of_generated

end ConstructionTargets.t97A03Closure
