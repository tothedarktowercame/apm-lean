import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

/-!
# Simply connected open covers

Infrastructure toward the two-open-set gluing theorem for simple connectivity.
The first lemma isolates the local step: paths with the same endpoints that
remain in one simply connected set are homotopic in the ambient space.
-/

open Set

noncomputable section

variable {X : Type*} [TopologicalSpace X]

open scoped unitInterval

/-- Select one of two sets without putting the selection proof into the type of
points or paths. -/
def twoChart (U V : Set X) (side : Bool) : Set X :=
  if side then U else V

/-- Two paths with the same endpoints that remain in a simply connected set
are homotopic in the ambient space. -/
theorem IsSimplyConnected.pathsHomotopic_of_mem {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    Path.Homotopic p q := by
  let xs : s := ⟨x, p.source ▸ hp 0⟩
  let ys : s := ⟨y, p.target ▸ hp 1⟩
  let ps : Path xs ys :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let qs : Path xs ys :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have hsub : Path.Homotopic ps qs := by
    letI : SimplyConnectedSpace s := hs
    exact SimplyConnectedSpace.paths_homotopic ps qs
  simpa [ps, qs] using hsub.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))

/-- A vertex lying in two incident charts can be connected to a fixed overlap
point by a path lying in the intersection of those charts.  The chart-label
case split is confined to the proof of this existential; its result has a
uniform, non-dependent type. -/
theorem exists_path_mem_twoChart_inter {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c x : X} (hc : c ∈ U ∩ V)
    (i j : Bool) (hxi : x ∈ twoChart U V i) (hxj : x ∈ twoChart U V j) :
    ∃ p : Path x c, ∀ t, p t ∈ twoChart U V i ∩ twoChart U V j := by
  cases i <;> cases j
  · have hxV : x ∈ V := by simpa [twoChart] using hxi
    have h := hV.isPathConnected.joinedIn x hxV c hc.2
    exact ⟨h.somePath, fun t ↦ by simpa [twoChart] using
      (⟨h.somePath_mem t, h.somePath_mem t⟩ : h.somePath t ∈ V ∩ V)⟩
  · have hxV : x ∈ V := by simpa [twoChart] using hxi
    have hxU : x ∈ U := by simpa [twoChart] using hxj
    have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩
    have h := hUV.joinedIn x hxUV c hc
    exact ⟨h.somePath, fun t ↦ by simpa [twoChart, and_comm] using h.somePath_mem t⟩
  · have hxU : x ∈ U := by simpa [twoChart] using hxi
    have hxV : x ∈ V := by simpa [twoChart] using hxj
    have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩
    have h := hUV.joinedIn x hxUV c hc
    exact ⟨h.somePath, fun t ↦ by simpa [twoChart] using h.somePath_mem t⟩
  · have hxU : x ∈ U := by simpa [twoChart] using hxi
    have h := hU.isPathConnected.joinedIn x hxU c hc.1
    exact ⟨h.somePath, fun t ↦ by simpa [twoChart] using
      (⟨h.somePath_mem t, h.somePath_mem t⟩ : h.somePath t ∈ U ∩ U)⟩

/-- Uniformly choose the interior-vertex connectors after proving their
existence.  Neither the connector type nor its range certificate branches on
the adjacent chart labels. -/
theorem exists_twoChart_connectors {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c : X} (hc : c ∈ U ∩ V)
    (vertex : ℕ → X) (side : ℕ → Bool)
    (hleft : ∀ k, vertex (k + 1) ∈ twoChart U V (side k))
    (hright : ∀ k, vertex (k + 1) ∈ twoChart U V (side (k + 1))) :
    ∃ conn : ∀ k, Path (vertex (k + 1)) c,
      ∀ k t, conn k t ∈
        twoChart U V (side k) ∩ twoChart U V (side (k + 1)) := by
  choose conn hconn using fun k ↦
    exists_path_mem_twoChart_inter hU hV hUV hc
      (side k) (side (k + 1)) (hleft k) (hright k)
  exact ⟨conn, hconn⟩

/-- Connector edges telescope after passing to path-homotopy classes. -/
theorem Path.Homotopic.concat_connector_telescope {n : ℕ}
    (point : Fin (n + 1) → X) (c : X)
    (conn : (k : Fin (n + 1)) → Path (point k) c) :
    Path.Homotopic
      (Path.concat point fun k ↦
        (conn k.castSucc).trans (conn k.succ).symm)
      ((conn 0).trans (conn (Fin.last n)).symm) := by
  induction n with
  | zero =>
      simpa [Path.concat_zero] using
        (⟨Path.Homotopy.reflTransSymm (conn 0)⟩ :
          Path.Homotopic (Path.refl _) ((conn 0).trans (conn 0).symm))
  | succ n ih =>
      rw [Path.concat_succ]
      simp_rw [Fin.succ_castSucc]
      refine (Path.Homotopic.hcomp
        (ih (point ∘ Fin.castSucc) (fun k ↦ conn k.castSucc))
        (Path.Homotopic.refl _)).trans ?_
      let a := conn 0
      let b := conn (Fin.last n).castSucc
      let d := conn (Fin.last (n + 1))
      have hinner : Path.Homotopic (b.symm.trans (b.trans d.symm)) d.symm :=
        (Path.Homotopic.trans_assoc b.symm b d.symm).symm.trans <|
          (Path.Homotopic.hcomp (Path.Homotopic.symm_trans b)
            (Path.Homotopic.refl d.symm)).trans
              (Path.Homotopic.refl_trans d.symm)
      exact (Path.Homotopic.trans_assoc a b.symm (b.trans d.symm)).trans <|
        Path.Homotopic.hcomp (Path.Homotopic.refl a) hinner

/-- Choose all connectors for a positive-length cyclic subdivision at once.
The endpoint identification is part of the existential result, so no
chart-dependent path type escapes the construction. -/
theorem exists_cyclic_twoChart_connectors {U V : Set X}
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {c : X} (hc : c ∈ U ∩ V)
    {n : ℕ} (point : Fin (n + 2) → X) (side : Fin (n + 1) → Bool)
    (hpiece : ∀ k, point k.castSucc ∈ twoChart U V (side k) ∧
      point k.succ ∈ twoChart U V (side k))
    (hcycle : point 0 = point (Fin.last (n + 1))) :
    ∃ conn : (k : Fin (n + 2)) → Path (point k) c,
      (∀ k t, conn k.castSucc t ∈ twoChart U V (side k) ∧
        conn k.succ t ∈ twoChart U V (side k)) ∧
      Path.Homotopic (conn 0)
        ((conn (Fin.last (n + 1))).cast hcycle rfl) := by
  have hxFirst : point 0 ∈ twoChart U V (side 0) := (hpiece 0).1
  have hxLast : point 0 ∈ twoChart U V (side (Fin.last n)) := by
    rw [hcycle]
    exact (hpiece (Fin.last n)).2
  obtain ⟨boundary, hboundary⟩ :=
    exists_path_mem_twoChart_inter hU hV hUV hc
      (side 0) (side (Fin.last n)) hxFirst hxLast
  have hinter : ∀ k : Fin n, ∃ p : Path (point k.succ.castSucc) c,
      ∀ t, p t ∈ twoChart U V (side k.castSucc) ∩
        twoChart U V (side k.succ) := by
    intro k
    apply exists_path_mem_twoChart_inter hU hV hUV hc
    · simpa only [Fin.succ_castSucc] using (hpiece k.castSucc).2
    · exact (hpiece k.succ).1
  choose interior hinter_mem using hinter
  let boundaryLast : Path (point (Fin.last (n + 1))) c :=
    boundary.cast hcycle.symm rfl
  let conn : (k : Fin (n + 2)) → Path (point k) c :=
    Fin.cases boundary fun i ↦
      Fin.lastCases boundaryLast (fun k ↦ interior k) i
  have conn_last : conn (Fin.last n).succ = boundaryLast := by
    simp only [conn, Fin.cases_succ, Fin.lastCases_last]
  refine ⟨conn, ?_, ?_⟩
  · intro k t
    constructor
    · refine Fin.cases ?_ (fun j ↦ ?_) k
      · simpa [conn] using (hboundary t).1
      · rw [← Fin.succ_castSucc]
        simpa [conn] using (hinter_mem j t).2
    · refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · rw [conn_last]
        simpa [boundaryLast, Path.cast_coe] using (hboundary t).2
      · rw [Fin.succ_castSucc]
        simpa [conn] using (hinter_mem j t).1
  · have hzero : conn 0 = boundary := by rfl
    have hlast : (conn (Fin.last (n + 1))).cast hcycle rfl = boundary := by
      apply Path.ext
      simpa only [← Fin.succ_last, conn_last, boundaryLast, Path.cast_coe]
    rw [hzero, hlast]

/-- Finite, positive-length wrapper around Mathlib's `ℕ`-indexed subdivision
of the unit interval.  Cover labels are chosen before restricting the
subdivision to `Fin`, avoiding dependent reindexing. -/
theorem exists_fin_Icc_subset_open_cover_unitInterval {ι : Type*}
    {cover : ι → Set unitInterval} (hopen : ∀ i, IsOpen (cover i))
    (hcover : (Set.univ : Set unitInterval) ⊆ ⋃ i, cover i) :
    ∃ n : ℕ, ∃ t : Fin (n + 2) → unitInterval,
      ∃ side : Fin (n + 1) → ι,
        t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
          Monotone t ∧ ∀ k, Set.Icc (t k.castSucc) (t k.succ) ⊆ cover (side k) := by
  obtain ⟨u, hu0, humono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  choose label hlabel using hsub
  refine ⟨m, fun k ↦ u k.val, fun k ↦ label k.val, ?_, ?_, ?_, ?_⟩
  · exact hu0
  · exact hm (m + 1) (Nat.le_succ m)
  · intro i j hij
    exact humono (by exact_mod_cast hij)
  · intro k
    simpa only [Fin.val_castSucc, Fin.val_succ] using hlabel k.val

/-- A space covered by two open simply connected sets with path-connected
overlap is simply connected. -/
theorem simplyConnectedSpace_of_union_eq_univ {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : SimplyConnectedSpace X := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · rw [pathConnectedSpace_iff_univ, ← hcover]
    exact hU.isPathConnected.union hV.isPathConnected hUV.nonempty
  · intro x p
    obtain ⟨c, hc⟩ := hUV.nonempty
    let cover : Bool → Set unitInterval := fun b ↦
      if b then p ⁻¹' U else p ⁻¹' V
    have cover_open : ∀ b, IsOpen (cover b) := by
      intro b
      cases b <;> simp [cover, hUopen, hVopen, IsOpen.preimage p.continuous]
    have cover_all : (Set.univ : Set unitInterval) ⊆ ⋃ b, cover b := by
      intro t _
      have hpt : p t ∈ U ∪ V := by rw [hcover]; trivial
      rcases hpt with htU | htV
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [cover] using htU⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [cover] using htV⟩
    obtain ⟨n, t, side, ht0, ht1, htmono, hsub⟩ :=
      exists_fin_Icc_subset_open_cover_unitInterval cover_open cover_all
    let point : Fin (n + 2) → X := fun k ↦ p (t k)
    have hpiece : ∀ k, point k.castSucc ∈ twoChart U V (side k) ∧
        point k.succ ∈ twoChart U V (side k) := by
      intro k
      have hle : t k.castSucc ≤ t k.succ := htmono k.castSucc_le_succ
      have hl := hsub k ⟨le_rfl, hle⟩
      have hr := hsub k ⟨hle, le_rfl⟩
      cases hside : side k <;>
        simp [cover, hside] at hl hr <;>
        simpa [point, twoChart, hside] using And.intro hl hr
    have hcycle : point 0 = point (Fin.last (n + 1)) := by
      simp only [point, ht0, ht1, p.source, p.target]
    obtain ⟨conn, hconn, hconnCycle⟩ :=
      exists_cyclic_twoChart_connectors hU hV hUV hc point side hpiece hcycle
    let piece : (k : Fin (n + 1)) →
        Path (point k.castSucc) (point k.succ) := fun k ↦
      p.subpath (t k.castSucc) (t k.succ)
    have piece_mem (k : Fin (n + 1)) (s : unitInterval) :
        piece k s ∈ twoChart U V (side k) := by
      have hs : piece k s ∈ Set.range (piece k) := Set.mem_range_self s
      simp only [piece] at hs
      rw [Path.range_subpath_of_le p _ _ (htmono k.castSucc_le_succ)] at hs
      rcases hs with ⟨r, hr, hrs⟩
      have hm := hsub k hr
      rw [← hrs]
      cases hside : side k <;> simpa [cover, twoChart, hside] using hm
    have replacement_mem (k : Fin (n + 1)) (s : unitInterval) :
        ((conn k.castSucc).trans (conn k.succ).symm) s ∈
          twoChart U V (side k) := by
      rw [Path.trans_apply]
      split_ifs
      · exact (hconn k _).1
      · exact (hconn k _).2
    have hreplace (k : Fin (n + 1)) : Path.Homotopic (piece k)
        ((conn k.castSucc).trans (conn k.succ).symm) := by
      cases hside : side k
      · apply hV.pathsHomotopic_of_mem
        · intro s; simpa [twoChart, hside] using piece_mem k s
        · intro s; simpa [twoChart, hside] using replacement_mem k s
      · apply hU.pathsHomotopic_of_mem
        · intro s; simpa [twoChart, hside] using piece_mem k s
        · intro s; simpa [twoChart, hside] using replacement_mem k s
    have hconcat := Path.Homotopic.concat_hcomp point piece
      (fun k ↦ (conn k.castSucc).trans (conn k.succ).symm) hreplace
    have htelescope := Path.Homotopic.concat_connector_telescope point c conn
    have hparts := Path.Homotopic.concat_subpath p t
    have hx0 : point 0 = x := by simp [point, ht0, p.source]
    have hxlast : point (Fin.last (n + 1)) = x := by simp [point, ht1, p.target]
    let pCast : Path (point 0) (point (Fin.last (n + 1))) :=
      p.cast hx0 hxlast
    have hparts' : Path.Homotopic (Path.concat point piece) pCast := by
      have hend : p.subpath (t 0) (t (Fin.last (n + 1))) = pCast := by
        ext s
        simp [Path.subpath, ht0, ht1, pCast, Path.cast_coe]
      simpa [point, piece] using hparts.trans (hend ▸ Path.Homotopic.refl pCast)
    let cycleRefl : Path (point 0) (point (Fin.last (n + 1))) :=
      (Path.refl (point 0)).cast rfl hcycle.symm
    have htail : Path.Homotopic
        ((conn 0).trans (conn (Fin.last (n + 1))).symm) cycleRefl := by
      let last := conn (Fin.last (n + 1))
      have hcastTrans : (last.cast hcycle rfl).trans last.symm =
          (last.trans last.symm).cast hcycle rfl := by
        apply Path.ext
        simp [Path.trans_apply, Path.cast_coe]
      have hcastRefl : (Path.refl (point (Fin.last (n + 1)))).cast hcycle rfl =
          cycleRefl := by
        apply Path.ext
        exact funext fun _ ↦ hcycle.symm
      refine (Path.Homotopic.hcomp hconnCycle (Path.Homotopic.refl last.symm)).trans ?_
      rw [hcastTrans]
      exact (Path.Homotopic.pathCast (Path.Homotopic.trans_symm last) hcycle rfl).trans <|
        hcastRefl ▸ Path.Homotopic.refl cycleRefl
    have hall := hparts'.symm.trans (hconcat.trans (htelescope.trans htail))
    have hall' := Path.Homotopic.pathCast hall hx0.symm hxlast.symm
    have hpCast : pCast.cast hx0.symm hxlast.symm = p := by
      apply Path.ext
      simp [pCast, Path.cast_coe]
    have hrefl : cycleRefl.cast hx0.symm hxlast.symm = Path.refl x := by
      apply Path.ext
      exact funext fun _ ↦ hx0
    rw [hpCast, hrefl] at hall'
    exact hall'

/-- A unit sphere is simply connected once the orthogonal complement of one
unit pole has real rank greater than one. -/
theorem simplyConnectedSpace_sphere_of_pole
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1)
    (hrank : 1 < Module.rank ℝ (ℝ ∙ v)ᗮ) :
    SimplyConnectedSpace (Metric.sphere (0 : E) 1) := by
  let north : Metric.sphere (0 : E) 1 := ⟨v, by simpa [mem_sphere_zero_iff_norm]⟩
  let south : Metric.sphere (0 : E) 1 := -north
  let eN := stereographic hv
  let eS := stereographic (show ‖-v‖ = 1 by simpa using hv)
  have hsouth : eN south = 0 := by simpa [north, south, eN] using stereographic_apply_neg north
  have hnorth : eS north = 0 := by simpa [north, south, eS] using stereographic_neg_apply north
  have hNsimple : IsSimplyConnected eN.source := by
    let e := eN.toHomeomorphSourceTarget
    let et : eN.target ≃ₜ (ℝ ∙ v)ᗮ :=
      (Homeomorph.setCongr (by simp [eN])).trans (Homeomorph.Set.univ _)
    letI : SimplyConnectedSpace eN.target :=
      et.toHomotopyEquiv.simplyConnectedSpace
    exact e.toHomotopyEquiv.simplyConnectedSpace
  have hSsimple : IsSimplyConnected eS.source := by
    let e := eS.toHomeomorphSourceTarget
    let et : eS.target ≃ₜ (ℝ ∙ (-v))ᗮ :=
      (Homeomorph.setCongr (by simp [eS])).trans (Homeomorph.Set.univ _)
    letI : SimplyConnectedSpace eS.target :=
      et.toHomotopyEquiv.simplyConnectedSpace
    exact e.toHomotopyEquiv.simplyConnectedSpace
  have hopenN : IsOpen eN.source := eN.open_source
  have hopenS : IsOpen eS.source := eS.open_source
  have hns : north ≠ south := by
    intro h
    have hvneg : v = -v := congrArg Subtype.val h
    have hv0 : v = 0 := by
      have htwo : (2 : ℝ) • v = 0 := by
        calc
          (2 : ℝ) • v = v + v := two_smul ℝ v
          _ = -v + v := congrArg (fun z ↦ z + v) hvneg
          _ = 0 := neg_add_cancel v
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [hv0, norm_zero] at hv
    norm_num at hv
  have hcover : eN.source ∪ eS.source = Set.univ := by
    change (stereographic hv).source ∪
      (stereographic (show ‖-v‖ = 1 by simpa using hv)).source = Set.univ
    rw [stereographic_source, stereographic_source]
    ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    by_cases hx : x = north
    · exact Or.inr fun hxs ↦ hns (hx.symm.trans hxs)
    · exact Or.inl hx
  have hoverlap : IsPathConnected (eN.source ∩ eS.source) := by
    have hpunct : IsPathConnected ({0}ᶜ : Set (ℝ ∙ v)ᗮ) :=
      isPathConnected_compl_singleton_of_one_lt_rank hrank 0
    have himage := hpunct.image'
      (eN.symm.continuousOn.mono (by intro; simp [eN]))
    have hset : eN.symm '' ({0}ᶜ : Set (ℝ ∙ v)ᗮ) = eN.source ∩ eS.source := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨eN.symm.map_source (by simp [eN]), ?_⟩
        simp only [eS, stereographic_source, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        intro h
        apply hy
        calc
          y = eN (eN.symm y) := (eN.right_inv (by simp [eN])).symm
          _ = eN south := congrArg eN h
          _ = 0 := hsouth
      · rintro ⟨hxN, hxS⟩
        refine ⟨eN x, ?_, eN.left_inv hxN⟩
        intro hz
        apply hxS
        have hsouthN : south ∈ eN.source := by simpa [eN] using hns.symm
        calc
          x = eN.symm (eN x) := (eN.left_inv hxN).symm
          _ = eN.symm 0 := congrArg eN.symm hz
          _ = eN.symm (eN south) := congrArg eN.symm hsouth.symm
          _ = south := eN.left_inv hsouthN
    rw [← hset]
    exact himage
  exact simplyConnectedSpace_of_union_eq_univ hopenN hopenS hcover
    hNsimple hSsimple hoverlap

#print axioms IsSimplyConnected.pathsHomotopic_of_mem
#print axioms exists_path_mem_twoChart_inter
#print axioms exists_twoChart_connectors
#print axioms Path.Homotopic.concat_connector_telescope
#print axioms exists_cyclic_twoChart_connectors
#print axioms exists_fin_Icc_subset_open_cover_unitInterval
#print axioms simplyConnectedSpace_of_union_eq_univ
#print axioms simplyConnectedSpace_sphere_of_pole
