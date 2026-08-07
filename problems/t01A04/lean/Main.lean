import Mathlib

/-!
# APM t01A04 — the fundamental group and double covers of `T² ∨ S¹`

## Statement repairs

None.

## Encoding note

The wedge and both covering total spaces are concrete quotients.  For the
kernel detecting the extra-circle generator, two torus copies are attached at
the two points of a doubled circle.  For the kernel detecting one torus
generator, two circle copies are attached at the two points over the basepoint
of a doubled torus.  The theorem exhibits the actual covering maps and pins
their induced fundamental-group ranges to the two parity kernels.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t01a04_Torus := Circle × Circle
abbrev apm_t01a04_Parity := Multiplicative (ZMod 2)

inductive apm_t01a04_wedgeRel :
    Sum apm_t01a04_Torus Circle → Sum apm_t01a04_Torus Circle → Prop
  | base : apm_t01a04_wedgeRel (.inl (1, 1)) (.inr 1)

def apm_t01a04_X := Quotient (Relation.EqvGen.setoid apm_t01a04_wedgeRel)

noncomputable instance : TopologicalSpace apm_t01a04_X :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01a04_Torus Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_wedgeRel) z)
    inferInstance

def apm_t01a04_basepoint : apm_t01a04_X := Quotient.mk _ (.inl (1, 1))

def apm_t01a04_sheetPoint (i : Fin 2) : Circle :=
  if i = 0 then 1 else Circle.exp Real.pi

@[simp] lemma apm_t01a04_sheetPoint_zero :
    apm_t01a04_sheetPoint 0 = 1 := by
  simp [apm_t01a04_sheetPoint]

@[simp] lemma apm_t01a04_sheetPoint_one :
    apm_t01a04_sheetPoint 1 = Circle.exp Real.pi := by
  simp [apm_t01a04_sheetPoint]

inductive apm_t01a04_circleCoverRel :
    Sum (Fin 2 × apm_t01a04_Torus) Circle →
      Sum (Fin 2 × apm_t01a04_Torus) Circle → Prop
  | glue (i : Fin 2) :
      apm_t01a04_circleCoverRel (.inl (i, (1, 1)))
        (.inr (apm_t01a04_sheetPoint i))

def apm_t01a04_CircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t01a04_circleCoverRel)

noncomputable instance : TopologicalSpace apm_t01a04_CircleCover :=
  TopologicalSpace.coinduced
    (fun z : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_circleCoverRel) z)
    inferInstance

def apm_t01a04_circleCoverBase : apm_t01a04_CircleCover :=
  Quotient.mk _ (.inl (0, (1, 1)))

inductive apm_t01a04_torusCoverRel :
    Sum apm_t01a04_Torus (Fin 2 × Circle) →
      Sum apm_t01a04_Torus (Fin 2 × Circle) → Prop
  | glue (i : Fin 2) :
      apm_t01a04_torusCoverRel
        (.inl (apm_t01a04_sheetPoint i, 1)) (.inr (i, 1))

def apm_t01a04_TorusCover :=
  Quotient (Relation.EqvGen.setoid apm_t01a04_torusCoverRel)

noncomputable instance : TopologicalSpace apm_t01a04_TorusCover :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01a04_Torus (Fin 2 × Circle) =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_torusCoverRel) z)
    inferInstance

def apm_t01a04_torusCoverBase : apm_t01a04_TorusCover :=
  Quotient.mk _ (.inl (1, 1))

abbrev apm_t01a04_piOne := FundamentalGroup apm_t01a04_X apm_t01a04_basepoint

theorem apm_t01a04 :
    ∃ (a b c : apm_t01a04_piOne)
      (φc φa : apm_t01a04_piOne →* apm_t01a04_Parity)
      (pc : C(apm_t01a04_CircleCover, apm_t01a04_X))
      (pa : C(apm_t01a04_TorusCover, apm_t01a04_X))
      (hpc : pc apm_t01a04_circleCoverBase = apm_t01a04_basepoint)
      (hpa : pa apm_t01a04_torusCoverBase = apm_t01a04_basepoint),
      a * b = b * a ∧
      Subgroup.closure {a, b, c} = ⊤ ∧
      (∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
        ∃! F : apm_t01a04_piOne →* G,
          F a = ga ∧ F b = gb ∧ F c = gc) ∧
      φc a = Multiplicative.ofAdd 0 ∧
      φc b = Multiplicative.ofAdd 0 ∧
      φc c = Multiplicative.ofAdd 1 ∧
      φa a = Multiplicative.ofAdd 1 ∧
      φa b = Multiplicative.ofAdd 0 ∧
      φa c = Multiplicative.ofAdd 0 ∧
      Function.Surjective φc ∧ Function.Surjective φa ∧
      φc.ker.index = 2 ∧ φa.ker.index = 2 ∧ φc.ker ≠ φa.ker ∧
      IsCoveringMap pc ∧ IsCoveringMap pa ∧
      MonoidHom.range
        (hpc ▸ FundamentalGroup.map pc apm_t01a04_circleCoverBase) = φc.ker ∧
      MonoidHom.range
        (hpa ▸ FundamentalGroup.map pa apm_t01a04_torusCoverBase) = φa.ker ∧
      ¬Nonempty (apm_t01a04_CircleCover ≃ₜ apm_t01a04_TorusCover) := by
  /-
  CLOSER HOP 1 boundary. The two attaching points are now normalized by
  `apm_t01a04_sheetPoint_zero` and `apm_t01a04_sheetPoint_one`.

  Mathlib's `AlgebraicTopology.FundamentalGroupoid.Product` computes products
  of fundamental groupoids, but the source search found no Seifert--van
  Kampen theorem computing the fundamental group of this concrete quotient
  wedge. Consequently there is no available route to construct `a`, `b`, and
  `c` with the frozen universal property, and hence no route to define the two
  parity characters on the actual `FundamentalGroup` rather than on an
  abstract presentation.

  The total spaces and base are quotients by generated relations. Mathlib has
  general covering-map and quotient-covering infrastructure, but no gluing
  theorem showing that these particular maps obtained by gluing sheets along
  points are covering maps. Even after constructing `pc` and `pa`, identifying
  the ranges of their induced fundamental-group maps with the parity kernels
  needs the covering/subgroup correspondence, which is likewise not packaged
  for these raw quotients. Finally, distinguishing the total spaces requires
  computing `H₂` (two torus classes versus one), and the singular-homology
  corpus has no quotient-wedge calculation supporting that argument.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/` modules,
  closed covering/wedge siblings (`t00A02`, `t01A01`, `t01A03`, `t97A03`),
  Mathlib's covering, fundamental-groupoid product, quotient, and singular-
  homology sources, and git history. None supplies these four assemblies.
  -/
  sorry
