| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m00A01 | faithful | Defines the orthogonal complement and both projections, proves the restricted complement map bijective, and gives the requested positive lower bound. | — |
| m01J01 | stronger | States and proves both theorems and also explicitly proves the requested implication from Open Mapping to Closed Graph. | — |
| m01J02 | faithful | Uses genuine orthogonal projections and states the sum/orthogonality and product/commutation equivalences, including range `M ⊓ N`. | — |
| m01J03 | stronger | Gives the requested finite-dimensional projection limit in operator-norm topology, stronger than an unspecified convergence mode. | — |
| m02A01 | faithful | Defines genuine weak convergence, proves uniqueness and strong-to-weak convergence, supplies the standard `ℓ²` counterexample, and handles finite dimension. | — |
| m02A04 | faithful | Under the documented necessary correction of the divergent printed `+t³x²` to `-t³x²`, it gives the exact formula and hence the leading asymptotic. | — |
| m02J02 | narrower | “Basis” is encoded only as linear independence plus density of finite spans in the graph norm; it does not assert a Schauder/orthonormal basis or unique convergent expansions. | — |
| m93A02 | faithful | Proves the local quantitative solution and supplies an explicit nonsurjective counterexample for part (b). | — |
| m93A03 | faithful | States exactly that weak convergence together with convergence of norms implies norm convergence. | — |
| m93J04 | faithful | States the correct distributional fundamental-solution identity against compactly supported smooth tests on `(0,1)`. | correction: the bank’s bare `ContDiff ℝ ⊤` required analyticity; the later change to `((⊤ : ℕ∞) : WithTop ℕ∞)` correctly means `C^∞`. |

### m00A01

The registered theorem is `apm_m00a01` (lowercase suffix). Its supporting definitions encode `Nᗮ`, orthogonal projection by range/residual, and the restriction of `I-P`. Lines 53–69 state:

```lean
theorem apm_m00a01 ...
    (hdisjoint : M ⊓ N = ⊥) (hsum : M ⊔ N = ⊤)
    (P : H →L[𝕜] N)
    (hP : ∀ x, x - (P x : H) ∈ apmOrthogonalComplement N) :
    apmIsOrthogonalProjectionTo N (fun x => (P x : H)) ∧
      apmIsOrthogonalProjectionTo (apmOrthogonalComplement N)
        (fun x => x - (P x : H)) ∧
      Function.Bijective (apmRestrictedComplement M N P hP) ∧
      ∃ α : ℝ, 0 < α ∧
        ∀ x : M, α * ‖(x : H)‖ ≤ ‖(x : H) - (P x : H)‖ := by
```

This is faithful; interpreting the malformed source as `M ∩ N = {0}` is forced by the claim. No local axiom, opaque declaration, or sorry occurs.

### m01J01

Lines 19–28 define the usual Banach-space Open Mapping and Closed Graph statements. Lines 30–33 state:

```lean
theorem apm_m01j01 :
    apm_m01j01_OpenMappingTheorem ∧
    apm_m01j01_ClosedGraphTheorem ∧
    (apm_m01j01_OpenMappingTheorem → apm_m01j01_ClosedGraphTheorem) := by
```

It proves slightly more than the exercise demands because the closed graph theorem is also established independently. No local axiom, opaque declaration, or sorry occurs.

### m01J02

`apm_m01j02_IsOrthogonalProjection` at lines 21–27 requires idempotence, self-adjointness, and the specified range. The registered theorem at lines 29–48 includes:

```lean
(M.starProjection + N.starProjection = (M ⊔ N).starProjection ↔ M ⟂ N) ∧
((∃ A : Submodule 𝕜 H,
  apm_m01j02_IsOrthogonalProjection
    (M.starProjection.comp N.starProjection) A) ↔
  M.starProjection.comp N.starProjection =
    N.starProjection.comp M.starProjection) ∧
...
apm_m01j02_IsOrthogonalProjection
  (M.starProjection.comp N.starProjection) (M ⊓ N)
```

The `HasOrthogonalProjection` instances make explicit the existence presupposed by the notation in the problem. Correcting printed `P ∩ N` to `M ∩ N` is necessary. No local axiom, opaque declaration, or sorry occurs.

### m01J03

The dependencies define `T†T`, its eigenvalue-one kernel, and an orthogonal projection by idempotence/self-adjointness/range. Lines 72–84 state:

```lean
theorem apm_m01j03 ...
    (T : H →L[𝕜] H) (hT : IsCompactOperator T) (hnorm : ‖T‖ = 1) :
    Module.Finite 𝕜 (apm_m01j03_topEigenspace T) ∧
    ∃ P : H →L[𝕜] H,
      apm_m01j03_IsOrthogonalProjection P
        (apm_m01j03_topEigenspace T) ∧
      Filter.Tendsto
        (fun n : ℕ => (apm_m01j03_selfAdjointSquare T) ^ n)
        Filter.atTop (nhds P) := by
```

The ambient topology on continuous linear maps is operator norm, so this strengthens any strong-operator reading. No local axiom, opaque declaration, or sorry occurs.

### m02A01

The registered declaration is `apm_m02a01`. Its weak convergence definition (lines 21–24) is convergence in Mathlib’s weak topology. Lines 31–46 state uniqueness, strong-to-weak convergence, the `ℓ²(ℕ,ℝ)` unit-vector counterexample, and finite-dimensional equivalence. In particular:

```lean
(apm_m02A01_weaklyConverges apm_m02A01_basisVector 0 ∧
  ¬Tendsto apm_m02A01_basisVector atTop (nhds 0)) ∧
(∀ ... [FiniteDimensional ℝ X] ...,
  apm_m02A01_weaklyConverges x a ↔ Tendsto x atTop (nhds a))
```

No local axiom, opaque declaration, or sorry occurs.

### m02A04

The printed positive quadratic coefficient makes the integral divergent for positive `t`; the file documents and applies the minimal sign correction. Lines 15–19 define:

```lean
noncomputable def apm_m02a04_integral (t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-t ^ 3 * x ^ 2 + t ^ 2 * x)

noncomputable def apm_m02a04_leadingTerm (t : ℝ) : ℝ :=
  Real.sqrt Real.pi * Real.rpow t (-(3 : ℝ) / 2) * Real.exp (t / 4)
```

Lines 32–36 state exact equality for every `t>0` and ratio convergence to one. The correction was already present in the first committed bank statement, so there is no later repair commit to classify. No local axiom, opaque declaration, or sorry occurs.

### m02J02

The registered declaration is `apm_m02j02`. Its crucial representation boundary is lines 45–53:

```lean
def apm_m02j02_IsH10Basis
    (s : Set ℝ) (e de : ℕ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, apm_m02j02_InH10 s (e n) (de n)) ∧
  LinearIndependent ℝ (fun n ↦ (e n, de n)) ∧
  ∀ u du : ℝ → ℝ, apm_m02j02_InH10 s u du →
    ∀ ε : ℝ, 0 < ε → ∃ c : ℕ →₀ ℝ, ...
```

The conclusion at lines 7107–7116 applies this predicate to sine functions, odd Hermite functions on the half-line, and all Hermite functions on `ℝ`. This proves a complete linearly independent system, but not the usual stronger meanings of “basis” (orthonormal or Schauder basis with unique expansions). The file itself explicitly calls this reading weak, so the statement is narrower. No local axiom, opaque declaration, or sorry occurs.

### m93A02

Lines 64–82 state the quantitative local solution and the explicit counterexample:

```lean
(∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
  ∀ k : K, ‖k‖ < ε →
    ∃ h : H, L h + Q h h = k ∧ ‖h‖ ≤ B * ‖k‖) ∧
(∀ ε : ℝ, 0 < ε →
  ∃ k : ℝ × ℝ, ‖k‖ < ε ∧
    ¬ ∃ h : ℝ, (h, 0) + (0, h * h) = k) := by
```

Replacing the source’s ill-typed `L(H)` by `L h` is necessary. Replacing strict `<` by `≤` is also necessary because the quantified neighborhood includes `k=0`; these repairs were already in the first bank statement. No local axiom, opaque declaration, or sorry occurs.

### m93A03

The registered declaration is `apm_m93a03`. Lines 18–27 state:

```lean
theorem apm_m93a03 ...
    (hweak : ∀ g : F,
      Tendsto (fun n => inner 𝕜 (f n) g) atTop (nhds (inner 𝕜 f₀ g)))
    (hnorm : Tendsto (fun n => ‖f n‖) atTop (nhds ‖f₀‖)) :
    Tendsto f atTop (nhds f₀) := by
```

This is exactly the prelim claim, uniformly over real and complex Hilbert spaces. No local axiom, opaque declaration, or sorry occurs.

### m93J04

The registered declaration is `apm_m93j04`. The exact piecewise kernel is defined at lines 23–24, and the formal adjoint of `x²D²-xD+1` is correctly defined at lines 80–81 as `x²φ''+5xφ'+4φ`. Lines 203–213 state:

```lean
theorem apm_m93j04 :
    ∀ y : ℝ, y ∈ Ioo (0 : ℝ) 1 →
      ∀ φ : ℝ → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
        HasCompactSupport φ →
        Function.support φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x in Ioo (0 : ℝ) 1,
            apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) = φ y := by
```

This is precisely the weak fundamental-solution identity. The final history commit corrected the bank’s analytic bare `⊤` hypothesis to the intended `C^∞` order shown above. No local axiom, opaque declaration, or sorry occurs.
