| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m93J07 | faithful | Answers all twelve existence/nonexistence questions with genuine Banach, operator, and `MemLp` assertions. | — |
| m94A03 | faithful | States exactly that `log ‖x‖` is not in `H¹` in dimension 2 and is in `H¹` in dimensions 3 and 4. | — |
| m94A04 | faithful | Constructs the stated Nemytskii operator and its Fréchet derivative `h ↦ 3f²h` at every `f`. | — |
| m94A05 | faithful | Gives an explicit positive smallness threshold and a continuous solution of the integral equation. | — |
| m94J01 | faithful | States convergence to zero in `𝓓′` and nonconvergence in `𝓢′` in the defining weak senses. | — |
| m94J02 | narrower | Replaces the requested `‖fg‖ ≤ ‖f‖‖g‖` with the weaker `‖fg‖ ≤ (5/4)‖f‖‖g‖`. | — |
| m94J04 | faithful | Uses the documented necessary correction of the malformed piecewise definition and computes its weak curl. | — |
| m94J05 | narrower | Proves uniqueness only among solutions bounded by a fixed radius, not unrestricted uniqueness among all solutions. | correction (`8cf4ec3ee`) |
| m95A02 | faithful | Uses the exact weighted Fourier realization and states the ONB, Hölder estimate, and weak-to-uniform convergence. | — |
| m95A04 | hypothesis-carries-core | Hypotheses `regular`, `Dtest`, and `Ddist` already supply the locally-integrable embedding and distributional derivative definitions requested in parts (a)–(b). | — |

### Evidence

#### m93J07

The bundled space has a complete real normed-space carrier, and reflexivity, separability, and dual separability have their standard meanings (lines 22–38). The theorem gives the first five requested examples and correctly states nonexistence for a nonseparable space with separable dual (lines 821–832); it gives both dense proper linear maps (833–835), both whole-line `L²/L⁴` witnesses (836–837), the finite-interval `L²\L⁴` witness (838–840), and correctly states that finite measure makes `L⁴\L²` impossible (841–843).

#### m94A03

`apm_m94a03_InH1UnitBall` requires both `log ‖x‖ ∈ L²` and an `L²` weak gradient, with the weak integration-by-parts identity tested against compactly supported smooth functions (lines 739–754). The theorem is exactly
`¬ apm_m94a03_InH1UnitBall 2 ∧ apm_m94a03_InH1UnitBall 3 ∧ apm_m94a03_InH1UnitBall 4`
(lines 1162–1165). The use of the open unit ball is immaterial to this Sobolev membership question.

#### m94A04

The operator predicate states `T f(t)=sin t+(f t)^3` almost everywhere (lines 102–107). The derivative predicate includes bounded linearity and the Fréchet remainder estimate (109–123). Lines 364–374 assert existence of that operator and, for every `f`, a derivative satisfying `L h(t)=3(f t)^2h(t)` almost everywhere. No extra restriction on the point `f` is introduced.

#### m94A05

The Picard map is the rearranged equation (lines 22–24). The theorem assumes the explicit sufficient condition `0 < ε < 1/(4π)` and concludes a function continuous on `[0,π]` satisfying the equation pointwise there (lines 292–297). An explicit bound is a valid realization of “sufficiently small.”

#### m94J01

Lines 740–744 say every compactly supported smooth test evaluation tends to zero, hence the `𝓓′` limit is zero. Lines 745–749 deny existence of any tempered distribution giving limits on all Schwartz tests, exactly nonconvergence in `𝓢′`. The factors `(-1)^n iteratedDeriv n φ n` are the problem's delta-derivative evaluations.

#### m94J02

The coefficient membership, printed norm, evaluation, Cauchy product, dilation, and spectrum are defined literally at lines 23–55. Completeness and continuity are stated at lines 1097–1106, powers at 1111–1114, compactness through sequential compactness of the unit ball at 1115–1120, and the expected spectrum at 1121–1122. However, lines 1107–1110 only prove
`apm_m94J02_norm (apm_m94J02_mul a b) ≤ (5 / 4) * ...`,
where problem.md explicitly asks for constant `1`. Thus the registered claim does not establish the requested normed-algebra inequality.

#### m94J04

The source text's conditions overlap on `{x>0,z<0}` and leave `{x≤0,z≥0}` undefined. The file documents the necessary correction of the second branch to `x≤0` (lines 6–11), and defines `f(p)=p₁` for `p₀>0`, otherwise `p₀` (lines 29–39). It defines the claimed curl `(0,0,-1_{x>0})` (lines 55–57), and lines 458–462 state equality of the weak-curl pairing with the regular distribution represented by that field for every test function. This is faithful to the only documented well-defined interpretation, rather than silently assuming the inconsistent literal clauses.

#### m94J05

`IsM94J05Solution` accurately states `C²`, both boundary conditions, and the ODE (lines 25–29). The current theorem produces fixed `ε,r>0`, a solution with `|x|≤r`, and uniqueness only against competitors satisfying the same bound (lines 1241–1252). The bank statement at `bc427c2bc` instead asserted `∃! x, IsM94J05Solution f x` with no radius. Commit `8cf4ec3ee` narrows this to the contraction-controlled small branch. That repair is a **correction** because the file records that unrestricted uniqueness is false even at zero forcing due to a nonzero large branch (lines 8–12); it does not provide a compiled counterexample theorem, but explicitly records the mathematical refutation motivating the repair.

#### m95A02

The file identifies `m95A02H = ℓ²(ℤ,ℂ)` as the exact normalized Fourier realization of the printed Sobolev inner product (lines 9–14, 21–28). The theorem gives the normalized Fourier Hilbert basis (lines 799–802), the requested `1/2`-Hölder estimate with constant one (803–805), and weak convergence implying convergence of the custom maximum distance to zero (806–809), which is the maximum-norm conclusion.

#### m95A04

The theorem does prove the requested formulas and consequences: equality of regular distributions iff a.e. equality, `D|x|=sign`, `D sign=2δ`, injectivity/noninjectivity, a causal fundamental solution, and completeness (lines 674–682). But it assumes a map
`regular : (ℝ → ℝ) → apm_m95A04_Dist`
together with the exact integration formula for every locally integrable function (lines 644–648), and assumes both the test derivative and distribution derivative with the defining duality formula (649–654). These hypotheses are precisely the principal content requested in parts (a) and (b), and their existence is never concluded. The later `habs`, `hsign`, `hδ`, and `hcausal` assumptions (655–663) also prepackage the relevant named distributions, though the derivative identities themselves remain nontrivial.

No audited registered theorem depends on an `axiom`, `opaque`, or `sorry`-typed declaration. The sole textual `sorry` match in m93J07 is prose in an old boundary comment, not a declaration or proof term. Except for m94J05's explicit repair, history inspection found no post-bank theorem-type change.
