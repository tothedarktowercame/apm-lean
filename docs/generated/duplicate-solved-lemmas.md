# Duplicate proved lemmas in completed problems

Source coverage: 900 proved helper-lemma rows from 188 completed problems; 0 index rows unparsed.
Cross-problem exact-normalized clusters: 24.

This is lexical clustering, not Lean definitional equality.

## Timing summary

Dated members: 49; undated: 0. Earliest or same-day: 46;
post-dating the cluster's earliest day: 3. Later members for which an equivalent
problem row was already in `LEMMA-INDEX.md`: 3.

Among the 25 non-earliest members, 22
were introduced on the earliest member's calendar day and 3 were later-day
duplicates. All three later-day duplicates post-date an equivalent indexed row.

## Normalization

Explicitly typed binder names are alpha-renamed `v0`, `v1`, ... in encounter order;
APM problem-local identifier prefixes become `apm_local_`; capitalized namespace
qualification is reduced to its basename; whitespace is removed. Operators, constants,
binder order, implicit/explicit delimiters, and proposition structure are retained.

## Clusters

### 1. 3 problems / 3 declarations

Normalized: `(v0:ℂ[X])(v1:v0.Monic)(v2:ℂ)(v3:ℝ):zeroCountInClosedBall(funz↦aevalzv0)v2v3=(v0.roots.filter(funz↦distzv2≤v3)).card`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a92J05 | `zeroCountInClosedBall_aeval_eq_card_filter` | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R = (q.roots.filter (fun z ↦ dist z c ≤ R)).card` | 2026-08-01 d4198ec5 / earliest-or-same-day | 2026-08-06 497acbdd |
| a94A09 | `apm_a94a09_zeroCount_aeval_eq_card_filter` | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R = (q.roots.filter (fun z ↦ dist z c ≤ R)).card` | 2026-08-09 a9fa1ab5 / post-dates-earliest | 2026-08-10 ae23c954 |
| a97A08 | `zeroCountInClosedBall_aeval_eq_card_filter` | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R = (q.roots.filter (fun z ↦ dist z c ≤ R)).card` | 2026-08-01 b4e979d5 / earliest-or-same-day | 2026-08-06 497acbdd |

### 2. 2 problems / 2 declarations

Normalized: `(v0:0<p.natDegree)(x:↥((lemniscatep)ᶜ))(v1:componentSetx⊆sublevelp):∃z∈componentSetx,aevalzp=0`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `exists_root_in_componentSet_of_subset_sublevel` | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ)) (hsub : componentSet x ⊆ sublevel p) : ∃ z ∈ componentSet x, aeval z p = 0` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `exists_root_in_componentSet_of_subset_sublevel` | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ)) (hsub : componentSet x ⊆ sublevel p) : ∃ z ∈ componentSet x, aeval z p = 0` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 3. 2 problems / 2 declarations

Normalized: `(v0:0<p.natDegree):(rootsp).toFinset.card≤p.natDegree`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `card_roots_le_degree` | `(hp : 0 < p.natDegree) : (Polynomial.roots p).toFinset.card ≤ p.natDegree` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `card_roots_le_degree` | `(hp : 0 < p.natDegree) : (Polynomial.roots p).toFinset.card ≤ p.natDegree` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 4. 2 problems / 2 declarations

Normalized: `(v0:0<p.natDegree):IsBounded(sublevelp)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `isBounded_sublevel` | `(hp : 0 < p.natDegree) : IsBounded (sublevel p)` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `isBounded_sublevel` | `(hp : 0 < p.natDegree) : IsBounded (sublevel p)` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 5. 2 problems / 2 declarations

Normalized: `(v0:0<p.natDegree){xy:↥((lemniscatep)ᶜ)}(v1:componentSetx⊆superlevelp)(v2:componentSety⊆superlevelp):(x:ConnectedComponents↥((lemniscatep)ᶜ))=y`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `component_eq_of_subset_superlevel` | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)} (hxsuper : componentSet x ⊆ superlevel p) (hysuper : componentSet y ⊆ superlevel p) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `component_eq_of_subset_superlevel` | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)} (hxsuper : componentSet x ⊆ superlevel p) (hysuper : componentSet y ⊆ superlevel p) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 6. 2 problems / 2 declarations

Normalized: `(v0:ℂ)(v1:ℝ):‖exp(-(v1:ℂ)*v0)‖=exp(-v0.re*v1)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a01A09 | `abs_laplace_kernel` | `(z : ℂ) (t : ℝ) : ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t)` | 2026-05-01 25bcef42 / earliest-or-same-day | 2026-08-06 497acbdd |
| a99J09 | `apm_a99j09_norm_kernel` | `(z : ℂ) (t : ℝ) : ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t)` | 2026-08-07 c5fef77d / post-dates-earliest | 2026-08-08 39a3f1a0 |

### 7. 2 problems / 2 declarations

Normalized: `(v0:ℂ[X])(v1:Setℂ):DiffContOnClℂ(v2v3:ℂ=>aevalv3v0)v1`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `diffContOnCl_aeval` | `(p : ℂ[X]) (U : Set ℂ) : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `diffContOnCl_aeval` | `(p : ℂ[X]) (U : Set ℂ) : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 8. 2 problems / 2 declarations

Normalized: `(v0:ℝ)(v1:0≤v0):IsPathConnected{v2:ℂ\|v0<‖v2‖}`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `exterior_pathConnected` | `(R : ℝ) (hR : 0 ≤ R) : IsPathConnected {z : ℂ \\| R < ‖z‖}` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `exterior_pathConnected` | `(R : ℝ) (hR : 0 ≤ R) : IsPathConnected {z : ℂ \\| R < ‖z‖}` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 9. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ))(v0:componentSetx⊆superlevelp):¬IsBounded(componentSetx)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `not_isBounded_componentSet_of_subset_superlevel` | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) : ¬ IsBounded (componentSet x)` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `not_isBounded_componentSet_of_subset_superlevel` | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) : ¬ IsBounded (componentSet x)` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 10. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):(componentSetx).Nonempty`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_nonempty` | `(x : ↥((lemniscate p)ᶜ)) : (componentSet x).Nonempty` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_nonempty` | `(x : ↥((lemniscate p)ᶜ)) : (componentSet x).Nonempty` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 11. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):IsConnected(componentSetx)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_connected` | `(x : ↥((lemniscate p)ᶜ)) : IsConnected (componentSet x)` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_connected` | `(x : ↥((lemniscate p)ᶜ)) : IsConnected (componentSet x)` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 12. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):IsOpen(componentSetx)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_open` | `(x : ↥((lemniscate p)ᶜ)) : IsOpen (componentSet x)` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_open` | `(x : ↥((lemniscate p)ᶜ)) : IsOpen (componentSet x)` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 13. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):componentSetx⊆(lemniscatep)ᶜ`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_subset_compl` | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ (lemniscate p)ᶜ` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_subset_compl` | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ (lemniscate p)ᶜ` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 14. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):componentSetx⊆superlevelp∨componentSetx⊆sublevelp`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_subset_superlevel_or_sublevel` | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_subset_superlevel_or_sublevel` | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 15. 2 problems / 2 declarations

Normalized: `(x:↥((lemniscatep)ᶜ)):frontier(componentSetx)⊆lemniscatep`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_frontier_subset_lemniscate` | `(x : ↥((lemniscate p)ᶜ)) : frontier (componentSet x) ⊆ lemniscate p` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_frontier_subset_lemniscate` | `(x : ↥((lemniscate p)ᶜ)) : frontier (componentSet x) ⊆ lemniscate p` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 16. 2 problems / 2 declarations

Normalized: `:IsClosed(lemniscatep)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `isClosed_lemniscate` | `: IsClosed (lemniscate p)` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `isClosed_lemniscate` | `: IsClosed (lemniscate p)` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

### 17. 2 problems / 2 declarations

Normalized: `:card(ConnectedComponents↥((lemniscatep)ᶜ))≤p.natDegree+1`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `connectedComponents_complement_lemniscate_le` | `: Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `connectedComponents_complement_lemniscate_le` | `: Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 18. 2 problems / 2 declarations

Normalized: `:volumecantorSet=0`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a95J06 | `cantorSet_measure_zero` | `: volume cantorSet = 0` | 2026-07-26 dfe0cd3e / earliest-or-same-day | 2026-08-06 497acbdd |
| t91J01 | `apm_t91J01_cantorSet_measure_zero` | `: volume cantorSet = 0` | 2026-08-07 5370a078 / post-dates-earliest | 2026-08-08 39a3f1a0 |

### 19. 2 problems / 2 declarations

Normalized: `{v0:Setℂ}(v1:IsOpenv0)(v2:IsBoundedv0)(v3:v0⊆sublevelp)(v4:frontierv0⊆lemniscatep)(v5:v0.Nonempty):∃z∈v0,aevalzp=0`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : ∃ z ∈ U, aeval z p = 0` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : ∃ z ∈ U, aeval z p = 0` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 20. 2 problems / 2 declarations

Normalized: `{v0:Setℂ}(v1:IsOpenv0)(v2:IsBoundedv0)(v3:v0⊆superlevelp)(v4:frontierv0⊆lemniscatep)(v5:v0.Nonempty):False`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `not_bounded_isOpen_superlevel_frontier_lemniscate` | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : False` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `not_bounded_isOpen_superlevel_frontier_lemniscate` | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : False` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 21. 2 problems / 2 declarations

Normalized: `{v0:Setℂ}(v1:IsPreconnectedv0)(hSL:Disjointv0(lemniscatep)):v0⊆superlevelp∨v0⊆sublevelp`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `isPreconnected_subset_superlevel_or_sublevel` | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) : S ⊆ superlevel p ∨ S ⊆ sublevel p` | 2026-07-13 e6365451 / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `isPreconnected_subset_superlevel_or_sublevel` | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) : S ⊆ superlevel p ∨ S ⊆ sublevel p` | 2026-07-13 182c2743 / earliest-or-same-day | 2026-08-06 497acbdd |

### 22. 2 problems / 2 declarations

Normalized: `{v0:ℝ}(v1:0<v0){v2:ℝ→ℝ}(v3:MemLpv22volume):letτ:ℝ→C(ℝ,ℝ)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a94J04 | `poisson_translation_average_toLp` | `{y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` | 2026-08-01 43271c8e / earliest-or-same-day | 2026-08-06 497acbdd |
| a96A04 | `heat_translation_average_toLp` | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` | 2026-08-01 a354e5b9 / earliest-or-same-day | 2026-08-06 497acbdd |

### 23. 2 problems / 2 declarations

Normalized: `{v0:ℝ→ℝ}(v1:MemLpv02volume):letτ:ℝ→C(ℝ,ℝ)`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a94J04 | `poisson_translation_average_tendsto_L2` | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` | 2026-08-01 43271c8e / earliest-or-same-day | 2026-08-06 497acbdd |
| a96A04 | `heat_translation_average_tendsto_L2` | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` | 2026-08-01 987ab3de / earliest-or-same-day | 2026-08-06 497acbdd |

### 24. 2 problems / 2 declarations

Normalized: `{xy:↥((lemniscatep)ᶜ)}{v0:ℂ}(v1:v0∈componentSetx)(v2:v0∈componentSety):(x:ConnectedComponents↥((lemniscatep)ᶜ))=y`

| Problem | Lemma | Original signature | Introduced / class | Indexed |
|---|---|---|---|---|
| a00J04 | `componentSet_eq_of_common_point` | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ} (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` | 2026-07-30 3e9a506e / earliest-or-same-day | 2026-08-06 497acbdd |
| a01A08 | `componentSet_eq_of_common_point` | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ} (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` | 2026-07-30 c512690e / earliest-or-same-day | 2026-08-06 497acbdd |

## Deep dive: a00J04 and a01A08

The two problem files first entered history on 2026-07-13. Their completed
lemniscate developments were introduced by `3e9a506e` at
2026-07-30T19:24:37+01:00 (`a00J04`) and `c512690e` at
2026-07-30T19:31:38+01:00 (`a01A08`): seven minutes apart on the same day.
All 19 shared cluster members therefore classify as same-day/concurrent under
the preregistered rule, not post-dating discoverability failures.

The relevant problem rows first appeared in `LEMMA-INDEX.md` at `497acbdd` on
2026-08-06, a week after both completed developments. The index could not have
prevented this duplication. The later file does, however, explicitly say that its
TeX problem is identical to `a00J04` and that it adapts the `a00J04` formalization
(`problems/a01A08/lean/Main.lean`, current lines 17--20 and 44--45). Thus this is
documented consultation and adaptation of an intentionally duplicated problem,
not an unnoticed independent re-derivation.

## Unparsed index rows

None.
