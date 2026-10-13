# Blueprint for m96J02

## Triage and repair

**Verdict: false as printed; the current Lean theorem contains the necessary repairs.**

The source assumes only continuity of `g`, which does not imply uniqueness. Set

```text
g(t,x) = sqrt |x|,   α = β = 0.
```

Then both `x(t)=0` and `y(t)=t⁴/144` solve the differential equation and the corresponding Volterra equation on every positive interval, since `y''(t)=t²/12=sqrt(y(t))` for nonnegative `t`. Thus no choice of `T>0` can force equality. The intended contraction argument in `informal-solution.md` explicitly uses local Lipschitz continuity in the second variable, so `RevisedMain.lean` adds precisely that hypothesis via `apm_m96j02_LocallyLipschitzInSecond`.

There is a second encoding repair already incorporated in the canonical file. Relative `C²` regularity on `[0,T]` must be paired with `derivWithin`, not Mathlib's totalized global `deriv`. With global derivatives, `x(t)=|t|` agrees with the identity on `[0,T]`, while its nonexistent two-sided derivative at zero is totalized to zero; this creates a spurious counterexample even for `g=0`. The repaired statement consistently uses within-derivatives.

The remaining degeneracies behave correctly. The theorem chooses `T>0`, so the interval is nonempty. Constant `g` is Lipschitz with constant zero and gives the unique quadratic solution. Zero initial data with `g=0` yields only the zero solution. The centered-box definition of local Lipschitzness is sufficient because one may choose a radius larger than `|α|+1` and then choose `T` small enough to keep both trajectories in that box.

## Reused proved lemmas

The two lemmas from `Main.lean` are copied with their complete proofs:

- `apm_m96j02_continuousOn_comp_graph` proves continuity of `t ↦ g t (y t)`.
- `apm_m96j02_intervalIntegrable_comp_graph` turns that continuity into interval integrability.

Neither contributes `sorryAx`.

## Remaining lemmas

### `apm_m96j02_ivp_to_volterra`

**Statement.** A relatively `C²` solution of the repaired second-order IVP on `[0,T]`, with the prescribed value and within-derivative at zero, satisfies the Volterra integral equation throughout the interval.

**Proof sketch.** Use the `ContDiffOn` hypothesis to obtain continuity of the relevant within-derivative. Apply the interval fundamental theorem once to

```text
derivWithin x (Icc 0 T)
```

using the supplied second within-derivative equation, and once more to `x`. This yields a nested integral. Rewrite it as the kernel integral `∫₀ᵗ (t-s)g(s,x(s)) ds`, either by interval Fubini or, more conveniently in Lean, by proving that both sides have the same within-derivative and the same value at zero. The two copied graph lemmas supply continuity and integrability of the forcing. Endpoint side conditions use `uniqueDiffOn_Icc`/the corresponding interval derivative API rather than converting to global derivatives.

**Estimate.** 150–250 lines.

**Dependencies.** Only the definitions and the two already proved graph/integrability lemmas.

**Truth check.** For `g=0`, the formula reduces to `x(t)=α+βt`. For constant `g=c`, it gives `x(t)=α+βt+ct²/2`, matching two direct differentiations. At `t=0`, the integral is zero and the identity becomes exactly `x(0)=α`.

### `apm_m96j02_local_volterra_uniqueness`

**Statement.** For continuous `g` locally Lipschitz in its second variable, there is a positive time depending only on `g,α,β` on which any two continuous solutions of the same Volterra equation agree.

**Proof sketch.** Choose `R>|α|+1`, obtain a Lipschitz constant `L` on the centered box of radius `R`, and use compactness/continuity to bound `|g|` there by `M`. Choose positive `T` with `T≤1`, `T≤R`,

```text
|β|T + M T²/2 < R-|α|,
L T²/2 < 1.
```

A first-exit argument applied separately to each Volterra solution keeps both graphs inside the box. Subtract the two equations. If `D = sup {|x(t)-y(t)| : t∈[0,T]}`, the Lipschitz estimate gives

```text
D ≤ (L T²/2) D.
```

Compactness makes the supremum finite/attained, and the strict contraction factor forces `D=0`. In Lean, an equivalent pointwise Grönwall/iterated-Volterra argument may avoid constructing the supremum explicitly.

**Estimate.** 200–300 lines.

**Dependencies.** The definition of local Lipschitzness and the proved graph/integrability lemmas; independent of the IVP-to-Volterra calculus lemma.

**Truth check.** For `L=0`, subtraction gives equality immediately. For `g(t,u)=λu`, the bound is the familiar `|λ|T²/2`; direct linear ODE uniqueness confirms the conclusion. The non-Lipschitz `sqrt |u|` example fails the hypothesis exactly where uniqueness fails.

## Dependency layers

- **Layer 1, parallel:** `apm_m96j02_ivp_to_volterra` and `apm_m96j02_local_volterra_uniqueness`.
- **Layer 2:** the main theorem applies the calculus bridge to `x` and the uniqueness lemma to `x,y`; this assembly is already proved without `sorry`.

## Compilation and axioms

`RevisedMain.lean` and `Blueprint.lean` compile under the prescribed 12 GB memory scope. The blueprint prints:

```text
'apm_m96j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only sources of `sorryAx` are the two named Layer 1 lemmas.
