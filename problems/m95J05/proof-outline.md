# Proof Outline: m95J05

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J05.md`

## Compiled progress

- `apm_m95J05_fundamental_isFundamentalKernel` proves the complete weak
  fundamental-solution identity.  It differentiates the compactly supported
  product `exp (-λt) ψ(t)` and applies
  `HasCompactSupport.integral_Ioi_deriv_eq`.

## Remaining boundary

- Extract a finite lower support bound for the test function and rewrite the
  moving `Iic` integral as an ordinary interval integral.
- Prove its first derivative by interval FTC, then bootstrap the ODE identity
  to the required `C∞` regularity.
