import ConstructionTargets.SchwarzEquality
import ConstructionTargets.RadialIntegrationR3
import ConstructionTargets.Rouche
import ConstructionTargets.LemniscateComponents
import ConstructionTargets.UnivalentDeriv
import ConstructionTargets.BanachZarecki
import ConstructionTargets.HerglotzRigidity

/-!
# ConstructionTargets — reusable lemmas built to unblock specific APM problems

Library root. Added 2026-07-30: before this, `ConstructionTargets/` had no
`lean_lib` entry and no root module, so the directory was not on the module
path — `import ConstructionTargets.SchwarzEquality` failed with "unknown module
prefix" and no `.olean` was ever produced. The lemmas below were proved but
mechanically unreachable from the problems they were built for.

Downstream problems should import the SPECIFIC submodule they need, not this
root: `Rouche` and `LemniscateComponents` are partial results that still carry
`sorry`, and importing the root would bring those declarations into scope
needlessly.

| Module | Status | Built to unblock |
|---|---|---|
| `SchwarzEquality` | sorry-free | a95A08, a95J01 |
| `RadialIntegrationR3` | sorry-free | a95A03 |
| `Rouche` | partial (`sorry` remains) | a92J05, a94A10 |
| `LemniscateComponents` | partial (`sorry` remains) | a00J04, a01A08 |
| `UnivalentDeriv` | partial (`sorry` remains) | a95J01 |
| `BanachZarecki` | complete, sorry-free monotone Banach--Zarecki theorem | a95J06 |
| `HerglotzRigidity` | sorry-free | a94A10 |
-/
