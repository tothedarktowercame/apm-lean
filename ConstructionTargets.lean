import ConstructionTargets.BanachZarecki
import ConstructionTargets.CircleParam
import ConstructionTargets.CircleHomology
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.HerglotzRigidity
import ConstructionTargets.KernelAverage
import ConstructionTargets.L2Translation
import ConstructionTargets.LemniscateComponents
import ConstructionTargets.LpRepresentative
import ConstructionTargets.LusinN
import ConstructionTargets.RadialIntegrationR3
import ConstructionTargets.RadialMajorantAE
import ConstructionTargets.Rouche
import ConstructionTargets.SchwarzEquality
import ConstructionTargets.Sinc
import ConstructionTargets.Surfaces
import ConstructionTargets.UnivalentDeriv
import ConstructionTargets.YoungConvolution
import ConstructionTargets.SetIntegralPrimitive
import ConstructionTargets.OrientedIntegration
import ConstructionTargets.Intersection
import ConstructionTargets.CoveringDegree
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.SimplyConnectedOpenCover
import ConstructionTargets.SingularExcision
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.SingularSubdivision
import ConstructionTargets.SphereHomology
import ConstructionTargets.SphereOneH1Concrete
import ConstructionTargets.T02A06DiskPairShift
import ConstructionTargets.T02A06DiskRadialComparison
import ConstructionTargets.T02A06HemisphereCoordinates
import ConstructionTargets.T02A06HemisphereExcision
import ConstructionTargets.T02A06SphereH0
import ConstructionTargets.T02A06SphereOne
import ConstructionTargets.T02A06SphereShift
import ConstructionTargets.T02A06SphereVanishingBridge

/-!
# ConstructionTargets — reusable lemmas built to unblock specific APM problems

Library root. Added 2026-07-30: before this, `ConstructionTargets/` had no
`lean_lib` entry and no root module, so the directory was not on the module
path — `import ConstructionTargets.SchwarzEquality` failed with "unknown module
prefix" and no `.olean` was ever produced. The lemmas below were proved but
mechanically unreachable from the problems they were built for.

Downstream problems should still import the SPECIFIC submodule they need rather
than this root — it is a roll-up for auditing, and pulling in fifteen modules to
use one lemma is wasteful. But the old reason for the warning is gone: as of
2026-08-01 **every module here is sorry-free**, so importing the root no longer
risks bringing a hole-carrying declaration into scope.

## Status, measured 2026-08-01

All fifteen modules verified at committed HEAD: zero `sorry`, zero `axiom`, zero
definition-free `opaque`. The consumer column is DERIVED (grep for
`ConstructionTargets.<Module>` across `problems/*/lean/Main.lean`), not asserted
— the previous table named `a94A10` as a `Rouche` consumer, which was never true
and cost a day of misrouted dispatches. a94A10 closed via `HerglotzRigidity`.

| Module | Consumers (measured) |
|---|---|
| `BanachZarecki` | a95J06 |
| `CircleParam` | a97A07 |
| `HerglotzRigidity` | a94A10 |
| `KernelAverage` | *(none)* |
| `L2Translation` | a94A03, a94J04, a96A04 |
| `LemniscateComponents` | *(none)* |
| `LpRepresentative` | a94A03, a94J04, a96A04 |
| `LusinN` | a95J06; also imported by `BanachZarecki` |
| `RadialIntegrationR3` | a95A03 |
| `RadialMajorantAE` | a94J04 |
| `Rouche` | a92J05, a97A08 |
| `SchwarzEquality` | a95A08, a95J01 |
| `Sinc` | a02J05, a97A06 |
| `UnivalentDeriv` | a95A08, a95J01 |
| `YoungConvolution` | a94A03, a95J08, a96A04 |

## Known debt

`LusinN` was built by COPYING `problems/a95A02/lean/Main.lean` rather than by
extracting from it. It shares **17 of its 18 declarations** with that file, with
byte-identical proofs, and a95A02 does not import it — so they are two
independent copies and a fix to one does not reach the other. Its net unique
contribution is a single lemma,
`absolutelyContinuousOnInterval_maps_null_to_null`. The cleanup (import +
`open`, delete the 17 copies) is specified but held while a95A02's statement
defect is under review. Contrast `BanachZarecki`, which shares zero declarations
with a95J06 — that is what extraction looks like. See rule R2 in
`futon3c/holes/labs/M-codex-sorry-loop/construction-targets.md`.
-/
