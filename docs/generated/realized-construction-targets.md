# Realised ConstructionTargets return

This is an empirical layer over repository history and imports, not a prediction
of future cost. The primary cost unit is **changed source lines**: additions plus
deletions reported by `git log --follow --numstat` for each module. It is reproducible
and distinguishes differently sized commits, but it counts formatting and rewrites,
misses design/review effort, and charges a shared commit to every module it touches.
Touching commits and current source lines are retained as secondary measurements.

Consumers are distinct problem bundles reaching a module through direct or transitive
`ConstructionTargets` imports. They show use, not causal necessity or successful closure.

| Module | Changed lines | Touch commits | Current lines | Consumers | Consumers / 100 changed lines |
|---|---:|---:|---:|---:|---:|
| Surfaces | 94 | 1 | 73 | 5 | 5.319 |
| SchwarzEquality | 70 | 1 | 62 | 3 | 4.286 |
| L2Translation | 88 | 2 | 55 | 3 | 3.409 |
| RadialIntegrationR3 | 70 | 1 | 58 | 2 | 2.857 |
| LpRepresentative | 174 | 2 | 163 | 3 | 1.724 |
| CircleParam | 74 | 1 | 67 | 1 | 1.351 |
| Rouche | 504 | 6 | 465 | 6 | 1.190 |
| YoungConvolution | 430 | 6 | 247 | 5 | 1.163 |
| UnivalentDeriv | 197 | 3 | 164 | 2 | 1.015 |
| SchwarzPick | 207 | 1 | 185 | 1 | 0.483 |
| Sinc | 729 | 6 | 604 | 2 | 0.274 |
| RadialMajorantAE | 775 | 11 | 727 | 2 | 0.258 |
| BanachZarecki | 553 | 3 | 456 | 1 | 0.181 |
| HerglotzRigidity | 718 | 6 | 647 | 1 | 0.139 |
| LusinN | 1060 | 9 | 524 | 1 | 0.094 |
| Intersection | 687 | 7 | 603 | 0 | 0.000 |
| KernelAverage | 48 | 1 | 40 | 0 | 0.000 |
| LemniscateComponents | 650 | 2 | 532 | 0 | 0.000 |
| OrientedIntegration | 111 | 1 | 94 | 0 | 0.000 |
| SetIntegralPrimitive | 30 | 1 | 25 | 0 | 0.000 |

## Consumers

- **Rouche** — 6/27: `a01J05`, `a92J05`, `a94A09`, `a97A08`, `aunk04`, `t94J06`
- **Surfaces** — 5/27: `t03J03`, `t03J05`, `t91J05`, `t97A01`, `t98A01`
- **YoungConvolution** — 5/27: `a94A03`, `a95J08`, `a96A04`, `a98J03`, `m99A06`
- **L2Translation** — 3/27: `a94A03`, `a94J04`, `a96A04`
- **LpRepresentative** — 3/27: `a94A03`, `a94J04`, `a96A04`
- **SchwarzEquality** — 3/27: `a95A08`, `a95J01`, `a96J06`
- **RadialIntegrationR3** — 2/27: `a95A03`, `m94A03`
- **RadialMajorantAE** — 2/27: `a94J04`, `a98J03`
- **Sinc** — 2/27: `a02J05`, `a97A06`
- **UnivalentDeriv** — 2/27: `a95A08`, `a95J01`
- **BanachZarecki** — 1/27: `a95J06`
- **CircleParam** — 1/27: `a97A07`
- **HerglotzRigidity** — 1/27: `a94A10`
- **LusinN** — 1/27: `a95J06`
- **SchwarzPick** — 1/27: `a94A09`
- **Intersection** — 0/27: none observed
- **KernelAverage** — 0/27: none observed
- **LemniscateComponents** — 0/27: none observed
- **OrientedIntegration** — 0/27: none observed
- **SetIntegralPrimitive** — 0/27: none observed

`LusinN` has one transitive consumer: `a95J06` imports `BanachZarecki`,
which imports `LusinN`. It is not directly imported and is not unused.

## Validation against observed imports

Population: 27 problem bundles with a
ConstructionTargets import. The observed ground truth contains
38 transitive problem-module edges.

- Precision: 6/8 = 75.0%.
- Recall: 6/38 = 15.8%.
- Problems with any correct module prediction: 6/27.
- False positives: 2; false negatives: 32.

A prediction is made only when the frozen-statement map's
`provided_by_construction_targets` declaration resolves to a declaration owned by
a module. The low recall is the result: statement vocabulary usually does not name
the proof infrastructure later imported to close it. The score validates the map as
a topic/object map, not as a reliable predictor of required ConstructionTargets modules.
The two false positives also expose basename collisions in the lexical symbol map.

## Reproduce

```sh
python3 scripts/realized-construction-targets.py
```

The adjacent JSON contains every cost component, import edge, prediction, true
positive, false positive, and false negative.
