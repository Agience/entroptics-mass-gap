# Section 1: theorem-to-Lean map

Declarations in the Lean library, prefix `MassGap.` omitted. Hypotheses transcribed from the Lean signatures.

| Theorem | Lean declaration | Open hypotheses |
|---|---|---|
| Theorem 1.1 | `OneInput.clayStatement_of_strongEnd` (conclusion `ClayStatementG.ClayStatementOf (SU N)`) | (S) `CouplingTower.StrongEnd N`; (M) `MeasuredTower.MeasTowerG (SU N) βs` and (E) `ConstantPhysicsLine.ExistAlong N βs` along every tower, frequently near `0⁺` |
| Theorem 1.1 (one tower) | `ConstantPhysicsLine.clayStatementOf_of_tower`, `ConstantPhysicsLine.seed_near` | (M), (E) |
| Theorem 1.1 (weakest) | `OneInput.residual_of_reads`, `OneInput.clayStatementOf_of_reads'`; `CouplingTower.measTowerG_of_confinedAt_uv` | (UV), (E) |
| Theorem 1.1 (no critical point) | `OneInput.clayStatement_of_noCriticalPoint` | `DisclosureFloor.NoCriticalPoint` (stronger than (S)), the residual |
| definitions | `CouplingTower.CouplingTower`; `CouplingTower.StrongEnd`; `MeasuredTower.MeasTowerG`; `ConstantPhysicsLine.ExistAlong` | — |
