Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 04:16:33 UTC 2026

Sources: ticket, `docs/tickets/checks/T2371-check.lean`, RBM3D `Universality/Pins.lean`, `PinsDens.lean:180-260`, `GUELocalBootstrap.lean:905-960`, `Endpoints.lean`, `Test/Axioms.lean`, `docs/reports/T2162-portmap.md:204,206`; RBM2D `Main/BUniv.lean` (46 lines), `Main/BUnivHolds.lean` (61 lines), `Universality/Pins.lean:510` at RBM2D `9e0f275`.

### (i) Leaf table: arguments of `un_bUniv_of_rows'` (`PinsDens.lean:233`) against RBM2D `bUniv_of_rows` (`Pins.lean:510`)

Registry lines are in `RBM3D/Test/Axioms.lean` (`borrowedProps` :92, `owedProps` :183-212; the ticket's `:182`, `:190`, `:195-197` are one line lower than on `main` e586ec8: `UNBUniv` :183, `UNOUClaims` :191, band rows :196-198).

| # | leaf of `un_bUniv_of_rows'` | RBM2D leaf | status on `main` | producer of an owed leaf |
|---|---|---|---|---|
| 1 | `UNInfty1Row'` | `Infty1Row` | PROVED `un_infty1Row'` `GUETranslation.lean:787` | - |
| 2 | `UNUnivMainRow` | `UnivMainRow` | PROVED `univMainRow` `UnivMain.lean:533` | - |
| 3 | `UNClaimRow` | `ClaimRow` | PROVED `unClaimRow` `UnivMain.lean:476` | - |
| 4 | `UNEMCTE2Row` | `EMCTE2Row` | PROVED `unEMCTE2Row` `EMCTE2.lean:683` | - |
| 5 | `UNJakUywRow` | `JakUywRow` | PROVED `jakUywRow` `Uyw.lean:881` | - |
| 6 | `UNOURow` = `(∀d, UNMLOut d) → UNLocAvgBand → UNQueBand → UNOUClaims` (`Pins.lean:793`) | `OURow` (from `G1Row`) | PROVED `ouRow_of_pins g1Row g2bRow`: `ouRow_of_pins` `ZeroModeProfile.lean:719`, `g1Row` `GUEPhase/RandomLayerB.lean:468`, `g2bRow` `QUEFlow.lean:953`. Not unconditional: the row is an implication whose premises are leaves 10-12 | - |
| 7 | `UNGreenCorrAll` | `GreenCorrAll` | PROVED `greenCorrAll` `GreenCorr.lean:873` | - |
| 8 | `UNL32` | `L32` | BORROWED (`borrowedProps` :92; LSY Thm 2.2, DECISIONS §5) | external |
| 9 | `UNDensBandRow` (`Pins.lean:826`) | none (RBM2D proves it inside `Step1RegularityB`) | OWED, registry `:198`, owner comment "UN-01" | no ticket. `T2162-portmap.md:206` row UN-12 lists it, but T2208 (UN-12) and T2201 (UN-01c) do not prove it (T2201 only has `unDensBandRow'_of_row`, `PinsDens.lean:193`); `T2220` says "not used" |
| 10 | `UNTrLocalBandRow` (`Pins.lean:842`) | none (`Step1RegularityA`) | OWED, registry `:197`, owner "UN-01" | portmap row UN-10 (`T2162-portmap.md:204`) only; no ticket with group UN-10 in `docs/tickets/` |
| 11 | `UNNormBandRow` (`Pins.lean:834`) | none (`Step1RegularityA/B`) | OWED, registry `:196`, owner "UN-01" | same as 10 |
| 12 | `UNMLOut d`, `∀d` | `P7Out`, `P7ExpOut` (proved in RBM2D: `p7Out_holds`) | OWED, registry `:192`, consumed (ST-6/MA `STMainInd`) | ST-6/MA gate; no merged theorem |
| 13 | `UNLocAvgBand` | `locSC` (proved: `locSC_holds`) | OWED consumed MA input, registry `:193`; MA bridge `locSC_to_UNLocAvgBand` `Endpoints.lean:519` | MA-06 (`locSC` is registry `:231`, MA-04 chain) |
| 14 | `UNQueBand` | `QDiff` through `QUE_of_QDiff` | OWED consumed MA input, registry `:194`; bridge `QUE_to_UNQueBand` `Endpoints.lean:530` | MA-05/MA-06 (`QUE` registry `:232`) |
| 15 | `UNGUELocal` | `GUELocal` (proved: `gueLocal`) | OWED, registry `:184` | reduced to leaf 16 by merged `un_gueLocal_of_tail` `GUELocalBootstrap.lean:952` |
| 16 | `UNGUESchurTail` (`GUELocalBootstrap.lean:915`) | `GUESchurTail`, proved by RBM2D `GUELocalSchur.lean:516` | OWED, registry `:212` ("proved by UN-10 `GUELocalSchur`") | portmap row UN-10 only (needs `EigenInterlacing`, UN-03b, unwritten); no ticket |

Reading of the table:
- The check file's `BUnivFromLeaves` has leaves 8-15 as arguments (the ticket's list). Everything in rows 1-7 plugs in as a theorem.
- Leaf 16 is the owed pin under 15 and has a named producer in the registry comment ("UN-10 `GUELocalSchur`") and in the portmap; it has no ticket.
- Owed leaves with no ticket anywhere (report to the dispatcher): 9, 10, 11, 16. None blocks target 2 (they stay hypotheses): `state: returned` is not needed.
- Registry rows that stay: `UNBUniv` (not proved unconditionally: leaves 8-15 remain) and `UNOUClaims` (premises of leaf 6 remain). Target 4 is comment edits of `UNBUniv` and `UNOUClaims`, no `owedProps` line deleted. If leaves 9, 10 (or 11) are proved here as theorems with the statements of `Pins.lean:826-846` unchanged, their `owedProps` lines are deleted (leaf 10's statement already carries `UNLocAvgBand →` as a premise).

### (ii) Can each band row be proved here from merged lemmas? (routes; line counts are estimates)

**Leaf 9, `UNDensBandRow`. Yes (deterministic).** Take `κ' = min(κ,1)`, `δ = κ'/2` (`δ ≤ κ/2`; `|x-E| ≤ δ`, `|E| ≤ 2-κ` give `|x| ≤ 2-κ'/2`).
- Lower bound for `0 < η ≤ 10`: write `m = a+ib`; `msc_mul` gives `b² + bη = 1 + a² + a x ≥ 1 - x²/4 ≥ 7κ'/16`, and `b ≤ ‖msc‖ < 1` (`norm_msc_lt_one`) so `11 b ≥ 7κ'/16`, `c = 7κ'/176`. This is `un_msc_im_ge` (`Pins.lean:1378`, only `|x| ≤ 1/2`, constant `9/100`) re-run at general `κ'`; `fcs_msc_im_ge` (`FreeConvStability.lean:147`) is private and capped at `Im z ≤ 3`.
- Upper bound `C = 1` by `norm_msc_lt_one`. Lipschitz in `x`, `Lp = 1/c²`: `(m₁-m₂)(1-m₁m₂) = (z₁-z₂)m₁m₂`, `Re(1-m₁m₂) ≥ b₁b₂ ≥ c²` (the proof of `un_msc_lip`, `Pins.lean:1396`, with `c` in place of `9/100`), or `freeConvST_sub_le` through `freeConvST_zero_eq_msc` as in `un_msc_box_zero` (`PinsDens.lean:536`).
- Limit: `FreeConvStability.msc_tendsto_mE` (public, `|E| < 2`) and `mE_im` (`Semicircle.lean:42`): `Im mE E / π = √(4-E²)/(2π) = rhoSC E`.
- Estimate 120-170 lines. Numerical check of the constants below.

**Leaf 10, `UNTrLocalBandRow`. Yes, from `UNLocAvgBand` (its own premise).** `UNTrLocal sz band msc E δ` at `(ε,τ,D)`: event `{∃ z, |Re z - E| ≤ δ, N^{-1+ε} ≤ Im z ≤ 1, W^τ Bctl(n,1-Im z) < ‖stieltjesN(H) z - msc z‖}`. Since `δ ≤ κ/2`, `|E| ≤ 2-κ`: `|Re z| ≤ 2-κ/2`, so `z ∈ locDomain (κ/2) ε n`. `stieltjesN = N⁻¹ tr G = L^{-d} Σ_a (W^{-d} Σ_{x∈[a]} G_xx)` (`N = L^d W^d`, `card_Idx` `Sizes.lean:160`, blocks `Iblk` `:92`, `card_Iblk` `:95`), so the trace deviation is at most the largest block deviation; the event is inside the `UNLocAvgBand` event at `(κ/2, ε, τ, D)`, then `measure_mono`. No Gaussian input. Estimate 100-160 lines (the sum over blocks is the only fiddly step).

**Leaf 11, `UNNormBandRow`. Yes in principle, the most expensive.** `CV₀ = 3`. The coordinates of `ω` under `seqP` are `gaussianReal 0 (seqGvar)` (`seqP_map_eval`, `FineModel.lean:516`) with variance `≤ 1` (rows of `S` sum to 1, `FineModel.lean:640`; the coordinate variance is `S` or `S/2`). Chernoff: `P(|g| > N) ≤ 2 exp(-N²/2)`; union over at most `N²` coordinates; then `|h_xy| ≤ √2 N` and `|λ| ≤ N max|h_xy| ≤ √2 N² ≤ N³`. It needs the sub-Gaussian tail of `gaussianReal`, measurability/union bound over `Idx × Idx × Bool`, and the Gershgorin-type eigenvalue bound for a Hermitian matrix (no merged lemma found by grep of `RBM3D/Analysis` for an eigenvalue-vs-entry bound; RBM2D has `Step1RegularityB_eigenvalue_le`). Estimate 200-320 lines.

**Leaf 16 / 15.** `UNGUESchurTail` is the Schur complement + Hanson-Wright + Ward union bound (RBM2D `GUELocalSchur.lean`, 578 lines per portmap, with unwritten `EigenInterlacing`): not provable here within the stop line. Recommended for `bUniv_holds`: replace `UNGUELocal` by `UNGUESchurTail` through `un_gueLocal_of_tail` (the ticket allows it when the pin has a named producer: registry `:212` and portmap row UN-10 name `GUELocalSchur`; no ticket, see above). A statement-level cost: `bUniv_holds`'s hypotheses are then not literally a subset of `BUnivFromLeaves`'s (the ticket accepts this).

**Leaves 12-14** stay hypotheses (consumed MA/ST-6 pins; the MA bridges to `locSC`, `QUE` exist, `UNMLOut` has none).

### (i, cont.) Exponent / constant table

| quantity | value | constraint | slack |
|---|---|---|---|
| `d` | 3 | `3 ≤ d` (`UNBUniv`) | 0 (edge, as `Endpoints.lean:inst_BUniv`) |
| `𝔠` | 1/6 | `0 < 𝔠`, `N^𝔠 ≤ W` eventually | n=0: `N^𝔠 = 11.314 ≤ W = 32`; all `n < 3000` |
| `𝔡` | 1/10 | `0 < 𝔡`, `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` | n=0: `W^{-1.4} = 0.0078125 ≤ lam = 0.015625 ≤ 10` |
| `κ` | 1/10 | `0 < κ`, `|E| ≤ 2-κ` | `E = 0`: 1.9 |
| `k` | 1 | `1 ≤ k` | 0 |
| `O` | `bump` | `IsTestFun` (merged `bump_testFun`, as `inst_BUniv`) | - |
| `N` | `(WL)^3 = 2097152` at n=0 | `→ ∞` (`SizeTendsto`) | `N(10) ≈ 1.2e25` |
| band row 9 | `δ = κ'/2`, `c = 7κ'/176`, `C = 1`, `Lp = 1/c²` | `δ ≤ κ/2`, `c ≤ Im msc`, Lipschitz | `κ = 1/10`: `c = 0.00398` vs observed min `0.0956` (E=1.9) |
| band row 10 | `κ_loc = κ/2` | `|Re z| ≤ 2 - κ/2` | `κ=1/10, E=0, δ=1/20`: `0.05 ≤ 1.95` |
| band row 11 | `CV₀ = 3` | `√2 N² ≤ N^{CV₀}`, tail `≤ N^{-D}` | `N=2^21`: `ln(union) = -2.2e12 ≤ -D ln N` for all `D ≤ 1000` shown |

### (ii) Concrete nondegenerate instance (the data of `Endpoints.lean` `inst_BUniv`, line 600-606)

`d = 3`, `sz0` (`Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`, `𝒪 = bump`. Every deterministic hypothesis of `bUniv_holds` is discharged there; only leaves 8, 12-16 (and 9-11 if not proved) stay hypotheses. Not vacuous: `N = 2097152`, `W = 32`, `L = 4`, no empty index, no collapsed window. External hypothesis `UNL32` is borrowed (registry :92); the concrete limit computation for its premises at these sizes is not redone here (this ticket adds no new external hypothesis; the `Bandwidth`/`WO` rows above are the parameter facts of the instance).

```
$ python3 -I .../scratchpad/T2371/inst.py     (script kept in the scratchpad, not in the repo)
n=0: L,W,N,lam = 4 32 2097152 0.015625
Bandwidth W>=N^c (n<3000): True ; WO W^{-d/2+dd}<=lam<=1/dd: True ; n=0 slack: N^c=11.314<=W=32 ; W^(-1.4)=0.007813<=lam=0.015625<=10
N(n)->inf: N(0),N(10),N(100)= 2097152 11659991713824860234842112 2508503070931240586116700541954360451530752
|E|=0<=2-kappa=1.90; k=1>=1; kappa>0; d=3>=3
kappa=0.1 E=0: delta=0.05 c=7k'/176=0.00398 <= min Im msc=0.09902 : True ; Lip_obs=0.012 <= 1/c^2=63216.3 : True
kappa=0.1 E=1.9: delta=0.05 c=7k'/176=0.00398 <= min Im msc=0.09556 : True ; Lip_obs=2.166 <= 1/c^2=63216.3 : True
kappa=0.1 E=-1.9: delta=0.05 c=7k'/176=0.00398 <= min Im msc=0.09556 : True ; Lip_obs=2.166 <= 1/c^2=63216.3 : True
kappa=0.01 E=1.99: delta=0.005 c=7k'/176=0.00040 <= min Im msc=0.07062 : True ; Lip_obs=6.971 <= 1/c^2=6321632.7 : True
kappa=1 E=1: delta=0.5 c=7k'/176=0.03977 <= min Im msc=0.09694 : True ; Lip_obs=0.556 <= 1/c^2=632.2 : True
kappa=1.5 E=0.5: delta=0.5 c=7k'/176=0.03977 <= min Im msc=0.09809 : True ; Lip_obs=0.284 <= 1/c^2=632.2 : True
E=0: Im msc(E+1e-9 i)/pi=0.31830989 ; rhoSC=0.31830989
E=1.9: Im msc(E+1e-9 i)/pi=0.09939223 ; rhoSC=0.09939223
max |Re z| = 0.05 <= 2-kappa/2 = 1.95 ; blocks: L^d*W^d = 2097152 = N = 2097152
D=1: ln(union)=-2.199e+12 <= -D ln N = -1.456e+01 : True   (D=10, 100, 1000 likewise True)
sqrt2*N^2 <= N^3 at N=2097152: True
```
(The `msc` grid values are sampled over 41 points and `η ∈ {1e-6,...,10}`: a sanity check of the constants, not a proof.)

### (iii) Plan against the stop line 500 (`wc -l` of the two files together; all line counts are estimates)

1. `Main/BUniv.lean`: `unOURow`, `bUniv_of_leaves` (as the check file's `BUnivFromLeaves`): about 40 lines, as RBM2D's 46.
2. `Main/BUnivHolds.lean` skeleton: `bUniv_holds` with leaves 8, 12-15 (or 16 in place of 15) plus the three band rows as hypotheses, docstring listing the leaves of the table above, and the nonempty instance at the data above: about 100-130 lines. Running total about 150-170. Commit.
3. Prove leaf 9 (`UNDensBandRow`): +120-170, total about 300-340. Commit.
4. Prove leaf 10 (`UNTrLocalBandRow`): +100-160, total about 400-500. Commit if `wc -l` stays under 500.
5. Leaf 11 (`UNNormBandRow`): +200-320 does not fit after step 4. It stays a hypothesis of `bUniv_holds` and is reported as owed with no ticket (together with leaf 16). If steps 3-4 come in at the low estimates and 11 would fit in the remainder, the prover may take it; otherwise do not start it.
6. Registry: comment edits for `UNBUniv`, `UNOUClaims`; delete `owedProps` lines of `UNDensBandRow` and `UNTrLocalBandRow` only if steps 3 and 4 land as theorems; run the pre-check `import RBM3D` + `import RBM3D.Main.BUnivHolds` + `#assert_rbm_axioms`.

Paper-delta candidate: T2371a: leaf `UNGUELocal` replaced by `UNGUESchurTail` in `bUniv_holds` (not a paper statement; a reduction of a Lean pin).

### Verdicts

- Target 1 (`unOURow`, `bUniv_of_leaves`): PASS. All six rows plus `ouRow_of_pins g1Row g2bRow` are merged theorems with the signatures read above (`un_bUniv_of_rows'` takes `UNInfty1Row'`, `UNUnivMainRow`, `UNClaimRow`, `UNEMCTE2Row`, `UNJakUywRow`, `UNOURow`, three band rows, then `UNL32`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNGUELocal`, `UNGreenCorrAll`).
- Target 2 (`bUniv_holds`): PASS. Leaves that may drop: 9 and 10 (routes above), 11 only if it fits.
- Target 3 (instances): PASS. Every deterministic hypothesis holds at the data above.
- Target 4 (registry): PASS. `UNBUniv` and `UNOUClaims` stay owed (conditional proofs); comment edits only, plus deletions of lines 9-10 if proved.
- To the dispatcher (UN closing REQ): owed leaves with no ticket in any plan: `UNNormBandRow`, `UNTrLocalBandRow`, `UNDensBandRow` (if not proved here), `UNGUESchurTail`; and the consumed MA/ST-6 leaves `UNMLOut`, `UNLocAvgBand`, `UNQueBand`.

## (b) Script output — Sat Oct 10 05:29:48 UTC 2026

Resume after the API stop. Ticket Amend 1 (`docs/tickets/T2371-amend-1.md`) applied: leaf 11 `UNNormBandRow` stays a hypothesis of `bUniv_holds`; the leaf-11 proof that branch commit ba6da7e contained is removed from the tree; registry line of `UNNormBandRow` is untouched.

```
$ git log --oneline main..t/T2371
8f08c54 T2371: Amend 1: leaf UNNormBandRow stays a hypothesis of bUniv_holds (producer T2372), docstring names producers, registry line of UNNormBandRow kept
b01782f T2371: registry (owner comments UNBUniv, UNOUClaims; delete owed lines of the three proved band rows)
ba6da7e T2371: prove leaf UNNormBandRow (unNormBandRow); bUniv_holds leaves: UNL32, UNMLOut, UNLocAvgBand, UNQueBand, UNGUESchurTail; docstring, two instances
478ec20 T2371: prove leaf UNTrLocalBandRow (unTrLocalBandRow); bUniv_holds drops it
c517507 T2371: prove leaf UNDensBandRow (unDensBandRow); bUniv_holds drops it
8653af4 T2371: skeleton unOURow, bUniv_of_leaves, bUniv_holds (3 band rows as hypotheses) + instance

$ lake build RBM3D.Main.BUniv RBM3D.Main.BUnivHolds 2>&1 | grep -v "^info:" | tail -6
ℹ [3874/3885] Replayed RBM3D.Induction.LoopC2N
ℹ [3875/3885] Replayed RBM3D.Universality.GUEPhase.DuhamelA1
Build completed successfully (3885 jobs).
$ lake build RBM3D.Main.BUniv RBM3D.Main.BUnivHolds 2>&1 | grep -c "Main/BUniv"   (warnings or errors naming the new files)
0

$ wc -l RBM3D/Main/BUniv.lean RBM3D/Main/BUnivHolds.lean   (stop line 500)
      52 RBM3D/Main/BUniv.lean
     261 RBM3D/Main/BUnivHolds.lean
     313 total

$ git diff main...t/T2371 --stat
 RBM3D/Main/BUniv.lean      |  52 +++++++++
 RBM3D/Main/BUnivHolds.lean | 261 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   6 +-
 3 files changed, 315 insertions(+), 4 deletions(-)

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Main/BUniv.lean RBM3D/Main/BUnivHolds.lean   (no output = none)
```

```
$ lake env lean ax2.lean   (scratch: BUnivFromLeaves copied from docs/tickets/checks/T2371-check.lean; #print axioms; #check)
  'RBM.Endpoints.unOURow' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.Endpoints.bUniv_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.Endpoints.unDensBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.Endpoints.unTrLocalBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
  Endpoints.bUniv_holds : UNNormBandRow →
    UNL32 → (∀ (d : ℕ), UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNBUniv
  Endpoints.bUniv_of_leaves : UNDensBandRow →
    UNTrLocalBandRow → UNNormBandRow → UNL32 → (∀ (d : ℕ), UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNBUniv
  (exit 0; the file contains: example : RBM.Endpoints.T2371Check.BUnivFromLeaves := @RBM.Endpoints.bUniv_of_leaves)

$ target statements (sed of the files)
-- RBM3D/Main/BUniv.lean:41
theorem unOURow : UNOURow := ouRow_of_pins GUEPhase.g1Row g2bRow
-- RBM3D/Main/BUniv.lean:45-50
theorem bUniv_of_leaves :
    UNDensBandRow → UNTrLocalBandRow → UNNormBandRow →
      UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNBUniv :=
  fun rD rT rN h32 hML hLoc hQ hGL =>
    un_bUniv_of_rows' un_infty1Row' univMainRow unClaimRow unEMCTE2Row jakUywRow unOURow rD rT rN
      h32 hML hLoc hQ hGL greenCorrAll
-- RBM3D/Main/BUnivHolds.lean:227-231
theorem bUniv_holds :
    UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail →
      UNBUniv :=
  fun hN h32 hML hLoc hQ hT =>
    bUniv_of_leaves unDensBandRow unTrLocalBandRow hN h32 hML hLoc hQ (un_gueLocal_of_tail hT)
-- RBM3D/Main/BUnivHolds.lean:119 and :205 (leaves proved here)
theorem unDensBandRow : UNDensBandRow := by
theorem unTrLocalBandRow : UNTrLocalBandRow := by
```

```
$ sed -n 236,261p RBM3D/Main/BUnivHolds.lean   (the two compiled instances; built by lake build RBM3D.Main.BUnivHolds above)

/-- **`bUniv_holds` at the merged instance data** `sz0`, `d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`, `k = 1`, `κ = 1/10`,
`E = 0`, `𝒪 = bump`: every deterministic hypothesis is discharged, only the leaves stay hypotheses. -/
example (hN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand)
    (hT : UNGUESchurTail) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0) :=
  bUniv_holds hN h32 hML hLoc hQ hT 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible 1 le_rfl (1 / 10)
    (by norm_num) 0 (by norm_num) bump bump_testFun

/-- The same at the edge energy `E = 19/10 = 2 - κ` of the allowed window. -/
example (hN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand)
    (hT : UNGUESchurTail) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) (19 / 10) (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues
        ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) (19 / 10) (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0) :=
  bUniv_holds hN h32 hML hLoc hQ hT 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible 1 le_rfl (1 / 10)
    (by norm_num) (19 / 10) (by norm_num) bump bump_testFun

end Inst

end RBM.Endpoints

$ registry pre-check (temporary, uncommitted): lake env lean precheck.lean, precheck.lean = "import RBM3D / import RBM3D.Main.BUnivHolds / #assert_rbm_axioms", after lake build RBM3D.Test.Axioms
axiom audit: 10835 theorems, 3186 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
84:  RBM.Univ.UNBUniv: 4 [no certificate]
97:  RBM.Univ.UNNormBandRow: 18 [no certificate]
111:  RBM.Univ.UNGUESchurTail: 4 [no certificate]
173: RBM.Univ.UNBUniv,
non-vacuity certificates: 0 of 126 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would 
exit=0

$ full lake build with the two temporary root imports added to RBM3D.lean (restored afterwards; git status of RBM3D.lean clean)
Build completed successfully (4183 jobs).
lake build  46.29s user 6.30s system 104% cpu 50.248 total
0

$ name-clash grep on main (declarations of the new public names; docstring hits excluded by the pattern)
unOURow:        0
bUniv_of_leaves:        0
bUniv_holds:        0
unDensBandRow:        0
unTrLocalBandRow:        0

$ RBM2D port: git -C ../RBM2D --no-optional-locks log -1 --format=%h ; diff --stat against the commit of section (a)
9e0f275
(empty diff-stat: the RBM2D files are unchanged since 9e0f275; ported: RBM2D/Main/BUniv.lean:38 ouRow_of_g1Row, :42 bUniv_of_g1Row; RBM2D/Main/BUnivHolds.lean:31 bUniv_holds, as at commit 9e0f275)
```

### Narrative (b)
- Targets 1-2. `unOURow` (`Main/BUniv.lean:41`) and `bUniv_of_leaves` (`:45`) are RBM2D's `ouRow_of_g1Row` and `bUniv_of_g1Row` re-plugged into `un_bUniv_of_rows'`; the check file's `example : BUnivFromLeaves := @bUniv_of_leaves` compiles (exit 0 above).
- `bUniv_holds` (`Main/BUnivHolds.lean:227`) has the hypotheses `UNNormBandRow`, `UNL32`, `∀ d, UNMLOut d`, `UNLocAvgBand`, `UNQueBand`, `UNGUESchurTail`. These are a subset of `BUnivFromLeaves`'s leaves except that `UNGUESchurTail` replaces `UNGUELocal` through `un_gueLocal_of_tail` (the ticket allows it; paper-delta candidate T2371a).
- Leaves proved here: `unDensBandRow` (`:119`; `κ' = min κ 1`, `δ = κ'/2`, `c = 7κ'/176`, `C = 1`, `Lp = 1/c²`, limit by `FreeConvStability.msc_tendsto_mE`) and `unTrLocalBandRow` (`:205`; from its own premise `UNLocAvgBand`, trace = average of block averages, `BUniv_trace_le`). Both statements are those of `Pins.lean:826, :842`, unchanged.
- The leaf table with status and producer of every leaf of `un_bUniv_of_rows'` is the module docstring of `Main/BUnivHolds.lean` (lines 8-38), as the ticket asks. Producers named there: `UNNormBandRow` T2372, `UNGUESchurTail` T2373, `UNMLOut` ST-6, `UNLocAvgBand` and `UNQueBand` MA inputs, `UNL32` borrowed (Amend 1).
- Amend 1: no proof of leaf 11 is in the tree (`git diff main...t/T2371 | grep -c "^+.*unNormBandRow"` = 1: the docstring line that names T2372's producer; the type `UNNormBandRow` occurs as a hypothesis). `Test/Axioms.lean`: the `UNNormBandRow` line is as on `main`; the lines of `UNTrLocalBandRow` and `UNDensBandRow` are deleted (proved here as theorems, statements unchanged); owner comments of `UNBUniv` and `UNOUClaims` updated (comment edits only).
- Stop line: `wc -l` of the two new files is 313 (stop 500). No ticket scope exceeded: the diff touches the two new files and `Test/Axioms.lean` only; `RBM3D.lean` was restored with `git checkout -- RBM3D.lean` and is not committed.
- Instances: both `example`s (E = 0 and E = 19/10 = 2 - κ) apply `bUniv_holds` at `sz0`, `d = 3`, `(𝔠,𝔡) = (1/6,1/10)`, `k = 1`, `κ = 1/10`, `𝒪 = bump`. The deterministic hypotheses (`3 ≤ d`, `sz0_admissible`, `1 ≤ k`, `0 < κ`, `|E| ≤ 2 - κ`, `bump_testFun`) are discharged; only the leaves stay hypotheses of the examples. The numeric non-degeneracy check of these data is in section (a).
- Special case: `bUniv_holds` is conditional on the six leaves; it is not the unconditional Theorem 2.4 (CLAUDE.md §5.6). The registry pins `UNBUniv` and `UNOUClaims` stay owed.

## (c) Verified Mathlib names (`#check` in a scratch file, output below)
```
Complex.abs_re_le_norm : ∀ (z : ℂ), |z.re| ≤ ‖z‖
Complex.abs_im_le_norm : ∀ (z : ℂ), |z.im| ≤ ‖z‖
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Complex.re_le_norm : ∀ (z : ℂ), z.re ≤ ‖z‖
Complex.im_le_norm : ∀ (z : ℂ), z.im ≤ ‖z‖
Finset.sum_fiberwise : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ] 
norm_sum_le : ∀ {ι : Type u_1} {E : Type u_2} [inst : SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E), ‖∑ i ∈ s, f 
ZMod.card : ∀ (n : ℕ) [inst : Fintype (ZMod n)], Fintype.card (ZMod n) = n
Finset.sum_const : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card
Finset.card_univ : ∀ {α : Type u_1} [inst : Fintype α], Finset.univ.card = Fintype.card α
nsmul_eq_mul : ∀ {α : Type u_1} [inst : NonAssocSemiring α] (n : ℕ) (a : α), n • a = ↑n * a
MeasureTheory.measure_mono : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeas
Real.norm_eq_abs : ∀ (r : ℝ), ‖r‖ = |r|
norm_inv : ∀ {α : Type u_1} [inst : NormedDivisionRing α] (a : α), ‖a⁻¹‖ = ‖a‖⁻¹
norm_pow : ∀ {α : Type u_1} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass α] (a : α) (n : ℕ), ‖a ^ n‖ = ‖a‖ ^
Complex.norm_natCast : ∀ (n : ℕ), ‖↑n‖ = ↑n
abs_le : ∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b ↔ -
sq_le_sq' : ∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {a b : α}, -b ≤ a → a ≤ b 
```

## (d) Open issues and paper-delta candidates — Sat Oct 10 05:30:55 UTC 2026
- T2371a: `UNGUELocal` is replaced by `UNGUESchurTail` in `bUniv_holds` (reduction of a Lean pin through `un_gueLocal_of_tail`, not a paper statement).
- Lead for T2372 (not part of this ticket's diff): branch commit ba6da7e contains a proof `unNormBandRow` of `UNNormBandRow` (`CV₀ = 3`, sub-Gaussian tail of `seqP` coordinates, union bound, `‖H‖_∞` eigenvalue bound); `lake env lean` of that commit's `Main/BUnivHolds.lean` exited 0 on Sat Oct 10 05:29:36 UTC 2026. It was removed from the tree by Amend 1.
- Producers still owed (by Amend 1): `UNNormBandRow` T2372, `UNGUESchurTail` T2373. Consumed inputs without a merged theorem: `UNMLOut` (ST-6), `UNLocAvgBand`, `UNQueBand` (MA). Borrowed: `UNL32`.
