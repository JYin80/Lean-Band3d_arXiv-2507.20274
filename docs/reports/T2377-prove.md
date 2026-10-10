Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 09:20:56 UTC 2026

Base: `main` = 17ccf68 (T2375 merged; `unMLOut_holds` at `Induction/MainIndHolds.lean:61`, namespace `RBM.Univ`). All line numbers below are of that `main`.

### (i) Exponent table, merged signatures, registry table, `τ₀`, plan

**Constants** (`Defs/Sizes.lean`: `sz0` :260, `Admissible` :177, `Bandwidth` :168, `WO` :164; `ouTauMax` `Universality/ZeroModeProfile.lean:78`)

| constant | value (n = 0) | constraint | slack |
|---|---|---|---|
| `𝔠` | 1/6 | `W ≥ N^𝔠`, `N = (WL)^3` (`Main_DEL_COND`) | `W/N^𝔠 = 2.828` at n=0, `11.3` at n=1, grows (`m^2`, `m = n+1`) |
| `𝔡` | 1/10 | `W^{-3/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`eq:WO`) | lower: `lam/W^{-7/5} = 2m` (2 at n=0); upper: `1/64 ≤ 10` |
| `(L,W,lam,N)` | `(4m, (2m)^5, (2m)^{-6}, 128^3 m^18)` | `N → ∞`, `3 ≤ L` | n=0: `(4, 32, 1/64, 2097152)` |
| `κ` | 1/10 | `|E| ≤ 2-κ` | `E = 0`: 1.9; `E = 19/10`: 0 (edge) |
| `ε₀, c` (QUE) | `1/30, 1/60` | `0<ε₀<𝔡/2=1/20`; `0<c<ε₀`; `c<𝔡/5=1/50` | `1/20-1/30=1/60`; `1/30-1/60=1/60`; `1/50-1/60=1/300` |
| `ε` (locSC, QDiff) | 1/20 | `ε > 0` | domain `N^{-1+ε} ≤ Im z ≤ 1`: `Im z = N^{-4/5}` fits |
| `τ, D` | locSC/QDiff `1/10, 2`; decol `1/10, 1`; QUE `τ=1/10` | all `> 0` | none needed (no upper bound) |
| `τ₀ = ouTauMax 𝔠 𝔡` | `min(min(𝔠/12, 𝔠𝔡/12), 1/100) = 1/720` | `0 < τU ≤ τ₀` for `UNOUQUE` | `τU = 1/1000 ≤ 1/720`, slack `1/720-1/1000 = 7/18000` |
| `k, E, 𝒪` (BUniv) | `1, 0, bump` | `E` in the `2-κ` bulk; `bump` smooth compact | `UNL32` is the only hypothesis left |

**Target signatures composed** (all merged; `⟶` = type after unfolding the `def`)

| target | composition | signature used |
|---|---|---|
| `locSC_holds : locSC` | `netLoc (locSCFixed_of_ML unMLOut_holds)` | `locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed` `Main/FixedZ.lean:100`; `netLoc : MANetLoc` `Main/ZNet.lean:999`, `MANetLoc := locSCFixed → locSC` :82 |
| `QDiff_holds : QDiff` | `netQD (QDiffFixed_of_ML unMLOut_holds)` | `FixedZ.lean:419`; `netQD : MANetQD` `ZNet.lean:1024`, `MANetQD := QDiffFixed → QDiff` :85 |
| `QUE_holds : QUE` | `QUE_of_QDiff QDiff_holds` | `QUE_of_QDiff : MAQUE` `Main/QUEFromQDiff.lean:502`, `MAQUE := QDiff → QUE` :234 |
| `decol_holds : decol` | `decol_of_locSC locSC_holds` | `decol_of_locSC : MADecol` `FixedZ.lean:789`, `MADecol := locSC → decol` :787 |
| `unLocAvgBand_holds`, `unQueBand_holds` | the two bridges | `locSC_to_UNLocAvgBand : locSC → UNLocAvgBand` `Endpoints.lean:519`; `QUE_to_UNQueBand : QUE → UNQueBand` :530 (no other premise) |
| `unOUClaims_holds : UNOUClaims` | `unOURow unMLOut_holds unLocAvgBand_holds unQueBand_holds` | `unOURow : UNOURow` `Main/BUniv.lean:41`; `UNOURow := (∀ d, UNMLOut d) → UNLocAvgBand → UNQueBand → UNOUClaims` `Universality/Pins.lean:793` |
| `unBUniv_of_L32 : UNL32 → UNBUniv` (+ `BUniv` form) | `bUniv_holds unNormBandRow h32 unMLOut_holds unLocAvgBand_holds unQueBand_holds gueSchurTail` | `bUniv_holds : UNNormBandRow → UNL32 → (∀ d, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNBUniv` `Main/BUnivHolds.lean:227`; `unNormBandRow` `NormBand.lean:173`, `gueSchurTail` `GUELocalSchur.lean:540` (both premise-free); `abbrev BUniv := UNBUniv` `Endpoints.lean:209` |
| `unClaimRowBA_holds : UNClaimRowBA` | `unClaimRowk _` | `unClaimRowk : ∀ K, UNClaimRowk K` `UnivMain.lean:466`; `UNClaimRowBA := UNClaimRowk (fun d => UNKind.ba d)` `BA/UNPins.lean:136` (in scope: `MainIndOut` imports `BA.UNPins`) |
| `band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff` | the five above; no cycle (`locSC`, `QUE` do not use `UNBUniv`) | targets are `Endpoints.lean:165, 172, 182, 197, 209`; four conjuncts are unconditional, `UNL32` enters only `BUniv` |

Scan note (`Test/Axioms.lean:423-446`, `scanPremises`): a premise counts as proved when a theorem's conclusion head is that constant. So each new theorem must have the registered predicate itself as head (`locSC_holds : locSC`, not an alias such as `MANetLoc`); `BUniv` needs its own head (`UNL32 → BUniv`), `band_terminal` (head `And`) proves none of them.

**(iii) `UNOUQUE` / `τ₀` decision.** `unOURow` does not expose `τ₀`: `UNOUClaims` is `∃ τ₀, 0 < τ₀ ∧ ∀ τU, 0 < τU → τU ≤ τ₀ → UNOUQUE sz 𝔡 τU ∧ UNOUDiag sz τU` (`Pins.lean:659-661`), so `unOURow`'s type hides it. The value is visible one level down: `ouRow_of_pins` (`ZeroModeProfile.lean:719-723`) takes `τ₀ := ouTauMax 𝔠 𝔡`, and its premises `UNG1Row` (:126-129) and `UNG2bRow` (:132-134) quantify over `τU ≤ ouTauMax 𝔠 𝔡` explicitly. Literal reading of the ticket ("if `unOURow` exposes") gives: no. Proposed (needs the auditor to accept the reading): a projection **not through `unOURow`**, `∀ d, 3 ≤ d → ∀ 𝔠 𝔡 sz, sz.Admissible 𝔠 𝔡 → ∀ τU, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUQUE sz 𝔡 τU`, body `g2bRow d hd 𝔠 𝔡 sz hA τU hτ hle (GUEPhase.g1Row unMLOut_holds unLocAvgBand_holds unQueBand_holds d hd 𝔠 𝔡 sz hA τU hτ hle).2` (`g1Row` `GUEPhase/RandomLayerB.lean:468`, `g2bRow` `QUEFlow.lean:953`, both unconditional rows). This is exactly the supervisor's C1 form with `τ₀ = ouTauMax`. If the auditor reads "exposes" literally, drop it: `UNOUQUE` stays owed with a comment saying `UNOUClaims` hides `τ₀`. Either way is consistent; the registry rows below are marked accordingly.

**Registry table** (`Test/Axioms.lean`, lines at 17ccf68; find by name). Old class = list the name is in now.

| name | old | new | justification |
|---|---|---|---|
| `UNBUniv` (:168) | owed | deleted | `unBUniv_of_L32 : UNL32 → UNBUniv` (premise only the borrowed `UNL32`) |
| `Endpoints.decol, locSC, QUE, QDiff` (:209-212) | owed | deleted | `decol_holds, locSC_holds, QUE_holds, QDiff_holds` (no premise) |
| `Endpoints.BUniv` (:213) | owed | deleted | `UNL32 → BUniv` (same head, abbrev) |
| `UNOUClaims` (:175) | owed | deleted | `unOUClaims_holds` (no premise) |
| `UNLocAvgBand` (:176), `UNQueBand` (:177) | owed | deleted | `unLocAvgBand_holds`, `unQueBand_holds` (no premise) |
| `UNClaimRowBA` (:198) | owed | deleted | `unClaimRowBA_holds := unClaimRowk _` |
| `UNOUQUE` (:171) | owed | deleted **iff** the projection of (iii) is written; else stays owed | projection concluding `UNOUQUE sz 𝔡 τU` for `0<τU≤ouTauMax 𝔠 𝔡` |
| `UNTrLocal` (:169) | owed | structural | band `unTrLocalBandRow` (`BUnivHolds.lean:205`); BA `UNTrLocalBARow` (registered owed, BA-N1) |
| `UNNormBound` (:178) | owed | structural | band `unNormBandRow` (`NormBand.lean:173`); BA `UNNormBARow` (BA-N1) |
| `UNClaim417` (:170) | owed | structural | band `unClaimRow` (`UnivMain.lean:476`) + `un_claimAll_of_rows` (`Pins.lean:849`); BA `un_claimAll_of_rowsBA` (`BA/UNPins.lean:142`), carried by `UNEMCTE2RowBA`, `UNJakUywRowBA` (BA-N3), `UNOURowBA`, and `UNClaimRowBA` (discharged here) |
| `GUEPhase.GUEPathBounds` (:202) | owed | structural | band `gueGrid_pathBounds` (`GUEPhase/PathBounds.lean:550`) / `g1Row`; BA carried by `UNG1Rowk` at `UNKind.ba` (BA-C5) |
| `UNTrLocalInit'` (:190) | owed | structural | band `unTrLocalInit'_band_zero` (`PinsC2.lean:792`); BA `UNTrLocalInitBARow'` (BA-N1) |
| `UNQuek` (:186) | owed | structural (optional) | BA `UNQueBA` (`BA/UNPins.lean:99`, not itself a registered name: it is proved from the registered `BAEnd_QUEL` (BA-M3) by `UNQueBA_of_BAEnd_QUEL` :357); the pointer names `BAEnd_QUEL` |
| `UNLocAvgk` (:187) | owed | structural (optional) | BA `UNLocAvgBA` (registered, BA-M1) |
| `UNOUQUEk` (:182) | owed | structural (optional) | BA `UNOURowBA` (registered; `ouRowk_of_pins` `OUInterfaceK.lean:292` + BA-C3, BA-C5) |
| `UNClaim417C` (:179) | owed | structural (optional) | `un_claimAll_of_rowsBA` as for `UNClaim417` |
| `UNEMCTE2k, UNEMCTE2Rowk, UNJakk, UNUywk, UNJakUywRowk, UNCoreC'', UNGreenCorrC, UNGreenCorrAllC` (:180, :181, :183, :184, :185, :188, :189, :191) | owed | owed (not moved) | E1-E4: owner comment becomes "BA-N3 (stage M/N; supervisor 0853 C2)" |
| `UNEMCTE2RowBA` (:196), `UNJakUywRowBA` (:197) | owed | owed | E1/E2 BA rows: owner comment becomes BA-N3 (the other `…BA` rows keep their owners) |
| `STLWB` (:129), `STLWT` (:130), `STOptL2` (:128) | owed | superseded | no `3 ≤ d` premise in the definitions (`Step2Defs.lean:406, 421, 667`), so `∀ d, P d` is unprovable; guarded replacements: `STLWB_of_LWterm (hd : 3 ≤ d) : LWterm d → STLWB d` (`Step2Events.lean:1355`) at `lwterm_holds` (`Graph/LWTermHolds.lean:682`); `STLWT_of_LWtermExp hd` (:1427) at `lwtermExp_holds` (:1604); `stOptL2_of_pins hd` (`OptL2b.lean:195`) at the two above and `stGridMart_holds` (`Path/DifREP2.lean:2283`). Not yet done by T2375 (the three lines are still in `owedProps` with "stays owed"). |

Observation for the dispatcher: `supersededProps` is documented as "consumed by nothing the closure needs"; these three are consumed by guarded theorems (`stStep2_holds`, `MainIndHolds.lean:38-41`). The ticket fixes the class; the comment should say "unguarded form superseded by the guarded consumer", and the docstring of `supersededProps` should be widened (paper-delta/doc candidate `T2377a`).

**(iv) Plan against stop line 500** (`wc -l RBM3D/Main/BandTerminal.lean`): header and docstring ~35; the 10 theorems of target 1 (one line each plus docstring) ~60; the `UNOUQUE` projection ~15; `band_terminal` ~10; instances at `Endpoints.lean` §`Inst` (`inst_decol`, `inst_locSC`, `inst_QUE`, `inst_QDiff`, `inst_BUniv`, :561-605, each taking the endpoint as hypothesis, applied to the projections of `band_terminal h32`) plus the projection at `τU = 1/1000` ~60-80. Central ~200, upper ~300. `Test/Axioms.lean` is not counted by `wc`. Registry pre-check: `import RBM3D` + `import RBM3D.Main.BandTerminal` + `#assert_rbm_axioms`, uncommitted.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` at `(𝔠,𝔡) = (1/6, 1/10)`, `κ = 1/10`; decol `(τ,D)=(1/10,1)`; locSC/QDiff `(ε,τ,D)=(1/20,1/10,2)`; QUE `(ε₀,c,τ)=(1/30,1/60,1/10)`; BUniv `k=1, E=0, 𝒪=bump`; `UNOUQUE` at `τU = 1/1000`. The instance applies the theorems at `n = 0` data (`N = 2097152`) and eventually in `n`; all hypotheses hold for every `n ≥ 0`, not only for huge `n`.

Command (script in the scratchpad `T2377/inst.py`, Python only):
`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2377/inst.py`

```
tau0 = ouTauMax = 1/720  tauU=1/1000 ok: True
n=0 L=4 W=32 lam=1/64 N=2097152 | W>=N^c:True (W/N^c=2.828) WO_lo:True (ratio lam/W^-1.4=2.000) WO_hi:True
n=1 L=8 W=1024 lam=1/4096 N=549755813888 | W>=N^c:True (W/N^c=11.314) WO_lo:True (ratio lam/W^-1.4=4.000) WO_hi:True
n=2 L=12 W=7776 lam=1/46656 N=812479653347328 | W>=N^c:True (W/N^c=25.456) WO_lo:True (ratio lam/W^-1.4=6.000) WO_hi:True
n=5 L=24 W=248832 lam=1/2985984 N=212986666247081951232 | W>=N^c:True (W/N^c=101.823) WO_lo:True (ratio lam/W^-1.4=12.000) WO_hi:True
n=50 L=204 W=11040808032 lam=1/1126162419264 N=11425969980610183329762199225554173952 | W>=N^c:True (W/N^c=7356.739) WO_lo:True (ratio lam/W^-1.4=102.000) WO_hi:True
N(n=0) = (32*4)^3 = True
|E|<=2-kappa: E=0: True  E=19/10: True
QUE: 0<e0<dd/2: True  0<c<e0: True  c<dd/5: True  tau=1/10>0
locSC/QDiff: eps=1/20>0 tau=1/10>0 D=2>0; decol tau=1/10 D=1; BUniv k=1,E=0
eps=0.1: N^(-1+eps)=2.044e-06 <= Im z=8.764e-06 <= 1 : True  |Re z|=1/2<=1.9
eps=0.05: N^(-1+eps)=9.873e-07 <= Im z=8.764e-06 <= 1 : True  |Re z|=1/2<=1.9
UNL32 arithmetic premises (n=0, tau=1/2): True True True True True True
rho_sc(0)=1/pi: True  int O = 0.44399382
rho=0.31831  int O(rho a) rho da = 0.44399382
rho=0.20000  int O(rho a) rho da = 0.44399382
rho=0.50000  int O(rho a) rho da = 0.44399382
rho=1.00658  int O(rho a) rho da = 0.44399382
```

External hypothesis `UNL32` (borrowed, `Pins.lean:281`; LSY arXiv:1609.09011 Thm 2.2, v4 with the factors `ρ^{-k}`), concrete limit at `k = 1`, bulk `E = 0`. In `kPoint 1 O' E λ = Σ_i O'(N(λ_i - E))` the expectation is `∫ O'(α) p^{(1)}(E + α/N) dα` with `p^{(1)} → ρ` (`Pins.lean:74-76`). Left side: `O' = O(ρ_n ·)` with `ρ_n = lim Im m_n(E+iη)/π = ρ_fc(E)`, limit `∫ O(ρ_n α) ρ_n dα = ∫ O(β) dβ`. Right side: `ρ = ρ_sc(0) = √4/(2π) = 1/π`, limit `∫ O(β) dβ`. So the difference tends to `0` for every `ρ_n > 0`; the script shows `∫ O(ρ a) ρ da` is the same number for `ρ ∈ {1/π, 0.2, 0.5, 1/(π√0.1)}` (stand-in smooth compact `O(x) = exp(-1/(1-x²))`, not the Lean `bump`; the identity is `∫O(ρα)ρ dα = ∫O` by substitution). The factors `ρ^{-k}` are in the Lean statement (`O (ρ n • α)`, `O (rhoSC (E n) • α)`), so the two limits agree and `UNL32` is not contradicted by its other premises; its six arithmetic premises hold at `N = 2097152`, `τ = 1/2` (script line above; Lean twin `inst_L32_arith_half`, `Pins.lean:1555`). The regularity premise `IsRegular32` is not instantiated by preflight: it is the content of the merged band proofs that consume `UNL32` (not this ticket's hypothesis set, which keeps `UNL32` as a hypothesis of the example).

### Verdicts

- Target 1 (`locSC_holds`, `QDiff_holds`, `QUE_holds`, `decol_holds`, `unLocAvgBand_holds`, `unQueBand_holds`, `unOUClaims_holds`, `unBUniv_of_L32` + `BUniv` form, `band_terminal`, `unClaimRowBA_holds`): **PASS** (every composition type-matches the merged signatures listed in (i); no exponent to close).
- Target 1, `UNOUQUE` projection: **PASS** with decision (iii): projection via `g1Row`/`g2bRow` with `τ₀ = ouTauMax 𝔠 𝔡`, not via `unOURow`; fallback if the literal reading is enforced: no projection, line stays owed.
- Target 2 (instances): **PASS** (data of (ii); `Inst.inst_*` of `Endpoints.lean:561-605` apply to `band_terminal h32`).
- Target 3 (registry): **PASS**, with the observation on `supersededProps` wording and the `UNQuek` pointer (`UNQueBA` is not a registered name; point to `BAEnd_QUEL`).

## (b) Script output — Sat Oct 10 09:33:46 UTC 2026
Branch t/T2377: a8cba44 cade12c 56c0f10 (base 17ccf68); files: `RBM3D/Main/BandTerminal.lean` (new), `RBM3D/Test/Axioms.lean`.

### Registry (`Test/Axioms.lean`): every list change (`regtable.py` parses the five lists at 17ccf68 and at the branch)
```
owed/structural/superseded sizes old: 105 109 14 -> new: 82 118 17
owedProps -> (deleted) (11): Endpoints.BUniv Endpoints.QDiff Endpoints.QUE Endpoints.decol Endpoints.locSC Univ.UNBUniv Univ.UNClaimRowBA Univ.UNLocAvgBand Univ.UNOUClaims Univ.UNOUQUE Univ.UNQueBand
owedProps -> supersededProps (3): Gauss.Sizes.STLWB Gauss.Sizes.STLWT Gauss.Sizes.STOptL2
owedProps -> structuralProps (9): Univ.GUEPhase.GUEPathBounds Univ.UNClaim417 Univ.UNClaim417C Univ.UNLocAvgk Univ.UNNormBound Univ.UNOUQUEk Univ.UNQuek Univ.UNTrLocal Univ.UNTrLocalInit'
$ grep -o "^   `RBM[A-Za-z0-9_.']*, .*owner BA-N3 (stage M/N; supervisor 0853 C2)" RBM3D/Test/Axioms.lean | cut -d, -f1   # owed, owner comment changed
Univ.UNGreenCorrC Univ.UNGreenCorrAllC Univ.UNEMCTE2k Univ.UNJakk Univ.UNUywk Univ.UNEMCTE2Rowk Univ.UNJakUywRowk Univ.UNCoreC'' Univ.UNEMCTE2RowBA Univ.UNJakUywRowBA 
```

### Builds
```
$ lake build RBM3D.Main.BandTerminal | tail -1
Build completed successfully (4146 jobs).
$ lake build RBM3D   # branch root WITHOUT the hub import (registry deletions need BandTerminal in the root)
error: RBM3D.lean:425:0: axiom audit: 8 premise(s) that no theorem of this development proves are in
error: build failed
  [RBM.Endpoints.QUE, RBM.Univ.UNOUClaims, RBM.Univ.UNClaimRowBA, RBM.Endpoints.locSC, RBM.Univ.UNOUQUE, RBM.Endpoints.QDiff, RBM.Endpoints.decol, RBM.Endpoints.BUniv]
$ same with `import RBM3D.Main.BandTerminal` added after the last import line of RBM3D.lean (uncommitted, removed after; the hub does this at merge)
info: RBM3D.lean:426:0: axiom audit: 10986 theorems, 3213 definitions, 0 axioms in `RBM` (compiler-generated declaration
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
registry: 2 borrowed + 82 owed + 118 structural + 7 refuted + 17 superseded; 113 registered premise(s) carry nothing yet
Build completed successfully (4194 jobs).
$ registry pre-check (uncommitted): import RBM3D / import RBM3D.Main.BandTerminal / #assert_rbm_axioms ; lake env lean precheck.lean
axiom audit: 10986 theorems, 3213 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
exit code: 0
```

### Axioms, check file, acceptance example, size, diff
```
locSC_holds: [propext, Classical.choice, Quot.sound]
QDiff_holds: [propext, Classical.choice, Quot.sound]
QUE_holds: [propext, Classical.choice, Quot.sound]
decol_holds: [propext, Classical.choice, Quot.sound]
unLocAvgBand_holds: [propext, Classical.choice, Quot.sound]
unQueBand_holds: [propext, Classical.choice, Quot.sound]
unOUClaims_holds: [propext, Classical.choice, Quot.sound]
unOUQUE_holds: [propext, Classical.choice, Quot.sound]
unClaimRowBA_holds: [propext, Classical.choice, Quot.sound]
unBUniv_of_L32: [propext, Classical.choice, Quot.sound]
BUniv_of_L32: [propext, Classical.choice, Quot.sound]
band_terminal: [propext, Classical.choice, Quot.sound]
exit code of ax.lean (the 12 #print axioms and the ticket's example `UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff := band_terminal`): 0
exit code of lake env lean docs/tickets/checks/T2377-check.lean: 0
sorry|admit|native_decide|axiom in BandTerminal.lean: 0
wc -l RBM3D/Main/BandTerminal.lean (stop line 500): 159
$ git diff --stat main...t/T2377 | head -3
 RBM3D/Main/BandTerminal.lean | 159 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |  72 +++++++++-----------
 2 files changed, 191 insertions(+), 40 deletions(-)
```

### Target statements (awk from `RBM3D/Main/BandTerminal.lean`, namespace `RBM.Endpoints`)
```
theorem locSC_holds : locSC := netLoc (locSCFixed_of_ML unMLOut_holds)
theorem QDiff_holds : QDiff := netQD (QDiffFixed_of_ML unMLOut_holds)
theorem QUE_holds : QUE := QUE_of_QDiff QDiff_holds
theorem decol_holds : decol := decol_of_locSC locSC_holds
theorem unLocAvgBand_holds : UNLocAvgBand := locSC_to_UNLocAvgBand locSC_holds
theorem unQueBand_holds : UNQueBand := QUE_to_UNQueBand QUE_holds
theorem unOUClaims_holds : UNOUClaims := unOURow unMLOut_holds unLocAvgBand_holds unQueBand_holds
theorem unOUQUE_holds : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUQUE sz 𝔡 τU :=
theorem unClaimRowBA_holds : UNClaimRowBA := unClaimRowk _
theorem unBUniv_of_L32 : UNL32 → UNBUniv := fun h32 =>
theorem BUniv_of_L32 : UNL32 → BUniv := unBUniv_of_L32
theorem band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff := fun h32 =>
```

### Compiled nonempty instances (same file; `Inst.inst_*` of `Endpoints.lean` §7 at `sz0`, d = 3, (𝔠,𝔡) = (1/6,1/10), κ = 1/10, E = 0, bump)
```
example (h32 : UNL32) :=
  Inst.inst_decol (band_terminal h32).1
example (h32 : UNL32) :=
  Inst.inst_locSC (band_terminal h32).2.1
example (h32 : UNL32) :=
  Inst.inst_QUE (band_terminal h32).2.2.1
example (h32 : UNL32) :=
  Inst.inst_BUniv (band_terminal h32).2.2.2.1
example (h32 : UNL32) :=
  Inst.inst_QDiff (band_terminal h32).2.2.2.2
example := And.intro (Inst.inst_decol decol_holds) (And.intro (Inst.inst_locSC locSC_holds)
  (And.intro (Inst.inst_QUE QUE_holds) (Inst.inst_QDiff QDiff_holds)))
example (h32 : UNL32) :=
  Inst.inst_BUniv (unBUniv_of_L32 h32)
example := And.intro (Inst.inst_bridge_loc locSC_holds) (Inst.inst_bridge_que QUE_holds)
example : ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUE sz0 (1 / 10) τU ∧ UNOUDiag sz0 τU :=
  unOUClaims_holds 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible
example : UNOUQUE sz0 (1 / 10) (1 / 1000) :=
  unOUQUE_holds 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (le_min (le_min (by norm_num) (by norm_num)) (by norm_num))
```

### Name-clash grep and ports
```
$ grep -rnE "(theorem|def|lemma|abbrev) (<the 12 new names>)|BandTerminal_" RBM3D --include="*.lean" | grep -v "^RBM3D/Main/BandTerminal.lean" | wc -l
0
```
Ports from RBM1D/RBM2D: none; the file composes merged RBM3D theorems only (no diff-stat to give).

### Evidence for the narrative: which moved lines the scan still finds (registry line of the full build above, after the root import)
```
$ python3 -I unusedcheck.py <registry line of the full build>
UNTrLocal: in the 'carry nothing' list (not found by the scan)
UNClaim417: in the 'carry nothing' list (not found by the scan)
UNClaim417C: in the 'carry nothing' list (not found by the scan)
UNTrLocalInit': in the 'carry nothing' list (not found by the scan)
GUEPhase.GUEPathBounds: in the 'carry nothing' list (not found by the scan)
UNLocAvgk: in the 'carry nothing' list (not found by the scan)
STOptL2: in the 'carry nothing' list (not found by the scan)
STLWB: in the 'carry nothing' list (not found by the scan)
STLWT: in the 'carry nothing' list (not found by the scan)
UNNormBound: found by the scan (assumed, no theorem has it as head)
UNQuek: found by the scan (assumed, no theorem has it as head)
UNOUQUEk: found by the scan (assumed, no theorem has it as head)
```
### Narrative
- `RBM3D/Main/BandTerminal.lean` (159 lines, stop line 500) is the composition of the ticket's target 1, as listed in (a) (i): the four endpoints `locSC_holds`, `QDiff_holds`, `QUE_holds`, `decol_holds` have no hypothesis; `UNL32` enters only `unBUniv_of_L32` / `BUniv_of_L32`, hence `band_terminal`. No helper lemma, no `private`, no port from RBM1D/RBM2D.
- `unOUQUE_holds` follows the preflight decision (a) (iii): it is not a projection of `unOURow` (the type `UNOUClaims` hides `τ₀` under an `∃`, `Pins.lean:659-661`); it takes `τ₀ = ouTauMax 𝔠 𝔡` from the two rows `g1Row` (`GUEPhase/RandomLayerB.lean:468`) and `g2bRow` (`QUEFlow.lean:953`), which are the premises of `ouRow_of_pins`. Fallback if the auditor reads the ticket's "if `unOURow` exposes an explicit `τ₀`" literally: delete `unOUQUE_holds` and its example, put `UNOUQUE` back into `owedProps` with the comment "`UNOUClaims` hides `τ₀`" (both files are in the sole writable set).
- Registry: the table above is the full list of changes (23 names moved or deleted, 10 owner comments changed). Class of each move follows (a) (i) table; every moved line's comment names the band instance (a merged theorem) and the registered BA line with its producer (0853 Q2 (d)); `UNQuek` points at `BAEnd_QUEL` because `UNQueBA` is not a registered name. The four optional UN-01b lines (`UNQuek`, `UNLocAvgk`, `UNOUQUEk`, `UNClaim417C`) were moved. `STLWB`, `STLWT`, `STOptL2` went to `supersededProps` with the guarded consumers named, T2375 had not done it (its comments in `owedProps` said "stays owed"); the text of the superseded class was widened in the module header and in the docstring of `def supersededProps`.
- The scan counts a premise as proved only when a theorem has it as conclusion head, so the deletions of the 8 names printed under "lake build RBM3D" above need `import RBM3D.Main.BandTerminal` in the root: the branch root (which only the hub edits) fails exactly on those 8 names, the root with the import passes. The merge must add the root import in the same commit as `Test/Axioms.lean`.
- No instance for `unClaimRowBA_holds` (a discharge of the BA row `UNClaimRowk (UNKind.ba)` whose conclusion needs BA bulk data; the ticket's target 2 names `band_terminal`).

## (c) Verified names
- `RBM.Endpoints.Inst.inst_decol`, `inst_locSC`, `inst_QUE`, `inst_QDiff`, `inst_BUniv`, `inst_bridge_loc`, `inst_bridge_que` (`Endpoints.lean` §7): used by the examples, compiled. `le_min`, `And.intro`: used, compiled. Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
1. `T2377a` (doc, not a statement difference): widen the class text of `supersededProps` in DECISIONS §66 (2) / §76 (3): "pins whose unguarded form `∀ d, P d` is unprovable and whose guarded consumer is named" (done in `Test/Axioms.lean` only).
2. `T2377b`: the `UNOUQUE` reading above (projection with `τ₀ = ouTauMax 𝔠 𝔡` through `g1Row`/`g2bRow`, not through `unOURow`); the dispatcher or auditor confirms or takes the fallback.
3. `T2377c` (registry reading): nine of the moved lines (`UNTrLocal`, `UNClaim417`, `UNClaim417C`, `UNTrLocalInit'`, `GUEPathBounds`, `UNLocAvgk`, `STOptL2`, `STLWB`, `STLWT`) are not found by the scan (evidence block above), so their class change is ledger bookkeeping that the scan does not enforce; `UNNormBound`, `UNQuek`, `UNOUQUEk` are found, so they need a class.
4. E1-E4 (`UNEMCTE2k`, `UNEMCTE2Rowk`, `UNJakk`, `UNUywk`, `UNJakUywRowk`, `UNCoreC''`, `UNGreenCorrC`, `UNGreenCorrAllC`) and the BA rows `UNEMCTE2RowBA`, `UNJakUywRowBA` stay owed, owner comment BA-N3 (stage M/N; supervisor 0853 C2): no producer written here.
5. No Lean/paper statement difference: the five endpoints are the frozen `Endpoints.lean:165-209` statements, unchanged.
