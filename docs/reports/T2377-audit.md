Auditor model: claude-opus-5-5

# T2377 audit (MA-06a, band terminal), round 1 — Sat Oct 10 09:39:12 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2377-audit1`, detached at `t/T2377` = a8cba44 (merge-base 17ccf68; `main` = ebb6850 touches no Lean file since 17ccf68).

## 1. Diff scope and hygiene
```
$ git diff --name-only main...HEAD
RBM3D/Main/BandTerminal.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD --stat -- RBM3D/Endpoints.lean RBM3D.lean      # frozen file / root
(empty)
$ grep -nE "sorry|admit|native_decide|^axiom| axiom " RBM3D/Main/BandTerminal.lean | wc -l
0
$ wc -l RBM3D/Main/BandTerminal.lean        # stop line 500
159
```

## 2. Build, axioms, acceptance example, check file
```
$ lake build RBM3D.Main.BandTerminal RBM3D.Test.Axioms | grep -E "^error|Build completed"
Build completed successfully (4147 jobs).
$ lake env lean ax.lean   # import RBM3D.Main.BandTerminal; the ticket's example; 12 #print axioms
'RBM.Endpoints.locSC_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QDiff_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QUE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.decol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unLocAvgBand_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unQueBand_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unOUClaims_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unOUQUE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unClaimRowBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unBUniv_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.BUniv_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0      # includes: example : RBM.Univ.UNL32 → RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧
            #   RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff := RBM.Endpoints.band_terminal
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2377-check.lean | grep error ; echo exit
check exit 0
```

## 3. Statements against the pin
```
$ diff <(band_terminal type from BandTerminal.lean) <(T2377-check.lean:20 pinned Prop) && echo IDENTICAL
IDENTICAL          # UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff
```
Target statements (from the file): `locSC_holds : locSC`, `QDiff_holds : QDiff`, `QUE_holds : QUE`, `decol_holds : decol`,
`unLocAvgBand_holds : UNLocAvgBand`, `unQueBand_holds : UNQueBand`, `unOUClaims_holds : UNOUClaims`,
`unClaimRowBA_holds : UNClaimRowBA`, `unBUniv_of_L32 : UNL32 → UNBUniv`, `BUniv_of_L32 : UNL32 → BUniv`,
`band_terminal` as above; each body is exactly the composition the ticket names (file lines 47-109). The four endpoints
are the frozen `Endpoints.lean` statements (file untouched), with no hypothesis; `UNL32` (borrowed) enters only `BUniv`.

`unOUQUE_holds` (ticket: projection "for admissible `sz` and `0 < τU ≤ τ₀`, with `τ₀` named"):
```
theorem unOUQUE_holds : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUQUE sz 𝔡 τU
#print RBM.Univ.UNOUClaims : ∀ d, 3 ≤ d → ∀ 𝔠 𝔡 sz, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀, 0 < τ₀ ∧ ∀ τU, 0 < τU → τU ≤ τ₀ → UNOUQUE sz 𝔡 τU ∧ UNOUDiag sz τU
#print RBM.Univ.ouTauMax : fun 𝔠 𝔡 => min (min (𝔠 / 12) (𝔠 * 𝔡 / 12)) (1 / 100)
Defs/Sizes.lean:177  def Admissible (𝔠 𝔡) := 0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡
```
Same binder order and guard as `UNOUClaims`, `τ₀ = ouTauMax 𝔠 𝔡 > 0` under `Admissible` (range of `τU` nonempty), no
premise (axioms above). It is the C1 form of supervisor 0853 with `τ₀` named. See observation O1 on the ticket's wording.

Hypotheses / vacuity / cycles: no structure field carries a hypothesis (all targets are closed terms or take `UNL32`
only); dependencies are merged theorems (`unMLOut_holds : ∀ d, UNMLOut d`, `g1Row : UNG1Row`, `g2bRow : UNG2bRow`,
`unClaimRowk : ∀ K, UNClaimRowk K`, all printed by `#check`); no cycle (`locSC`, `QUE` are built without `UNBUniv`).
`UNL32` is the borrowed external input; its limit check is in prove report (a)(ii) (`ρ^{-k}` scaling makes both limits
`∫ O`); it is not a new hypothesis of this ticket.

## 4. Compiled nonempty instances (same file, lines 117-157; compiled in the build above)
```
#check @RBM.Endpoints.Inst.inst_decol : decol → ∀ᶠ n, sz0.seqP {decolBad sz0 n (1/10) (1/10)} ≤ ofReal (Nsz sz0 n ^ (-1))
#check @RBM.Endpoints.Inst.inst_locSC : locSC → ∀ᶠ n, … locBad1/2 sz0 (1/10) (1/20) (1/10) n … ≤ ofReal (Nsz sz0 n ^ (-2))
#check @RBM.Endpoints.Inst.inst_QUE   : QUE → ∀ᶠ n, ∀ E, |E| ≤ 2 - 1/10 → … queBadMat 3 … (1/30) (1/60) … queBound … (1/10)
#check @RBM.Endpoints.Inst.inst_BUniv : BUniv → Tendsto (… kPoint 1 bump 0 … − … gueP …) atTop (nhds 0)
#check @RBM.Endpoints.Inst.inst_QDiff : QDiff → ∀ᶠ n, … qd1Bad/qd2Bad sz0 (1/10) (1/20) (1/10) … ∧ ∀ z, locDomain …
```
Each takes the endpoint as its only premise, so `Inst.inst_X (band_terminal h32).…` discharges every deterministic
hypothesis at `d = 3`, `sz0`, `(𝔠,𝔡) = (1/6,1/10)`, `κ = 1/10`, `E = 0`, `bump`; only `UNL32` remains. The four
unconditional endpoints and the two bridges are also instantiated with no hypothesis; `unOUClaims_holds` at
`(3, 1/6, 1/10, sz0, sz0_admissible)`; `unOUQUE_holds` at `τU = 1/1000 ≤ ouTauMax (1/6) (1/10) = 1/720`. Nondegenerate
(`sz0`: `N(n=0) = 2097152`, growing; no empty index, no `False` premise).

## 5. Registry (Test/Axioms.lean): class changes by script (`reg.py` parses the five lists at `main` and branch)
```
borrowedProps 2 -> 2 | owedProps 105 -> 82 | structuralProps 109 -> 118 | refutedProps 7 -> 7 | supersededProps 14 -> 17
Endpoints.BUniv/QDiff/QUE/decol/locSC: owed -> (deleted)
Univ.UNBUniv, UNClaimRowBA, UNLocAvgBand, UNOUClaims, UNOUQUE, UNQueBand: owed -> (deleted)
Gauss.Sizes.STLWB, STLWT, STOptL2: owed -> superseded
Univ.GUEPhase.GUEPathBounds, UNClaim417, UNNormBound, UNTrLocal, UNTrLocalInit': owed -> structural
Univ.UNClaim417C, UNLocAvgk, UNOUQUEk, UNQuek: owed -> structural      (optional moves of the ticket)
$ grep -c "owner BA-N3 (stage M/N; supervisor 0853 C2)" RBM3D/Test/Axioms.lean
10      # E1-E4 (8 lines) + UNEMCTE2RowBA, UNJakUywRowBA; all still owed
```
Line by line against the ticket: deletions = the 10 listed + `UNOUQUE` (projection exists); structural = the 5 required
+ the 4 optional, each comment names a band instance and a registered BA line with producer. Pointer check:
```
unNormBandRow : UNNormBandRow | unClaimRow : UNClaimRow | un_claimAll_of_rows : UNClaimRow → … | un_claimAll_of_rowsBA : UNClaimRowBA → …
@unTrLocalInit'_band_zero, @GUEPhase.gueGrid_pathBounds : exist | UNQuek_band : (UNQuek band) ↔ UNQueBand
UNQueBA_of_BAEnd_QUEL : (∀ d, BAEnd_QUEL d) → UNQueBA | UNLocAvgk_band : … ↔ UNLocAvgBand
@UNOUQUEk_band : UNOUQUEk (UNKind.band d) sz 𝔡 τU ↔ UNOUQUE sz 𝔡 τU | ouRowk_of_pins : exists
@STLWB_of_LWterm : 3 ≤ d → LWterm d → STLWB d | @STLWT_of_LWtermExp : 3 ≤ d → LWtermExp d → STLWT d
grep: BUnivHolds.lean:205 theorem unTrLocalBandRow | PinsK.lean:174 theorem UNClaim417C_toC
      OptL2b.lean:195 theorem stOptL2_of_pins {d} (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d
BA lines in owedProps (branch): UNTrLocalBARow UNNormBARow UNEMCTE2RowBA UNJakUywRowBA UNOURowBA
      UNTrLocalInitBARow' UNG1Rowk BAEnd_QUEL UNLocAvgBA : all True
Step2Defs.lean:406/421/667  def STLWB/STLWT/STOptL2 (d : ℕ) : Prop := ∀ κ ε 𝔡, … (no 3 ≤ d premise)
```
Registry pre-check (root `RBM3D.lean` copied to scratch with `import RBM3D.Main.BandTerminal` after its last import,
line 422; source not edited; `lake env lean`):
```
axiom audit: 10986 theorems, 3213 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; …
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
registry: 2 borrowed + 82 owed + 118 structural + 7 refuted + 17 superseded; …
exit 0
```
Without the root import, `lake build RBM3D` on the branch fails as expected:
```
error: RBM3D.lean:425:0: axiom audit: 8 premise(s) that no theorem of this development proves are in none of …
```
i.e. the hub must add `import RBM3D.Main.BandTerminal` in the same merge commit (CLAUDE.md §3 (A) step 4 does this).

## 6. Paper deltas
No Lean/paper statement difference is introduced: the five endpoints are the frozen `Endpoints.lean` statements,
unchanged; `unOUQUE_holds` and the registry moves are internal pins/bookkeeping. Prove report (d) proposes `T2377a`
(doc: class text of `supersededProps`), `T2377b` (the `UNOUQUE` reading), `T2377c` (scan-visibility of moved lines).
Coverage complete.

## 7. Observations (no statement, instance, build, axiom or delta effect)
- O1. The ticket says a `UNOUQUE` projection only "if `unOURow` exposes an explicit `τ₀`… Otherwise no projection".
  `unOURow`'s type hides `τ₀` (∃ in `UNOUClaims`), and the prover proved the projection from the same rows `g1Row`,
  `g2bRow` with `τ₀ = ouTauMax 𝔠 𝔡`. The statement is exactly supervisor 0853 C1's required form ("one projection
  theorem concluding `UNOUQUE sz 𝔡 τU` for admissible `sz` and `0 < τU ≤ τ₀`, with `τ₀` named"), premise-free, with a
  nondegenerate instance; O3 ("leaves with `UNOUClaims`") is then met. Accepted; recorded as `T2377b` for the dispatcher.
- O2. `unClaimRowBA_holds` (a premise-free registry discharge, not a ticket endpoint of target 2) has no instance in the
  file; the ticket's target 2 scopes instances to `band_terminal`.
- O3. Merge needs the root import (§5); this is the standard hub step, not a defect.

## Verdict
- Target 1 (assembly theorems, `band_terminal`, `unOUQUE_holds`, `unClaimRowBA_holds`): **PASS**.
- Target 2 (instances): **PASS**.
- Target 3 (registry, pre-check): **PASS**.
- Ticket T2377: **PASS**. No dispatcher sign-off required.
