Auditor model: claude-opus-5-5

# T2498c audit (round 1): row c (U3s3c), new `Chain/QEndB1Gen`, targets 11-13
Branch `t/T2498c` at 04fe369f; `main` 9cd059a4 (merge base 051e596f); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498c-audit1` (detached).
Ticket `docs/tickets/T2498.md` (:57-59 targets 11-13, :62-78 family table) + Amend 1 (family row 9, `∃ C₆` after `κ`); check `docs/tickets/checks/T2498-check.lean` :180-206 (binding).
Started Wed Oct 14 08:34:34 UTC 2026. Scratch files (uncommitted): `<scratchpad>/T2498c/{audchk.lean,closure.lean,txt.py}`.

## 1. Statement against the pin
```
$ python3 -I txt.py docs/tickets/checks/T2498-check.lean QEndB1Gen.lean   # comments stripped, whitespace collapsed, name mapped
STXiRoundPTgL'' IDENTICAL up to the name 680 680
STOeqQtRoundPTgL'' IDENTICAL up to the name 319 319
target 12 C1 hits: ['Lloop'] | KLloopOf occurrences: 1
STXiRoundPTgL'' C1 hits: []
STOeqQtRoundPTgL'' C1 hits: []
U5S-C3 '∀ (sz : Sizes d)' in target 12 statement: 26
```
(`Lloop` = substring of `KLloopOf` in `hKK`, a hypothesis whose text is the merged `stOeqNQPTgL''_of`'s, below.)
```
$ lake env lean audchk.lean   # check defs :172-233 copied verbatim + the lines below; exit 0
example : @T2498_XiRoundPTgL'' = @STXiRoundPTgL'' := rfl                 -- compiles
example : @T2498_OeqQtRoundPTgL'' = @STOeqQtRoundPTgL'' := rfl           -- compiles
example : @T2498_KerEK4 = @RBM.Ind.QProxyG_KerEK4 := rfl                  -- compiles (D1, hypothesis hEK4)
example : @T2498_KerEK4Fam = @RBM.Ind.QProxyG_KerEK4Fam := rfl            -- compiles
-- MetaM: telescope of stOeqQtRoundPTgL''_of; NQ pin binders instantiated with the same fvars, compared by name with ==
conclusion head: RBM.BA.STOeqQtRoundPTgL''  args: 5
conclusion defeq T2498_OeqQtRoundPTgL'' at the same args: true
mk arg: fun sz z => (mkM sz z).toFlowFM
binders (36): [d, law, Flow, mkM, T0, Hf, E, lam', gK, Ψ, Aof, hSE, hFlow, hSpec, hL, hW, hLaw, hC, hWard, hKcal, hEK, hm, hSeq, hS, hRow, hKK, hExp, hKL, hKT, hU, hKerFam, hR1, hT0, hEK4, hTh, hB45]
NQ pin hypotheses: 22; syntactically identical in target 12: 22; differing: []; missing: []
NQ conclusion: STOeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2498-check.lean   # in the audit worktree
exit 0; lines containing "error": 0
```
The three hypotheses beyond the 22 (bundle fixed at `T2498-1a-audit.md:93-98`):
```
$ sed -n 939,943p RBM3D/Chain/QEndB1Gen.lean
    -- ticket row 8 (D1 of the alternating endpoint, `∃ C4` before `(sz, z)`) and row 9 (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`, Amend 1; `B45Gen_Facts`)
    (hEK4 : QProxyG_KerEK4Fam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM)) :
```
- `hEK4` = pinned D1 family (rfl above): `∃ C4` after `(k, κ, ε, 𝔡, KL)`, before `(sz, 𝔠, z)`.
- `hTh` = family row 9 with Amend 1: `∀ 𝔡 > 0, ∀ κ > 0, ∃ C₆ > 0, ∀ sz ε 𝔠 z, Flow → Step5KerGen_ThDecay … (gK sz z) 𝔡⁻¹ C₆`; `∃ C₆` after `κ`, before `(sz, z)`.
- `hB45` = `B45Gen_Facts d Flow mk` (merged class, row 9).
- Pinned `∃` (`𝔠d` in the conclusion, `C4`, `Ck`, `C₆`, `Aof κ`) all before `(sz, z)`; `∃ κm`, `∃ τ` after `(sz, z)` are rows 6, 12 as tabled. No `∀ n` drift premise (`hExp hKL hKT hU` are `∀ᶠ n`; `hKK` is the `∀ n` link, as in the NQ pin).
- Ticket rows 10 (R1 window) and 11 (`hη`) list premises the Lean text does not carry beyond the NQ pin's `hR1`; an absent premise only strengthens target 12. No defect.
Target 11: PASS. Target 12 statement: PASS (conclusion = `T2498_OeqQtRoundPTgL''`; hypotheses = the 1a-audit bundle).

## 2. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class`; every hypothesis is in the signature; all 25 are merged Props or pinned D1.
- Non-vacuity of the bundle: `stOeqQtRoundPTgL''_band (d) (hd : 3 ≤ d)` (`:1035-1070`) applies `stOeqQtRoundPTgL''_of` at the band family (`Hf = seqHflow`, `E = STflowE`, `lam' = gK = sz.lam`, `Ψ = 0`, `Aof = 1`) with all 25 hypotheses discharged by merged theorems (no hypothesis left; axioms below).
- Cycle check (band theorem not used by the generic one):
```
$ lake env lean closure.lean   # transitive constant closure of stOeqQtRoundPTgL''_of
RBM.Ind.stOeqQtRoundPT''_holds in closure of stOeqQtRoundPTgL''_of: false
RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band in closure of stOeqQtRoundPTgL''_of: false
RBM.BA.stOeqQtRoundPT''_holds_of_gen in closure of stOeqQtRoundPTgL''_of: false
closure size: 64403
```
PASS.

## 3. Compiled nonempty instances (`:1101-1120`, namespace `QEndB1GenCheck`)
```
$ sed -n 1101,1109p RBM3D/Chain/QEndB1Gen.lean | grep -v "^/--\|^rows\|^`STXi"
example (hKb : STKboundgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)) (hKw : STKwardgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0))
    (hLK : STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst)
    (hStep2 : STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst 1) :
    STXiRoundPTgL'' (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst := by
  obtain ⟨𝔠d, h0, -, hC⟩ := stOeqQtRoundPTgL''_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact hC (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI hKb hKw hLK (sz0_con 𝔠d h0) hStep2
```
- Data: `d = 3`, `sz0` (n = 0: `L = 4`, `W = 32`, `lam = 1/64`), flow `z0` with `flow_z0` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`, `Cd = 1`, window `s ≡ 0 < t ≡ 1/16 ≤ lemT z0` (`sz0_hs0 sz0_hst sz0_ht`), `STCaseI` (`sz0_caseI`), `STConStInd` (`sz0_con 𝔠d h0`) discharged; all 25 deterministic rows discharged through `stOeqQtRoundPTgL''_band3`.
- Remaining example hypotheses `hKb hKw hLK hStep2` = `STKboundgL`, `STKwardgL`, `STLKgL`, `STStep2ConclgL`: the stochastic pins of `STIngRgL` (ticket :89, other gates' pins), allowed.
- Second example (`:1112-1115`): band pin `STOeqQtRoundPT'' 3` via `stOeqQtRoundPT''_holds_of_gen 3` at `(sz0, z0)` through merged `inst_ing`, no hypothesis. Third (`:1117-1119`): the band bridge at `d = 3`.
- Not degenerate: `N = 2^21`, nonempty index, `s < t`, no `False` premise. PASS (target 13).

## 4. Build, axioms, hygiene, diff
```
  Wed Oct 14 08:30:26 UTC 2026
  Build completed successfully (3920 jobs).
  Wed Oct 14 08:30:55 UTC 2026
  ^ lake build RBM3D.Chain.QEndB1Gen in the audit worktree; module's own warnings: 10 longLine (header), nothing else
$ lake env lean RBM3D/Chain/QEndB1Gen.lean   # full re-elaboration of the source, longLine lines filtered
  Wed Oct 14 08:31:28 UTC 2026
  exit 0
  Wed Oct 14 08:31:45 UTC 2026
$ #print axioms (audchk.lean)
'RBM.BA.STXiRoundPTgL''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STOeqQtRoundPTgL''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQtRoundPTgL''_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQtRoundPT''_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STXiRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STOeqQtRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " QEndB1Gen.lean  -> 0;  grep -cE "^import RBM3D\.BA"  -> 0
$ git diff --name-status main...t/T2498c
M	RBM3D.lean
A	RBM3D/Chain/QEndB1Gen.lean
A	RBM3D/Probe/T2498Pins.lean
$ git diff main...t/T2498c -- RBM3D.lean | grep "^[+-][^+-]"
+import RBM3D.Chain.QEndB1Gen
$ git diff --name-only main...t/T2498c -- RBM3D/Induction RBM3D/Chain/NQ* RBM3D/Chain/QEndGridGen.lean RBM3D/BA RBM3D/Test | wc -l
0
$ git grep -l "import RBM3D.Chain.QEndB1Gen" t/T2498c -- RBM3D RBM3D.lean
t/T2498c:RBM3D.lean
$ public new names on main (git grep -wF -c, files): STXiRoundPTgL'' 0, STOeqQtRoundPTgL'' 0, stOeqQtRoundPTgL''_of 0,
  bandFM_STXiRoundPT'' 0, bandFM_STOeqQtRoundPT'' 0, stOeqQtRoundPTgL''_band 0, stOeqQtRoundPT''_holds_of_gen 0
```
All files are sole writable files. `RBM3D/Probe/T2498Pins.lean` (row a's probe, `t/T2498` only) appears only through stacking; per the ticket and the hub it is never merged. Band `QEndB1`, `QEndGrid`, `QtXiRoundLift` untouched; no frozen signature changed. File 1,126 lines (< 2,000; reserve `QEndB1Gen2` unused). PASS.

## 5. Paper deltas
Lean/paper differences: target 12's carrier hypotheses (D1 `hEK4`, `hTh`, `hB45` in place of the band's `|E| ≤ 2 − κ'`, `qProxy4C`, `2/√κ'`), and the in-proof devices (D1 at `KL = 1/𝔠`, `K₆ = max C₆' 1`, `Γ = κm⁻¹`, Hermitian initial event). Proposed as `T2498o`-`T2498r` (prove report (d)); `T2498a`-`n` numbered as D722/D724/D726 (`docs/paper-deltas.md:1791-1812`). Coverage complete. PASS.

## Observations (no RETURN)
- O1. Prove report is 264 lines; ticket :107 asks ≤ 250 (CLAUDE.md §6 cap 300). No statement/instance/build effect.
- O2. Check :254-258 (non-binding BA shape) still has `∃ C₆` before `κ`; Amend 1 governs and the Lean text follows it. Dispatcher may update the shape.
- O3. Prover's observation on `Test/Axioms.lean:218` (`STXiBootgL'` owner text "proofs: U3s3, U3s4") is for the dispatcher; row c has no registry text assigned.
- O4. Target 13 lists `szB`/`zB` or `sz0` data; instances use `sz0`/`z0` (same as rows a, b).

## Verdict
- Target 11 (`STXiRoundPTgL''`, `STOeqQtRoundPTgL''`): **PASS**.
- Target 12 (`stOeqQtRoundPTgL''_of`): **PASS**.
- Target 13 (band re-derivation and instances): **PASS**.
Ticket T2498c: **PASS**. No dispatcher sign-off needed. Finished Wed Oct 14 08:34:34 UTC 2026.
