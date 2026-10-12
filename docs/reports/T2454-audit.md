Auditor model: claude-opus-5-5

# T2454 audit, round 1 (stage 2; scope T7a: split confirmed at 1a-audit round 2, `T2454-1a-audit.md` §3, §9; CONTROL H248 (2))

Written Mon Oct 12 15:53 UTC 2026 (`date -u`). Own detached worktree `../RBM3D-wt/T2454-audit1` at `t/T2454` = `6affbeb`; main `ab5746d`; merge-base `4fad610`.
Scratch files (not committed): `<scratchpad>/T2454/audit/{audit,stmt,check,regcheck}.lean`, `defdiff.py`, `hyp.py`.
T7a targets: 1-6 (`Chain/DecayGen.lean`), 12 and the target-13 instances of target 6 (`Chain/DecayGenTw.lean`), 3 registry lines.
Out of scope by the confirmed split: targets 8-11 and the target-10 instance (T7b, to be filed by the dispatcher); target 7 moved to U2 (ticket rule: no `Chain/Step34Gen` on main).

## 1. Build and axioms (CLAUDE.md §6 item 4)

```
$ lake build RBM3D.Chain.DecayGen RBM3D.Chain.DecayGenTw      # Mon Oct 12 15:48:21 -> 15:48:33 UTC
Build completed successfully (4012 jobs).   exit=0   ; lines matching "error": 0 ; warnings mentioning Chain/DecayGen*: 0
$ lake env lean audit.lean     # exit=0, 0 errors; #print axioms of the 10 public theorems:
'RBM.BA.bandFM_STDecayLoopU' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.BA.bandFM_STDecayLoopPT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STKcalDecay' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.BA.DecayGen_bandSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.DecayGen_ward' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.BA.DecayGen_bandWardPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stDecayLoopAtgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.BA.stDecayLoopPTgL_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stDecayLoopUgL_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.BA.DecayGenTw_baWardPair' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE 'sorry|admit|native_decide|^\s*axiom\b' RBM3D/Chain/DecayGen.lean RBM3D/Chain/DecayGenTw.lean
RBM3D/Chain/DecayGenTw.lean:0   RBM3D/Chain/DecayGen.lean:0
$ wc -l RBM3D/Chain/DecayGen.lean RBM3D/Chain/DecayGenTw.lean     # stop line 2,000 per file
     657 RBM3D/Chain/DecayGen.lean
      80 RBM3D/Chain/DecayGenTw.lean
```
Registry pre-check (branch root imports + the two new modules + `#assert_rbm_axioms`, `regcheck.lean`; deps built first, 4279 jobs):
```
$ lake env lean regcheck.lean      # reg-exit=0, 15:52:26 -> 15:53:15 UTC
axiom audit: 13299 theorems, 4175 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STKcalDecaygL: 4 [no certificate]
  RBM.BA.STStep2DecayPTgL: 2 [no certificate]
  RBM.BA.STGdecayWgL: 2 [no certificate]
```

## 2. Diff, layering, names

```
$ git diff main...HEAD --stat
 RBM3D/Chain/DecayGen.lean   | 657 +++  RBM3D/Chain/DecayGenTw.lean |  80 +++  RBM3D/Probe/T2454Pins.lean  | 397 +++  RBM3D/Test/Axioms.lean |   4 +
$ git diff main...HEAD -- RBM3D/Induction/ RBM3D.lean | wc -l
       0
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep '^[-+]' (truncated to 60 chars)
+   -- T2454 (BA-T T7a, DECISIONS §264): the far decay of `𝒦
+   `RBM.BA.STKcalDecaygL, -- the far decay of `𝒦` over a fl
+   `RBM.BA.STStep2DecayPTgL, -- `(Eq:Gdecay_w)` per time ov
+   `RBM.BA.STGdecayWgL, -- `(Eq:Gdecay_w)` uniformly in `u
$ git diff --stat 4fad610 main -- RBM3D/Test/Axioms.lean RBM3D/Chain/ RBM3D/Induction/DecayLoopA.lean RBM3D/Induction/DecayLoopB.lean RBM3D/BA/{TwistPins,EMn2BA,Step2BA}.lean
 RBM3D/Chain/Step5Gen.lean | 666 +++     # (new file on main; no overlap with the branch's files)
$ grep -n '^import RBM3D.BA' RBM3D/Chain/DecayGen.lean ; grep -rln "import RBM3D.Chain.DecayGen" RBM3D RBM3D.lean
(no output)
RBM3D/Chain/DecayGenTw.lean
$ clash scan: 16 public names, `git grep -nw <name> main -- RBM3D RBM3D.lean` (Probe/ excluded) on ab5746d: 0 clashes
STDecayLoopUgL STDecayLoopPTgL STKcalDecaygL DecayGen_Spec DecayGen_WardPair STDecayLoopAtgL bandFM_STDecayLoopU bandFM_STDecayLoopPT
bandFM_STKcalDecay DecayGen_bandSpec DecayGen_ward DecayGen_bandWardPair stDecayLoopAtgL_of stDecayLoopPTgL_of_step2 stDecayLoopUgL_of_step2 DecayGenTw_baWardPair
```
All files are sole writable files; the probe is never merged (hub brings in only the module files). Band files untouched (G1 not applicable under (A)). Public helpers carry the stems `DecayGen_*`/`DecayGenTw_*` (H248 (2)); the others are pinned or ticket-named.

## 3. Statements against the pins (CLAUDE.md §6 item 1)

```
$ lake env lean audit.lean   # check-file bodies copied verbatim as AUD_DecayLoopUgL, AUD_KcalDecaygL; exit=0, 0 errors
example … : STDecayLoopUgL C μ s t ↔ AUD_DecayLoopUgL C μ s t := Iff.rfl                    -- target 1 (content binding)
example … : STKcalDecaygL C ↔ AUD_KcalDecaygL C := Iff.rfl                                   -- target 3 (shape kept)
example … : STDecayLoopPTgL C μ s t ↔ <check-file target-2 shape> := Iff.rfl                -- target 2
example : ∀ d sz E s t, STDecayLoopU sz E s t ↔ AUD_DecayLoopUgL (bandFM sz E) (seqP sz) s t := … bandFM_STDecayLoopU
example : ∀ d sz E κ 𝔠 𝔡, 3 ≤ d → 0 < κ → Admissible → (∀ n, |E n| ≤ 2-κ) → AUD_KcalDecaygL (bandFM sz E) := … bandFM_STKcalDecay
example : ∀ d sz C μ s t Cd, twSteps C μ s t Cd → AUD_DecayLoopUgL C μ s t := … h.2.2.2
$ cp docs/tickets/checks/T2454-check.lean check.lean; lake env lean check.lean      # on the branch
check-exit=0   errors: 0
$ python3 -I defdiff.py      # pin bodies, probe (1a-audited, e949c71) vs file, whitespace-joined text
STDecayLoopUgL probe==file: True ; STDecayLoopPTgL True ; STKcalDecaygL True ; DecayGen_Spec True ; DecayGen_WardPair True ; STDecayLoopAtgL True
$ lake env lean stmt.lean    # probe Props T2454_stDecayLoop{At,PT,U}gL_* (probe :84-98, verbatim) inhabited by the theorems; exit=0
example : T2454_stDecayLoopAtgL_of := fun d hd sz C μ => @stDecayLoopAtgL_of d hd sz C μ
example : T2454_stDecayLoopPTgL_of_step2 := fun d => @stDecayLoopPTgL_of_step2 d
example : T2454_stDecayLoopUgL_of_step2 := fun d => @stDecayLoopUgL_of_step2 d
$ #check @RBM.BA.stDecayLoopUgL_of_step2
∀ {d}, 3 ≤ d → ∀ sz C μ κm 𝔠 𝔡 s t Cd, DecayGen_Spec C κm → sz.Admissible 𝔠 𝔡 → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
  DecayGen_WardPair C → STKcalDecaygL C → STGdecayWgL C μ s t Cd → STDecayLoopUgL C μ s t
```
Against the band (`DecayLoopA.lean:85, 938, 970`; `DecayLoopB.lean:1637`, read): target 4's pin is `STDecayLoopAt` with `0 < κ`, `|E n| ≤ 2-κ` replaced by `DecayGen_Spec C κm`
and `Lloop`/`STKloop`/`PrecPT` by `C.L`/`C.K`/`PrecPTL`; the remaining premises (Admissible, `0 ≤ u`, `u < 1`, `1 ≤ P ≤ N^{C₀}` eventually, the `(+,-)` decay input
for every `D`) and the conclusion (`∀ k ≥ 1, ∀ τ' > 0, ∀ D' > 0`, same indicator `ℓ_u W^{τ'} ≤ diam_∞`, bound `W^{-D'}`) are unchanged, same order.
Targets 5, 6: `STFlow`, `0 < ε`, `t ≤ lemT` become `Spec`, `Admissible`, `0 ≤ s`, `t < 1` (+ `s ≤ t` and F6 `N⁻¹ ≤ 1-t` eventually for target 5); F4, F5 are explicit binders.
Fixed parameters precede `∀ᶠ n` in every pin. Forbidden-token scan of public statements (`hyp.py`; tokens mE zt etaT STFlow lemT pathP pathH SB ‖m‖ |E Lloop STKloop seqHflow Step2Data STflowE):
```
every generic declaration: []      bandFM_STKcalDecay ['|E']   DecayGen_bandSpec ['|E']      # band readings: allowed by the ticket
```
Ticket wording check: target 6's setting is `FlowFM` plus facts (the ticket allows it "unless the 1a shows that `FlowFM` plus facts suffices"; 1a showed it). Target 4's pin is a definition (1a decision allowed).

## 4. Vacuity, hidden hypotheses, cycles (item 2)

- No structure field added; `DecayGen_Spec`, `DecayGen_WardPair`, `STKcalDecaygL` are `Prop` defs taken as explicit binders. Spec and Ward pair are proved at the band
  (`DecayGen_bandSpec`, `DecayGen_bandWardPair`) and the Ward pair at BA (`DecayGenTw_baWardPair`, unconditional; audit.lean also instantiates it at `baFM sz0 0 0`, compiles).
- `STKcalDecaygL` is proved at the band from the merged `inst_stKcalDecay_admissible`; at BA it is open, owner U2/U2-BA (registered in `owedProps`, §1).
  `STGdecayWgL`, `STStep2DecayPTgL` are merged pins (`Step2Gen:503, 542`) owed by T1/T1-BA, now registered. Limit checks of these external inputs: (a) `ext.py`, rerun at 1a-audit §2.
- No cycle: `DecayGen` imports `Induction.DecayLoopB`, `Chain.Step2Gen` (merged); `DecayGenTw` imports `DecayGen` and merged `BA/` modules; no importer of either (§2).

## 5. Compiled nonempty instances (item 3); all compile in the module build of §1

| endpoint | instance | data | open hypotheses |
|---|---|---|---|
| target 6 + bridge 1 + F5 band reading | `DecayGen.lean:619` | `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`), `z0`, `[s,t]=[0,1/16]` (`Defs.lean:439-440`), `κ=1/10`, `𝔠=1/6`, `𝔡=1/10` | `STGdecayWgL` (T1's pin) |
| target 5 + bridge 2 | `DecayGen.lean:627` | same; F6 discharged by `DecayGen_inst_hN` | `STStep2DecayPTgL` (T1's pin) |
| target 4 | `DecayGen.lean:637` | `sz0`, `E≡0`, `κ=1`, `u≡1/2`, `P≡1`, `C₀=0`, `k=3`, `τ'=1/10`, `D'=1` | the `(+,-)` 2-loop decay input (a section of the Step 2 output) |
| target 12 | `DecayGenTw.lean:54, 63` | `Iff.rfl`; `h.2.2.2` | none |
| target 13 (BA) | `DecayGenTw.lean:71` | `baFMz sz z`, `seqP (sz.withLam 0)`, statement level as the ticket asks | `BAFlow`, `STKcalDecaygL` (U2-BA), `STGdecayWgL` (T1-BA) |

Every deterministic hypothesis (`DecayGen_Spec`, `Admissible`, Ward pair, `STKcalDecaygL` at the band, `0 ≤ s`, `t < 1`, `s ≤ t`, `N⁻¹ ≤ 1-t`, `1 ≤ P ≤ N^{C₀}`) is discharged at
`sz0`; no `N = 0`, empty index or collapsed window (`k = 3`, window length 1/16).

## 6. Paper deltas (item 5)

Lean/paper differences of T7a: F4 explicit (`DecayGen_WardPair`), `|E| ≤ 2-κ` replaced by `DecayGen_Spec` and the energy-free `STKcalDecaygL`, target 5's F6 and target 6's dropped
`s ≤ t`, `ε`, `STFlow`: candidates `T2454a`, `T2454c`, `T2454d` (prove report (a), (a″), (d)). `docs/paper-deltas.md:1598` lists `T2454a–d` as pending numbering at row merge. Covered.

## 7. H248 (2) items

| item | finding |
|---|---|
| BA-side facts in leaf `DecayGenTw` with `import RBM3D.BA.EMn2BA`, stays a leaf | met: imports `DecayGen`, `BA.TwistPins`, `BA.Step2BA`, `BA.EMn2BA`; no importer (§2) |
| F7 proved in `DecayGenTw` or recorded as T1-BA obligation | not needed in T7a (used only by target 11, T7b; 1a-audit §7, O4) |
| T7a only if the split was confirmed at 1a-audit round 2 | confirmed (`T2454-1a-audit.md` §3, §9); the branch carries no `Step2EventsGen` |
| file-stem prefixes for public helpers | met (§2) |

## 8. Observations (no RETURN)

- O1. The prove report (d) lists T7b's items but does not name F7 (`S2EvGen_Rot3`/`Step2EventsGen_loopFine_rot3`) among them; its placement is recorded only in (a) ("F7 by T1-BA") and in the 1a-audit (§7, O4: T7b). The T7b ticket should carry it.
- O2. The prove report is 241 lines, above the ticket's 200 (within CLAUDE.md §6's 300).
- O3. `bandFM_STDecayLoopPT` is not literally pinned (ticket target 2 asks for an `Iff.rfl` bridge without a name); the name fits the `bandFM_*` pattern of targets 1 and 3.
- O4. The hub adds the root imports `RBM3D.Chain.DecayGen`, `RBM3D.Chain.DecayGenTw` at merge (the branch has none); the merged `Test/Axioms.lean` lines are additive and main has not touched that file since `4fad610`.

## 9. Verdict

| target | verdict |
|---|---|
| 1 `STDecayLoopUgL` + `bandFM_STDecayLoopU` | PASS |
| 2 `STDecayLoopPTgL` + `bandFM_STDecayLoopPT` | PASS |
| 3 `STKcalDecaygL` + `bandFM_STKcalDecay` | PASS |
| 4 `stDecayLoopAtgL_of` (pin `STDecayLoopAtgL`) | PASS |
| 5 `stDecayLoopPTgL_of_step2` | PASS |
| 6 `stDecayLoopUgL_of_step2` | PASS |
| 12 TLF-C5 examples | PASS |
| 13 instances of target 6 (band, BA statement level) | PASS |
| 7 | moved to U2 (ticket rule; no `Chain/Step34Gen` on main) |
| 8-11, target-10 instance | T7b (confirmed split); not in this branch |

**Overall: PASS (T7a).** No dispatcher sign-off requested; the dispatcher files T7b as pre-signed in H248 (2).
