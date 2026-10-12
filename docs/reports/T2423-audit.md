Auditor model: claude-opus-5-5

# T2423 audit, round 1 (stage 2), Mon Oct 12 04:00:30 UTC 2026

Inputs: ticket `docs/tickets/T2423.md`; Amend 1 `docs/tickets/T2423-amend-1.md` (S1 frame level only, `BAMatchTw` → L3b4′; S2 third file `BASim3`; report ≤ 400 lines; pins `PGraph.BAEquivC`, `BAPGraph.twist`; O2 merged `BAShape`/`BTStep`); check `docs/tickets/checks/T2423-check.lean`; `docs/reports/T2423-prove.md` (394 lines); branch `t/T2423` at `eac746f`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2423-audit1` (detached at `eac746f`). Scratch: `<scratchpad>/T2423/`.

**Verdict: PASS** (all four targets). No dispatcher sign-off needed.

## 1. Statements against the pins (script diff)
The ticket's check file names merged declarations only; the target statements are the probe pins of the 1a design gate (1a-audit round 2 PASS; Amend 1: "No statement in the probe changes"). Probe unchanged since `796a2dc`; every pin is diffed against the final file text (whitespace-normalized), the merged `BAScost` for the three O2 names.
```
$ git diff --stat 796a2dc HEAD -- RBM3D/Probe/T2423Pins.lean | wc -l
       0
$ python3 $SP/pindiff.py RBM3D/Probe/T2423Pins.lean RBM3D/Graph/BASim.lean RBM3D/Graph/BAScost.lean
BAPGraph.outsOf        probe   23 | BASim.lean:52    identical=True
BAPGraph.withinOuts    probe   27 | BASim.lean:56    identical=True
BAPGraph.splitOuts     probe   34 | BASim.lean:63    identical=True
BAFrameStep            probe   47 | BASim.lean:76    identical=True
BAShape                probe   74 | BAScost.lean:163   identical=True
BTStep                 probe   76 | BAScost.lean:167   identical=True
untag                  probe   77 | BAScost.lean:169   identical=True
BAGraph.extraB         probe   81 | BASim.lean:104   identical=True
BAPGraph.outsT         probe   85 | BASim.lean:108   identical=True
BAGraph.tagStd         probe   90 | BASim.lean:113   identical=True
BAGraph.tagT1          probe   92 | BASim.lean:115   identical=True
BAPGraph.withinOutsT   probe   95 | BASim.lean:118   identical=True
BAPGraph.splitOutsT    probe  102 | BASim.lean:125   identical=True
BAFrameStepT           probe  115 | BASim.lean:138   identical=True
WEdge.sameRev          probe  144 | BASim.lean:169   identical=True
DEdge.sameU            probe  146 | BASim.lean:172   identical=True
PGraph.BAEquiv         probe  150 | BASim.lean:177   identical=True
BAMatch                probe  172 | BASim.lean:199   identical=True
BAExtraGood            probe  176 | BASim.lean:203   identical=True
BAFrameStepT_untag     probe  179 | BASim.lean:206   identical=True
BAsim                  probe  183 | BASim.lean:210   identical=True
BAPGraph.baInv         probe  188 | BASim.lean:215   identical=True
PGraph.baInv           probe  190 | BASim.lean:217   identical=True
BAsim'                 probe  195 | BASim.lean:222   identical=True
identical 24 of 24
$ lake env lean $SP/ax.lean   # #check lines (endpoint signatures, no extra hypotheses)
baMatch_holds : ∀ (m : ℂ), BAMatch m
@baExtraGood_holds : BAExtraGood
baSim'_holds : ∀ (m : ℂ), BAsim' m
@baFrameStepT_untag_holds : BAFrameStepT_untag
```
Against the ticket's mathematics (L4-C1 items 1-4, as decided by Amend 1):
- **Item 1 `BAMatch m`** (`BASim.lean:199`): `∀ E P LT, BAFrameStepT P LT → P.g.Normal → ∀ Q, (band,Q) ∈ LT → ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img`. Normal BA graph `P`, band step at R0's image `P.img`, outputs up to relabelling (`BAEquiv`: bijections of `E'`,`I'` over `ext`, solid up to order, waved up to order and reversal, `×`-dots as sets, coefficient not read). Per output (`∃ L'` inside `∀ Q`), as item 3 permits; frame level only (Amend 1 S1). The other tags are the remaining `BAShape` constructors; `s1` is never assigned (grep: 0 in each file), paper-delta `T2423a`.
- **Item 2** `BAsim' m` (`:222`) is proved, not the literal `BAsim m` (`:210`, pinned, not derived): the band step is at `T.img` for a normal `T` with `T.baInv = P.baInv`. This is the "relabelled form" the ticket allows (item 2, L3a4 re-proves `ba_lvl1StepGood_of_sim`); `BAsim'` quantifies over **all** outputs of `BAFrameStep` (untagged), so its content does not depend on the tag choice. Paper-delta `T2423b`.
- **Item 3**: per output (`gg`: `A2` needs the swapped selector). Paper-delta `T2423c`.
- **Item 4 `BAExtraGood`** (`:203`): every `e1`/`e2` output of every `BAFrameStepT` constructor (so including the `lw4`/`gg4` `(M⁺S⁺)` and `W − 1` term lists) has `ord P < ord Q ∨ nExt Q < nExt P`. Closes T2395 audit O1 at graph level for the pinned notion of "extra" (`extraB`).
- **Amend 1 O4 pins** exist under exactly the pinned names, public: `PGraph.BAEquivC` (`BASim.lean:234`), `BAPGraph.twist` (`:249`).
- **Item 5 (not here)**: no `BASimC`, `BASimP`, `ScostLL` lemma in the three files.

## 2. Hidden hypotheses, vacuity, cycles
- The four endpoint theorems take no hypothesis beyond `m : ℂ` (above); the pins are `Prop` definitions with no structure fields. `LocStep` (`LWLvl1.lean:3260`) is the merged band step with three genuine constructors; `BAMatch` also demands `R ∈ L'`, so it is not satisfiable by an empty list.
- No cycle: all imports of the three files are on `main`, the chain is `BASim → BASim2 → BASim3`.
```
$ grep -h "^import" RBM3D/Graph/BASim{,2,3}.lean | sort -u | (check each on main)
RBM3D.Graph.BAExpandW on main | RBM3D.Graph.BAGGOp on main | RBM3D.Graph.BAScost on main | RBM3D.Graph.BASymm1 on main
RBM3D.Graph.BAWeightOp on main | RBM3D.Graph.BASim NOT on main (own file) | RBM3D.Graph.BASim2 NOT on main (own file)
```
- No external hypothesis (no limit check applies).

## 3. Compiled nonempty instances (in the files, built in §4)
| Target | Instance | Data |
|---|---|---|
| `baFrameStepT_untag_holds` | `BASim.lean:1971` | `gg` at `P_A` (`E = Fin 2`, `I = Fin 3`, 3 solid, 1 waved, `M`-dot `{2,3}`), `ggF.length = 31` by `decide +kernel` |
| `baMatch_holds`, `baExtraGood_holds` | `BASim3.lean:1915` | `gg` at `P_A` (band and `e2` outputs), `ggSplit` at `P_C` (band and `e1`) |
| same | `BASim3.lean:1938` via `inst_match_extra` (`:1927`) | `within` at `P_B`, `weight` at `P_W` (`E = Fin 1`, `I = Fin 2`, self-loop), `edge` at `P_E` (degree-3 internal vertex); band and extra tags exist by `decide +kernel` |
| `baSim'_holds` | `BASim3.lean:1942` | one output of each of the five kinds (`0 < outs.length` by `decide +kernel`) |
| census | `BASim3.lean:1910` | `gg`@`P_A`: 31 = 23 band + 8 `e2`; `ggSplit`@`P_C`: 48 = 8 + 1 `e1` + 5 `e2` + 34 `macroB` |

Every `BAFrameStep(T)` hypothesis (`hp`, `h`, `hx`, `hwf`, `hint`, `hnb`, `hbad`, `hne`, `hsame`, `hj`) and `P.g.Normal` are discharged by `decide`/`rfl`/membership terms (`BASim3.lean:1893-1903`, `:1955-1961`); no pin is left as a hypothesis. Nondegenerate: nonempty `E` and `I`, nonempty output lists, non-trivial atom. `BASim_Goal` (`BASim3.lean:1639`) is the body of `BAsim'` (the proof of `baSim'_holds` uses `change BASim_Goal m P Q'`, so Lean checks the identity).

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.BASim RBM3D.Graph.BASim2 RBM3D.Graph.BASim3     # audit worktree
✔ [3819/3821] Built RBM3D.Graph.BASim (8.8s)
✔ [3820/3821] Built RBM3D.Graph.BASim2 (9.2s)
✔ [3821/3821] Built RBM3D.Graph.BASim3 (35s)
Build completed successfully (3821 jobs).
$ grep -c "^error" build.out; grep -E "^(error|warning): RBM3D/Graph/BASim" build.out | wc -l
0
       0
$ lake env lean $SP/ax.lean
'RBM.Graph.baFrameStepT_untag_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baMatch_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baExtraGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSim'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
declarations in BASim/BASim2/BASim3: 872; with an axiom outside the standard three: 0 #[]
$ lake env lean docs/tickets/checks/T2423-check.lean; echo exit=$?; grep -ci error check.out
check exit=0
0
$ per file: wc -l; grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom '; grep -cE 'unsafe|implemented_by|@\[extern|ofReduceBool'; grep -c maxHeartbeats
RBM3D/Graph/BASim.lean:  wc=1979 sorry/admit/native_decide/axiom=0 unsafe/implemented_by/extern/ofReduceBool=0 maxHeartbeats=0
RBM3D/Graph/BASim2.lean: wc=1928 sorry/admit/native_decide/axiom=0 unsafe/implemented_by/extern/ofReduceBool=0 maxHeartbeats=0
RBM3D/Graph/BASim3.lean: wc=1962 sorry/admit/native_decide/axiom=0 unsafe/implemented_by/extern/ofReduceBool=0 maxHeartbeats=0
$ git diff --stat main...HEAD
 RBM3D/Graph/BASim.lean     | 1979 +++
 RBM3D/Graph/BASim2.lean    | 1928 +++
 RBM3D/Graph/BASim3.lean    | 1962 +++
 RBM3D/Probe/T2423Pins.lean |  352 +++
$ git diff main...HEAD --name-only | grep -v -E "^RBM3D/Graph/BASim(2|3)?\.lean$|^RBM3D/Probe/T2423Pins.lean$|^RBM3D.lean$"; echo exit=$?
exit=1   (no file outside the sole writable files)
$ public declaration names of the three files vs declaration lines on main 4b3bb8a (git grep, RBM3D/ without Probe)
382 public names; same name declared on main: 0
```
All three files are below the binding stop line of 2,000 (margins 21 / 72 / 38). No frozen file is touched (only new files). The probe is a sole writable file of the 1a and is not to be merged (hub: bring in only `BASim`, `BASim2`, `BASim3` and the three import lines). `RBM3D.lean` is untouched on the branch; the full `lake build` with `#assert_rbm_axioms` is the hub's at merge.

## 5. Paper deltas
Every Lean/design difference found above is proposed in the prove report (d): `T2423a` (`s1` never assigned; BA `A1` matched with the band `R2 (δ,m)` option; T2395 §1.5 claim fails at graph level), `T2423b` (`BAsim'` in place of literal `BAsim`), `T2423c` (per output), `T2423d` (`BAEquiv`/`BAEquivC` relation, coefficient and `×`-dot multiplicity not read; `BAImgSim` withdrawn). Frame level only (`BAMatchTw` → L3b4′) is a scope decision of Amend 1 S1, recorded in prove report (d) open issue 1. No uncovered difference.

## 6. Observations (no verdict change)
- O1. E* of (a′) §2 (any identification of two atoms of `P`) is not a Lean statement; only the pinned `BAExtraGood` (identification along a solid edge of `P`, `extraB`) is proved. The ticket and Amend 1 require only the pin; prove report (d) item 3 says so.
- O2. Landed 5,869 lines against the (a′) prediction 3,450; stop-line margins 21 / 72 / 38: any repair touching these files needs a fourth file (prove report (d) item 4).
- O3. The instance namespace `RBM.Graph.BASimInst` holds public helpers without the `BASim_` prefix (`tag_exists`, `inst_match_extra`, `hTA`…`hTE`, `baPA`…); the namespace carries the stem, and no clash exists on `main` (§4). Rule (E) is met in substance.
- O4. The `baSim'_holds` instance applies the theorem at one output per kind (an `∃ Q ∈ outs`); every hypothesis is discharged at the data, so it meets CLAUDE.md §4 step 2.

## Verdict per target
- `baFrameStepT_untag_holds` (`BASim.lean:281`): **PASS**
- `baMatch_holds` (`BASim3.lean:218`): **PASS**
- `baExtraGood_holds` (`BASim3.lean:658`): **PASS**
- `baSim'_holds` (`BASim3.lean:1830`): **PASS**
- Pins `PGraph.BAEquivC`, `BAPGraph.twist` (Amend 1 O4): present under the pinned names, public.
