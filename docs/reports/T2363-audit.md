Auditor model: claude-opus-5-5
# T2363 audit (round 2, after repair `f2adfa5`) — UN-51 RandomLayerA/B

Date: Sat Oct 10 04:05:45 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2363-audit2`, detached at `t/T2363` = `f2adfa5`, merge base `010cad9`. Scratch: scratchpad `T2363/`.

## 1. Diff scope, hygiene, build, axioms

```
$ git diff --stat refs/heads/main...HEAD
 RBM3D/Test/Axioms.lean                        |   4 +-
 RBM3D/Universality/GUEPhase/RandomLayerA.lean | 582 ++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/RandomLayerB.lean | 514 +++++++++++++++++++++++
 3 files changed, 1098 insertions(+), 2 deletions(-)
$ git diff --word-diff=porcelain refs/heads/main...HEAD -- RBM3D/Test/Axioms.lean | grep -E '^[-+][^-+]'
+band:
-`RandomLayerB` `g1Rowk`;
+(`g1Rowk_band`); BA: BA-C5 (T inputs) + BA-N2 (instance);
+band:
-`RandomLayerA/B`;
+(`g1Rowk_band`); BA: BA-C5 (T inputs) + BA-N2 (instance);
$ git diff --stat d11d0a4 HEAD      # round-1 audited commit -> repair
 RBM3D/Universality/GUEPhase/RandomLayerB.lean | 226 ++++++++++++++++----------
$ grep -nE "sorry|admit|native_decide|^ *axiom " RandomLayer{A,B}.lean | wc -l
       0
$ grep -n "^import" RandomLayer{A,B}.lean | cut -d: -f3
import RBM3D.Universality.GUEPhase.Eq729B
import RBM3D.Universality.GUEPhase.RandomLayerA
import RBM3D.Universality.GUEPhase.LLTransfer
import RBM3D.Universality.GUEPhase.PathBounds
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.ZeroModeProfile
$ wc -l RandomLayerA.lean RandomLayerB.lean      # stop line 1300, cut A at 750
     582 RandomLayerA.lean;  514 RandomLayerB.lean;  1096 total
$ lake build RBM3D.Universality.GUEPhase.RandomLayerA RBM3D.Universality.GUEPhase.RandomLayerB | grep -E "^error|RandomLayer|Build completed|^exit"
✔ [3835/3837] Built RBM3D.Universality.GUEPhase.RandomLayerA (11s)
✔ [3837/3837] Built RBM3D.Universality.GUEPhase.RandomLayerB (3.8s)
Build completed successfully (3837 jobs).
exit=0
$ grep -cE "^(error|warning).*RandomLayer" build.out
0
```
Diff = the two new files + the two owner comments of `Test/Axioms.lean` (comment text only; both entries stay owed, as O5). No `import RBM3D`, no ST-6 file.

`ax.lean` = `import ...RandomLayerB`, two pin checks, then 18 `#print axioms`:
```
example : RBM.Univ.UNG1Row := g1Row
example : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d, UNMLOut d) UNLocAvgBand UNQueBand := g1Rowk_band
$ lake env lean ax.lean > ax.out; echo exit=$?; grep -c "" ax.out; sed -E "s/.*depends on axioms: //" ax.out | sort | uniq -c
exit=0
18
  18 [propext, Classical.choice, Quot.sound]
```
(the 18: `RandomLayer_lem28`, `_rows_flow`, `_rows`, `_rowsLL`, `_rowsQ`, `_etaLL_pos`, `_etaLL_le_one`, `_etaQ_pos`, `_etaQ_le_one`, `g1Rowk_of_inputs`, `g1Rowk_band`, `g1Row`, `inst_g1Row`, `inst_g1Rowk`, `inst_g1Rowk_of_inputs`, `inst_rowsLL`, `inst_rowsQ`, `inst_lem28`.)
Full `lake build` / registry pre-check: not re-run here (the hub runs it at merge, CLAUDE.md §4).

## 2. Target 1 (RandomLayerA) — PASS

`RandomLayerA.lean` is byte-identical to the round-1 audited commit (`git diff --stat d11d0a4 HEAD` lists only B). Round-1 check stands, re-read against the file:
- `RandomLayer_lem28` (`:59`): `|e| ≤ 2-κ`, `0<η≤1` ⇒ `0<Im z`, `|lemE z| ≤ 2-κ`, `1/16 ≤ lemT z < 1`, `etaT = √t₀ η`, `η/4 ≤ etaT ≤ η`, `1-t₀ ≤ η/c_κ`, `c_κ = √(κ(4-κ))/8`.
- `RandomLayer_rows` (`:151`): `r1..r4` ⇒ `|lemE| ≤ 2-κ`, `0 ≤ t₁ ≤ t₀ < 1` (all n), `h730`, `hscale`, `hell (≤ lam²)`, `hell1 (≤ 1)` (eventually); quantifiers `∀ n` / `∀ᶠ n in atTop` as the 1a table.
- `RandomLayer_rowsLL` (`:213`), `RandomLayer_rowsQ` (`:335`): `3 ≤ d`, `Admissible 𝔠 𝔡`, `0 < τU ≤ ouTauMax 𝔠 𝔡`, `t ≤ ouTStar` ⇒ `r1..r4` at `ouEtaLL = N^{-1+2τU}` (`τD = τU/2`) resp. `ouEtaQ = W^{-𝔡/3} lam W^{d/2}/N` (`τD = τU`) (definitions `ZeroModeProfile.lean:81,84`). U3: only `τU ≤ ouTauMax` is assumed — no pin change (`ouTauMax'`) needed.
- `_etaLL_pos/le_one` unconditional / `τU ≤ 1/2`; `_etaQ_pos` needs `0 < lam n`, `_etaQ_le_one` eventual (recorded T2363e).
Instances (`RandomLayerA.lean:528-576`): `inst_lem28` (`e=0, η=1/2, κ=1/10`), `inst_rowsLL`, `inst_rowsQ` at `sz0`, `Admissible (1/6) (1/10)`, `τU = ouTauMax = 1/720`, `t = ouTStar`; an `example` applies `RandomLayer_rows` at `z_n = i η_LL` with all of `r1..r4` from `inst_rowsLL`; `inst_etaLL`, `inst_etaQ`. Nondegenerate (`N = 2097152` at `n=0`, `t > 0`).

## 3. Target 2 `g1Rowk_of_inputs` — PASS (round-1 RETURN repaired)

Statement (`RandomLayerB.lean:316-331`): parameters `K P`, `fE fT` (flow maps), `Fl` (flow domain), `MO` (G-loop outputs), `KF PB` (primitive family, path bounds); hypotheses `hT1 Flow`, `hT1' Dom`, `hT6 Bulk`, `hT2 Prod`, `hT3 LL`, `hT4 Que` (each `∀ d, 3 ≤ d →`), `hT5 : ML → ∀ d, 3 ≤ d → MLout`; conclusion `UNG1Rowk K P ML Loc Que` — the pin itself (`OUInterfaceK.lean:101`), so the conclusion is checked by Lean against the pin.

Round-1 Required list, item by item:
1. (a) ML outputs: `sz.STLK/STLocalEntry/STExp2` no longer occur in `RandomLayerB_MLout` (`:123`), `_Prod` (`:132`), `_Que` (`:166`); they are the parameter `MO` (band: `RandomLayerB_MOband`, `:371`). (b) flow domain: `_Dom`, `_MLout` take `Fl` (band: `RandomLayerB_Flband := STFlow`, `:367`). (c) `RandomLayerB_KFam` is now the parameter `KF` of `_Prod`, `_Que` (band value `:63`). Done.
2. Report: (a′) 4, narrative 4 and 6, T2363b, open issue (4) rewritten; B2–B4 re-pasted at `f2adfa5`. Done.
3. `g1Rowk_band`, `g1Row` statements token-exact (two pin checks §1, exit 0); `inst_g1Row`, `inst_g1Rowk` kept; new `inst_g1Rowk_of_inputs`. Done.

Residual band vocabulary (disclosed, not a defect under U1 "a band-only proof is not a FAIL, but … names the band-only pieces"):
```
$ grep -n "etaT\|2 - κ" RandomLayerB.lean | awk -F: '$1<200'   (code lines)
106:      |fE sz n z| ≤ 2 - κ ∧ 1 / 16 ≤ fT sz n z ∧ fT sz n z < 1 ∧
107:        etaT (fE sz n z) (fT sz n z) = Real.sqrt (fT sz n z) * z.im ∧ 1 - fT sz n z ≤ ...
137:    (∀ n, |fE sz n (z n)| ≤ 2 - κ) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ fT sz n (z n)) →
140:      Nsz sz n ^ (-τD) * etaT (fE sz n (z n)) (fT sz n (z n))) →
173:        (∀ n, |fE sz n (z n)| ≤ 2 - κ ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
```
T1 (`Flow`), T2 (`Prod`, also `gueScale`) and T4 (`Que`) keep the semicircle `etaT E t = (1-t) Im mE(E)` (`Loop/GLoop.lean:75`) and the window `|E'| ≤ 2-κ`. These are named in prove report (a′) 4, narrative 4/6, T2363b and open issue (4). See observation O1.

No hidden hypothesis: the seven inputs are explicit `Prop` hypotheses (definitions in the file, not structure fields); `ML` is the pin's own premise; `Loc`, `Que` unused (T2363d). No cycle: the band inputs are discharged by merged lemmas (`RandomLayer_lem28`, `gueK_exists`, `Sizes.stKbound_holds`, `gueGrid_pathBounds`, `oull_of_pathBounds`, `Eq729B_eq747_of_inputs`) plus `UNMLOut` as hypothesis.

Compiled nonempty instance: `g1Rowk_band` (`:454`) applies `g1Rowk_of_inputs` at `UNKind.band`, `UNOUProfile.band`, `lemE`, `lemT`, `Flband`, `MOband`, `KFam`, `PBband` with all seven inputs discharged by the public lemmas `RandomLayerB_{flow,dom,bulk,prod,LL,Que,ML}_band` (`:343-451`); `inst_g1Rowk_of_inputs` (`:497`) does the same and evaluates at `d=3`, `sz0`, `𝔠=1/6`, `𝔡=1/10`, `τU = ouTauMax` (`ouTauMax_pos`, `le_rfl`), with only `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (other gates' pins) as hypotheses. Nondegenerate. The `κ > 2` branches of `_flow_band`, `_bulk_band` are the empty-bulk case required by T6, not the instance.

## 4. Target 3 `g1Row`, `g1Rowk_band` — PASS

`g1Rowk_band : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d, UNMLOut d) UNLocAvgBand UNQueBand` and `g1Row : UNG1Row := UNG1Rowk_band.1 g1Rowk_band` (`UNG1Rowk_band : … ↔ UNG1Row`, `OUInterfaceK.lean:392`), no hypothesis; both elaborate against the pins (§1). Instances `inst_g1Row` (`:483`), `inst_g1Rowk` (`:489`) at `sz0`, `τU = ouTauMax (1/6) (1/10)`.

## 5. Paper deltas

Prove report (d): T2363a (`hell1`, not in the paper), T2363b (generic in `fE fT Fl MO KF PB`; T1/T2 keep the semicircle `etaT` and `2-κ` — band vocabulary), T2363c (finite modification of `z_n` for `STFlow`), T2363d (`Loc`, `Que` unused; 3 of 5 `UNMLOut` conclusions), T2363e (not-ported RBM2D items, `η_Q`, `n₀ = 3`). Every Lean/paper difference found in §2–§4 is covered.

## 6. Observations (no verdict effect)

- O1 (for BA-C5, dispatcher information). The paper's BA flow (`7_8_light_weight.tex:1798`, `(eq:t0E0_BA)`) defines `t₀ = Im m(z,λ)/(Im m(z,λ)+Im z)` with the BA `m`, and states its bulk as `|E| ≤ e_g − κ` (`:1848`). So the residual semicircle `etaT` identity of T1 (`etaT (fE z) (fT z) = √(fT z) Im z`) and the `|fE| ≤ 2-κ` hypotheses of T1/T2/T4 will probably not hold for the BA choice `fE = BAflowEs`, `fT = BAflowT0`. Making `etaT` and the energy window parameters would then be BA-C5's job. Prove report open issue (4) flags this but gives no BA line-cost estimate (U1 asks for one in the band-only case). It changes no statement of this ticket.
- O2. Prove report (a)(iii) and the (a) Target-2 verdict line still say "kind-generic, not band-only"; the correction is in (a′) 4, as the rules require ((a) is not edited).
- O3. Ticket text names `Eq729B_bridge`, `Eq729B_goodFlow` for `g1Row`; the proof uses `Eq729B_eq747_of_inputs` with a generic finite modification of `z_n` instead ((a′) 2). No statement changes.
- O4. `RandomLayer_rowsQ` uses `τ_D = τ_U` (RBM2D `τ_U/2`): a stronger row; differs from RBM2D only, not from the paper.
- O5. `RandomLayer_rows_flow`, the seven `RandomLayerB_*_band` lemmas and `RandomLayerB_Flband/MOband/PBband/KFam` are public, prefixed with the file stem (§3 (E)); round-1/prove B7 name-clash grep reports 0 hits.

## Verdict

- Target 1 (`RandomLayer_lem28`, `_rows`, `_rowsLL`, `_rowsQ`, `_eta*`): **PASS**.
- Target 2 (`g1Rowk_of_inputs`): **PASS** (round-1 Required items 1–3 satisfied; the residual band vocabulary is disclosed in T2363b and open issue (4)).
- Target 3 (`g1Row`, `g1Rowk_band`): **PASS**.
Ticket T2363: **PASS**. Build of both modules exit 0, axioms standard, diff scope as the ticket. No dispatcher sign-off needed (O1 is information for BA-C5).
