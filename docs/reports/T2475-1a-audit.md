Auditor model: claude-opus-5-5
# T2475 1a-audit (design gate D1-D2, probe step) — Mon Oct 12 22:51:30 UTC 2026

Inputs: ticket, `T2475-prove.md` (a), (a″), branch `t/T2475` = efeab400 (probe blob `646eddc6…`), check file. Audit
worktree (detached): `/Users/junyin/Lean_proof/RBM3D-wt/T2475-audit1a`. Scratch: `$A = scratchpad/T2475/audit1a/`.

## 1. Probe compile, diff, hygiene
```
$ lake env lean RBM3D/Probe/T2475Pins.lean        (Mon Oct 12 22:46:02 UTC 2026)
'RBM.Univ.GUEPhase.RBG_Comp_of_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.g1Rowk_of_inputsG_of_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.band_D2_at_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_flow_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_dom_ml_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_D2_at_S0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' <probe> -> grep-exit=1;  wc -l -> 399
$ git diff --stat main...HEAD -> RBM3D/Probe/T2475Pins.lean | 399 +++ (only file);  check file: lake env lean exit=0
```

## 2. Statements against the check (scratch `$A/eqv.lean` = probe :12-389 + check :152-336 + 21 auditor examples)
```
$ lake env lean $A/eqv.lean   (Mon Oct 12 22:48:37 UTC 2026) -> exit=0, 0 warnings, 0 errors
```
Auditor examples (all compile): `RBG_X K … ↔ T2475_RBG_X K … := Iff.rfl` for X = Flow, Dom, Prod, Que (targets 1-4,
GMN-C3 binding), Comp; `RBG_ProfComp ↔ T2475_ProfComp := Iff.rfl`; `g1Rowk_of_inputsG_stmt ↔ T2475_g1Rowk_of_inputsG
:= Iff.rfl`; `BAEd ↔ T2475_BAEd`, `BAMO ↔ T2475_BAMO := Iff.rfl`; `T2475_PadSubseq := pad_subseq`;
`T2475_FlowGOfBand d := flowG_of_band`; `T2475_ba_dom_of_bulk := @ba_dom_of_bulk`; `T2475_ba_flowG d := ba_flowG d`;
`T2475_ba_domG d := ba_domG d`; `T2475_ba_mlout d := fun hd h => ba_mlout d hd h` (targets 9-12 as pinned, binder
form only). Part 4 shapes: BA Comp (`ba_comp d`), band Comp+ProfComp, band Dom, band Prod (identity datum),
`T2475_g1Rowk_of_inputsG → UNG1Rowk band …` (all premises from the probe's band lemmas). The check's Part 4 **Que**
shape with the plain band `Ed` (`:311`) is not the type of `RBG_Que_band` (which takes `bandEd`):
`error: Type mismatch RBG_Que_band hd has type RBG_Que … bandEd … but is expected … (fun κ x x_1 z => |lemE z| ≤ 2 - κ) …`
The auditor closed it with the probe's proof, `(hgood n).1.1` → `(hgood n).1` (compiles, exit 0 above). Not binding
(Part 4); see observation O1.
D2 binder order vs the merged `g1Rowk_of_inputs` (`RandomLayerB.lean:316`): T1 `Flow′`, T1′ `Dom′`, T6 ↦ `RBG_Comp`,
T2 `Prod′`, T3 `RandomLayerB_LL` (unchanged), T4 `Que′`, T5 `ML → RandomLayerB_MLout` (unchanged); new binder `Ed`
only; conclusion the merged `UNG1Rowk K P ML Loc Que` (`OUInterfaceK.lean:101`). `ProfComp` is not a D2 premise (it
enters through `ba_comp`). Matches the ticket's D2 proposal exactly.

## 3. Generic layering and hypothesis rules
```
== generic part (probe 13-281) with imports RandomLayerB, SizesComp, Nat.Nth only -> exit=0
== grep -nE "lemE|lemT|msc|etaT|gueScale|STFlow|2 - κ|BA[A-Za-z]" on probe 13-216 (generic) -> no hit; on 217-281 (band) -> 12
```

## 4. Premise scan (`import RBM3D` + probe :12-389 + `RBM.Audit.scanPremises`)
```
== scan_all   scan: 137 premises, unregistered: [RBM.Univ.GUEPhase.RBG_QueSeq, RBM.Univ.GUEPhase.RBG_LLSeq,
               RBM.BA.BAMO, RBM.Univ.GUEPhase.RBG_Eq747Seq, RBM.Univ.GUEPhase.RBG_OullSeq]
== scan_ign   (ignoring g1Rowk_pad, g1Rowk_of_inputsG_of_seq, RBG_LLSeq/QueSeq/OullSeq/Eq747Seq,
               g1Rowk_of_inputsG_stmt, band_D2_at_sz0, ba_D2_at_S0)   scan: 132 premises, unregistered: []
```
Reproduces (a″) row (viii). Registry lines expected: none, provided the 1b keeps the one-sequence lemmas private and
the BA reading of D2 an `example`/private (O4). `Test/Axioms.lean:172-173` are the `UNOULLk`/`UNG1Rowk` owner lines
("BA: BA-C5 (T inputs) + BA-N2 (instance)"), as the ticket says.

## 5. Numerics rerun (prover's scripts copied to `$A`, run unchanged) and an independent check
```
$ python3 band2.py
tauU=ouTauMax=0.0013889 eps=0.011111 4*sqrt(cT)=1.0
n=0 N=2097152 eta_LL=4.965e-7 eta_Q=1.202e-6 lemT(0+i eta_LL)=0.999999503488 | … True | … True | … True | … True
n=1 … lemT=0.999999999998 | True (×4);  n=10 N=11659991713824860234842112 … lemT=1.0 | True (×4)
eventual thresholds at tauU=1/720: r1 N^(tauU/2)>=4 <=> log10 N >= 866.966 ; cT-threshold … =1 holds for every N>=1
$ python3 ba2.py
flow pt: t0=0.549212073 g0=0.222326531 E_*=6.46e-83 Im m0=0.889306125 resid(self_m at E_*,g0)=1.06e-81
kappa_*=0.28307493 kappa_0=(pi kappa_*)^5/2048=0.00027159794 cT=0.00027152419 1/(4sqrt cT)=15.171752 pi*kappa_*<=1: True
n=0 N=2097152 eta=N^(-19/20)=9.873e-7 fT=0.999998889803 | eta_Q=1.71e-5 fT=0.999980775351 | … ok: True | … True True | … True | … True
n=1 … fT=0.999999999943 | fT(eta_Q)=0.999999905384 | True (all);  n=10 … fT=1.0 | True (all)
tauU=1/720=ouTauMax: LL needs N^(tauU/4)>=15.1718 => log10 N >= 3401.38 ; Q needs N^(tauU/2)>=15.1718 => log10 N >= 1700.69
$ python3 v3.py
n=0 N=2.097e+06 Im m_S=0.832488 Im z_S=0.367512 t0=0.693740 | 1/2<=Im m: True | N^(-9/10)<=Im z<=1: True | t0>=2/3: True
n=1, n=10: t0=0.694444 | True True True;  limit lam_n->0: … t0 -> 0.694444 = 25/36 >= 2/3
$ python3 $A/indep.py   (auditor's own)
kappa0=2.71597929e-04 cT=2.71524184e-04 1/(4sqrt cT)=15.171753 pi*kappa<=1:True
tauMax(1/6,1/10)=0.0013889  LL log10N>=3401.38  Q log10N>=1700.69
ba_t0_ineq random violations: 0 / 200000
LL tD'=0.000347222 threshold log10N=3401.38 holds at L+1: True fails at L-1: True  | Q tD'=0.000694444 … 1700.69 … True True
```
Output identical to (a) (ii) line for line (abridged here with "…"). The `τD′` algebra checked against the merged
signatures: `RandomLayer_rowsLL` (`RandomLayerA:213`) gives `t ≤ N^{-τU/2} η/4`, `4(Nη)⁻¹ ≤ N^{-τU/2}` for any
`c > 0`; with `√fT ≥ √cT` both `Prod′` scale rows at `τD′ = τU/4` follow iff `N^{τU/4} ≥ 1/(4√cT)` (Q: `rowsQ :335`,
`τD′ = τU/2`, `N^{τU/2} ≥ 1/(4√cT)`); all `∀ᶠ`, `Nsz → ∞` on admissible sizes. Band: `4√(1/16) = 1`, no threshold.

## 6. Written argument (D2 one-sequence lemmas, not in the probe)
Read the merged `RandomLayerB_oull_seq :205` and `_eq747_seq :241`. Every use of T1 is `c`, `1/16 ≤ t0`, `t0 < 1`,
the `etaT` identity and `1 - t0 ≤ η/c` (→ `rows_flow`), and `|fE| ≤ 2-κ` (→ T2/T4 premise). Under the repair:
`Ed κ'` feeds `Prod′`/`Que′` (both quantify the margin separately from the bulk `κ`), `cT ≤ fT` replaces `1/16`,
`Prod′` states the rows in `√fT·Im z` so the identity is not needed; `Dom′` gives `Fl` at `κ''`, consumed by T5 (`∀ κ`);
T3 needs only `PB` and the bulk. No premise outside D1-D2 (no bulk nonemptiness, no `sz.lam` window, no profile fact
beyond `RBG_ProfComp`). The padding step (`g1Rowk_pad`: `pad_subseq`, `comp_admissible`, `comp_size` by `rfl`,
both directions of `RBG_Comp`) is compiled. Residual 1b work: `RBG_OullSeq`, `RBG_Eq747Seq` by copy-and-edit.

## 7. Copy-table anchors (row (v))
```
$ grep -nE … RandomLayerB.lean / RandomLayerA.lean / SizesComp.lean
103 Flow | 111 Dom | 117 Bulk | 123 MLout | 132 Prod | 151 LL | 166 Que | 186 private _pad | 205 private _oull_seq
241 private _eq747_seq | 316 g1Rowk_of_inputs | 351 _flow_band | 376 _dom_band | 392 _ML_band | 400 _prod_band | 427 _LL_band | 439 _Que_band | 497 inst_g1Rowk_of_inputs
A:98 RandomLayer_rows_flow | A:213 RandomLayer_rowsLL | A:335 RandomLayer_rowsQ
SizesComp: 55 def comp | 68 comp_size (rfl) | 70 withLam_comp | 93 comp_admissible | 239 seqP_withLam_reindex_preimage | 245 measurePreserving_reindex
```
All (a) row (v) and target-8 anchors match.

## 8. Name clash (main + 30 branches `t/T245*`–`t/T249*` except `t/T2475`, `RBM3D/**/*.lean` minus `Probe/`)
`RBG_Flow=0 RBG_Dom=0 RBG_Prod=0 RBG_Que=0 RBG_Comp=0 RBG_ProfComp=0 ProfComp=0 RBG_Comp_of_law=0 RBG_Comp_band=0 RBG_Dom_band=0 RBG_Prod_band=0 RBG_Que_band=0 RBG_ProfComp_band=0 bandEd=0 flowG_of_band=0 flowG_of_band_id=0 g1Rowk_of_inputsG=0 g1Rowk_pad=0 pad_subseq=0 BAfT=0 BAfE=0 BAEd=0 BAMO=0 ba_flowG=0 ba_domG=0 ba_mlout=0 ba_dom_of_bulk=0 ba_Ed_of_im=0 ba_comp=0 RandomLayerBG=0`

## 9. H250 (4) deliverables table and stop lines
| # | status |
|---|---|
| (i) | met: (a) table; constants Lean-fixed in `ba_flowG`; thresholds reproduced (§5) |
| (ii) | met: band `sz0` n=0,1,10; BA `S0` κ_*, κ₀, cT, fT, η=N^{-19/20}, η_Q; V3 antecedent (§5) |
| (iii) | met: D1 predicate form `RBG_Comp` + `RBG_ProfComp` compiled; band `RBG_Comp_band` and BA `ba_comp` close through `RBG_Comp_of_law` (law-level form = the proof, not a second pin); padding compiled |
| (iv) | met: D2 text compiled, `Iff.rfl` to the check; reduction `g1Rowk_of_inputsG_of_seq`; band reading `band_D2_at_sz0` (sz0, 1/6, 1/10, ouTauMax) and BA reading `ba_D2_at_S0` elaborate |
| (v) | met (prose table; anchors verified by script, §7) |
| (vi) | met: band `Dom′`/`Prod′`/`Que′` theorems compiled; band `Ed` = `bandEd` (identity carried), reported |
| (vii) | met: owners Flow′/Dom′/Comp/T5 leaf; ProfComp C3; Prod′/LL/Que′ C5; ML V3 |
| (viii) | met: scan reproduced (§4); registry none; owner text given |
| (ix) | met: generic part compiles with no `BA/*` import (§3); only the probe touched (§1) |
| (x) | met: generic ≈402 + header, leaf ≈107 + header; stop line 2,000 far |
| (xi) | met (§8) |

Stop lines: none hit (targets 1-4 `Iff.rfl`; 9-12 inhabited as pinned; a compatibility form closes at band and BA;
D2 has no premise outside D1-D2; no edit of RandomLayerA/B, OUInterfaceK, PinsK, SizesComp, merged BA/*; no `BA/*`
import in the generic part; sizes far below 2,000). Paper deltas: T2449b is already D689 (b)
(`docs/paper-deltas.md:1653`); `T2475a` (subsequence padding replaces T6), `T2475b` (band `Ed` carries the identity)
proposed in (a″) point 3.

**Fixed by this audit (ticket: "targets 5 and 7 equal the probe texts passed at the 1a-audit"):** target 5 = probe
`:72-82` (`RBG_Comp`, `RBG_ProfComp`, names as in the probe) plus `pad_subseq` `:63`; target 7 = `g1Rowk_of_inputsG`
with statement `g1Rowk_of_inputsG_stmt` (`:177-191`).

## 10. Observations (no RETURN)
- O1. (a″) says the check's Part 4 Que shape is inhabited by `RBG_Que_band`; the prover's `eq_tail.lean` substituted
  `bandEd` into that shape. The plain-`Ed` shape also closes (§2). The 1b may prove either; the D2 band reading needs `bandEd`.
- O2. `ba_dom_ml_at_S0` concludes `True` (η ≡ 1, the window's upper end; T5 at `t ≡ 0`). In the 1b, target 14's
  instance should state the applied conclusions (`BAFlow … ∧ BAMO …`), not `True`.
- O3. Public names not pinned by the ticket (`flowG_of_band_id`, `bandEd`, `RBG_Comp_of_law`, `RBG_*_band`,
  `RBG_ProfComp_band`, `ba_comp`) need the §3 (E) stems `RandomLayerBG_` / `RandomLayerBGBA_` in the 1b, or a
  dispatcher pin. Keeping the pinned `flowG_of_band` and adding the `bandEd` version is additive (ticket target 8: "report").
- O4. Premise scan: keep `g1Rowk_pad` and the one-sequence statements private, and keep the BA D2 reading an
  `example`, or `BAMO`/`RBG_*Seq` appear unregistered (§4).
- O5. The final report must also list T2449b (ticket "Report" item); the 1a does not.

## Verdict
T2475 stage 1a (design gate D1-D2 + probe): **PASS**. Every H250 (4) row is met and no binding stop line is hit. No
dispatcher sign-off is needed. Stage 1b may start under the texts fixed in §9 and observations O1-O5.
