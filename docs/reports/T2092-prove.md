Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 01:05 UTC 2026 (`date -u`)

Source: probe `git show 0362cbc:RBM3D/Probe/T2039Pins.lean` (6041 lines), `$S` = scratchpad (`.../scratchpad`), scripts in `$S/T2092/`. Worktree HEAD = main HEAD = 6583ca2.

### (i) Exponent table (constants of the targets; paper `3_5` = `paper/tex/3_5_Loop_Hierarchy.tex`)

| constant | value / source | constraint (where used) | slack |
|---|---|---|---|
| loss exponent `C_d` | `3C+1`, `C` of `STNewKLKAt` (`ST_step2_of_pins`) | `C_d > 0` (`hC : 0<C`) | `C_d > 1` |
| `𝔠_d` | `min(1/100, 1/(60 C_d), 𝔠₀)`, `𝔠₀` of `STOptL2` | `0<𝔠_d<=1/100` (`STStep2`); `𝔠_d<=𝔠₀` (`hOpt` call); `C_d 𝔠_d<=1/60` (`h3`) | `C_d 𝔠_d<=1/60` is tight when `1/(60 C_d)` is the min (equality) |
| Grönwall bound exponent | `1/5` (`3_5:530`) | `ST_hq_arith`: `r^{C_d} b^{1/5} <= b^{1/6}` needs `1/5 - C_d 𝔠_d >= 1/6`, i.e. `C_d 𝔠_d <= 1/30` | `1/30 - 1/60 = 1/60` |
| scale-step exponent | `1/6` (`3_5:572`, `STScaleAdm` clause 4) | `ST_next`: `q = r^{C_d}b^{1/5} <= b^{1/6} <= 1` (the `hq` hypothesis) | as above |
| engine closure (probe 3830–3860, merged `ST_hsmall_aux`) | `b^{1/30}` | `-(3C+1)𝔠_d + 1/30 >= 1/60` | `0` at `(3C+1)𝔠_d = 1/60` (equality allowed) |
| loss `ε₁` (`ST_selfImprove_section`) | `min(τ/6, c/400)` | `ε₁ < c/4`; `3ε₁ < c/60`; `3ε₁ < τ` | `c/4-ε₁ >= 99c/400`; `c/60-3ε₁ >= 11c/1200`; `τ-3ε₁ >= τ/2` |
| `C_K'` (grid size `K = ⌈N^{C_K'}⌉`) | `max(C_K, 2(C₀+D+3))` | `C₀ - C_K'/2 <= -(D+3)` | `0` at `C_K' = 2(C₀+D+3)` |
| `D_m` | `D'+2D+10` | `D'+4 <= D_m`; `2D+6 <= D_m` | `2D+6`; `D'+4` |
| `D_i` (init. floor) | `(D+3)/𝔠` | `W^{-D_i} <= N^{-(D+3)}` from `N^𝔠 <= W` (`sz.Bandwidth 𝔠`) | `0` (equality in `W = N^𝔠`) |
| `D₁` (`ST_L2_decay_pt`) | `1/𝔠` | `W^{-D₁} <= N^{-1}` from `Bandwidth 𝔠` | `0`; constant `2+2C_K` |
| `STBdata` (`ST_Bdata_holds`) | `cB=(𝔡^{-2}+1)^{-1}`, `c=min(2𝔡𝔠,ε)/2` | `2c<=2𝔡𝔠`, `2c<=ε`, `5N^{-c}<=1` eventually; `1-u>=Im z/4`, `Im z>=N^{-1+ε}` | `min` attained; `5N^{-c}<=1` needs `N>=5^{1/c}` |
| label count | `#STLab <= N^3` (`ST_card_lab_le`, merged) | `N>=4`; uses `L^d <= N=(WL)^d` only, no `L^d <= W^K` | none needed |
| `ST_base_inv` constant | `(C_K+1)` | `C_K*prof^L + B <= (C_K+1) prof^0` (`prof^L <= prof^0`, `B <= prof^0`, both for every real `u`) | none |

Proof-internal eventualities (conclusion is `∀ᶠ n`; NOT hypotheses): `12 c* N^{3ε₁-c/60} < 1`, `c* = 3+3/(√κ/2)` needs `log10 N > 15847` at `c=1/60, τ>=1/60, κ=1/10` (script (ii)b). The theorems state `Prec`/`PrecPT` (asymptotic), so no finite-`N` witness is required for any hypothesis.

**DECISIONS §29 items for `ST_iterate` and `ST_base_inv`** (read from the probe text and the merged lemmas they call; a hypothesis not listed is not used):
- (1) time domain: neither statement has `0<=s`, `t<1`; the proofs use only `s<=u<=t` inside the hypotheses `hq`, `hK2`, `hAdm`, `hOpt`, and merged lemmas without a time premise (`ST_tailW_scale_step`, `ST_tailW_L_le`, `tailT_antitone`, `ST_STprof_pos`: probe 2300–2523, 4540–4620, `Defs/Tail.lean:88`). `Bctl`, `ellT` use `|1-u|`. The consumer `ST_step2_of_pins` supplies `0<=s`, `t<=lemT z<1` (`lemT_lt_one`) when it builds `hq`, `hK2e`. PASS.
- (2) case (ii) boundary `1-ilambda²/L²`: not used; `ellT = min (max (g/√|1-t|) 1) L` is one formula (`Defs/Params.lean:32`), no case split in either statement; `K_u<=(log W)^{10} ℓ_u` appears only inside the merged `STScaleOk`. PASS.
- (3) `L^d <= W^K`: not used. `ST_iterate` and `ST_base_inv` use `N=(WL)^d` (card bound) and `hsz : SizeTendsto`; `Bandwidth 𝔠` (`W>=N^𝔠`, a field of `STFlow`) is used only by `ST_Bdata_holds`, `ST_selfImprove_section`, `ST_L2_decay_pt`. PASS.
- (4) `∀ n` vs `∀ᶠ n`: `hK2`, `hq`, `STScaleOk`, `STScaleAdm` (all clauses but `K_0=0`), `PrecPT` are eventual; the only `∀ n` clauses are `hst : s n<=t n` and `Kseq 0 n u = 0`; `hst` holds at the instance (`0<=1/16`) and `Kseq 0 n u = 0` is a clause of `STScaleAdm` (supplied by `stScaleExists_holds`). PASS.

**Declarations moved and their role in the closure `ST_step2_of_pins`** (script (iii): 54 to move, 34 already merged; the 34 are used by name, not copied, in particular also `STScaleOk`, `STScaleAdm` (Step2Defs) which the ticket's range 2277–2297 would otherwise copy):
- §10: `STSelfImp` (def: conclusion of one Grönwall step), `ST_PT_mono_eventually`, `ST_zdistInf_le`, `ST_next` (`Inv(K_m)+SelfImp(K_m) ⇒ Inv(K_{m+1})`), `ST_decay_of_final` (last scale ⇒ `STStep2DecayPT`).
- Main: `ST_selfImprove_section` (stopped Grönwall bootstrap at one time section; hypotheses `STLWT`, `STEMn2Exp`, `STNewKLKAt`, `STGridMartAt` as pins). Iterate2: `ST_hq_arith`, `ST_selfImprove` (all sections), `ST_iterate`, `ST_decay_pt`.
- §12: `ST_STWB_lower`, `ST_prof_L_le`, `ST_L2_cmp`, `ST_L2_decay_pt` (`(eq:L2_decay)`); `ST_one_sub_lemT`, `ST_Bdata_holds` (size data); `hsize_ev`, `ST_prof_zero_ge`, `ST_prof_L_le_zero`, `ST_base_inv` (base `Inv(K_0=0)`), `ST_ratio_le`, `ST_step2_of_pins`.
- §12.1: `ST_Gres_false`, `ST_Eblk_herm`, `ST_Lloop_one_false`, `ST_Kloop_one`, `ST_avg_pointwise`, `ST_avgU_of_avg`, `ST_concl_of_step2`, `ST_step2_concl` (`ST_step2_concl` is not used by the closure; `ST_avgU_of_avg`, `ST_concl_of_step2` are used by the adapted last step, D-1).
- §12.2: 6 `ST*M_seqHflow`, 16 identity lemmas (`STLKM_eq_STLKIM` … `STgDrift_eq_STgDriftN`, `KLloopOf_cut*`, `STeeLoop_one/two`), `ST_gridMart_of_repN` (`STGridRepN ⇒ STGridMart`), `ST_step2_of_pinsN`.
- Pins that stay hypotheses of `ST_step2_of_pins`: `STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridMart` (or `STGridRepN` in `…N`), `STOptL2`, `STLocalAvgOfL2`; `STK2decay`, `STNetLift2`, `STScaleExists` are also hypotheses there but are now proved: `stK2decay_holds d` (`Induction/Step2K2.lean:132`, T2093), `stNetLift2_holds d` (`Path/NetLift2.lean:688`), `stScaleExists_holds d` (`Induction/Step2Scale.lean:430`), none needs `3<=d`. So the corollary `…_of_pins'` discharges those three and keeps the six pins above (`STLWT`/`STEMn2Exp` as hypotheses; bridges `STLWT_of_LWtermExp` need `(hd : 3 <= d)`). `STLWB` is not a hypothesis of `ST_step2_of_pins`.

**Finding D-1 (adaptation required, not a false statement).** Merged `STStep2 d` (`Step2Defs.lean:599–607`) concludes the bundle `STStep2Concl` (`STLocalEntryU ∧ STAvgU ∧ STGdecayW`); the probe's `STStep2` (probe 805–818) concludes `STStep2Local ∧ STStep2Avg ∧ STStep2Decay`, and `STAvgU` is not `STStep2Avg` (`^1` form, both charges; paper-delta T2039g). Copied verbatim, the last line of `ST_step2_of_pins` (`exact hNet …`, triple) and the body of `ST_step2_concl` (`ST_concl_of_step2 sz hL hA hD`, where `hA` would now be `STAvgU`, not `STStep2Avg`) do not typecheck. Required in 1b: end `ST_step2_of_pins` with `obtain ⟨hl,ha,hd⟩ := hNet …; exact ST_concl_of_step2 sz hl ha hd` (same statement text `STStep2 d`, same hypotheses); restate `ST_step2_concl` over a new public name for the probe's triple form (e.g. `STStep2Parts d`, grep first) or drop it as redundant; propose paper-delta `T2092a`. Math is unaffected: the bodies of `STLocalEntryU`/`STGdecayW` (`Step34Pins.lean:199–215`) and `STStep2Local`/`STStep2Decay` (`Step2Defs.lean:248–270`) read the same, and `ST_concl_of_step2` (probe 4863) is the bridge.

### (ii) Concrete nondegenerate instance (d = 3, `sz0`, `flow_z0`, `s≡0`, `t≡1/16`)
Data: `sz0` (`Defs/Sizes.lean:260`): `L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`, `N=(WL)^3`; `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n=1/2+iN^{-4/5}` (`Induction/Defs.lean:413,435`). Pin constants chosen: `C=1, δ₀=1/10, C₀=1, 𝔠₀=1/100, C_K=1`, so `C_d=4`, `𝔠_d=1/240`; `τ=D=D'=1`. Pins stay hypotheses (`STNewKLKAt 3 κ 𝔡 1 δ₀`, `STGridMartAt 3 1`, `STLWT 3`, `STEMn2Exp 3`, `STOptL2 3`, `STLocalAvgOfL2 3`, `STDecay`, `STStep1Weak`, `STScaleInv`); `hAdm` comes from `stScaleExists_holds 3` at `flow_z0`.
(a) command `python3 $S/T2092/inst.py` (columns: `con_st_ind`: `Bctl(t_n)^{𝔠_d}<=15/16`; `hq` at `u=0,t`; `Bdata`: `cB W^{-3} <= Bctl <= N^{-c}` at `u=0,t` (`Bctl` is increasing in `u`); `WO`: `W^{-7/5}<=lam<=10`; `Bandw`: `N^{1/6}<=W`; `locDom`; `t<=lemT z_n`, `lemT=|msc|²`):
```
Cd = 4  cd = 1/240  Cd*cd = 1/60  (<= 1/60: True ) cd<=1/100: True
hq exponent: 1/5 - Cd*cd = 11/60  >= 1/6: True  slack 1/60
hsmall exponent: 1/30 - (3C+1)*cd = 1/60  >= 1/60: True  slack 0
cB = 1/101  c = 1/60
eps1 = 1/24000   eps1-c/4<0: True   3eps1-c/60 = -11/72000 <0: True   tau-3eps1>0: True
CK' = 10  C0-CK'/2 = -4  <= -(D+3)= -4 : True
 n      L          W        lam      log10 N   B(t)^cd<=15/16  hq(u=0,t)  Bdata(lo,hi)  WO   Bandw  locDom  t<=lemT
 0      4           32  1.56e-02     6.32   False (0.9579)  True    True         True  True   True   True 
 1      8         1024  2.44e-04    11.74   True  (0.9173)  True    True         True  True   True   True 
 2     12         7776  2.14e-05    14.91   True  (0.8943)  True    True         True  True   True   True 
 3     16        32768  3.81e-06    17.16   True  (0.8784)  True    True         True  True   True   True 
 4     20       100000  1.00e-06    18.90   True  (0.8662)  True    True         True  True   True   True 
 5     24       248832  3.35e-07    20.33   True  (0.8564)  True    True         True  True   True   True 
 6     28       537824  1.33e-07    21.53   True  (0.8482)  True    True         True  True   True   True 
 7     32      1048576  5.96e-08    22.58   True  (0.8411)  True    True         True  True   True   True 
 8     36      1889568  2.94e-08    23.50   True  (0.8350)  True    True         True  True   True   True 
 9     40      3200000  1.56e-08    24.32   True  (0.8295)  True    True         True  True   True   True 
10     44      5153632  8.82e-09    25.07   True  (0.8245)  True    True         True  True   True   True 
```
`con_st_ind` fails at `n=0` and holds from `n=1`: it needs `Bctl(t_n)<=(15/16)^{240}=1.875e-07` and `Bctl(t_n)<=9.95e-10` at `n=1`, decreasing in `n` (`W_n^{-3}` factor). `STConStInd` is `∀ᶠ`, so this is the eventual threshold `n₀=1`, small.
(b) command `python3 $S/T2092/thr.py` (output):
```
(15/16)^240 = 1.8754536520940796e-07  -> con_st_ind needs Bctl(t_n) <= that
n=1: Bctl(t) upper bound W^-3*(1/(15/16)+1/(L^3*15/16)) = 9.953510016202927e-10
cstar = 21.973665961010276  gap c/60-3*eps1 = 0.00015277777777777777  proof-internal threshold (12 cstar N^-gap<1): log10 N > 15847.093729475091
```
External/limit hypotheses (TEAM §8 lesson 14), concrete limits for `sz0`: `N_n=(128 (n+1)^6)^3 → ∞` (`SizeTendsto`); `W_n^{-3/2+𝔡}=(2(n+1))^{-7} <= (2(n+1))^{-6}=lam_n <= 1<=𝔡^{-1}` for all `n` (`WO`); `N_n <= W_n^6` since `L_n=4(n+1) <= W_n` (`Bandwidth 1/6`); `Bctl(t_n) <= 1.1·W_n^{-3} → 0`. These are the merged compiled facts `sz0_admissible : sz0.Admissible (1/6) (1/10)` (`Defs/Sizes.lean:331`), `flow_z0` (`Induction/Defs.lean:435`).
(c) Per target: every deterministic hypothesis holds at this data (`0<=s`, `s<=t`, `t=1/16<1`, `t<=lemT z_n`, `hs0`, `ht1`, `hCK`, `hband`, `hsz`, `hBd`, `hCon` for `n>=1`, `hq` as in the table, `h3` with equality); the Kseq of `ST_iterate`/`ST_decay_pt` is `stScaleExists_holds 3`.

### (iii) Diff against the probe, probe names replaced by merged ones (script output)
Command: `python3 $S/T2092/names.py $S | awk …; python3 $S/T2092/cmp2.py $S` (every probe declaration `ST*`/`KL*` with a merged namesake, compared text-for-text after whitespace/comment normalisation):
```
decls in ranges 2243-2525,3572-5346: merged(True)=34 to-move(False)=54
verbatim-same 178 differ 5
('STStep2', 'RBM3D/Induction/Step2Defs.lean')       -> conclusion `STStep2Concl` (D-1)
('ST_LW_sections', 'RBM3D/Induction/Step2Events.lean')  -> only `ST2_Bctl_pos` -> `STBctl_pos` (1 line)
('ST_event_lw', ...Step2Events.lean)  ('ST_event_mg', ...Step2Events.lean)  -> only `ST2_Bctl_pos` -> `STBctl_pos` (1 line each)
('ST_good_engine', 'RBM3D/Induction/Step2Core.lean') -> only `ST2_Bctl_pos/mono` -> `STBctl_pos/mono` (6 lines)
```
Names the new file must rename (D115): probe lines 3821, 3905, 4696, 4697, 4704, 4706 use `ST2_Bctl_pos/mono`; `STBctl_pos`, `STBctl_mono` (`Induction/ScaleFacts.lean:64,74`) have the same statements as probe 1738–1750 (`theorem` line and hypotheses identical). No other probe identifier of the moved ranges is unresolved: all `ST*`/`KL*`/`LW*`/`Prop5*` tokens are merged or defined in the ranges (script `toks.py`: only `ST2_Bctl_mono`, `ST2_Bctl_pos`). Probe sections `§10, Main, Iterate2, Final, Final2, Bdata, Step2, Concl, §12.2` are `namespace RBM.Probe.T2039` with `open RBM.Gauss.Sizes`; in the library they go to `RBM.Gauss.Sizes` (as T2080 did).

### Verdicts
- `ST_selfImprove_section`, `ST_iterate`, `ST_decay_pt`, `ST_L2_decay_pt`, `ST_base_inv`, `ST_Bdata_holds`, `ST_avgU_of_avg`, `ST_gridMart_of_repN`: PASS (exponents close with the slacks above; hypotheses hold at the instance; §29 items (1)–(4) clean).
- `ST_step2_of_pins`, `ST_step2_of_pinsN`, `ST_step2_concl`: PASS with required adaptation D-1 (conclusion of merged `STStep2` is `STStep2Concl`; final step through `ST_concl_of_step2`/`ST_avgU_of_avg`; `ST_step2_concl` must be restated or dropped). Corollary `…_of_pins'` discharges `STK2decay`, `STNetLift2`, `STScaleExists`.
- Overall: PASS.

## (b) Script output — Sun Oct  4 01:19:16 UTC 2026 (`date -u`); commit 1c43ba9 on branch t/T2092

Files: `RBM3D/Induction/Step2Iterate.lean` (new,     2061 lines), `RBM3D/Test/Axioms.lean` (+7 registry lines).
```
$ git diff main...t/T2092 --stat
 RBM3D/Induction/Step2Iterate.lean | 2061 +++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean            |    7 +
 2 files changed, 2068 insertions(+)
$ lake build RBM3D.Induction.Step2Iterate | tail -2
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3759 jobs).
$ (RBM3D.lean with `import RBM3D.Induction.Step2Iterate` added temporarily, not committed) lake build | grep "axiom audit\|Build completed\|^error"
info: RBM3D.lean:135:0: axiom audit: 3058 theorems, 1144 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3836 jobs).
$ same full build BEFORE the 6 registry lines were added (registry pre-check, first run, verbatim):
error: RBM3D.lean:135:0: axiom audit: 6 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.STStep2Avg,
 RBM.Gauss.Sizes.STStep2Local,
 RBM.Gauss.Sizes.STScaleOk,
 RBM.Gauss.Sizes.STGridMartAt,
 RBM.Gauss.Sizes.STScaleAdm,
 RBM.Gauss.Sizes.STStep2Parts]
Classify each of them: borrowed from the literature, owed by this formalization, or a predicate that defines the objects under study.
Some required targets logged failures:
$ forbidden tokens: grep -c "sorry\|admit\|native_decide\|^axiom" Step2Iterate.lean
0
```

`#print axioms` of all 77 theorems/defs of the file and of the 14 `example`s (the examples turned into named defs in a scratch copy `axscratch.lean`, `lake env lean`):
```
lines:       91; lines with exactly [propext, Classical.choice, Quot.sound]: 84; lines with sorryAx: 0
other lines (subsets of the three standard axioms):
'RBM.Gauss.Sizes.KLloopOf_cutL' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.KLloopOf_cutR' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.KLloopOf_length2' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.KLloopOf_cutGlue1' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.KLloopOf_cutGlue2' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.STeeLoop_one' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.Sizes.STeeLoop_two' depends on axioms: [propext, Quot.sound]
targets:
'RBM.Gauss.Sizes.ST_selfImprove_section' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_decay_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_L2_decay_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_base_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_Bdata_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pins'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_avgU_of_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_gridMart_of_repN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsN'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step2_of_pinsLW'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements, extracted from the file by script (`stmts.py`, wrapped at 210 columns; `STStep2Parts` is the new def):
```lean
theorem ST_selfImprove_section (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n)) {C δ₀ C₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀) (hC₀ : 0 ≤ C₀) (hnew : STNewKLKAt d κ 𝔡 C δ₀) (hmart : STGridMartAt d C₀) (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60) (hDec :
    STDecay sz (STflowE z) s) (hCon : STConStInd sz 𝔠d s t) (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → cB * (((sz.W n : ℕ) :
    ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInv sz (STflowE z) s t Kf) (tt : ∀ n, TimeIcc s t n) (D : ℝ) (hD : 0 < D) :
    sz.Prec (U
theorem ST_iterate {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hCK : 0 < C_K) (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInv sz E s t Kf → STSelfImp sz Cd E s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n → 0 ≤ D → ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) (hq : ∀ᶠ n in
    atTop, ∀ u, s n ≤ u → u ≤ t n → ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧ 0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧ (sz.Bctl n u) ^ (1 / 6
    : ℝ) ≤ 1) (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq) (hbase : STScaleInv sz E s t (Kseq 0)) : ∀ m, STScaleInv sz E s t (Kseq m) ∧ STSelfImp sz Cd E s t (Kseq m)
theorem ST_decay_pt {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hCK : 0 < C_K) (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInv sz E s t Kf → STSelfImp sz Cd E s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n → 0 ≤ D → ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) (hq : ∀ᶠ n in
    atTop, ∀ u, s n ≤ u → u ≤ t n → ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧ 0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧ (sz.Bctl n u) ^ (1 / 6
    : ℝ) ≤ 1) (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq) (hbase : STScaleInv sz E s t (Kseq 0)) : STStep2DecayPT sz Cd E s t
theorem ST_L2_decay_pt {E s t : ℕ → ℝ} {Cd C_K : ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hCK : 0 < C_K) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) (hdec :
    STStep2DecayPT sz Cd E s t) (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n → 0 ≤ D → ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a
    0) (a 1)) (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧ 0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)
    ∧ (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1) : STL2decayPT sz E s t
theorem ST_base_inv {E s t : ℕ → ℝ} (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) {C_K : ℝ} (hCK : 0 < C_K) (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u → u ≤ t n → 0 ≤ D
    → ‖STKloop sz n (E n) u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) (hOpt : PrecPT sz (U
theorem ST_Bdata_holds (hd : 0 < d) : STBdata d
theorem ST_step2_of_pins (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d) (hK2 : STK2decay d) (hNet : STNetLift2 d) (hScale : STScaleExists d) (hOpt : STOptL2 d) (hClos :
    STLocalAvgOfL2 d) : STStep2 d
theorem ST_avgU_of_avg {E s t : ℕ → ℝ} (h : STStep2Avg sz E s t) : STAvgU sz E s t
theorem ST_step2_concl {d : ℕ} (h : STStep2Parts d) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z
    → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z)
    s t → STStep1Weak sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd
theorem ST_gridMart_of_repN {d : ℕ} (h : STGridRepN d) : STGridMart d
theorem ST_step2_of_pinsN {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hRep : STGridRepN d) (hK2 : STK2decay d) (hNet : STNetLift2 d) (hScale : STScaleExists d) (hOpt : STOptL2 d) (hClos :
    STLocalAvgOfL2 d) : STStep2 d
theorem ST_step2_of_pins' {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d
theorem ST_step2_of_pinsN' {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d
theorem ST_step2_of_pinsLW' {d : ℕ} (hd : 3 ≤ d) (hNew : STNewKLK d) (hLW : LWtermExp d) (hEMe : STEMn2Exp d) (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d
def STStep2Parts (d : ℕ) : Prop
```

Compiled nonempty instances (14 `example`s, line numbers in the file; helper theorems `bdata_sz0`, `k2_sz0`, `hq_inst`, `scale_sz0` discharge the size data, the `𝒦^{(2)}` bound, the closure arithmetic and the scale family at `(sz0, z0, s ≡ 0, t ≡ 1/16)`):
```
$ grep -n "^example" RBM3D/Induction/Step2Iterate.lean | cut -c1-118
1929:example : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ tInst n →
1937:example (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
1948:example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
1957:example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
1966:example (hdec : STStep2DecayPT sz0 (3 * 1 + 1) (STflowE z0) sInst tInst) :
1973:example (hOpt : PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) ×
1982:example (h : STStep2Avg sz0 (STflowE z0) sInst tInst) : STAvgU sz0 (STflowE z0) sInst tInst :=
1986:example {Cd : ℝ} (hL : STStep2Local sz0 (STflowE z0) sInst tInst)
1993:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
2003:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
2012:example (hNew : STNewKLK 3) (hLW : LWtermExp 3) (hEMe : STEMn2Exp 3) (hRep : STGridRepN 3)
2021:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hRep : STGridRepN 3)
2031:example (h : STStep2Parts 3) :
2041:example (hRep : STGridRepN 3) :
```

Name clash (declaration-line grep of the 77 public theorem/def names over the 131 `.lean` files outside `Probe/`) and moved-text comparison:
```
names checked: 77 files: 131 clashes: 0
$ python3 verb2.py   # probe text (git show 0362cbc:RBM3D/Probe/T2039Pins.lean, ticket ranges minus merged declarations) vs the file
probe-derived text (ranges of the ticket minus merged declarations, after the namespace/open/ST2_Bctl renames): 1723 lines
lines not found verbatim in the file: 28 of which blank: 0
code lines changed or dropped:
   theorem ST_step2_concl {d : ℕ} (h : STStep2 d) :
   section CopiesN
   end CopiesN
   section CopiesN2
   end CopiesN2
   variable {d : ℕ} (sz : Sizes d)
   variable {d : ℕ} (sz : Sizes d)
comment-text lines (headers of 12.1 and 12.2, one docstring line): 21
$ RBM1D/RBM2D ports: none (the moved text is the RBM3D probe at 0362cbc); no diff-stat applies.
```

Narrative (facts from the files and logs above):
- The file is the probe text of the ticket's ranges with 34 merged declarations dropped (`STScaleOk`, `STScaleAdm`, `STAvgU`, `STStep2Concl`, `STLI`..`STGridRepN`, ... are imported), assembled by script and then edited by hand; `verb2.py` lists every difference. Namespace `RBM.Gauss.Sizes`; six `ST2_Bctl_*` uses renamed to `STBctl_*` (file lines 517, 601, 1450, 1451, 1458, 1460).
- Adaptation D-1 (preflight): `ST_step2_of_pins` ends with `obtain ⟨hl, ha, hd'⟩ := hNet ...; exact ST_concl_of_step2 sz hl ha hd'` (probe: `exact hNet ...`). Statement text of `ST_step2_of_pins`, `ST_step2_of_pinsN` unchanged. `ST_step2_concl` is stated for the new def `STStep2Parts` (the probe's `STStep2`); the §12.1 block (`ST_concl_of_step2`) moved above `ST_step2_of_pins`, which now uses it.
- Corollaries `ST_step2_of_pins'`, `ST_step2_of_pinsN'` discharge `STK2decay`, `STNetLift2`, `STScaleExists`; remaining pins: `STNewKLK`, `STLWT`, `STEMn2Exp`, `STGridMart` (resp. `STGridRepN`), `STOptL2`, `STLocalAvgOfL2`. `ST_step2_of_pinsLW'` takes `(hd : 3 ≤ d)` and `LWtermExp d` (bridge `STLWT_of_LWtermExp`).
- New helpers `ST_K2e_of_flow` (the `hK2e` block, from `stK2decay_holds`) and `ST_hq_of_data` (the `hq` block): copies of the in-proof blocks of `ST_step2_of_pins`, public so the instances discharge `hK2`, `hq` at concrete data; `ST_step2_of_pins` itself does not use them.
- Instances at `d = 3`, `sz0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `C = 1` (`C_d = 4`, `𝔠_d = 1/240`, as the preflight instance). Discharged: `SizeTendsto`, `Bandwidth 1/6`, `STFlow`, time ranges, `STConStInd` (eventual; preflight: holds from `n = 1`), size data (`ST_Bdata_holds`), `hK2` (`ST_K2e_of_flow`), `hq` (`ST_hq_of_data`), `STScaleAdm`/`STScaleOk` (`stScaleExists_holds`). Left as hypotheses of the examples (other gates' pins or stochastic premises): `STLWT`, `STEMn2Exp`, `STNewKLKAt`, `STGridMartAt`, `STDecay`, `STStep1Weak`, `STScaleInv` (section example); `hSelf`, `hbase` (`ST_iterate`, `ST_decay_pt`); `STStep2DecayPT` (`ST_L2_decay_pt`); `STOptL2`'s conclusion (`ST_base_inv`); `STStep2Avg`, `STStep2Local`, `STStep2Decay` (`ST_avgU_of_avg`, `ST_concl_of_step2`); the pins of `ST_step2_of_pins*`, `STStep2Parts`, `STGridRepN`.
- Registry pre-check: with the file imported, the full build failed on 6 unclassified premises (log above: `STStep2Avg`, `STStep2Local`, `STScaleOk`, `STGridMartAt`, `STScaleAdm`, `STStep2Parts`); added to `owedProps` in `Test/Axioms.lean` with comments (class proposed: owed); the full build then passed (`3058 theorems, 1144 definitions, 0 axioms`). `STGoodAt` registry line untouched; `STBdata` has no registry line and was not flagged (`ST_Bdata_holds` proves it).
- The in-build linter warnings of the file (line length of the module doc, `maxHeartbeats` comments on the five copied `set_option ... in`, unused variables, `show`) are inherited from the probe text and do not affect acceptance.

## (c) Verified Mathlib names (all used by the new code or by the verbatim moved code; the module builds)
`Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_le_one`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `le_div_iff₀`, `Nat.ceil_pos`, `Nat.le_ceil`, `Set.mem_Icc`, `Exists.choose_spec`, `Filter.Eventually.of_forall`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- `T2092a`: merged `STStep2` concludes `STStep2Concl`; the probe's triple form is now `STStep2Parts` (new, here), bridged by `ST_concl_of_step2`/`ST_avgU_of_avg` (`STStep2Avg` is the `^1`, single-charge form; `STAvgU` has both charges; existing delta T2039g). `ST_step2_concl` takes `h : STStep2Parts d` (probe: `h : STStep2 d`) and concludes the statement text of the merged `STStep2`.
- `T2092b`: registry: six `owedProps` lines (listed above).
- `T2092c`: `ST_step2_of_pins'`, `ST_step2_of_pinsN'`, `ST_step2_of_pinsLW'`, `ST_K2e_of_flow`, `ST_hq_of_data` are new names, not in the probe.
- Pins still open for Step 2: `STNewKLK`, `STLWT`/`STEMn2Exp` (LW gate), `STGridMart`/`STGridRepN`, `STOptL2`, `STLocalAvgOfL2`. No statement of the probe was changed beyond D-1; no hypothesis added to a pinned signature.
- Hub: root import `import RBM3D.Induction.Step2Iterate` after the last import line of `RBM3D.lean` at merge (tested temporarily, not committed).
