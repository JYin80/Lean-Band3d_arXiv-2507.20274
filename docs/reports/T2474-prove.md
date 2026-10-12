Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 21:28:40 UTC 2026

Verdicts: targets 1-12 PASS (details at the end). **Class fields with no band discharge: none** (switch condition 2 not met). C6 (switch condition 1): not fired on the T2379 method (f_sem 0.255); 0.309 on the widest reading (row 12). Split rule (central > 1,950) fires (row 11).

### (i) Exponent / threshold / constant table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | Δ-orders of the one-step error | Expand Δ^{3/2} (`condExp_loop_drift`, LoopStep:310); K-step Δ²; U-step Δ² (`uStepC`) | each > 1 (error o(Δ)) | 1/2; at Δ=0.1: 0.0316, 0.0100, uStepC 0.0957 |
| 2 | `C²` bound of a k-loop | k(k+1) (= 2k + k(k-1) Leibniz terms), η^{-(k+2)}, N=(WL)^d | ‖D²f[y,y]‖ ≤ k(k+1) N η^{-(k+2)} ‖y‖², z-generic (needs only η ≤ \|Im z\|, LoopC2N:469-488) | measured ratio 1.3e-6 (k=3), 2.1e-4 (k=1) at generic m=0.3+0.5i |
| 3 | spectral data replacing \|E\|<2 | z=ztOf m E u, Im z = η=(1-u)Im m (GLoopFlow:55-58) | 0 < Im m, u < 1 | any m, Im m>0 (instance m=i, generic m=0.3+0.5i) |
| 4 | η ≤ 1-u (target 10 premise; K-envelope) | band: Im mE = √(4-E²)/2 ≤ 1 | 0<η≤1-u | E=0: η=1-u exactly (slack 0); u1=0.2: η=0.8=1-u1 |
| 5 | charge product of the U rows | band ‖m(σ)m(σ')‖=1 (`norm_mE`, \|E\|≤2) | UStep K3: row sum ≤ \|t-s\|(1-t)⁻¹; order 2: ≤ Δ²(1-u-Δ)⁻² | K3 sharp (ratio 1.0000 at t=0); order 2 ratio 0.9000 (10%) |
| 6 | range of s in K3 | all real s, 0≤t<1 (no order s≤t) | band lemma states "no order between v and w" (DifREP3:418-420) | asserted at s∈{-0.7,…,1.4} |
| 7 | S row sums (K-step Lipschitz, `norm_primBilS_le`) | Σ_b‖S a b‖ = 1 for SB (L≥3) | ≤ 1 | 0 (exact) |
| 8 | error constants (k=3, j=0, u1=0.2) | envConst Δ^{3/2}=3.7e30 (N⁴=1.93e25), kStepC Δ²=6.7e19 (Bk=1), uStepC=0.0957 | finite, positive; bound constants, not witnesses | n/a |
| 9 | envelope Bk of 𝒦 on [0,u1], length ≤ k | sup‖K2‖=3.05e-5; k≥3 by `GridDriftN_exists_envelope` | Bk ≥ sup | Bk=1: 3e4 on K2 |
| 10 | external `STKboundgL` (registered, KL7) along sz0 | ‖K^{(k)}‖ ≤ N^τ Bctl^{k-1} eventually | k=1: 1 ≤ N^τ; k=2: K2/Bctl ≤ N^τ | τ=0.01: K2/Bctl ≤ 0.985 (n=0), N^τ=1.157; 1.000000 vs 1.60 (n=5), 3.54 (n=500); k≥3 not computed (KL7) |
| 11 | split rule / stop line | own bottom-up central: StepDecompGen 1,245, HierDriftGen 1,503, total 2,748 (script below) | split if total > 1,950; stop 2,000/file; reserve if HierDriftGen > 1,800 | fires (ticket central 1,900, ratio 1.45); per file 755 / 497 below stop; reserve not needed; 2.6× ticket central: 2,080 / 2,860 / 4,940 (REQ line 3,900 is on central 2,748: below) |
| 12 | C6 f_sem(HierAlgebra) | 0.255 (196 raw lines of declarations naming a K closed form / 769), 0.283 (177/625 code lines), 0.309 (193/625 code lines, adds 2 helper lemmas that name no K formula) | ≤ 0.30 | 0.045 / 0.017 / -0.009 (T2379 measured 190/721 = 26% by the same token rule) |
| 13 | window | d=3, L=4≥3, W=32≥1, K=4≠0, j=0<4, k=3≥2, 0≤s=0.1≤t=0.5<1 | as in targets 8-10 | L: 1, K: 4 |

Class-(t) segments (HierAlgebra, lines of the current file): 471-476 `sum_Icc_one_eq_range` (helper), 477-483 `xiLoop`, 484-523 `thetaR_term`, 524-562 `thetaL_term`, 563-599 `couplingLen_two_eq_sum`, 601-614 `set_ofFn_eq_ofFn_update` (helper), 616-688 `couplingLen_two_Kval_eq_thetaOp`; also 714-720 `couplingLen_eq_ksimLK` (algebra, names `KLK`). None is copied into the new files: they are the band discharge of `KTwo`.

### (iii) Hypothesis table (band fact → class field → band discharge → BA source)
| class field | band discharge (all exist, merged) | BA source |
|---|---|---|
| LoopForm `0<Im m` | `mE_im_pos` from \|E n\|<2 | `BAReal` (T5-BA) |
| LoopForm `LM`, `LIM`, `eta` | `STLM`=`loopFine`(`zt`), `STLIM`=`loopL`(`blockMat`)(`zt`) (Step2Defs:60,713), `zt`=`ztOf (mE)` (GLoopFlow:60), `bandFM.eta`=`etaT`=`etaOf` (Carrier:209; `etaT_eq_etaOf`): rfl | `baStep2Mat` fields (Step2BA:57-62) |
| WalkForm Hermitian Ψ, `Pp`, `Hpath` | Ψ=0; `pathP (sz.withLam sz.lam)`=`pathP sz` by structure eta (merged precedent `Chain/CltGen.lean:177`); `Hpath` by `zero_add` | `baStep2Mat_Hpath` (rfl), `PsiI_isHermitian` |
| KLoop | `KLK_isKLoop` (KLTreeDeriv:1049, `Ico 0 1`, `mSigma E`=`PropSpin (mE E)`) + `IsKLoop_iff_IsKLoopS` | `BAKsol_isKLoopS` |
| KTwo | `couplingLen_two_Kval_eq_thetaOp` (HierAlgebra:620; D arbitrary, \|E\|≤2) + private `couplingLen_eq_ksimLK` :714 + `Step2Kern_ThetaN_band` | `baKsol_two`, `Step2Kern_thetaKer_BA` |
| Expand | `condExp_loop_drift` + `stLoopGenNForm_holds` + `Sizes.three_le_L`; WF loop = `loopOf` by private `gdn_loopOf_eq` :936 | T5-BA (TL word envelope; no merged statement) |
| UStep K3 | private `difRep3_sum_norm_uKer_sub_one` (DifREP3:420) via `Step2Kern_uKer_band` | `TwistGridWTail_norm_twU_sub_one_le` |
| UStep order 2 | private `gdn_row_UG` :428 + `gdn_thetaKer_eq` :460 via `Step2Kern_thetaKer_band` (hyps 0≤u, 0≤Δ, u+Δ<1, ‖μ‖=1) | not merged (T5-BA, ticket: ≤ 100 lines) |

Generic proofs need no field beyond these: integrability of the loop observable along the walk (measurable + bounded by `norm_gloop_le_of_le_abs_im`, Split:757, with Hermitian Ψ+pathH and η from `eta`); `condExp` of the constant 𝒦; `deriv 𝒦 = treeEqRhsS 𝒦` from KLoop; polarization `primRhs_split` is S-independent combinatorics (all cut pieces have length ≥ 2, `couplingLen_eq_zero_outside`). Bridge kinds (iv): `rfl` for every `bandStep2_*` of targets 4, 6, 8 (Step2Gen:1040-1058 exist for `STLIM … STeeM`, `STgDriftN`); proved (short): `ZvecN`, `YvecN`, `loopFamN` (`pathH_succ`, deriv of `y ↦ f(M+y(cX))` = c·deriv), `stoppedEdgeN`/`SubGaussStopN` (`Step2Kern_UN_band`), WalkForm `Hpath`, `HierarchyN`/`GridDriftN`/`QVPropagatedN` re-derivations. Observation (size driver): the QVN words/core (QVN:379-406, 414-426, 503-652, 678-695, 716-798: about 290 lines) read `greenBlk d L W E u M`/`zt E u`/`hE`, so they are copied at `z`, not `open private`; the z-free helpers (QVN:97-378, 407-413, 427-502, 653-677, 696-715) are reused. Ticket-cited privates exist at the cited lines (LoopC2N:116,365,424; QVN:716; GridDriftN:78,83,204,428,460,687,759,936; HierAlgebra:714; DifREP3:420).

### (ii) One concrete nondegenerate instance
Data: sz0, n=0 (`Defs/Sizes.lean:260-267`): d=3, L=4, W=32, lam=1/64, N=(WL)^d=2,097,152; E=0 (m=i, Im m=1); s=1/10, t=1/2, K=4 (Δ=1/10, u0=1/10, u1=1/5); j=0, k=3, σ=(+,-,+), labels distinct or equal; M Hermitian; Ψ=0 (band), lam'=sz.lam=1/64, g=lam; Cm.S=SB(1/64); Bk=1. All hypotheses of targets 1-10: |E|<2 ✓, 3≤L ✓, K≠0 ✓, j<K ✓, k≥2 ✓, 0≤s≤t<1 ✓, Σ_b‖S a b‖≤1 ✓, 0<η≤1-v ✓, UStep (both fields) ✓, Bk ≥ sup‖K‖ ✓, `STKboundgL` k=1,2 ✓ (limit rows), C² bound ✓ (non-band m too). Not in the script (merged Lean theorems): Expand, KLoop, KTwo, QV (rows (iii)).
```
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2474
$ python3 $S/instance.py
N=(WL)^d = 2097152  W^d = 32768
max row sum ||S_a.||_1 = 0.9999999999999999 (premise sum_b|S a b| <= 1)
UStep K3 (all s real, 0<=t<1) and order-2 field: all asserts passed; max ratio lhs/rhs K3=1.0000, order2=0.9000 (144 order-2 points)
Delta=0.100 u0=0.100 u1=0.200 eta(u0)=0.900 eta(u1)=0.800, eta<=1-v: True, t<1: True
stepErr terms (k=3,j=0): envConst*D^1.5=3.703e+30  kStepC*D^2=6.724e+19  uStepC=0.095703 (2nd term 0.048828)
Delta orders: 3/2 -> 0.0316, 2 -> 0.0100 (<= 1 required for Delta<=1 ordering)
sup|K2| over w in{0,.1,.2} = 3.052e-05 <= Bk=1
k=3 a=(0, 1, 2) |D2 f[y,y]|=1.7326e+01 <= k(k+1) N eta^-(k+2) |y|^2 = 1.3047e+07  (ratio 1.33e-06)
k=3 a=(0, 0, 0) |D2 f[y,y]|=2.7964e+01 <= k(k+1) N eta^-(k+2) |y|^2 = 1.3047e+07  (ratio 2.14e-06)
k=1 a=(0,) |D2 f[y,y]|=4.0900e+01 <= k(k+1) N eta^-(k+2) |y|^2 = 1.9570e+05  (ratio 2.09e-04)
n=  0 N=2.097e+06 lam=1.56e-02 Bctl=3.873e-05  K2/Bctl<=0.984911  N^tau=1.1567  -> K2<=N^tau*Bctl: True ; k=1: |m|=1<=N^tau: True
n=  5 N=2.130e+20 lam=3.35e-07 Bctl=8.114e-17  K2/Bctl<=0.999928  N^tau=1.5969  -> K2<=N^tau*Bctl: True ; k=1: |m|=1<=N^tau: True
n=500 N=8.293e+54 lam=9.88e-19 Bctl=1.213e-45  K2/Bctl<=1.000000  N^tau=3.5415  -> K2<=N^tau*Bctl: True ; k=1: |m|=1<=N^tau: True
$ python3 $S/fsem2.py
class-(t) code lines 193 band code lines (1..769) 625 f_sem=0.309
raw 216 raw/769=0.281
token-bearing decls raw 196 / 769 = 0.255
token decls code 177 / 625 = 0.283
$ python3 $S/lines.py
StepDecompGen central 1245  HierDriftGen central 1503  total 2748
ticket central 800 / 1100 / total 1900; ratio 1.56 1.37 1.45
split rule (central > 1950): True ; reserve rule (HierDriftGen > 1800): False ; stop line 2000: A 1245 B 1503
2.6 x ticket central: A 2080 B 2860 total 4940 ; 2.6 x own central: A 3237 B 3907 total 7144 ; REQ line 3900
```
Script notes: the C² rows use d=3, L=3, W=1 (N=27), generic m=0.3+0.5i, E=0.7, u=0.4 (z=E+(1-u)m, Im z=η), loops tr∏G(σ_i)E_{a_i} as `loopM` (GLoopFlow:92); second derivative by central difference h=1e-3. U rows use the definitions `uKer`, `thetaKer` (Kernel/Evolution:52-58) at the instance S, E∈{0, 1.3, -1.9}, all four charge pairs. `lines.py`: band spans restated × 0.88 (T2453 683/778) + instances × 0.6 + itemised new material (script source in `$S`).

### Verdicts
- T1 (classes), T2 (`hermTestFunLoopNOf`: `0<Im m` and `u<1` give η>0, proof z-generic), T3 (`QVPropagatedNg` under LoopForm and `Cm.S n = SB d (sz.L n) (g n)`), T4, T5, T6 (`KLoop`, `KTwo`, `loopDrift_sub_K_deriv_ng`), T7, T8, T9 (a)(b), T10, T11, T12: **PASS**. No false statement, no hypothesis set that cannot hold, every exponent closes (rows 1-10), every class field has a band discharge.
- Observation for 1b (no verdict effect): K3 is stated for all real s; the band lemma `difRep3_sum_norm_uKer_sub_one` covers it, `gdn_row_U` (Δ≥0, u≥0) does not. BA discharge of `Expand` and of UStep order 2 has no merged source (T5-BA).
- Decision inputs for the hub/dispatcher: split rule fires (row 11, own central 2,748 > 1,950): T5s2a = `StepDecompGen` (1,245), T5s2b = `HierDriftGen` (1,503, reserve not needed by the 1,800 rule); f_sem tripwire not fired on the T2379 method (row 12).

## (a′) Preflight corrections — Mon Oct 12 22:20:29 UTC 2026

One omission in (iii), no verdict change (targets 1-12 stay PASS). The link `Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a` for `w ∈ [0,1)` is
needed by target 9 and is in no pinned class: `predIncNg` reads the field `Cm.K` (`AvecNg` → `STLKMg`, `Chain/Step2Gen.lean:353`), while the 𝒦-step, the drift
identity and the envelope read `Cm.KI`. Evidence: `grep -nE "Cm\.K( |$)|C\.K( |$)"` on the check's Part 2 (lines 131-292) prints nothing; no `T2474_*` class mentions the field `K`.
Band discharge: `rfl` (`hierDriftGen_kLink_band`, `STKloop = KLK ∘ KLloopOf`); BA: `baStep2Mat_KI` (ticket target 10 already lists it as input (e)).
Handling: the pinned classes are unchanged; `gridDriftNg_at`, `gridDriftNg` take one extra explicit premise `HierDriftGen_KLink Cm n` (the shape of target 9 (b) is "not binding" in the check). The dispatcher
decides whether it becomes a class field instead (paper-delta candidate T2474b).

## (b) Script output
```
$ lake build RBM3D.Chain.StepDecompGen RBM3D.Chain.HierDriftGen 2>&1 | grep -E "Build completed|error|sorry"        (22:18 UTC)
Build completed successfully (3777 jobs).
$ lake env lean docs/tickets/checks/T2474-check.lean ; echo "exit $?"          (main worktree file, run in the t/T2474 worktree)
exit 0
$ git diff main...t/T2474 --name-only            # G1: target 12; the band files, Step2Gen, Step2Kern, Carrier, GridDuhamelGen, BA/ are untouched
RBM3D/Chain/HierDriftGen.lean
RBM3D/Chain/StepDecompGen.lean
$ git diff 97341078 t/T2474 --name-only -- RBM3D/Induction RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean RBM3D/Chain/GridDuhamelGen.lean RBM3D/BA | wc -l
0
$ wc -l (per commit; stop line 2000 per file)     StepDecompGen / HierDriftGen
8154da93 669/0   9e303ff9 1246/0   241111b4 1246/463   602d8261 1246/613   e2a43671 1246/955   7a847272 1246/1150   68da78e4 1246/1277   9a31da3d 1246/1384   662c05c2 1246/1381
$ git diff main...t/T2474 --stat | tail -1
 2 files changed, 2627 insertions(+)
```
**Lines and split.** `StepDecompGen` 1,246 and `HierDriftGen` 1,381 (reserve `HierDriftGen2` not used: 1,381 ≤ 1,800); both are below the stop line 2,000. Total 2,627 vs the 1a central 2,748
(row 11). The pre-signed split (central > 1,950) is therefore a hub/dispatcher choice: the file boundary is clean (`HierDriftGen` imports `StepDecompGen`; `StepDecompGen` imports neither). Both files are delivered on `t/T2474`.
**Layout.** `import` lines: `StepDecompGen` ← `Chain.GridDuhamelGen`, `Induction.StepDecompN`; `HierDriftGen` ← `Chain.StepDecompGen`, `Induction.GridDriftN`. `grep -n '^import RBM3D.BA'` on both: no output.
Importers of the new modules (`grep -rln "Chain.StepDecompGen\|Chain.HierDriftGen" RBM3D RBM3D.lean`): `RBM3D/Chain/HierDriftGen.lean` only (the root imports are the hub's, merge step 4).
**Axioms** (scratch file importing both modules; `#print axioms` of every public declaration, 114 of them, `Chain/StepDecompGen.lean`, `HierDriftGen.lean`):
```
$ lake env lean AxCheck.lean ; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out   -> 114   (grep -vc "depends on axioms" -> 0; grep -c sorryAx -> 0)
$ lake env lean AuditFull.lean     # import RBM3D + both modules + #assert_rbm_axioms (full environment); exit 0
axiom audit: 13884 theorems, 4415 definitions, 0 axioms in `RBM` ... All within [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Chain/StepDecompGen.lean RBM3D/Chain/HierDriftGen.lean   -> 0 and 0
```
The full `lake build` (with the root import lines) is the hub's merge step 5; the premise scan of `#assert_rbm_axioms` passes with both modules in the environment (every `Prop` that a theorem of these files takes as a hypothesis is concluded by a band theorem here, or is the registered `STKboundgL`).
**Statement diff against the pins** (scratch `StmtCheck.lean`: Part 2 of the check file copied verbatim, then `example : T2474_X ↔ <class> := Iff.rfl` for all 12 pinned classes/conclusions, `example : T2474_HermLoopOf := hermTestFunLoopNOf`,
`T2474_QVg`, `T2474_LoopDrift`, `T2474_HierarchyNg`, `T2474_GridDriftNg` from the generic theorems, and the four band re-derivations): `lake env lean StmtCheck.lean ; echo $?` -> exit 0, 0 `error` lines, 21 `example`s.
**Targets (declaration S:line = StepDecompGen, H:line = HierDriftGen).**
```
T1 classes : StepDecompGen_LoopForm S:60; StepDecompGen_WalkForm S:73; stepDecompGen_loopForm_band S:459; stepDecompGen_walkForm_band S:465
T2 C2      : HermTestFunLoopNOf S:86; hermTestFunLoopNOf S:101; StepDecompGen_hermLoop S:695; band hermTestFunLoopN_of_Of S:121
T3 QV      : QVPropagatedNg S:479; qvPropagatedNg S:505; band qvPropagatedN_of_Ng S:519
T4 vocab   : loopFamNg S:537; ZfamNg S:543; ZvecNg S:548; YvecNg S:554; stoppedEdgeNg S:560; SubGaussFormNg S:567; SubGaussStopNg S:575; bridges bandStep2_ZfamN S:615 _loopFamN S:624 _ZvecN S:630 _YvecN S:638 _stoppedEdgeN S:646 _SubGaussFormN S:654 _SubGaussStopN S:658
T5 ident   : ZvecNg_eq_stepZCN S:802; UN_stepZCNg S:812; martIncNg_eq_stepXiCN S:842; YvecNg_eq_stepYCN S:889; UN_stepYCNg S:902; subGaussStopNg_zvecNg S:941; band stepDecompGen_band_* S:1002-1087 (6)
T6 algebra : primBilS H:65; primRhsS_split H:208; norm_primBilS_le H:240; STllPairNg H:309 (bridge bandStep2_STllPairN H:314); HierDriftGen_KLoop H:320; HierDriftGen_KTwo H:326; loopDrift_sub_K_deriv_ng H:344; bands H:387, 394, 404
T7 hier    : HierarchyNg H:429; hierarchyNg_of H:441; band hierarchyN_of_Ng H:457
T8 pin     : stepErrNg H:619; bandFM_stepErrN H:625 (rfl); GridDriftNg H:630
T9 step    : HierDriftGen_Expand H:649; HierDriftGen_UStep H:666; HierDriftGen_KLink H:677; gridDriftNg_at H:818; gridDriftNg H:941; bands hierDriftGen_expand_band H:1197, _uStep_band H:1182, _kLink_band H:682, hierDriftGen_band_gridDriftN H:1227
T10 env    : HierDriftGen_exists_envelope H:1001; exists_norm_KI_le_wing H:1083; bands hierDriftGen_band_exists_envelope H:1241, hierDriftGen_band_exists_norm_Kcal_le_win H:1264
```
**Compiled nonempty instances** (`d = 3`, `sz0`: L_0 = 4, W_0 = 32, N = 2097152, band carrier `E ≡ 0`, `Ψ = 0`, `lam' = sz0.lam`, window `s ≡ 0, t ≡ 1/2, K ≡ 4`, `Δ = 1/8`; data lemmas `data` S:1152 / H:1307):
```
$ grep -nE "^(example|theorem hermTestFunLoopNOf_instance)" Chain/StepDecompGen.lean     (namespace StepDecompGenCheck)
1159 hermTestFunLoopNOf_instance (T2: m = 3/10 + i/2, E = 1/5, u = 1/2, k = 3, labels (0,1,2); both conjuncts at M = 0, y = 1)
1175 qvPropagatedNg Cm0 ... (T3: u = 1/2, M = 1, k = 3, κ ≡ 1)         1179 StepDecompGen_hermLoop (T1, T2 carrier corollary)
1182/1185 ZvecNg_eq_stepZCN j = 0, 1        1188/1190 martIncNg_eq_stepXiCN j = 0, 1        1192/1194 YvecNg_eq_stepYCN j = 0, 1
1196/1199 UN_stepZCNg j = 0, 1              1202/1204 UN_stepYCNg j = 0, 1        1231 SubGaussStopNg (τ ≡ K 0, {0 < τ} = univ; proxy c3 from the deterministic A_0)
$ grep -nE "^example|^private theorem env3" Chain/HierDriftGen.lean                          (namespace HierDriftGenCheck)
1312 norm_primBilS_le (SB, loop ((+,-),(0,0)), F = G = 1)       1318 primRhsS_split (every K, D)
1323 loopDrift_sub_K_deriv_ng (u = 1/2, M = 1, k = 3, σ = (+,-,+), a = (0,1,2))        1328 hierarchyNg_of (same data)
1333 GridDriftNg Cm0 s0 t0 K0 (the whole pin, every class discharged)        1339/1353 env3, env3' (HierDriftGen_exists_envelope on [0, u_1], [0, u_2])
1345/1358 gridDriftNg_at j = 0 (H_0 = 0), j = 1 (random H_1), envelope from env3/env3'        1366 band GridDriftN        1370 exists_norm_KI_le_wing (hypothesis: STKboundgL, registered)
```
Only hypotheses left in an example: `hKb : STKboundgL Cm0.toFlowFM (Sizes.seqP sz0)` (registered, `Test/Axioms.lean:134`); every deterministic hypothesis is discharged.
**Name clash.** `names.txt` (114 new public names): `git grep -w -l <name> <ref> -- RBM3D` outside the two new files, refs `main`, `t/T2465`, `t/T2467`, `t/T2469`, `t/T2469b`, `t/T2470`, `t/T2471`, `t/T2471b`, `t/T2472`, `t/T2475`: 0 hits at each ref.
**X1-C1** (`grep -nE "\bmE\b|zt E|zt \(|2 - κ|\|E\||etaT|mSigma|cycProd|sz\.lam|Ugen|ThetaN d|uKer d|KLK d|STKloop|pathP sz|pathH sz|SB d|gvarF|withLam"`, each hit assigned to its enclosing declaration by script):
```
StepDecompGen: doc 34; band bridges/discharges/re-derivations/instances 21; withLam: WalkForm (2), identification theorems of T5 and their helpers (the shifted walk `sz.withLam lam'`, by design);
  SB d / gvarF: the variance premise of T3 (QVPropagatedNg, qvPropagatedNg, StepDecompGen_eeN, _Ecut, _core: note (4)); sz.lam, mE: the band re-derivations qvPropagatedN_of_Ng, hermTestFunLoopN_of_Of; `pathH sz`: substring of StepDecompGen_pathH
HierDriftGen:  doc 12; band 22; SB d: hierarchyNg_of (variance premise, T7), HierDriftGen_sum_norm_uKer_sub_one (copy of DifREP3:420, band helper), hierDriftGen_SB_row; sz.lam: hierarchyN_of_Ng, hierDriftGen_SB_row (band)
```
No hit in a class, a generic conclusion or a pinned statement other than the stated ones.
**U-C4**: `grep -nE "^(noncomputable )?def |^abbrev "` on the new files (28 hits): Prop classes/pins, scalar-valued `loopDerivZ`, `eeN`, `primBilS`, `HierDriftGen_primBilLenS/_RS`, `couplingLenS`, `STllPairNg`, `stepErrNg`, vectors `ZfamNg`, `ZvecNg`, `YvecNg`, `stoppedEdgeNg`, the loop family `loopFamNg(Shift)`, and the walk `StepDecompGen_pathH` (an abbrev for `pathH (sz.withLam lam')`): no matrix- or tensor-valued kernel is defined; every kernel is `Step2Gen_UN`, `Step2Gen_uKer`, `Step2Gen_thetaKer`, `Step2Gen_ThetaN`.
**TN-C4**: `grep -c STGridRepNgL` on the new files: 0 and 0. **UBA-C1**: not triggered; `sz.lam` occurs only in band re-derivations and docs (X1-C1 table), no generic statement crosses a size-level coupling with a kernel coupling.
**Sources of the copies** (no port from RBM1D/RBM2D; all copies are from merged RBM3D band files at `main` `97341078`): `Induction/QVN.lean:378-424, 500-650, 677-695, 716-797` (words/Leibniz/cut at `z`, stem `StepDecompGen_`), `HierAlgebra.lean:41-310` (→ `primBilS`…, kernel `S`), `GridDriftN.lean:497-646` (K-lip/K-step), `:950-985` (envelope), `:1010-1188` (window), `Path/DifREP3.lean:420`. `open private` from: `LoopC2N` (3 names), `QVN` (17), `StepDecompN` (7), `HierAlgebra` (4), `GridDriftN` (12).
**Narrative.**
- Both files compile with `Build completed successfully`; no `sorry`; the three standard axioms only. The band files are not edited.
- Hypothesis table (iii) was used as stated, plus the K-link of (a′). The class-(t) segment (C6): `HierDriftGen_KTwo` is a hypothesis; its band discharge `hierDriftGen_kTwo_band` is H:394-401 (8 lines) using `couplingLen_two_Kval_eq_thetaOp` and the private `HierAlgebra_couplingLen_eq_ksimLK` by `open private`; no class-(t) segment of `HierAlgebra` (471-688) is copied, so the C6 count here is 0 copied lines of 1,381.
- Band re-derivations are stated under `∀ n, |E n| < 2` (the classes `LoopForm`, `WalkForm`, `KLoop`, … are `∀ n` objects); the band pointwise theorems of target 5 take `|E n| < 2` at one `n` (paper-delta candidate T2474c).
- `gridDriftNg_at` takes the whole `LoopForm`/`WalkForm` (they are `∀ n` by their pinned text) and, for the per-index objects, `Expand`, `KLoop`, `KTwo`, `UStep`, the row-sum bound and `KLink` at `n` only, and the window at `n` only.
- The helper premises `hder` (`∂_t KI = treeEqRhsS S KI` on `[0,1)`) and `hB` (envelope) of `HierDriftGen_K_lip/_K_step/_exists_envelope_of` are spelled out as hypotheses, not as named `Prop`s: a named `Prop` that no theorem concludes would be a new unclassified premise for `#assert_rbm_axioms` (`Test/Axioms.lean` is not writable).
- The envelope-window theorem (`exists_norm_KI_le_wing`) is generic in a probability measure `μ`; the band reading is `μ = seqP sz` (`STKbound sz E` is `STKboundgL (bandFM sz E) (seqP sz)` by unfolding).

## (c) Mathlib names (verified in `.lake/packages/mathlib`)
- `fderiv_comp_add_left` (`Analysis/Calculus/FDeriv/Add.lean:900`); `deriv_comp_mul_left` (`Analysis/Calculus/Deriv/CompMul.lean:43`); `condExp_sub` (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:336`); `condExp_const` (`:148`);
  `memLp_top_of_bound` (`MeasureTheory/Function/LpSeminorm/Basic.lean:611`); `mul_le_of_le_one_right` (used in `Topology/UnitInterval.lean:66`); `HasCondSubgaussianMGF` (`Probability/Moments/SubGaussian.lean`).
- Absent: none looked for.

## (d) Open issues and paper-delta candidates
- **T2474a** (carrier data form, ticket (8)): the per-step layer is stated for the shifted walk `Ψ n + pathH (sz.withLam lam')` with loops at `ztOf m E u`; band `m = mE E`, `Ψ = 0`, `lam' = sz.lam` (numbered at merge).
- **T2474b** (new premise): `gridDriftNg_at`/`gridDriftNg` carry `HierDriftGen_KLink Cm n` (`KI ∘ KLloopOf = K` on `[0,1)`), see (a′); band `rfl`, BA `baStep2Mat_KI`. If the dispatcher prefers a class field, `HierDriftGen_KLoop` is the natural home (one more conjunct; consumers `hierDriftGen_kLoop_band` and the BA reading change).
- **T2474c**: band re-derivations of target 5 and of `GridDriftN` hold under `∀ n, |E n| < 2`; the single-index band forms (`gridDriftN_at`, `ZvecN_eq_stepZCN` at one `n`) are not re-derived.
- Owed to T5-BA (statement level, in the check): the BA instances of `LoopForm`, `WalkForm`, `KLoop`, `KTwo`, `Expand`, `UStep`, `KLink`; `Expand` (word envelope of `TwistGridRem`) and the order-2 field of `UStep` have no merged BA source.
- Registered premise left in an example: `STKboundgL`. The auditor adds `example : <statement> := <name>` for Part 3 of the check (the band files are unedited; `lake env lean` of the check exits 0).
