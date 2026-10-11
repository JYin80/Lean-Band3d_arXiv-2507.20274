Auditor model: claude-opus-5-5
# T2414 1a-audit (design gate) — Sun Oct 11 09:56:00 UTC 2026

Inputs: ticket `docs/tickets/T2414.md`; section (a) and (a″) of `docs/reports/T2414-prove.md`; branch `t/T2414` at `6111b33`;
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2414-1aaudit` (detached, `.lake/build` APFS clone of main's).
Scratch: `$A = <scratchpad>/T2414/audit1a`. Section (a) is mathematics and pins only; no Lean on the branch except the probe.

## 1. Probe recompile (own worktree)
```
$ git diff --stat main...t/T2414
 RBM3D/Probe/T2414Pins.lean | 769 ++++   1 file changed, 769 insertions(+)
$ lake build RBM3D.Chain.NewKLKGen RBM3D.BA.FlowPins RBM3D.BA.KSolve RBM3D.BA.EKPins RBM3D.BA.KTreeRep
Build completed successfully (3768 jobs).
$ lake env lean RBM3D/Probe/T2414Pins.lean > $A/probe.out; echo exit=$?; grep -nE "error|warning" $A/probe.out
exit=0                                   (64 output lines, all #check output; no error/warning line)
$ grep -nE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2414Pins.lean; echo grep=$?
grep=1
$ lake env lean $S/AxiomsCheck.lean | grep "depends on" | sed 's/^.*axioms: //' | sort | uniq -c
  12 [propext, Classical.choice, Quot.sound]     (diff vs probe: only the 12 `example` -> `def T2414_inst_k` + 12 #print axioms)
```
Scratch feasibility (`$S/f6.lean`, `$S/f5b.lean`, not deliverables) recompiled here; their pin texts equal the probe's:
```
$ lake env lean $S/f6.lean; lake env lean $S/f5b.lean      -> f6 exit=0 errors=0 ; f5b exit=0 errors=0 ; sorry/admit grep: 0, 0
$ python3 (pin-text compare)   f6: 23 pins proved, all defined identically to probe: True
                               f5b: 5 pins proved, all defined identically to probe: True   (23 + 5 = 28 distinct pins)
```

## 2. Statement check: probe definitions vs merged text (script `$A/defdiff.py`)
```
STgDriftg: changed lines 0          STGridMartAtgL: 0      STGridMartgL: 0      STGridRepNgL: 0
STNewKLKAtgL: 0   STNewKLKgL: 0     STNewKLKAtgL': 0       STNewKLKgL': 0
STgDriftNg: 2   -  Step2Gen_ThetaN (Cm.S n) (fun i => STmsigg Cm n (σ i)) (gridTime s t K n k)
                +  Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n k)
STeeUMg: 4      -  Step2Gen_uKer (Cm.S n) (cycProd (fun i => STmsigg Cm n (σ i)) i) ...   [and !σ]
                +  Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate m i)) ...            [and (!σ i, !σ (finRotate m i))]
STGridRepNAtgL: 2  -  Step2Gen_UN ((mk sz z).S n) (fun i' => STmsigg (mk sz z) n (i.1 i'))
                   +  Step2Gen_UN (mk sz z).toFlowFM n i.1
NewKLKGenHyp: 5 (F7 only)  - ∀ (σ : Fin 2 → Bool) ... ‖(S n * Step2Gen_Theta (S n) (u * (m_σ0 * m_σ1))) a b‖
                           + ∀ (s s' : Bool)    ... ‖Step2Gen_thetaKer (mk sz (fun _ => E)).toFlowFM n s s' u a b‖
STthetaOpg: body  - (m_σ0 m_σ1) * (S Θ_{u m_σ0 m_σ1})(a i, b)   (same pair at both slots)
                  + Step2Gen_thetaKer Cm.toFlowFM n (σ i) (σ (finRotate 2 i)) u (a i) b
$ diff <(def STK2decaygL, Step2Gen.lean) <(def STK2decaygL', probe)
<  ... 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
>  ... 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →        (only change, as BAT-F2 asks)
```
Against the paper: `Step2Kern_Mss` = `W^{-d} Σ_{x∈[a],y∈[b]} M(σ)_{yx} M(σ')_{xy}` = `W^d tr(M(σ)E_aM(σ')E_b)` with
`(E_a)_{xy}=W^{-d}1(x=y∈[a])` (`1_2:81`, `eq:Msig` `1_2:1070`, `def:Theta_BA` `1_2:663-664`); `thetaKer = (MS)(1−tMS)⁻¹`,
`uKer = (1−sMS)(1−tMS)⁻¹`, slot `i` with `(σ_i, σ_{i+1})` cyclic: exactly `def:op_thn`, `def_Ustz` (`3_5:111-118`).
`BAMss` (`MFixedPoint:511`) is `M(σ₁)_{ba} M(σ₂)_{ab}`, `BAMsigma false = Mᴴ`; `BAUN` (`EKPins:53`) uses `finRotate`. Match.
Cut rejection verified: `baFM.K` is `BAKloop` = `BAKsol` = `h.choose` or `fun _ _ => 0` (`FlowPins:283-288`); `baFM.S = 1`,
`baFM.M = BAMfine` (`FlowPins:322-329`); `bandFM.M = if x = y then mE else 0`, `S = SB` (`Carrier:203-210`). The derived
kernel reads only `FlowFM.M`, `FlowFM.S`: no `FlowFM` field, `Carrier.lean` untouched (stop line not hit).

## 3. (ii) Changed declarations and consumers (grep)
```
$ grep -nE "Step2Gen_Theta\b|Step2Gen_thetaKer|_uKer|_ThetaN|_UN|cycProd|STthetaOpg|STeeUMg|STgDriftNg|STgDriftg" Step2Gen NewKLKGen
  uses at Step2Gen:195-199, 242, 643-645, 671, 695, 715-732, 789-791, 799-803, 822, 837, 841, 873, 875, 895;
  NewKLKGen:61, 390, 466, 485-487, 776      (all covered by (a)'s list; no other user)
$ git grep -lwE "<all changed names>" c33ef56 -- 'RBM3D/*.lean' RBM3D.lean   -> Chain/NewKLKGen.lean, Chain/Step2Gen.lean
$ git grep -lwE "<all changed names>" main(88d1b63) -- ...                  -> + BA/Step2BA.lean
$ git grep -nwE "<names>" main -- RBM3D/BA/Step2BA.lean                      -> lines 27, 28, 153, 167: docstrings only
$ git grep -nE "Step2Kern_|STK2decaygL'|stK2decaygL_of_primed" main | wc -l -> 0
$ python3 cone.py <branch wt> RBM3D.Chain.Step2Gen -> 76 (incl. Probe.T2414Pins; 75 without, as (a) says)
$ python3 cone.py <main> RBM3D.Chain.Step2Gen      -> 78; main − branch = BA.Step2BA, Graph.BASizeClaim, Graph.BASizeClaim2
  LWExpCert* in cone: 0
```
Bridges that stop being `rfl` (`Step2Gen:242, 695, 873, 875`, and the `Iff` bridges `:698, 701, 876, 879, 917, 919`) are
all pinned (`bandStep2_*_pin`, 10 pins); `bandStep2_STK2decay` stays `Iff.rfl` (STK2decaygL unchanged). Check file
`docs/tickets/checks/T2414-check.lean` uses only `#check @` and the two band `example`s: compatible with in-place redefinition.

## 4. (iii) Numerics: rerun of (a)'s script, then an independent script
```
$ cd $A && python3 ../check.py > rerun_check.out; diff <(rerun) <(block in T2414-prove.md:32-48) && echo IDENTICAL_TO_REPORT
IDENTICAL_TO_REPORT
  g=0.015625: max|Mfine-BAMss|=1.1e-16 max|ker-Th*Mss|=1.4e-14 ... max|old diag - BA ker|(+,-,u=.9)=2.367e-02
  g=1:        max|Mfine-BAMss|=5.6e-17 max|ker-Th*Mss|=1.3e-15 ... 6.333e-01
  g=10:       max|Mfine-BAMss|=5.6e-17 max|ker-Th*Mss|=2.3e-15 ... 9.178e-01
  (+,-): |fine - BAMss(s1,s2)|=1.8e-15  |fine - BAMss(s2,s1)|=1.36e+01  |fine - BAMss(s1,s2)^T|=1.36e+01
  slot-1 kernel (s1,s0) vs wrong reuse of (s0,s1) at slot 1: max diff = 2.357e+01
```
Independent (`$A/indep.py`: literal transcription of the probe definitions; scrambled fine ordering, block map only;
`M_xy = B(blk x, blk y)1{ofs x = ofs y}`; Newton solve of `(self_m)`; `UN` vs `BAUN` by tensor contraction):
```
$ python3 indep.py
g=0.01562  E=0.0: Im m=0.9993 max|Mss_lean-BAMss|=1.1e-16 max|thetaKer-BATheta*BAMss|=5.0e-14 max|UN-BAUN|(k=3,+,+,-)=1.7e-14
g=0.01562  E=0.3: Im m=0.9880 max|Mss_lean-BAMss|=2.2e-16 max|thetaKer-BATheta*BAMss|=4.6e-14 max|UN-BAUN|(k=3,+,+,-)=1.8e-14
g=1        E=0.0: Im m=0.6860 max|Mss_lean-BAMss|=1.1e-16 max|thetaKer-BATheta*BAMss|=1.8e-15 max|UN-BAUN|(k=3,+,+,-)=4.4e-15
g=1        E=0.3: Im m=0.6696 max|Mss_lean-BAMss|=1.1e-16 max|thetaKer-BATheta*BAMss|=1.2e-15 max|UN-BAUN|(k=3,+,+,-)=3.6e-15
g=10       E=0.0: Im m=0.6669 max|Mss_lean-BAMss|=1.1e-16 max|thetaKer-BATheta*BAMss|=1.6e-15 max|UN-BAUN|(k=3,+,+,-)=5.7e-15
g=10       E=0.3: Im m=0.6500 max|Mss_lean-BAMss|=1.1e-16 max|thetaKer-BATheta*BAMss|=1.3e-15 max|UN-BAUN|(k=3,+,+,-)=4.5e-15
band (E=0.5, random symmetric S, u=0.6): max|STthetaOpg_new - STthetaOpg_merged| over 4 charge pairs = 1.7e-16
Im m, g=1.0, E=0 (Newton): L=16 0.4160  L=64 0.4106  L=128 0.4106  L=256 0.4106
Im m, g=10.0, E=0 (Newton): L=16 0.2028  L=64 0.0764  L=128 0.0553  L=256 0.0477
```
(b) and (c) hold at all three `g` (and at `E = 0.3`); the `BAUN` identity of (c) holds (no obstacle); the new
`STthetaOpg` equals the merged one at the band for a non-diagonal `S`; the old diagonal reading differs at BA (BAT-F1).

## 5. Deliverables and stop lines
| Ticket item | Finding |
|---|---|
| (i) choice of (a), convention, in place vs new names, lines | block kernel (reason: cut is `Classical.choose`/0); charge/index order fixed and tested; in place. Lines given for the chosen route only (O2) |
| (ii) changed declarations, consumers, non-rfl bridges | complete by grep (§3); adds `STeeUMg`/`bandStep2_STeeUM` (forced by in-place `uKer`, O4) |
| (iii) (b), (c) written; numerics at g = 1/64, 1, 10; `BAUN` | written (a) l.25-26; reproduced identically and independently (§4); `BAUN` identity holds |
| (iv) lines vs 1,400 | ≈550 (450–750); scratch measured 44 (vocab) + 274 (proofs) + NewKLKGen −42/+38: consistent |
| Instances (target 8) | probe §8: band at `sz0` (L=4, W=32, N=2097152, E≡0, 4 charge pairs, k=3); BA at `sz0`/`zSeq`, n=0, `Im m>0` discharged by `BAmF_sz0_im_pos`, kron by `BAMfine_sz0_kron`; all 4 pairs proved (no numeric stand-in) |
| Stop: FlowFM field / Carrier edit | not needed |
| Stop: (b) or (c) fails | neither fails |
| Stop: 1,400 lines | not approached |

## 6. Observations (no statement, instance, build, axiom or delta-coverage change at this gate)
- **O1 (κ at g = 10).** Table rows 14-15 give `κ = 0.05` at `g = 10`; the independent Newton solve gives `Im m = 0.0477` at
  `L = 256` (still falling; supervisor 2254 G2 quotes ≈0.044 on the flow's `z`). `κ` enters no statement, constant or
  threshold of this ticket (the (c) identities are κ-free, the BA instance uses `BAmF_sz0_im_pos`), so per 2254 G2 it is
  harmless here. 1b should correct the row in `(a′)` (κ ≤ 0.044, or "not used").
- **O2.** (i) asks for predicted lines "of each"; only the chosen route has an estimate. The cut is excluded on a
  non-line ground (`BAKsol` is a choice), so the decision is unaffected.
- **O3.** `main` moved to 88d1b63 after the 1a base c33ef56: reverse cone of `Chain.Step2Gen` is now 78 modules (adds
  `BA/Step2BA`, `Graph/BASizeClaim`, `Graph/BASizeClaim2`; `Step2BA` names the changed pins in docstrings only). 1b's G1
  build of the cone must include them.
- **O4.** `STeeUMg` and `bandStep2_STeeUM` are outside the ticket's list but forced by redefining `Step2Gen_uKer` in
  place; same writable file, band statement unchanged through the bridge. I do not see a sign-off need.
- **O5 (paper deltas for 1b's report).** T2414a (`tr` normalisation), T2414b (extends T2405a) are proposed. The BAT-F2 premise
  change of `STK2decaygL'` (`|E| ≤ 2−κ` → `κ ≤ Im m`) and F7's quantification over all four `(s, s')` should also be
  listed (or cross-referenced to the T2405 Amend 1 entry) in 1b's section (d).

## 7. Verdict
Target 1 (a) PASS · 2 PASS · 3 (b) PASS · 4 (c) PASS (`BAUN` identity holds) · 5 (e) PASS · 6 (BAT-F2) PASS ·
7, 8, 9 design PASS. **Stage 1a: PASS.** No binding stop line hit; no dispatcher sign-off requested.
