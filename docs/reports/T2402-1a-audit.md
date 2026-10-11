Auditor model: claude-opus-5-5

# T2402 1a-audit (BA-G5c design gate) — Sun Oct 11 03:36:46 UTC 2026
Inputs: ticket `docs/tickets/T2402.md`; `docs/reports/T2402-prove.md` sections (a), (a′), (a″); branch `t/T2402` = `4b5f864`;
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2402-1a-audit` (detached at `4b5f864`). Scratch: `scratchpad/T2402/`.
G3a (T2390) merged: `git merge-base --is-ancestor cbda0ab 1181514` -> true. **Verdict: PASS (stage-1a deliverables), needs dispatcher sign-off before 1b (F2, D3).**

## 1. Diff, probe compile, forbidden tokens
```
$ git diff --stat main...t/T2402
 RBM3D/Probe/T2402Pins.lean | 592 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 592 insertions(+)                                # = the 1a sole writable Lean file
$ lake build RBM3D.Green.IBP RBM3D.BA.GreenSchur RBM3D.BA.GreenLDE RBM3D.BA.GreenCore | tail -2
✔ [3778/3778] Built RBM3D.BA.GreenCore (14s)
Build completed successfully (3778 jobs).
$ lake env lean RBM3D/Probe/T2402Pins.lean > probe.out 2>&1; echo "exit code: $?"      # 03:21:18 -> 03:21:26 UTC
exit code: 0
$ grep -c . probe.out; grep -nE "error|warning|sorry" probe.out
36                                                                 # the 20 #check lines only; no error/warning line
$ grep -nE "sorry|admit|axiom|native_decide|^theorem|^lemma" RBM3D/Probe/T2402Pins.lean; echo $?
1
$ sed -n 1,214p RBM3D/Probe/T2402Pins.lean | grep -nE "lam n ≤|\.lam .*≤|‖M - |\(C.*λ\)\^|c_λ"
198:the premises ... No `∃ c`, no `g ≤ W^{-ε}`, no smallness of `‖M - m₀ I‖`.   # docstring only: no C1-forbidden hypothesis in any pin
```

## 2. Numerics reproduced (scripts copied from `docs/reports/T2402/`, run in scratch)
```
$ python3 consts5c.py | diff - consts5c.out && echo IDENTICAL      -> IDENTICAL-consts
$ python3 inst5c.py   | diff - inst5c.out   && echo IDENTICAL      -> IDENTICAL-inst
$ python3 ibpcost.py .../RBM3D/Green/IBP.lean | diff - ibpcost.out -> IDENTICAL-ibpcost
$ python3 fit.py ravg_d1.out ravg_d3.out | diff - fit.out          -> IDENTICAL-fit
$ python3 disp.py 2 20 100000 777 4 10 0.5 | diff - disp_szP.out    -> IDENTICAL-disp_szP   (21.5 s wall)
$ cmp stab.py docs/reports/T2390/stab.py                           -> (no output: byte-identical)
$ python3 ravg.py 10 3 3 W ns   (nsamp of the original not recorded; independent rerun)
ns=400 W=2: RMS|R_uu|/W^-d = 0.303  RMS|<R>_a|/W^-d = 0.102   (report: 0.303 / 0.105)
ns=50  W=3: RMS|R_uu|/W^-d = 0.562  RMS|<R>_a|/W^-d = 0.101   (report: 0.565 / 0.100)
ns=50  W=4: RMS|R_uu|/W^-d = 0.857  RMS|<R>_a|/W^-d = 0.110   (report: 0.855 / 0.111)
```
consts5c (row g = 10, verbatim excerpt): `kappa=0.04  Im m=0.0439>=kappa True  t0=0.0439 g0=2.0955<=Lam True |m0|=0.2095 ... 2/kappa=50.0
rho_off=446.9983  sum|M|^2 off=0.956090 vs 1-|m0|^2=0.956090` — N1, N2, N3, N4, N5 of the table match.

**Independent check of F1** (the pointwise claim rests on `R_uu`, N7; the display needs `E_u R_uu`). Audit script `scratchpad/T2402/scripts/euR.py`
(model of `rem.py`: d = 3, L = 3, t = 0.9 t0, row u resampled by Schur complement, 20000 draws, 8 rests; `R_uu` formula checked against
`-Σ_{v≠u} M_uv (YG)_vu` from the full inverse):
```
g=1  W=2 N=216   residual 1.4e-15  RMS|R_uu|/W^-d/2 = 0.070  RMS|E_u R_uu|/W^-d/2 = 0.063  RMS|E_u R_uu|/W^-d = 0.179
g=1  W=3 N=729   residual 1.5e-15  RMS|R_uu|/W^-d/2 = 0.065  RMS|E_u R_uu|/W^-d/2 = 0.049  RMS|E_u R_uu|/W^-d = 0.257
g=1  W=4 N=1728  residual 7.8e-16  RMS|R_uu|/W^-d/2 = 0.066  RMS|E_u R_uu|/W^-d/2 = 0.059  RMS|E_u R_uu|/W^-d = 0.468
g=10 W=2 N=216   residual 4.4e-14  RMS|R_uu|/W^-d/2 = 0.099  RMS|E_u R_uu|/W^-d/2 = 0.086  RMS|E_u R_uu|/W^-d = 0.243
g=10 W=3 N=729   residual 7.6e-14  RMS|R_uu|/W^-d/2 = 0.070  RMS|E_u R_uu|/W^-d/2 = 0.062  RMS|E_u R_uu|/W^-d = 0.324
g=10 W=4 N=1728  residual 1.4e-13  RMS|R_uu|/W^-d/2 = 0.107  RMS|E_u R_uu|/W^-d/2 = 0.095  RMS|E_u R_uu|/W^-d = 0.762
```
`E_u R_uu` scales as `W^{-d/2}` (first order), not `W^{-d}`: F1 and paper-delta candidate T2402b are supported.

## 3. Merged facts cited in (a): file:line on main `1181514` (name within ±3 lines; script output)
```
BA/GreenSchur.lean:219 BAGt_sub_BAMfine 1 | :93 BAMfine_eq 1 | :173 BAMfine_row_l1 1 | :293 green_diag_split 1 | :335 green_off_split 1
BA/GreenSchur.lean:265 BAPsiI_inBlock 1 | :196 BAflowPert 2 | BA/Ward.lean:89 BAMB_diag_eq 1 | :108 BAMB_ward_row 1 | :136 BAm_norm_le_one 1
BA/GreenCore.lean:755 GreenCore_E0 1 | :84 GreenCore_E1 1 | :651 GreenCore_Arow_eq 1 | :1130 GreenCore_Xi 1 | :1066 GreenCore_Xstar 1
BA/GreenCore.lean:400 GreenCore_m1 1 | :1684 GreenCoreInst 1 | :1348-1354 GreenCore_R0/Xb/Ab (defs at 1348,1350,1352)
Green/IBP.lean:92 green_sub_smul_one_eq 1 | :122 hasDerivAt_Hflow_update 2 | :142 hasDerivAt_green_Hflow_update 2 | :271 zt_im_ne_zero_of_lt_one 2
Green/IBP.lean:279 tame_green_apply 2 | :315 hasDerivAt_green_apply_update 2 | :344 tame_green_mul_mul_green_apply 2 | :368 integral_coord_mul 1
Green/IBP.lean:675 sum_gvar_Bmat_sandwich_diag 2 | :686 ..._mul 2 | :722 tame_const_mul_green_apply 2 | :736 tame_const_mul_sandwich_apply 2
Green/IBP.lean:755 integral_coord_mul 2 | :884 condRow_coord_mul 2 | :953 hasDerivAt_const_mul_green_apply_update 2 | :1000 condRow_coord_mul_Bmat_mul_green_diag 2
Green/IBP.lean:1043 condRow_Hflow_mul_green_diag 1 | :1165 tame_Hflow_mul_green_apply 2 | :1205 IBP_sum_svarF_row 1 | :1227 condExpDiag_eq_sum_Sblk 1
Green/IBP.lean:1331 ibpRem 2 | :1344 ibpRem_eq_add 1 | Green/IBPPoly.lean:309 gaussIBP 1 | Green/FlucVanish.lean:309 finDepOffRow_of_minor 1
Green/CondDom.lean:496 perTimeDomAt_condRow_of_envelope 1 | :697 "1/2" 2 | Green/LocalLaw.lean:186 IBPDetThm 2 | Green/IBPRem.lean:126 IBPRem_hΨlow_of_floor 1
BA/GreenLDE.lean:46 BAGt_eq_green 1 | :55 ba_G_data 1 | BA/GreenStab.lean:46 baStab_of_real 1 | BA/Step1Boot.lean:79 BAGiiGEX 1
BA/CouplingWindow.lean:849 szP 1 | Defs/Sizes.lean:260 sz0 1 | BA/FlowPins.lean:1214 flow_sz0 1 | :1254 half_lt_t0 1
```
Every cited merged fact is at its line.

## 4. Deliverables (ticket "Stage 1a, design gate")
**(i) Display — met.** Checked against the signatures: `GreenCore_E0`/`BAGt_sub_BAMfine` give `Δ = −MYG`; with `M = M^B⊗I`, `M_uu = m`
(`BAMfine_eq`+`BAMB_diag_eq`), entry `(u,u)` is `Δ_uu = −m(YG)_uu + R_uu`, `R_uu = −Σ_{v≠u} M_uv (YG)_vu` (pin `GreenIBP_delta_eq_pin`,
probe `:81`; numerical residual 2.5e-16, `inst5c.out`). Row-u Stein: `E_u[−m(YG)_uu] = t m Σ_k S_uk E_u[G_uu(G_kk − m)]` uses only
`Σ_k S_uk = 1` and `∂G = −G B G` (independent of the deterministic `D`); it is the band `condExpDiag_eq_sum_Sblk` (`IBP:1227`, at `D = 0`,
`z = zt E t`, `m = mE E`) with `D` Hermitian and `Im z ≠ 0` free (pin `:93`). Splitting with `ibpRem` gives
`E_uΔ_uu = t m² v̄_[u] + t m Σ_k S_uk ibpRem(u,k) + E_u R_uu` (uses `M_kk = m`, `S_uk = W^{-d}1_{[k]=[u]}`). Monte-Carlo N10 reproduced
(`disp_szP.out` identical; max |z| 1.44). Off-diagonal analogue written (non-scalar `M_uy` kept), not pinned (no consumer): acceptable.
Band-term classification D2 (12 class-G twins, reused statements, `R` as the new term) checked against §3 lines.
**(ii) Remainder — met.** `k ∈ [u]∖u`: `M_ku = 0` (`GreenIBP_cross_offset_pin`, from `BAMfine_eq`), so `|G_ku| = |Δ_ku|`;
`G_kk − G^{(u)}_kk = G_ku G_uk / G_uu`, `|G_uu| ≥ |m| − δ ≥ κ/2` on `Ω_δ` (pin `:120`, constant `2/κ`, N3); `G^{(u)}_kk` is `E_u`-invariant;
`k = u` carries `S_uu = W^{-d} ≤ Ψ²`. Hence `‖E_u[−m(YG)_uu] − t m² v̄_[u]‖ ≺ Ψ²` (`rem.out`: `RMS|KE|/W^{-d}` decreasing in W, reproduced
via the identical `consts5c`/`inst5c` and the fit). The new term `R` is bounded at first order only (`GreenIBP_R_eq_pin`, `_R_bound_pin`);
its `Ψ²` average `⟨R⟩_a` is the two-block fluctuation averaging that supervisor 2254 G1 assigns to G5a (`ravg` slope −d reproduced).
So (i)/(ii) close within G5c's scope; the stop line "(i) or (ii) cannot be closed" is not hit.
**(iii) Interface — met, with a dispatcher question.** Provided: `BAIBPDet d` (probe `:201`): `∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow → ∀ t (0 ≤ t ≤ T₀)
→ ∀ ε₀ > 0 → ∀ Ψ δ ≥ 0, ∀ᶠ W^{-d/2} ≤ Ψ, ∀ᶠ Ψ ≤ W^{-ε₀}, ∀ᶠ δ ≤ κ/2 → hΩ → hll → (‖E_u[−m(YG)_uu] − t m² v̄_[u]‖ ≺ Ψ²)`; fixed parameters
before `∀ᶠ n`, no `∃`. Compared with the band `IBPDetThm` (`LocalLaw:186`): same shape (local law premise → display bound), conclusion
restricted to the row-u part (F1). **F2** (T2401's G.5–G.6 route consumes no G5c row) is reported, not resolved: dispatcher decision.
**(iv) C1 / G2 — met.** Constants at g = 1/64, 1, 10 with κ uniform in L (0.5/0.25/0.04 ≤ Im m 0.8325/0.3435/0.0439) and g₀ ≤ Λ = 10
(`consts5c.out` identical). §1 grep: no `g ≤ W^{-ε}`, no `‖M − m₀I‖` smallness, no `(Cλ)^{|a−b|}` in any pin.
**(v) Pins, files, split — met.** All 10 pins compile (§1) as `Prop`s/`def`; File 1 `BA/GreenIBP.lean` 560/760/1210, File 2
`BA/GreenIBPRem.lean` 730/1020/1600: central total 1780 > 1500 so the split is made; **every file < 2000 at hi (binding stop line not hit)**.
Layout (C5): twin vs in place `574×0.97 − 574×0.24 = 557 − 138 = +419` (ibpcost identical): the "≈100 lines" condition fails and the 1a
explains why: allowed by the ticket ("or explains why not"); choosing between them is for the dispatcher.

## 5. Probe instances (nonvacuity of the pins)
| pin | example | deterministic hypotheses discharged at |
|---|---|---|
| condRow_Hflow_mul_G_diag, delta_eq, display, ibpRem_eq_add | `:280`, `:287`, `:302`, `:308` | `sz0.withLam 0`, n = 0 (L = 4, W = 32), t = 1/2, `D = g₀Ψ` Hermitian, `Im z_t > 0`, `M = BAMfine`, `M_ii = m`, `3 ≤ L` |
| cross_offset | `:315` | k = e₀ ≠ u = 0 in one block; conclusion `M_ku = 0` produced |
| minor_replace | `:336` | `Fin 2`, G = [[1,1/2],[1/2,1]], κ = 1, `G_ku G_uk ≠ 0` |
| R_eq | `:343` | sz0, n = 0, t = 1/2, every ω (`GreenCore_carrier`) |
| R_bound | `:403` | merged `GreenCoreInst` data (n = 3, t₁ = 1e-11, ω = 0, G ≠ M) |
| BAIBPDet / baIBPDet_holds | `:352` / `:374` | sz0, flow_sz0, t ≡ 1/2 ≤ T₀, ε₀ = 1/10, Ψ = δ = W⁻¹; `hΩ`, `hll` (G6a output) kept |
None uses N = 0, an empty index, a collapsed window or a `False` premise. The `hll` scale is attained numerically (`‖Δ‖_max W^{d/2}` ∈ [0.89, 1.17],
d = 3, g = 1, 10; `fit.out` identical): limit check present.

## 6. Paper deltas
Proposed: T2402a (non-scalar `R`), T2402b (pin is the row-u part; pointwise `Ψ²` for `E_uΔ_uu` false — §2 supports it), T2402c (`2/κ` for `2`).
No Lean/paper difference of the pins is left uncovered at the 1a level (the paper has no BA display; T2378 GE3).

## 7. Observations (no RETURN)
- O1. N7/F1 evidence in (a) measures `R_uu`, not `E_u R_uu`; the audit run in §2 closes this. 1b report may cite `E_u R_uu` directly.
- O2. `hΩ` (`‖G_t − M‖_max ≤ δ` w.h.p.) is a premise of `BAIBPDet` absent from the band `IBPDetThm`; it appears derivable from `hll`
  with `δ_n = N^τ Ψ_n ≤ κ/2` eventually. Not a hidden hypothesis (it is in the signature); 1b may drop it or list it as a delta.
- O3. `ravg.py` outputs do not record `nsamp`; the rerun matches to sampling error. N11 quotes the `hll` scale for g = 1, 10 only
  (`fit.out` at g = 1/64: [3.05, 4.39], small-W regime). The Lean instances are all at sz0 (λ ≤ 1/64); C1 constants are checked at g = 1, 10 numerically.
- O4. Estimate: 1290/1780/2810 vs ticket 946/1531/2294 (central +16%); not a stop line (per-file 2000 holds).

## 8. Verdict
**PASS** for the stage-1a design gate: (i)–(v) answered with file:line for every merged fact, numerics reproduced, no C1-forbidden step,
pins compile in the probe, no binding stop line hit.
**Needs dispatcher sign-off before stage 1b:** F2 (no consumer of G5c on T2401's `BAGbEXPav` route: drop 1b, File 1 only, or both) and D3
(new-file layout costs +419 central lines, not ≈100, against one certificate-lane merge in place).
