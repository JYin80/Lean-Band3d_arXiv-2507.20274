Auditor model: claude-opus-5-5

# T2484 1a-audit (design gate D1-D4, probe), Tue Oct 13 03:03 UTC 2026
Inputs: ticket `docs/tickets/T2484.md`; section (a) and (a″) of `docs/reports/T2484-prove.md`; branch `t/T2484` 354ff913 (probe only).
Audit worktree `../RBM3D-wt/T2484-1a-audit1` (detached at 354ff913, build cache cloned with `cp -c`). Scratch: `scratchpad/T2484/audit1a/`.

## 1. Probe compile in the audit worktree
```
$ cd ../RBM3D-wt/T2484-1a-audit1 && lake env lean RBM3D/Probe/T2484Pins.lean      (02:58:05 -> 02:58:16 UTC)
new premises found by the scan: []; with the two band results withheld from the proofs: [RBM.BA.T2484_KerFacts,
 RBM.BA.T2484_CltFlow]
RBM.BA.iniTermGen_kerFacts_band: [propext, Classical.choice, Quot.sound]
RBM.BA.iniTermGen_cltFlow_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_cltFar_of_cltFlow: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_UN_rep: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_zero_bound: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_core2_band: [propext, Classical.choice, Quot.sound]
probe exit code: 0                                                                  (rerun 03:03 UTC)
$ lake env lean docs/tickets/checks/T2484-check.lean   -> exit code: 0, error lines: 0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^import RBM3D.BA|withLam|^(noncomputable )?def' RBM3D/Probe/T2484Pins.lean
33:def T2484_KerFacts ...   54:def T2484_CltFlow ...   283:def T2484_Core2 : Prop :=      (three Prop defs; no kernel def)
$ git diff --stat main...t/T2484
 RBM3D/Probe/T2484Pins.lean | 398 +++++++++++++++++++++++++++++++++++++++++++++
```

## 2. Class texts against the check (script diff of the `def` blocks)
```
== diff check probe T2484_KerFacts (17 / 19 lines)
7a8,9
>       (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool,
>         STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t) ∧
== diff check probe T2484_CltFlow (13 / 13 lines)          (no difference)
```
**E1 (the added conjunct) checked independently.**
- Need: `Step5KerGen_UN_decomp` (Step5KerGen:71) gives slot `i` the pair `(σ i, σ (finRotate k i))`. So slot 1 of a 2-index tensor carries `(σ₁,σ₀)`. `STfFarg` (CltGen:36-46) uses `Step2Kern_Mss C n (σ 0) (σ 1)` in all three places, and `STThPropsg` (CltGen:127) has no charge swap. `probe_UN_rep` uses E1 at line 244 (`hE`), and it compiles. Restating `STfFarg` would violate X1-C4, so a class field is the right place for this fact.
- Not implied by `FlowFM`: `Step2Kern_Mss` (Step2Gen:181) gives `Mss(σ'σ) = Mss(σσ')ᵀ` only. swap.py row 3 (below) gives `7.2e-02` for a non-symmetric `M`.
- Band source: `bandFM_STThg` + `mul_comm` (probe 104-105, compiled).
- BA source: the auditor's scratch `audit1a/e1ba.lean` compiles. It states E1 at every `baFM sz lam0 E` whenever `0 < Im (BAmF sz lam0 E n)`. The proof uses `BAMfine_eq` (GreenSchur:93), `BAMB_symm` (Ward:83) and `Step2Kern_Mss_of_kron` (Step2Gen:238). `Step5CasesGen_FlowFacts` (Step5CasesGen:144) gives `0 < κm ≤ Im m` for every `n`.
```
$ lake env lean scratchpad/T2484/audit1a/e1ba.lean
'audit_E1_baFM' depends on axioms: [propext, Classical.choice, Quot.sound]
exit code: 0
```
**Fixed at this 1a-audit.**
- Target 1 = the probe's `T2484_KerFacts`: the check text plus E1 (19 lines, probe 33-51).
- Target 5 = the check's `T2484_CltFlow` (= probe 54-66).
- Targets 4, 7, 9 keep the check's hypothesis lists. Their binding conclusion heads are unchanged.

## 3. Numerics rerun (the preflight's scripts, copied to `audit1a/py/`; `python3 -I` fails because numpy is in the user site, so `-E` was used)
```
$ python3 -I py/inst.py   (rc=0; output identical to report lines 29-42; key lines:)
zB=(0.5+0.015625j): msc=-0.247983+0.960467j |msc|^2=T0=0.98399229 (>= 31/32=0.96875) E=lemE=0.499984 |E|<=2-kappa:True Im mE(E)=0.968248
 n=0: N=4096 WO 0.1436<=1.0<=10.0:True; N^c=4.000<=W=4:True; N^(-1+eps)=5.61e-04<=Imz=0.0156:True; 1-T0=1.601e-02 vs N^(-1+delta)=3.700e-04: 43.3x
n<=200000 violating WO, Bandwidth, N^(-1+eps)<=Im z, N^(-1+delta)<=1-T0: 0 ; N_n=(4(n+4))^3->inf
regime (i) window (s,t)=(0.895,0.9): ... con_st_ind ... holds iff W_n>=5.194, i.e. n>=2 (eventual hypothesis; Bctl decreasing in W)
$ python3 -E py/kerfacts.py   (rc=0; identical to report lines 44-54; BA rows:)
  BA g=0.01562 g0=0.009616  colsum relerr<=3e-11 C8_needed=   0.98 Cs_needed(c0=1/2)= 1.00 | A=(k+1)/k=2.640=g^2/g0^2:True R1:True ...
  BA g=1 g0=0.5088          colsum relerr<=5e-11 C8_needed=   1.24 Cs_needed(c0=1/2)= 2.49 | A=(k+1)/k=3.862=g^2/g0^2:True R1:True ...
  BA g=10 g0=4.422          colsum relerr<=4e-11 C8_needed= 252.38 Cs_needed(c0=1/2)= 0.20 | A=(k+1)/k=5.113=g^2/g0^2:True R1:True ...
$ (cd py && python3 -E d2.py)   (rc=0; identical to report lines 56-60)
  band mixed g=1 (X=S)  resolvent-identity err=1e-14; C6=max(1-v)||theta_v||_inf=1.000000; max entry |Th_v-Th_w|/(|v-w| C6(1+C6) Tm^2)=0.0016
  crossing g=10 g0=4.422 A=5.113: max tailT^g0/(A tailT^g)=0.4924
$ python3 -E py/swap.py   (rc=0; identical to report lines 62-64)
  M non-symmetric, S=1                         |Th(+-)-Th(-+)|=7.2e-02  |Th(+-)-Th(+-)^T|=7.2e-02
$ python3 -E audit1a/indep.py      (auditor's independent recomputation)
m(zB)=-0.247983+0.960467j |m|^2=T0=0.98399229 31/32<=T0:True selfres=0.0e+00
cltCk(0.1)=0.3122 cltCk(0.05)=0.2222 sqrt(2k)/2=0.2236
N^(1/6)=4.0000 N^(-0.95)=3.700e-04 1-T0=1.601e-02 ratio=43.3
(ii) lam^2/L^3=0.01562<=1-t=0.03125:True; 1-s=0.0625<=lam^2/L^2=0.0625:True
(i) (0.895,0.9): lam^2/L^2=0.0625<=1-t=0.1000:True; 1-s=0.1050<=lam^2:True
```
BA zero-mode and short-range sources, shapes read: `BAProp8` (FlowPins:217) is `‖BATheta0 .. 0 a‖ ≤ C (g²+|1-t|)⁻¹ ((|a|+1)^{d-2})⁻¹`. `BAProp5s` (FlowPins:184) is `‖BATheta σσ 0 a‖ ≤ C(δ_{a0} + g² e^{-c|a|})`. Both are guarded by `0 < g ≤ Λ` and match the field forms at `g = gK = g₀`. The translation to `STThg (baFMz ..)` is owed to U4-BA (a), as the ticket says.

## 4. Size and split
```
$ (cd scratchpad/T2484 && python3 -E audit1a/py/size.py)   (rc=0)
  IniTermIIGen : 0.81*  740 + extras 100 = central    699   upper (2.6x)   1818
  CltFarUGen   : 0.81*  443 + extras 190 = central    549   upper (2.6x)   1427
  IniTermIGen  : 0.81* 1438 + extras  25 = central   1190   upper (2.6x)   3093
  U4s2a = 699 (cap 1950); U4s2b = 1739 (cap 1950); total 2438 (stop if >3900); upper(2.6x) U4s2a 1818, U4s2b 4520
$ python3 -E audit1a/reserve.py decls_IniTermII_IniTermI.json   (auditor: does the reserve rule fit at 2.6x?)
  IniTermIGen without (c)-(d): central 719, 2.6x 1870 (<= 2000: True)
  IniTermIGen2 = (c)-(d): central 421, 2.6x 1095 (<= 2000: True)
```
- Every file whose upper reference exceeds 1,800 has a reserve (X1b-C2): `IniTermIIGen` (1,818) → `IniTermIIGen2`; `IniTermIGen` (3,093) → `IniTermIGen2`.
- With 8 (c)-(d) moved, both halves stay under 2,000 at 2.6×. No file is predicted over the stop line.
- **Split confirmed as pre-signed.** U4s2a = `IniTermIIGen` (targets 1-4 and their part of 10-11; central 699). U4s2b = `CltFarUGen` + `IniTermIGen` (targets 5-9 and their part of 10-11; central 1,739 ≤ 1,950), stacked on `t/T2484b`. The total central is 2,438 < 3,900, so there is **no third row**.

## 5. Name clash (auditor rerun)
```
$ git grep -n -e IniTermGen_ -e iniTermGen_ -e STCltFarUConclgL -e bandFM_STCltFarUConcl -e stIngR5gL_hyps_restrict -e stCltFarUgL_of \
    -e stIniTermIIgL_of -e stIniTermIgL_of -e iniTermIIGen_ -e iniTermIGen_ -e CltFarUGen_ <ref> -- RBM3D | wc -l ; new-module files
main (78f4cc14): hits 0, files 0      t/T2473: 0, 0   t/T2473b: 0, 0   t/T2478b: 0, 0   t/T2480: 0, 0
t/T2480b: 0, 0   t/T2481: 0, 0   t/T2482: 0, 0   t/T2483: 0, 0   t/T2483b: 0, 0
$ lake env lean scratchpad/T2484/op.lean   (open private of the 43 IniTermII names; 43 names counted)  -> exit 0
```

## 6. H250 (4) deliverables table (each row checked against the report and the reruns)
| # | deliverable | report | audit |
|---|---|---|---|
| (i) | exponent table | (a) l.6-23 | met: values reproduced by the §3 reruns |
| (ii) | instance + script; D1 at band and BA, `g = 1/64, 1, 10`, `g₀ < g` | l.24-65 | met (§3 reruns identical; independent recomputation agrees) |
| (iii) | hypothesis table band → field → discharge → BA | l.71 | met; E1's BA source compiled by the auditor (§2) |
| (iv) | D1 decided; probe lines | l.67, (a″) 205 | met: E1 added; band discharge compiled (probe 86-137) |
| (v) | D2 table, closure `t ↦ t'` | l.72, (a″) 206 | met: `probe_cltFar_of_cltFlow` + instance at `t' = 15/16` compile |
| (vi) | D3 decided | l.69, (a″) 207 | met: `B45_ward_fing` (main `Chain/B45Gen.lean:117`) has only the premise `ZeroModeGen_WardCls`, the target 9 premise; no new Ward text |
| (vii) | reader table | l.73, (a″) 208 | met (`:940` compiled as `probe_UN_rep`) |
| (viii) | scope table | l.74 | met |
| (ix) | UBA-C1 as planned | l.75, (a″) 210 | met; see observation 2 |
| (x) | premise scan, registry | (a″) 211 | met: scan `[]`; owner text only at `Test/Axioms:211-212` |
| (xi) | `open private`, copies | l.77, (a″) 212, 215-216 | met: 43 names compile (§5) |
| (xii) | lines per file vs 2,000, 2.6×, split | l.78 | met; reserve fit checked (§4) |
| (xiii) | name clash | l.79, (a″) 152-162 | met (§5 rerun) |

## 7. D1-D4 and the stop lines
- **D1.** PASS with E1. The other fields have band producers (compiled) and named BA sources whose shapes match (§3). No field lacks a BA source.
- **D2.** PASS. `HCltOf` is assembled at every `t' ∈ (s, t]` from the `t`-free class fields, `FlowFacts` and `STReg5I`/`STLocalEntryUgL`/`STGdecayWgL` on `[s, t']`. This is compiled (probe 172-188, 353).
- **D3.** PASS. The route is `ZeroModeGen_WardCls` → `B45_ward_fing`. `Step5CasesGen_WardIdent` does not suffice (reason at l.69).
- **D4.** PASS (§4).

Stop lines (ticket l.97-105), all checked; none hit:
- no file over 2,000 and the reserve rule fits;
- no binding conclusion changed;
- no field without a BA source, and D2 assembles;
- no kernel or propagator def, no `FlowFM` field, no `BA/*` or U4s3/U5/V import, no `STGridRepNgL`;
- no restated merged pin;
- no band or merged file edited (diff = the probe only);
- no `withLam` and no comparison form other than R1;
- no unregistered premise (scan `[]`).

## 8. Paper deltas
`T2484a` (ticket) and `T2484b` (E1 as a carrier datum) are proposed in (a) l.70 and (a″) finding 7. Coverage is complete for the 1a.

## 9. Observations (no RETURN)
1. **Base for 1b.** `t/T2484` is based on 86eb22f2, which does not contain `Chain/B45Gen` (merged in 78f4cc14). U4s2b (`t/T2484b`) needs a base that contains it. `IniTermIGen` then imports `Chain/B45Gen` (allowed by the layout; it imports no `IniTerm*` file).
2. **UBA-C1 table, targets 6-7.** "never" becomes "only the guard (g)" (the per-index R1 lemma), because the Lipschitz step M1 reads the `ThDecay` row sums at `gK`. This is R1 itself, not a second comparison form.
3. **Ticket text corrections.** (a) l.70 gives reader lines and says `IniTermII` §3, §4, §6 are regenerated, not opened. The size model already counts them.
4. **Generic case-(ii) core.** The probe compiles the non-binding shape `T2484_Core2`, an instance of it derived from the band theorem (nonzero tensor, `n = 0`), and the generic ingredients `𝒰 = K ⊗ K` (with E1) and `Θ̊` (with R1). The generic proof of target 2 itself is left to 1b. This is accepted as the probe deliverable.
5. **`STConStInd` in the merged case-(i) window.** At `(7/8, 15/16)`, `STConStInd` holds only for `W_n ≥ 1.147e10`. Any 1b instance that discharges it at concrete `n` should use the interior window `(0.895, 0.9)` (`n ≥ 2`), or keep it as the eventual hypothesis.
6. `python3 -I` cannot import numpy here; the scripts were rerun with `-E`.

## Verdict
**PASS.** Every stage-1a deliverable is met and no binding stop line is hit. The split U4s2a / U4s2b is confirmed, with no third row. Target 1's text is fixed with E1 and target 5's text as checked. No dispatcher sign-off is needed.
