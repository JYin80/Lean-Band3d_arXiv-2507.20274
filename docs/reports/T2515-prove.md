Prover model: claude-sonnet-5-5
## (a) Math preflight — Thu Oct 15 07:32:19 UTC 2026

Scope: stage 1a, mathematics only, no Lean written. `main` HEAD b2326aac (ticket cites a47cf1e1). Symbols: `λ = sz.lam n`, `t₀ = BAt0 z m = Im m/(Im m+Im z)`, `λ₀ = √t₀ λ`, `Q = BAMss(BAMB λ z m)(+,σ) = t₀ Q₀` (`Q₀` at the flow point `(λ₀,E_f,m₀)`), `s = 1-ζ`, `r` = row sum of `Q`, `Θ_s = PropThetaQ Q s`.

### (i) Exponent table (value; constraint; slack) and the ticket's fill-in rows
| # | quantity | value / source | constraint and slack |
|---|---|---|---|
| 1 | `κ'` | `(πκ)^5/2048`, `ba_dom_of_bulk` `RandomLayerBGBA:69` | `Im m(z) ≥ κ'` for `0<Im z≤1`, `BAbulk κ`; instance: `Im m = 0.652` vs `κ' = 9.6e-5` |
| 2 | `cT` | `κ'/(κ'+1)`, `ba_flowG` `RandomLayerBGBA:92` | `cT ≤ t₀ < 1`; instance `t₀ = 0.566` vs `cT = 9.6e-5`; `1-t₀ = Im z/(Im m+Im z) > 0`, no uniform lower bound is used |
| 3 | window | `0<λ≤𝔡⁻¹`; `λ₀ = √t₀ λ ≤ λ ≤ 𝔡⁻¹` | `Λ = 𝔡⁻¹` of `BAProp8` holds at the flow point; `λ₀² = t₀λ² ≥ cTλ²`; `𝔡⁻²λ⁻² ≥ 1` (⇔ `𝔡λ≤1`) |
| 4 | `C₈` | `C₈(d,𝔡⁻¹,κ')` = `∃C` of `baProp8_holds` `Prop6Path:1009` (`BAProp8` `FlowPins:217`, no `W^τ`, no `≺`) | before `L,g,E,m`; depends on `(d,Λ,κ')` only, not on `(sz,z,ζ)`; **lossless** (O9 (a) is on `main`) |
| 5 | flow-point data | `BAdom_real` `MFixedPoint:479`: `BAReal d L λ₀ κ' E_f m₀`, `Im m₀ = Im m/√t₀ ≥ κ'` | `0<λ₀≤Λ`, `3≤L` (`sz.three_le_L`) |
| 6 | time | `t = s t₀ ∈ [0,t₀] ⊂ [0,1)` (`BAt0_lt_one` `MFixedPoint:285`) | `BAProp8` needs `0≤t<1`; `g²+|1-t| ≥ λ₀²` |
| 7 | `C_osc` | `2C₈/cT` | `‖Θ̃(u,v)-Θ̃(0,0)‖ = ‖Θ_s(0,v-u)-Θ_s(0,0)‖ ≤ 2C₈(λ₀²+|1-t|)⁻¹ ≤ 2C₈(cTλ²)⁻¹` |
| 8 | `C_diff` (`thetaDiff`, `ζ=0`) | `2C₈/cT + 𝔡⁻²` | `ΘQ = Θ-1` at `s=1`: `|ΔΘ| ≤ 2C₈/(cTλ²)`, `|δ_ab-δ_ab'| ≤ 1 ≤ 𝔡⁻²λ⁻²` |
| 9 | `C_prof` (`UNOUProfRowk`) | `4C₈/cT + 4𝔡⁻²` | `ζ≤1/2` (`s≥1/2`): `Θ_sQ=(Θ_s-1)/s`, `s⁻¹≤2` gives `4C₈/cT+2𝔡⁻²`; `ζ>1/2` (`s<1/2`): Neumann, entry `≤ t₀/(1-st₀) < 2`, difference `≤ 4 ≤ 4𝔡⁻²λ⁻²` |
| 10 | zero mode | `QJ = JQ = rJ`; `|r| ≤ t₀ < 1` | `(+,-)`: `Q_ab=|M_ab|²`, `r = t₀` (Ward `BAMB_ward_row` `Ward:108`); `(+,+)`: `Q_ab=M_ab²` (`BAMB_symm` `Ward:83`), `|r| ≤ Σ|M_ab|² = t₀`; so `1-r`, `1-sr ≠ 0`; max row abs sum of `Q` = `t₀` |
| 11 | Sherman–Morrison | `Θ̃_ζ = Θ_s + αJ/L^d`, `α = 1/(1-r) - 1/(1-sr)` (twin of `ThetaTilde_eq` `ZeroModeProfile:281`); `SBtilde d L 0 ζ = (1-ζ)1 + (ζ/L^d)J` (`EMn2BA_SB_zero` `EMn2BA:77`) | the constant matrix cancels in row differences; `ζ=0` is trivial (`S̃=1`), so a probe at `ζ=0` does not test it |
| 12 | `β_r` (GUE phase, D1 (iv)) | `β_r(t) = (t-t₁)r/(L^d(1-t₁r)(1-tr))` = `gueShift d L r t₁ t` (`KPrim:61`), `r` = row sum of `Q₀` at the flow point (`|r|≤1`) | `0≤t₁≤t≤t₀<1`: `1-t₁r, 1-tr ≠ 0`, slack `1-t₀`; ODE `β' = L^{-d} r p²`, `p = (1-t₁r)⁻¹+βL^d = (1-tr)⁻¹` |
| 13 | census, rows | row a `KPrim:1-783` + `ZeroModeProfile:220-528`; row b `EntryDet:1-897`, `EntryTail:1-908`, `EntryTailMain:1-602` (instances start at 784 / 898 / 909 / 603) | see census block below; split: **a \| b**, no b \| b′ |

**D1 decisions.** (i) **lossless**: `C = 2C₈/cT`, no `W^{τ'}`, no premise outside the coverage table; the stop rule of D1 (i) does not fire. Route for `T2515_ThetaTransfer`: `BAzztE_data` clause 5 (`MFixedPoint:297`) gives `BAMss(BAMB λ z m) = t₀ • BAMss(BAMB λ₀ E_f m₀)` for real `√t₀`, so `PropThetaQ(Q,s) = BATheta(λ₀,E_f,m₀)(s t₀)` for every real `s`; no `BASelf` premise is needed (`BAm_self` `MFixedPoint:809`, `BASelf_exists` `:691`). (ii) `thetaDiff` at `ζ=0` **deliverable** by row 8 (mathematically; the probe compiles it). (iii) profile text `T2515_ProfSpec` of the check serves `UNOUProfRowk` (N2) and the bridge `t₀K = P` (C5) unchanged; the flow-point form is equal by (i), not needed. (iv) text: `kTwoGUEBA(t₁,t)_{ab} = W^{-d}[(Θ_{t₁}(Q₀)Q₀)_{ab} + r β_r(t)]` for `Q₀ = BAMss(BAMB λ₀ E_f m₀)(σ₁,σ₂)` (= `W^{-d}((Θ_{t₁}+β_rJ)Q₀)_{ab}`), start `K(t₁)` = `baKsolve`'s 2-loop `W^{-d}(Θ_{t₁}Q₀)` (`KSolve:58`), equation (7.33) at `n=2`, `primRhsGUE_two` `KPrim:110` form `W^d(KS_GUEK)_{a₁a₂}`, `S_GUE = L^{-d}J`; bridge `t₀ kTwoGUEBA((1-ζ)t₀, t₀) = (UNOUProfile.ba d).pm / .pp` for `Q = t₀Q₀`. The band text reads a scalar `μ`; BA reads the matrix `Q₀` and the scalar `r`. No profile text conflict, no stop.

**Coverage table as used** (changes against the ticket): row 11 uses `BAMB_ward_row` at complex `z` (`Σ|M_ab|² = t₀`) or `BAMB_row_sq_real` (`=1`) at the flow point, both equivalent; `(+,+)` also needs `BAMB_symm`; row 13 is the Sherman–Morrison of row 11 above (no Neumann for `ζ≤1/2`); everything else as the ticket.

**Row b entry pin `GUEEntryMixBA`** (mathematics; consumer: C5's PathBounds twin through the EntryGrid twin, owner C5): `∀` real-axis flow data `(g_n,E_n,m_n)` with `BAReal d (sz.L n) g_n κ' E_n m_n`, `0<g_n≤𝔡⁻¹` (family premise, guarded by `0<κ'`; no `∃C` inside), grid `(a,b)_{n,k}`, `k≤K_n≤N^{n0}`, `u=a+b<1`, `δ_n≤N^{-c₀}`, `τ,D>0`: eventually `ouP(UNModelC.ba sz).toUNModel n` (= `ouP(UNModel.band(sz.withLam 0)) n`, `ouP_ba_eq_band` `UNPins:467`) of `{∃k,i,j: N^τ(maxLoop^{BA}_{(+,-)} + W^{-d}) < [if ∀x,y llErr^{BA}_{xy} ≤ δ_n then (llErr^{BA}_{ij})² else 0]}` is `≤ N^{-D}`; matrix `mixMatBA(a,b) = g Ψ_I + mixMat(sz.withLam 0)(a,b)` (`ouMatC_ba_eq_band_add` `UNPins:445`; reduces to the OU carrier at `(e^{-t},1-e^{-t})`); `llErr^{BA}_{(a,x),(b,y)} = |G_{(a,x),(b,y)}(z_u^{(E)}) - M^{(B)}_{ab}δ_{xy}|` with `M^{(B)} = BAMB g_n E_n m_n` and `z_u^{(E)} = ztOf m_n E_n u` (`MFixedPoint:297`); band text `GUEEntryMix` `EntryTail:94` reads `mE E`, `zt E u`, `Green.llErrMat` `Green/Pins:73`. Open for the 1a-audit: whether `g` in `mixMatBA` is the flow-point `λ₀` (ticket text) or `sz.lam n`; the proof (`stable_mixBA`) uses only `baOffDiag_holds`, `baPropM_holds` at `(g_n,E_n,m_n)`. `GUEEntryMix` has 0 lines in `Test/Axioms.lean` (grep), so no registry line is expected for the BA pin either.

**Census** (the ticket's script `$HOME/scr_c3/census2.py` does not exist: `ls $HOME/scr_c3` gives "No such file or directory"; reconstructed `T2515/census.py`, per-declaration B/P/M by the C1 regex on the statement/proof text, formula `1.24(0.85B+0.6P+0.05M)`):
```
KPrim 1-783        pure 458 19 246 -> 512 (wide 573) | ticket 469/41/173 -> 536
ZeroModeProfile    pure 285  0  24 -> 302 (wide 302) | ticket 274/0/15   -> 290
EntryDet 1-897     pure 508 102 232 -> 626 (wide 797) | ticket 561/108/98 -> 678
EntryTail 1-908    pure 212 131 512 -> 353 (wide 761) | ticket 249/38/478 -> 320
EntryTailMain 1-602 pure 139 288 126 -> 369 (wide 423) | ticket 244/161/115 -> 384
total census: pure 2,162 | ticket 2,208 (-2.1%); wide 2,957
```
| row | census (recon / ticket) | BA-only + inst + hdr | central (recon / ticket) | ×0.96–1.28 (recon) |
|---|---|---|---|---|
| a `GUEKPrim` | 814 / 826 | 150 + 150 | **1,114 / 1,126** | 1,069–1,426 |
| b `GUEEntry` (+2) | 1,348 / 1,382 | 0 + 300 | **1,648 / 1,682** | 1,582–2,109 |
| total | 2,162 / 2,208 | | **2,762 / 2,808** (T2449: 552/1,102/2,048) | 2,651–3,535 |
Row b: BA-only new is 0 in the ticket, but `stable_mixBA` replaces the scalar `m` of `EntryDet §4-5` by the matrix `M^{(B)}`; it is not priced (risk, not counted). Row a upper end 1,426 < stop line 1,500 < 2,000. Row b centrals exceed the stop line `GUEEntry` 1,300, so `GUEEntry2` is used (the ticket's Layout says "past 1,800", the stop lines say 1,300 + 700; each file ≤ 2,000 binds).
**Split verdict:** total central 2,762 (2,808) > 1,950, so **a | b at `GUEKPrim` | `GUEEntry`** (row a `t/T2515`, row b `t/T2515b`). Row b central 1,648 (1,682) ≤ 1,950 (margin 302–268), so **no b | b′** by the rule as written; the calibrated upper end (2,109 / 2,153) is over 1,950: forecast check at the 1b head.

### (ii) One concrete nondegenerate instance (all hypotheses of targets 1–8 at once)
`d=3, L=4` (64 blocks), `W=2` (enters only as the factor `W^{-d}`), `λ=0.3`, `𝔡=3` (`λ≤1/3`), `E=0.5`, `z=0.5+0.5i`, `ζ∈{0,1/2,1}`, both `σ`. Command: `python3 .../scratchpad/T2515/inst.py` (numpy; solves `(self_m)`, builds `M`, `Q`, `Θ̃`, flow point; asserts the transfer, Sherman–Morrison, bridge and ODE identities). `C₈` here is the empirical `max (λ₀²+|1-t|)|Θ̊_t(0,a)|(|a|+1)^{d-2}` (the Lean constant of `baProp8_holds` is not numerically accessible); the formal `C` is large because `cT = 9.6e-5`, it is a constant, not a witness size.
```
d=3 L=4 (blocks=64) W=2 lam=0.3 frakd=3.0 E=0.5 z=(0.5+0.5j)
rho_N(E)=0.256462 kappa=0.23 (BAbulk: kappa<=rho True); kappa'=(pi kappa)^5/2048=9.617e-05 cT=9.616e-05
Im m(z)=0.651941 >= kappa' True; t0=0.565950 cT<=t0<1 True; check BASelf resid=2.78e-17
Ward max|sum_b|M_ab|^2 - t0|=8.88e-16
flow point: g0=0.225689 (<=lam, <=1/frakd: True), E_f=0.455149, m0=-0.182009+0.866601j; BASelf resid=1.14e-16, Im m0>=kappa' True
conj5 sqrt(t0) M0 = M: 7.02e-16; Ward at E_f: max|sum|M0|^2-1|=1.11e-15
M symmetric: 1.8041124150158794e-16
sigma=+-: r(z)=0.5660, |r|<=t0: True, col sum=0.5660, r0(flow)=1.0000, max row abs sum Q=0.5660
sigma=++: r(z)=-0.3541-0.1357j, |r|<=t0: True, col sum=-0.3541-0.1357j, r0(flow)=-0.6257-0.2398j, max row abs sum Q=0.5660
transfer Theta_s(z)=BATheta(flow point, time s t0) verified for s in {0,1/2,1}, both charge pairs (asserts)
empirical C8 (Prop 8 at flow point, times s*t0, s in 0,1/2,1) = 1.0345
formal C_prof = 4 C8/cT + 4/frakd^2 = 4.303e+04; bound C_prof*lam^-2 = 4.781e+05
  +- zeta=0.0: rowdiff=0.8045 <= proof bound 5.27 <= C_prof lam^-2; bridge err 3e-15; ODE err 0e+00; |1-r0 t1|=0.434
  +- zeta=0.5: rowdiff=0.5713 <= proof bound 7.39 <= C_prof lam^-2; bridge err 2e-15; ODE err 6e-10; |1-r0 t1|=0.717
  +- zeta=1.0: rowdiff=0.4436 <= proof bound 4.00 <= C_prof lam^-2; bridge err 3e-15; ODE err 2e-09; |1-r0 t1|=1.000
  ++ zeta=0.0: rowdiff=0.3196 <= proof bound 5.27 <= C_prof lam^-2; bridge err 1e-15; ODE err 0e+00; |1-r0 t1|=1.361
  ++ zeta=0.5: rowdiff=0.3770 <= proof bound 7.39 <= C_prof lam^-2; bridge err 1e-15; ODE err 7e-10; |1-r0 t1|=1.179
  ++ zeta=1.0: rowdiff=0.4572 <= proof bound 4.00 <= C_prof lam^-2; bridge err 3e-15; ODE err 1e-09; |1-r0 t1|=1.000
thetaDiff +-: max row diff of Theta(z)Q = 0.8045 <= 2C8/(g0^2+1-t0)+1 = 5.266 <= (2C8/cT+1/frakd^2) lam^-2 = 2.39e+05
thetaDiff ++: max row diff of Theta(z)Q = 0.3196 <= 2C8/(g0^2+1-t0)+1 = 5.266 <= (2C8/cT+1/frakd^2) lam^-2 = 2.39e+05
max rowdiff over all cases: 0.8045 ; lam^-2 = 11.111 ; ratio rowdiff/(lam^-2) = 0.0724
  SM +- zeta=0.0: |~Th-(Th_s+alpha J/N)|=0e+00; osc=1.8045 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
  SM +- zeta=0.5: |~Th-(Th_s+alpha J/N)|=4e-15; osc=1.2857 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
  SM +- zeta=1.0: |~Th-(Th_s+alpha J/N)|=6e-15; osc=1.0000 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
  SM ++ zeta=0.0: |~Th-(Th_s+alpha J/N)|=0e+00; osc=0.7060 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
  SM ++ zeta=0.5: |~Th-(Th_s+alpha J/N)|=3e-15; osc=0.8292 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
  SM ++ zeta=1.0: |~Th-(Th_s+alpha J/N)|=7e-15; osc=1.0000 <= 2C8/g0^2=40.62 <= 2C8/(cT lam^2)=2.4e+05
```
(Output verbatim; `SM` = Sherman–Morrison identity `Θ̃_ζ = Θ_s + αJ/L^d`. The ODE check is vacuous at `ζ=0` (`t₁=t₀`) and nondegenerate at `ζ ∈ {1/2,1}`.) **External hypothesis:** none; every input is merged (`baProp8_holds`, `baKsolve`, `BAzztE_data`, `BAMB_ward_row`), so no limit computation applies.
Lean instance at `S0` (`UNPins:884`), `n=0`, `z = E_*+i/2`: `L=4`, `W=(2·1)^5=32`, `λ=(fp 4 _).g0 ∈ (0,3/10]` (`FlowPt.g0_pos/g0_le`), `𝔡=1/10` (`𝔡⁻¹=10≥λ`), `κ_*=Im m₀/π`, bulk by `cls_bulk` (`UNPins:863`); `fp` is `exists_flowPt …`.some, so its numbers are not computable and the script above is the numerical stand-in.

**Greps** (pasted results). C1 regex (`msc|mE|lemT|lemE|Theta d|SB d L|kTwoGUE|KLgen|UNModel.band|2 - κ|‖m‖ = 1`) on Part 2 of `T2515-check.lean` with docstrings stripped: 0 hits (the one docstring hit is `SB d L 0`, i.e. `g = 0`, allowed by the ticket's C1 rule). UBA-C1: `grep -n "Real.sqrt"` on Part 2 gives one line, in `T2515_ThetaTransfer` only; size-level statements read `sz.lam n`. Name clash on `main`, `grep -rn` over `RBM3D RBM3D.lean`: 0 hits for `baOUProfRowk_holds`, `baThetaDiff`, `baProfComp`, `kTwoGUEBA`, `gueK_existsBA`, `stable_mixBA`, `mix_detBA`, `GUEEntryMixBA`, `gueEntryMixBA`, `BA.GUEKPrim`, `BA.GUEEntry`; `UNOUProfile\.ba\b` has 2 hits, both docstrings (`RandomLayerBGBA:28, :125`), no declaration. Import closure (`T2515/closure.py`, transitive over `RBM3D/`) of the planned imports: 203 modules (row a), 102 (row b), 86 (`Prop5Short`, `QUEFromQDiff`); V modules (`BA.MainInd*`, `TwistPins`, `Step6*`) in each: none. Registry `Test/Axioms.lean:171` `UNOUProfRowk` is in the owed list with owner text "BA-C3 at `UNKind.ba`" as the ticket states (checked by `sed`); the ticket names `:170`, `:171` only (comment and move to `structuralProps`).

### Verdicts
- Targets 1–3 (profile, transfer and comparison, zero-mode identity and oscillation): **PASS** (table rows 1–11; instance).
- Target 4 `baOUProfRowk_holds`, target 5 `baProfComp`, target 6 `baThetaDiff` and `UNOUProfile.ba_zero`: **PASS** (rows 7–10, instance; `UNOUProfRowk` constant `4C₈/cT+4𝔡⁻²`).
- Targets 7–8 (`kTwoGUEBA`, bridges, `gueK_existsBA`, instances): **PASS** (row 12, bridge and ODE identities in the instance output).
- Targets 9–13 (row b): **PASS** on hypotheses and sizes; the `GUEEntryMixBA` text above is for the 1a-audit to sign (open point: `g` in `mixMatBA`); `stable_mixBA` is unpriced new BA mathematics (observation).
- Split: **a | b**; no b | b′. Probe compile outcomes (transfer, comparison, oscillation, `thetaDiff`) are not claimed here.

## (a″) Probe compile — Thu Oct 15 08:02:40 UTC 2026

Stage 1a probe step (D1), role `prover-max` (claude-sonnet-5-5). Probe `RBM3D/Probe/T2515Pins.lean`, branch `t/T2515`, commit 45195400, base `main` b2326aac. Section (a) is not edited. Scratch scripts (`textdiff2.py`, `closure2.py`, the line table) are in the scratchpad `T2515/`.

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2515 && { date -u; lake env lean RBM3D/Probe/T2515Pins.lean; echo "exit $?"; date -u; }
Thu Oct 15 07:59:31 UTC 2026
@unOUProfRowk_band : ∀ {d : ℕ}, 3 ≤ d → UNOUProfRowk (UNKind.band d) (UNOUProfile.band d)
@RandomLayerBG_profComp_band : ∀ {d : ℕ}, RBG_ProfComp (UNKind.band d) (UNOUProfile.band d)
Endpoints.thetaDiff : Endpoints.MAThetaDiff
@lemT_mul_kTwoGUE_pm_eq_profPMTilde : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {z : ℂ},
  0 < z.im →
    ∀ {ζ : ℝ},
      0 ≤ ζ →
        ζ ≤ 1 →
          ∀ (a b : Zd d (sz.L n)),
            ↑(lemT z) *
                kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true false a b =
              profPMTilde sz n ζ z a b
'RBM.BA.T2515Probe.probe_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_osc_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_rowk_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.kTwoGUEBA_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_kBridge_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
Thu Oct 15 07:59:40 UTC 2026
```
```
$ wc -l RBM3D/Probe/T2515Pins.lean                                             -> 287
$ grep -cE '\b(sorry|admit|axiom|native_decide)\b' RBM3D/Probe/T2515Pins.lean   -> 0
$ python3 -I closure2.py <the six imports of the probe>                         -> closure size 201 V modules in closure: []
$ grep -rln 'T2515Probe\|T2515Pins' RBM3D RBM3D.lean                           -> RBM3D/Probe/T2515Pins.lean (no importer)
C1 regex (word-bounded; docstrings, comments, #check lines stripped): 0 hits. X1-C4 grep on the six names: 0 hits.
`import RBM3D.BA.(MainInd|TwistPins|Step6)`: 0 hits. Registry and `RBM3D.lean`: untouched.
$ python3 -I textdiff2.py docs/tickets/checks/T2515-check.lean RBM3D/Probe/T2515Pins.lean
IDENTICAL (check Part 2 vs probe, docstrings stripped): T2515_CmpBA T2515_ProfCompBA T2515_ProfSpec T2515_ProfZero T2515_ThetaDiffBA T2515_ThetaTransfer
DIFFERENT: -
in check only: T2515_ProfRowBA T2515_ThetaTildeOscBA | new in probe: T2515_KBridgeBA T2515_KDerivBA T2515_ThetaTildeOscBA_zero
T2515_ThetaTildeOscBA[`0 ≤ ζ → ζ ≤ 1` := `ζ = 0`] == T2515_ThetaTildeOscBA_zero: True
```
Lines per item (script on the committed file; budget = the ticket's "Probe budget"):
```
 22 (budget  40)  transfer  [(29, 33), (37, 53)]
 12 (budget  15)  comparison  [(34, 36), (54, 62)]
 74 (budget  60)  oscillation at zeta=0  [(63, 128), (130, 137)]
 25 (budget  30)  thetaDiff  [(140, 164)]
 27 (budget  25)  profile text, rfl items  [(167, 193)]
 24 (budget  30)  instances + band #check  [(259, 282)]
 16 (budget   -)  zeta=0 slice of target 4  [(194, 209)]
 47 (budget   -)  D1 (iv) text, start, bridge, (7.33) text  [(211, 257)]
listed 247; rest (header, imports, docstring, section headers, blanks, #print axioms) 40; file 287
```

| D1 item | check text | probe declaration (standard axioms) | what is compiled |
|---|---|---|---|
| (i) transfer | `T2515_ThetaTransfer` | `probe_transfer` | all `lam`, `0 < Im z`; no `BASelf`, no `0 < lam` (`BAm_self`, `BAzztE_data` conj. 5) |
| (i) comparison | `T2515_CmpBA` | `probe_cmp` | `cT = κ'/(κ'+1)`, `κ' = (πκ)^5/2048`: the `cT` of `ba_flowG` |
| (i) oscillation | `T2515_ThetaTildeOscBA` | `probe_osc_zero` | text with `ζ = 0` (range only); `C = 2 C₈/cT`, `C₈ = C₈(d, 𝔡⁻¹, κ')` of `baProp8_holds` |
| (ii) `thetaDiff` | `T2515_ThetaDiffBA` | `probe_thetaDiff` | `C = 2 C₈/cT + 𝔡⁻²`; `Θ Q = Θ - 1` at `s = 1` |
| (iii) profile | `T2515_ProfSpec` | `probeProf`, `probe_profSpec` | `rfl` |
| (iii) `RBG_ProfComp` | `T2515_ProfCompBA` | `probe_profComp` | every `P` with `ProfSpec`; `RandomLayerBGBA_comp` takes it (example) |
| (iii) `ζ = 0` is the `BAprof` body | `T2515_ProfZero` | `probe_profZero` | every `P` with `ProfSpec` (`BAprof` of the T2449 probe `:164`, inline, not redefined) |
| target 4, `ζ = 0` | `UNOUProfRowk` (by name) | `probe_rowk_zero` | for the profile frozen at `ζ = 0` (slice, not target 4) |
| (iv) text, start | new `kTwoGUEBA` | `kTwoGUEBA_self` | at `t = t₁`: `W^{-d}(Θ_{t₁} Q₀)_{ab}`, the 2-loop of `BAKsolve` (`KSolve:58`) |
| (iv) bridge | new `T2515_KBridgeBA d Z` | `probe_kBridge_zero` | `Z = {0}` (the 1b's range is `0 ≤ ζ ≤ 1`) |
| (iv) (7.33), n = 2 | new `kTwoGUELoopBA`, `T2515_KDerivBA` | none | text compiles; not proved |
| instances | | 8 `example`s at `d = 3` | `S0` (`UNPins:884`: `L = 4`, `W₀ = 32`, `lam = (fp 4 _).g0 ∈ (0, 3/10]`), `n = 0`, `𝔡 = 1/10`, `κ_* = clsκ 4 _`, `z = E_* + i/2` (`zS0`), bulk by `cls_bulk`; transfer also at `(zS 4 10)` |

Band discharges of the same generic statements, printed by the four `#check` lines above: `unOUProfRowk_band`, `RandomLayerBG_profComp_band`, `thetaDiff`, `lemT_mul_kTwoGUE_pm_eq_profPMTilde`.

**Verdicts for the 1a-audit** (probe facts only):
- D1 (i), at `ζ = 0`: lossless. The proof (`probe_core`) uses `baProp8_holds` at the flow point `(√t₀ λ, E, m/√t₀)` and time `t₀`, with `(g₀² + |1 - t₀|)⁻¹ ≤ (cT λ²)⁻¹`; no `W^τ`, no `≺`. Merged names read: `baProp8_holds`, `BAdom_real`, `BAzztE_data`, `ba_dom_of_bulk`, `BAm_self`, `BAt0_pos`, `BAt0_lt_one`, `BAg0_le`, `baP8_BATheta_shift`, `BATheta_resolvent`, `EMn2BA_SB_zero`; no V name. The D1 (i) stop rule does not fire at `ζ = 0`.
- D1 (ii): delivered, with the statement `T2515_ThetaDiffBA` of the check unchanged (IDENTICAL above).
- D1 (iii)/(iv): one profile text (`T2515_ProfSpec`, IDENTICAL) feeds N2's `UNOUProfRowk` (`probe_rowk_zero`) and C5's bridge `t₀ K = P` (`probe_kBridge_zero`) at `ζ = 0`; the stop rule "no text serves both" does not fire at `ζ = 0`. Choices for the audit to sign: `r = ∑ c, Q₀ 0 c` inside `kTwoGUEBA`; the band scalar `gueShift d L r t₁ t` and `Jmat` reused by name; `T2515_KDerivBA` carries `BAReal d L g κ E m`, `0 ≤ t₁ ≤ t < 1`, `[NeZero W]`.
- Size: 287 lines; budgeted items 184 of the 200; unbudgeted: D1 (iv) 47, `ζ = 0` slice of target 4 16; header, imports, section headers, blanks, `#print axioms` 40. Cap 300 respected.
- Not compiled here (the 1b's): the oscillation and the bridge for `0 ≤ ζ ≤ 1` (Sherman-Morrison for the BA matrix `Q`, the case `ζ > 1/2`), `T2515_ProfRowBA` for all `ζ` (target 4), the proof of `T2515_KDerivBA`, `gueK_existsBA`, row b. The all-`ζ` bridge was checked numerically only, in section (a) (`bridge err` ≤ 3e-15 at `ζ ∈ {0, 1/2, 1}`, both charge pairs).
- Mathlib names used and present (compiled): `div_le_div_iff₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `eq_sub_of_add_eq'`, `one_le_div`, `div_le_div_of_nonneg_right`, `Real.sq_sqrt`, `Complex.norm_natCast`, `Matrix.mul_smul`, `Matrix.smul_apply`, `Matrix.one_apply`, `Exists.imp`.
- Paper-delta candidates from the probe: none beyond the ticket's `T2515a`, `T2515b`.

## (b) Script output, stage 1b row a (prover-max, claude-sonnet-5-5), written Thu Oct 15 09:07:19 UTC 2026

Branch `t/T2515` (worktree `../RBM3D-wt/T2515`), `main` 0deabaa8 merged first (commit 1d782264). Section commits, `git log` and `wc -l` of the file at the commit (stop size 1,500, binding 2,000):
```
02f5d22b 2026-10-15T01:33:50-07:00 lines=595 T2515: GUEKPrim section 1 (profile UNOUProfile.ba, transfer, zero-mode
55b2880d 2026-10-15T01:39:43-07:00 lines=1103 T2515: GUEKPrim section 2 (kTwoGUEBA, (7.33) at n=2, gueK_existsBA, br
037afdfa 2026-10-15T01:52:55-07:00 lines=1232 T2515: GUEKPrim section 3 (instances, root import, registry: UNOUProfR
9641ab61 2026-10-15T01:56:41-07:00 lines=1241 T2515: GUEKPrim final (docstring rewrap, linter options order; full la
ed3c0873 2026-10-15T02:07:00-07:00 lines=1241 T2515: GUEKPrim docstring: count of open private lemmas
```
**Name-level tables (0149 :98).** Merged declarations read by the new file, `file:line` on this branch (script `names_table.py`: identifiers of the final file that are declarations elsewhere in `RBM3D/`; `(p)` = private, read by `open private`; `GP` = `Universality/GUEPhase`, `U` = `Universality`):
```
BA/EKNonzero: EKNonzero_row_sum:60(p) EKNonzero_col_sum:70(p) EKNonzero_Mss_shift:110 EKNonzero_norm_Q_le:149(p) | BA/EMn2BA: EMn2BA_SB_zero:77 | BA/FlowPins: BAKsol:283 | BA/KBase: BATheta_isUnit:324 | BA/KInduct: baKsol_two:88 | BA/KKernel: BAMss_norm_eq_BAK:102 BAK_row_sum:124 | BA/MFixedPoint: BAMB:190 BAt0:279 BAflowE:280
BAt0_pos:282 BAt0_lt_one:285 BAzztE_data:297 BAm:379 BAbulk:429 BAReal:432 BAdom_real:479 BAg0_le:493 BAMsigma:507 BAMss:511 BATheta:515 BATheta0:519 BAm_self:809 zS_im_pos:872 | BA/Prop6Path: baP8_BATheta_shift:497 baProp8_holds:1009 | BA/RandomLayerBGBA: ba_dom_of_bulk:69 RandomLayerBGBA_comp:126 | BA/UNPins: cls_bulk:863 |
Propagator/Pins: PropThetaQ:214 | GP/Bootstrap: SBgue:54 SBgue_apply:56 primBilGUE:173 primRhsGUE:178 finite_loopIdx:430 | GP/KPrim: gueShift:61 primRhsGUE_two:110 kTwoGUE_deriv_identity:131 KPrim_ode_global:388(p) KPrim_two_le_length_cutGlueL:450(p) KPrim_two_le_length_cutGlueR:456(p) KPrim_length_cutGlueL_le:462(p)
KPrim_length_cutGlueR_le:468(p) KPrim_primRhsGUE_congr:481(p) KPrim_primRhsGUE_len_one:499(p) KPrim_eq_two:506(p) | GP/RandomLayerBG: RBG_Comp:115 RBG_ProfComp:123 | U/OUInterfaceK: UNOUProfile:43 UNOUProfRowk:56 UNG1Rowk:101 UNG2bRowk:109 ouRowk_of_pins:292 | U/PinsK: UNOURowk:426 | U/ZeroModeProfile: Jmat:62 SBtilde:65
ZeroModeProfile_Jmat_mul_Jmat:242(p) ZeroModeProfile_ringInverse_eq_of_mul_eq_one:251(p) | instances: UNPins fp:770 clsκ:855 clsκ_pos:858 S0:884; MFixedPoint zS:868 zS_im_pos:872 P:893
```
Coverage rows as used: the ticket's table, rows 4-14 (row 8 = `baProp8_holds`, row 14 through `baKsol_two`); the import `BA/KInduct` is added to the ticket's list (already in the closure: 203 modules with and without it); no V name; row 15 is row b's.

```
$ lake build RBM3D.BA.GUEKPrim 2>&1 | tail -1                  # 09:07:00-09:07:02 UTC at the last commit ed3c0873, file of 1,241 lines
Build completed successfully (3929 jobs).
$ lake build 2>&1 | tail -2   # whole library incl. `#assert_rbm_axioms`: 09:05:24-09:06:50 UTC (same file content), exit 0, 0 lines `^error`
non-vacuity certificates: 0 of 121 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4419 jobs).
registry: 2 borrowed + 119 owed + 142 structural + 7 refuted + 19 superseded
$ #print axioms (script ax2.lean) of the 20 new public declarations
exit 0; lines exactly [propext, Classical.choice, Quot.sound]: 20; other lines: 0; sorryAx: 0
RBM.Univ.UNOUProfile.ba RBM.Univ.UNOUProfile.ba_spec RBM.BA.baThetaTransfer RBM.BA.baT0Cmp RBM.BA.baThetaTilde_eq RBM.BA.baThetaTilde_osc RBM.BA.baThetaDiff RBM.BA.baOUProfRowk_holds RBM.BA.baProfComp RBM.Univ.UNOUProfile.ba_zero RBM.BA.kTwoGUEBA RBM.BA.kTwoGUELoopBA RBM.BA.kTwoGUEBA_self RBM.BA.kTwoGUEBA_eq_ThetaTilde RBM.BA.hasDerivAt_kTwoGUELoopBA RBM.BA.gueK_existsBA RBM.BA.kTwoGUEBA_bridge RBM.BA.kTwoGUEBA_bridge_pm RBM.BA.kTwoGUEBA_bridge_pp RBM.BA.GUEKPrimInst.zS0
```
**Target statements** (script `extract.py 420 <names>` on the committed file: comments stripped, whitespace collapsed, signature up to `:=`):
```
def UNOUProfile.ba (d : ℕ) : UNOUProfile (UNKind.ba d)
theorem UNOUProfile.ba_spec (d : ℕ) : ∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)), (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false; (UNOUProfile.ba d).pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧ (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true
    true; (UNOUProfile.ba d).pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)
theorem baThetaTransfer : ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ), 0 < z.im → ∀ (s : ℝ) (σ₁ σ₂ : Bool), let m := BAm d L lam z; let t0 := BAt0 z m; PropThetaQ (BAMss d L (BAMB d L lam z m) σ₁ σ₂) s = BATheta d L (Real.sqrt t0 * lam) (BAflowE z m) (m / (Real.sqrt t0 : ℂ)) (s * t0) σ₁ σ₂
theorem baT0Cmp : ∀ κ : ℝ, 0 < κ → ∃ cT : ℝ, 0 < cT ∧ ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ), BAbulk d L lam κ z.re → 0 < z.im → z.im ≤ 1 → cT ≤ BAt0 z (BAm d L lam z)
theorem baThetaTilde_eq {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t0 : ℝ} (ht0 : 0 ≤ t0) (ht1 : t0 < 1) {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (σ₁ σ₂ : Bool) : Ring.inverse (1 - ((t0 : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * SBtilde d L 0 ζ) = BATheta d L g E m ((1 - ζ) * t0) σ₁ σ₂ + gueShift d L (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) ((1 - ζ) * t0) t0 • Jmat d L
theorem baThetaTilde_osc : ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d L lam κ z.re → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → ∀ (σ : Bool) (u v : Zd d L), let Q := BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ; ‖Ring.inverse (1 - Q * SBtilde d L 0 ζ) u v - Ring.inverse (1 - Q * SBtilde d L 0 ζ) 0 0‖ ≤ C * (lam
    ^ 2)⁻¹
theorem baThetaDiff : ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → ∀ (σ : Bool) (a b b' : Zd d (sz.L n)), let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ; ‖(PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d - (PropThetaQ Q 1 * Q) a
    b' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d
theorem baOUProfRowk_holds : ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (UNKind.ba d) (UNOUProfile.ba d)
theorem baProfComp (d : ℕ) : RBG_ProfComp (UNKind.ba d) (UNOUProfile.ba d)
theorem RBM.Univ.UNOUProfile.ba_zero (d : ℕ) : ∀ P : UNOUProfile (UNKind.ba d), (∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)), (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false; P.pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧ (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L
    n) (sz.lam n) z)) true true; P.pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)) → ∀ (sz : Sizes d) (n : ℕ) (z : ℂ) (σ : Bool) (a b : Zd d (sz.L n)), (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ; (if σ then P.pp sz n 0 z a b else P.pm sz n 0 z a b) = (PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)
def kTwoGUEBA (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) : ℂ
def kTwoGUELoopBA (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 t : ℝ) (I : LoopIdx (Zd d L)) : ℂ
theorem kTwoGUEBA_self (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) : kTwoGUEBA d L W g E m t1 t1 σ₁ σ₂ a b = ((W : ℂ) ^ d)⁻¹ * (BATheta d L g E m t1 σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b
theorem kTwoGUEBA_eq_ThetaTilde (d L W : ℕ) [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t0 ζ : ℝ} (ht0 : 0 ≤ t0) (ht1 : t0 < 1) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (σ₁ σ₂ : Bool) (a b : Zd d L) : kTwoGUEBA d L W g E m ((1 - ζ) * t0) t0 σ₁ σ₂ a b = ((W : ℂ) ^ d)⁻¹ * (Ring.inverse (1 - ((t0 : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * SBtilde d L 0 ζ) * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b
theorem hasDerivAt_kTwoGUELoopBA (d : ℕ) : ∀ (L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t1 t : ℝ, 0 ≤ t1 → t1 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L), HasDerivAt (fun s => kTwoGUELoopBA d L W g E m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩) (primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t
theorem gueK_existsBA (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (hL : 3 ≤ L) {g κ E : ℝ} {m : ℂ} (hg : 0 < g) (hκ : 0 < κ) (hr : BAReal d L g κ E m) {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n0 : ℕ) : ∃ Kt : ℝ → LoopIdx (Zd d L) → ℂ, (∀ I, Kt t1 I = BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1 I) ∧ (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length → I.length ≤ n0
    → HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Set.Icc t1 t0) t) ∧ (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L, Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA d L W g E m t1 t σ₁ σ₂ a b)
theorem kTwoGUEBA_bridge (d : ℕ) : ∀ P : UNOUProfile (UNKind.ba d), (∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)), (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false; P.pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧ (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n)
    z)) true true; P.pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)) → ∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ), (0 ≤ ζ ∧ ζ ≤ 1) → ∀ (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n), let m := BAm d (sz.L n) (sz.lam n) z; let t0 := BAt0 z m; (t0 : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt t0 * sz.lam n) (BAflowE z m) (m / (Real.sqrt t0 : ℂ)) ((1 - ζ) * t0) t0 true false a b =
    P.pm sz n ζ z a b ∧ (t0 : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt t0 * sz.lam n) (BAflowE z m) (m / (Real.sqrt t0 : ℂ)) ((1 - ζ) * t0) t0 true true a b = P.pp sz n ζ z a b
theorem kTwoGUEBA_bridge_pm {d : ℕ} (sz : Sizes d) (n : ℕ) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {z : ℂ} (hz : 0 < z.im) (a b : Zd d (sz.L n)) : (BAt0 z (BAm d (sz.L n) (sz.lam n) z) : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) * sz.lam n) (BAflowE z (BAm d (sz.L n) (sz.lam n) z)) (BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) : ℂ)) ((1 - ζ) *
    BAt0 z (BAm d (sz.L n) (sz.lam n) z)) (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) true false a b = (UNOUProfile.ba d).pm sz n ζ z a b
theorem kTwoGUEBA_bridge_pp {d : ℕ} (sz : Sizes d) (n : ℕ) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {z : ℂ} (hz : 0 < z.im) (a b : Zd d (sz.L n)) : (BAt0 z (BAm d (sz.L n) (sz.lam n) z) : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) * sz.lam n) (BAflowE z (BAm d (sz.L n) (sz.lam n) z)) (BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) : ℂ)) ((1 - ζ) *
    BAt0 z (BAm d (sz.L n) (sz.lam n) z)) (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) true true a b = (UNOUProfile.ba d).pp sz n ζ z a b
```
**Statement diff and Lean check against the signed texts.** `textdiff3.py` compares check Part 2 / probe def bodies with the committed statements (`T2515_ProfSpec d P` expanded, `Z ζ := 0 ≤ ζ ∧ ζ ≤ 1`); `scratch_check.lean` (uncommitted, scratchpad) holds check Part 2 plus probe `T2515_KBridgeBA`, `T2515_KDerivBA` verbatim and 10 `example : T2515_X := …` (the general-`P` forms `T2515_ProfCompBA`, `T2515_ProfRowBA` through `P = UNOUProfile.ba d`):
```
T2515_ThetaTransfer:IDENTICAL T2515_CmpBA:IDENTICAL T2515_ThetaTildeOscBA:IDENTICAL T2515_ThetaDiffBA:IDENTICAL T2515_ProfSpec:IDENTICAL T2515_ProfZero:IDENTICAL T2515_KBridgeBA:IDENTICAL T2515_KDerivBA:IDENTICAL
$ lake env lean scratch_check.lean -> exit 0, 0 output lines; negative control `example : T2515_CmpBA := baThetaTransfer` -> `Type mismatch`
```
**Compiled nonempty instances** (namespace `RBM.BA.GUEKPrimInst`, lines 1120-1241; `d = 3`, `S0 = clsS 4 (3/10)`, `n = 0`, `z = E_* + i/2`, `κ_* = clsκ`, `𝔡 = 1/10`, `ζ ∈ {0,1/2,1}`; flow data `MFixedPointInst.P`, `fp 4 _`), by `exheads.py` and two of them verbatim (`UNG1Rowk`, `UNG2bRowk` stay hypotheses of the `ouRowk_of_pins` example only, other gates' pins):
```
examples: 23
UNOUProfile.ba_specx1 baThetaTransferx2 baT0Cmpx1 baThetaTilde_eqx3 baThetaTilde_oscx1 baThetaDiffx1 baOUProfRowk_holdsx1 ouRowk_of_pinsx1 RandomLayerBGBA_compx2 baProfCompx1 UNOUProfile.ba_zerox1 kTwoGUEBA_selfx1 kTwoGUEBA_eq_ThetaTildex1 hasDerivAt_kTwoGUELoopBAx2 kTwoGUEBA_bridge_pmx1 kTwoGUEBA_bridge_ppx1 kTwoGUEBA_bridgex1 gueK_existsBAx1
example := (baOUProfRowk_holds 3 le_rfl (1 / 10) (clsκ 4 hg) (by norm_num) (clsκ_pos 4 hg)).imp fun C h =>
  And.intro h.1 fun a b b' =>
    And.intro (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 0 le_rfl zero_le_one a b b')
    (And.intro (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) (1 / 2) (by norm_num) (by norm_num) a b b')
     (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 1 zero_le_one le_rfl a b b'))
example := gueK_existsBA 3 4 32 (by norm_num) (g := (fp 4 hg).g0) (κ := ((fp 4 hg).m0).im) (E := (fp 4 hg).E)
  (m := (fp 4 hg).m0) (fp 4 hg).g0_pos fp_im_pos (fp 4 hg).real (t1 := 1 / 4) (t0 := 1 / 2) (by norm_num)
  (by norm_num) (by norm_num) 4
```
**Greps, name clash, diff** (`greps.py`: public statements = non-private declarations, comments stripped):
```
public declarations scanned: 20
C1 regex hits on public statements: 0 []
X1-C4 definitions of UNOUProfRowk|RBG_ProfComp|BAProp8|BAprof|GUEEntryMix|SBtilde: 0
imports of BA.MainInd*|TwistPins|Step6*: 0
forbidden tokens sorry|admit|axiom|native_decide: 0
public statements containing Real.sqrt (flow point only): ['baThetaTransfer', 'kTwoGUEBA_bridge', 'kTwoGUEBA_bridge_pm', 'kTwoGUEBA_bridge_pp']
clash grep of the 19 new public names other than UNOUProfile.ba, and of GUEKPrimInst, in RBM3D, RBM3D.lean (excluding the new file, the probe, Test/Axioms.lean): 0 hits; UNOUProfile.ba: 2 docstring hits (RandomLayerBGBA:28,125)
$ git diff --name-only main...HEAD | paste -sd' ' -; git diff --shortstat main...HEAD
RBM3D.lean RBM3D/BA/GUEKPrim.lean RBM3D/Probe/T2515Pins.lean RBM3D/Test/Axioms.lean
 4 files changed, 1531 insertions(+), 2 deletions(-)
registry entries, main 0deabaa8 -> {'owedProps': 120, 'structuralProps': 141} -> branch {'owedProps': 119, 'structuralProps': 142}
```
Registry edits (`Test/Axioms.lean`, three edits found by content): `UNOUProfRowk` moved from `owedProps` to `structuralProps` with both instances named (DECISIONS §337 (4)); `UNG1Rowk` owner comment adds C3 (`baProfComp`); no new `owedProps` line. Ports: from RBM3D band files at main 0deabaa8 (`KPrim`, `ZeroModeProfile`), so no RBM1D/RBM2D diff-stat applies (no file of `../RBM1D`, `../RBM2D` was read in this stage).

**Narrative.**
1. Scope: row a only. One new file (1,241 lines; census central 1,114, stop line 1,500, binding 2,000: no stop rule fired), the root import line, the registry hunks. The probe stays on the branch; row b is not touched. No V module or name is read; no unproved `Prop` premise enters a target.
2. D1 as signed: (i) lossless at every `ζ ∈ [0,1]` (`baThetaTilde_osc`: `C = 2C₈/cT` from `baProp8_holds d 𝔡⁻¹ κ'` at the flow point, no `W^τ`, no `≺`); (ii) delivered (`baThetaDiff`); (iii) one profile text, `UNOUProfile.ba` with spec by `rfl`; (iv) `kTwoGUEBA` as signed, bridge for all `ζ ∈ [0,1]` (`kTwoGUEBA_bridge`).
3. Route. `Q = M^{(+,σ)}(z) = t₀ Q₀` (`GUEKPrim_Mss_flow`); `Q₀` is translation invariant with constant row and column sums `r₀`, `|r₀| ≤ 1`, `‖Q₀‖_{∞→∞} ≤ 1`. Sherman-Morrison (`GUEKPrim_SM`: the algebra of `ThetaTilde_eq` with `ξ S^{(B)}` replaced by `Q`) gives `Θ̃_ζ = Θ_{(1-ζ)t₀} + β J`, `β = gueShift d L r₀ ((1-ζ)t₀) t₀` (`baThetaTilde_eq`). The `J` part is constant, so the oscillation of `Θ̃_ζ` is that of `Θ_s` (`GUEKPrim_osc_core`, any `s ∈ [0,1]`) and the row differences of `Θ̃_ζ Q` are those of `Θ_s Q` (`GUEKPrim_rowdiff`, `C = 4C₈/cT + 4𝔡⁻²`): `s ≥ 1/2` through `s Θ_s Q = Θ_s - 1`, `s < 1/2` through `‖Θ_s‖ ≤ (1 - s t₀)⁻¹ ≤ 2` and `‖Q‖_{∞→∞} ≤ t₀`.
4. GUE phase. `hasDerivAt_kTwoGUELoopBA`: the abstract `GUEKPrim_deriv_abs` (row and column sums of `Θ_{t₁}Q₀` are `r₀(1 - t₁r₀)⁻¹`) re-uses the merged scalar identity `kTwoGUE_deriv_identity`. `gueK_existsBA`: `GUEKPrim_exists_upto` is the induction of `KPrim_exists_upto` (`KPrim.lean:570-743` copied, `KLgen (mSigma E) t₁ ↦ K0`, `kTwoGUELoop ↦ K2`; the ODE lemmas by `open private`), start `K0 = BAKsol … t₁`, level 2 by `baKsol_two`.
5. Differences from section (a): `baThetaDiff` has `C = 4C₈/cT + 4𝔡⁻²` (one lemma for all `s`), not `2C₈/cT + 𝔡⁻²` (the statement is `∃ C`); `GUEKPrim_flow` takes `κ = Im m` (the structure lemmas need no bulk); registry lines found by content (`UNG1Rowk` `:169`, `UNOUProfRowk` `:170`; audit observation 1).
6. Length: sections (a) and (a″) are 171 lines, so the ticket's 250-line cap is exceeded; CLAUDE.md §6's 300 holds (`wc -l` of this file, last line below).

## (c) Mathlib names used (all compiled in this file; none verified absent)
`Units.oneSub`, `Units.val_oneSub`, `Matrix.linfty_opNNNorm_def`, `Matrix.linfty_opNormOneClass` (`norm_one`), `norm_mul_le`, `Finset.single_le_sum`, `Finset.le_sup`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`, `eq_sub_of_add_eq'`, `sub_eq_iff_eq_add`, `Matrix.smul_mul`, `Matrix.mul_smul`, `Matrix.mul_apply`, `Matrix.smul_apply`, `Complex.ofReal_mul`, `Complex.norm_real`, `norm_smul`, `HasDerivAt.div`, `HasDerivAt.comp_ofReal`, `HasDerivAt.const_mul`, `HasDerivAt.const_add`, `HasDerivAt.congr_deriv`, `hasDerivWithinAt_const`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_add_distrib`, `Nat.le_induction`, `inv_mul_cancel₀`, `div_le_div_iff₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `one_le_div`, `div_le_div_of_nonneg_right`, `le_div_iff₀`, `div_le_iff₀`, `Real.sq_sqrt`, `Complex.norm_natCast`.

## (d) Open issues and paper-delta candidates
- `T2515a`: the BA OU profile `W^{-d} (Θ̃_ζ M^{(+,σ)})_{ab}`, `S̃_ζ = SBtilde d L 0 ζ = (1-ζ) 1 + (ζ/L^d) J` (`SB d L 0 = 1`), is the band `profPMTilde` with `ξ S^{(B)}` replaced by `M^{(+,σ)} S̃_ζ`; `grep -n zeta paper/tex/*.tex` (12 hits) finds no zero-mode profile (hits: the notations `ξ = O(ζ)`, `ξ ≺ ζ` of `1_2:218-237`, the graph quantity `ζ(α,β)` of `B:425-514`); `\wt S` of `1_2:108-110` is the doubly stochastic matrix of the mollified variance.
- `T2515b`: the BA `thetaDiff` is lossless: `1_2:535-537` (proof of Theorem `MR:QUE`) states `max |Θ^{(σ,σ')}_{ab} - Θ^{(σ,σ')}_{ab'}| ≺ ilambda⁻²`, with `≺` (an arbitrary `W^τ` loss, defined at `1_2:227-230`); Lean `baThetaDiff`, `baOUProfRowk_holds`: `≤ C λ⁻²`, `C = C(d,𝔡,κ)`, from `baProp8_holds` at the flow point.
- `T2515c`: the BA GUE-phase 2-loop is matrix-valued, `W^{-d}((Θ_{t₁}(Q₀) + β_r J) Q₀)_{ab}`, `r` the row sum of `Q₀ = M^{(σ₁σ₂)}` at the flow point, `β_r = gueShift d L r t₁ t` (the band text has a scalar `μ`); `gueK_existsBA` needs `0 < g`, `0 < κ`, `3 ≤ L` (from `baKsol_two`).
- Open: none for row a. Row b (`BA/GUEEntry`) is a separate branch and report.
$ wc -l docs/reports/T2515-prove.md -> 288 (this line included; CLAUDE.md §6 cap 300, ticket cap 250)
