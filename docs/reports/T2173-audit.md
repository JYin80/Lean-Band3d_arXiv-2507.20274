Auditor model: claude-opus-5-5
# T2173 audit (round 1) — BA-D2, block Anderson form of Claim (417); report-only design ticket
Written Mon Oct  5 06:39:26 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2173-audit1` (detached at `a543154` = `t/T2173`). Sources: `t/T2162` @ `73b451c`, `t/T2161` @ `82e72b3`.
**Verdict: PASS, needs dispatcher sign-off** on two design decisions the report proposes (section 6). No defect in statement, instance, build, axioms or paper-delta coverage.

## 1. Build, axioms, hygiene, diff scope
```
$ git diff --name-only main...t/T2173
RBM3D/Probe/T2173Pins.lean
$ lake build RBM3D.Probe.T2173Pins   (audit worktree)
ℹ [3329/3329] Built RBM3D.Probe.T2173Pins (10s)
Build completed successfully (3329 jobs).            (exit=0; no `error:`/`warning:` line for RBM3D/Probe)
$ lake env lean RBM3D/Probe/T2173Pins.lean; grep -vc "depends on axioms"; axiom sets
exit=0
0                                                    (only #print axioms lines in the output)
 149 [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" T2173Pins.lean   -> (no hits)
$ grep -c "#print axioms" ; grep -cE "^(theorem|lemma|example|private theorem|private lemma)"
149
149
```
Sole writable files: the probe (branch only) plus the two reports in the main worktree; the diff touches only the probe. No merged file is edited.

## 2. Verbatim copies and declared amendments (auditor script `declcmp.py`: each declaration, whitespace-normalised, against the same name in the source probe)
```
t62.lean common names 88 identical 83 differ 5
  DIFF UNModel probe:119 src:103
  DIFF UNModel.band probe:135 src:115
  DIFF UNModel.ba probe:146 src:124
  DIFF ouMat probe:179 src:149
  DIFF ouMat_isHermitian probe:191 src:153
t61.lean common names 112 identical 111 differ 1
  DIFF FlowFM.GM probe:1963 src:850
probe names 326 new names 126
```
The five T2162 differences are exactly amendment A1 (field `mean`/`mean_herm`, centred `ouMat`), declared in the report (top notice 1, b.3). `FlowFM.GM` differs only by making the section variables explicit (body `C.G n t ω x y - C.M n x y` identical). `UNClaim417`, `UNClaimAll`, `UNApriori`, `UNGreenCorr`, `UNCore`'s consumers etc. are identical to T2162.

## 3. Target 1 (interface): each new pin against the T2162 pin it modifies
Auditor script `subst.py`: apply to the T2162 text only the substitutions the report declares (`UNModel.band sz ↦ K.M sz`, `|E| ≤ 2 - κ ↦ K.bulk sz κ E n`, profile coupling of `L1t/L2t/scirc` `sz.lam n ↦ K.lamV sz n`), then compare:
```
UNOUQUE       T2162:636  -> UNOUQUEk      :2275 after declared substitutions identical: True
UNOUDiag      T2162:647  -> UNOUDiagk     :2284 after declared substitutions identical: True
UNEMCTE2      T2162:668  -> UNEMCTE2k     :2296 after declared substitutions identical: True
UNJak         T2162:693  -> UNJakk        :2316 after declared substitutions identical: True
UNUyw         T2162:707  -> UNUywk        :2329 after declared substitutions identical: True
UNQueBand     T2162:403  -> UNQuek        :2378  differs only: seqP sz ↦ (K d).M.μ, seqXmat ↦ (K d).M.H, |E|≤2-κ ↦ (K d).bulk
UNLocAvgBand  T2162:415  -> UNLocAvgk     :2390  differs only: law/matrix as above, locDomain ↦ bulk ∧ N^{-1+ε}≤Im z≤1, msc ↦ (K d).mdet
UNCore        T2162:759  -> UNCoreC       :2570  token diff: + UNTrLocalInit sz M m E δ →
UNStep1Good   T2162:583  -> UNStep1GoodC  :2553  token diff: UNTrLocal ↦ UNTrLocalInit, vOU ↦ vOUC
```
At `K = band` the k-pins are T2162's (`UNOUQUEk_band`, …, `UNOURowk_band`: `Iff.rfl`, compiled). BA data checked against merged/T2161 vocabulary:
- `UNKind.ba`: `M = UNModel.ba` (law `seqP (sz.withLam 0)`, `H = seqHBA` = `λΨ + seqXmat (sz.withLam 0)`, merged `Gauss/BlockAnderson.lean:96-99`), `lamV = 0`, `bulk = BAbulk` (ρ-bulk, DECISIONS §51), `mdet = BAm`. With `svarF d L W g = W^{-d} SBR d L g` (`Gauss/FineModel.lean:47`) and `SBR · 0` diagonal (`SBR_zero_ne`, probe `:3047`), `scirc … 0 = S^V − 1/N`, the variance of `V` (`1_2:606`): correct for the centred generator.
- QUE: `UNQueBA` uses `queBadMat … (sz.lam n)` = T2161 `BAqueBad` (window `W^{-ε₀} λ W^{d/2}/N`, threshold `W^{d-c}/N`), with the law `seqP (sz.withLam 0)`; `UNQueBA_of_BAEnd_QUEL` compiles.
- `(G_bound_ave)`: `W^{-d}Bparam(λ,1−η,0) = W^{-d}(λ²+η)^{-1} + (Nη)^{-1}` (`Defs/Params.lean:36-37`, `Sizes.lean:214`) equals T2161 `BAcalB n η 0`; only the `Prec` vs explicit `W^τ` form differs (bridge = BA-M1, disclosed, report (d)3).
- Target theorem `un_claimAll_of_rowsBA` (`:2496`): fixed parameters `d, 𝔠, 𝔡, sz, κ, E` before `∀ᶠ n`; premises `3 ≤ d`, `Admissible`, `0 < κ`, `E` eventually in `{ρ_N ≥ κ}`; conclusion `UNClaimAll sz (UNModel.ba sz) E`, the input of `UNCore/UNCoreC`. It is the generic `un_claimAll_of_rowsk` at `K = ba`; the proof is T2162's gluing. **PASS.**

## 4. Target 2 (drift)
- `ouMat` (`:179`) = `μ + e^{-t/2}(H−μ) + √(1−e^{-t}) H'`; `ouMatNC` (`:187`) is T2162's matrix. Compiled: `ouMat_eq_ouMatNC_add`, `ouMatNC_sub_ouMat`, `drift_entry` (derivative `−½e^{-t/2} μ_ij`), `ouMat_band` (A1 is the identity for `mean = 0`), `ouMat_ba_eq_band_add` (BA flow − λΨ = band flow of `sz.withLam 0`, same `ouP`).
- Independent exact check (auditor, `Φ = Tr H²`, `S^V` and GUE row sums 1): non-centred `𝔼ΦH_t = e^{-t}λ²TrΨ² + N`, so `d/dt = −e^{-t}λ²TrΨ²`; drift term `−½e^{-t/2}𝔼 dΦ[λΨ] = −e^{-t/2}·e^{-t/2}λ²TrΨ²` (equal); second-order term `−½e^{-t}Σ(S_ab−1/N)·2 = 0`. Centred: `𝔼Φ = λ²TrΨ² + N`, drift 0. Agrees with the report's Wick table (b.5).
- Decision (centred flow = paper's `(MBM)`, `1_2:686`) with the size of the alternative's error (`drift_not_absorbable`, N-independent naive bound 0.745 / 16.8) and the Step-1 shift `λ̂ = λe^{t*/2}` (`ouMat_ba_eq_ouMatNC`, `admissible_lamHat` at `(𝔠, 𝔡/2)`). RBM2D source cited (`OUGenerator.lean:940`, `EMCTE2.lean:440,493` at `c9a24cf`). **PASS.**

## 5. Targets 3–6
- 3 (GUE phase): per-file classes T/P/G for 27 files (portmap P.2), model-generic preference stated; **PASS** (design content; each UN-25..52 preflight re-checks, report (d)5).
- 4 (exponents): `c' = 𝔠𝔡/30`, `τ_U ≤ c'/(2(C_max+1))`, window, threshold, `ℙ(𝓑)` one block, drift size and κ-dependence (D403) at d = 3, two `(𝔠,𝔡)`, `L ∈ {4,5}`, `λ ∈ {0.3,10}` (section (a)); compiled arithmetic `inst_que_exponent_ba`, `inst_cprime_ba`, `inst_claim_exponent_ba`, `inst_window_sub_ba`. **PASS.**
- 5 (split): BA total `57 + 5 − 0 = 62 (61..66)` and the band-only alternative `75 (71..82) > 70` are on line 2 of the prove report, as required. **PASS** (sign-off item, section 6).
- 6 (instances) — see section 7. **PASS.**

## 6. Dispatcher sign-off items (not defects of this ticket)
1. **A1 amends merged signatures**: `UNModel` (main `RBM3D/Universality/Pins.lean:104`) gets fields `mean`, `mean_herm`; `ouMat` (`:150`) becomes centred; `OU.lean` needs 3 changed lines (report b.1a). CLAUDE.md §5.3 prefers a primed successor; the report gives the non-amending alternative (flow/init in `UNKind`, `UNClaim417`… copies) in (d)2. The dispatcher must choose before UN-01b is written.
2. **BA cap (§52)**: 62 ≤ 70 only if UN-25..52 are written model-generic; otherwise 75 > 70 and Jun must be asked.

## 7. Compiled nonempty instances (every endpoint/new pin) and extreme inputs
Data: `S0 = clsS 4 _ (3/10)` (`L = 4`, `W_n = (2(n+1))^5`, constant `g₀ = (fp 4 _).g0 ∈ (0, 3/10]`), `S0_adm` at `(1/6, 1/10)`, `κ_* = clsκ > 0`, `E_* = (fp 4 _).E` with `cls_bulk`; `sz0` with `flow_sz0`. All named theorems compile on the 3 standard axioms (section 1). Checked bodies:
- `inst_claimAll_ba` (`:3620`): `un_claimAll_of_rowsBA … 3 le_rfl (1/6) (1/10) S0 S0_adm κ_* (clsκ_pos …) E_* (S0_bulk huniq)` — every deterministic premise discharged.
- `inst_univ_ba` (`:3631`): `UNCoreC` at `UNModel.ba S0`, `m = BAm`, `ρ = BArho(E_*)`, `E' = 0`, `k = 1`, `O = bump` (`bump_nondegenerate`: values 1 and 0).
- `inst_UNOUQUEk/UNOUDiagk/UNEMCTE2k/UNJakk/UNUywk/UNQueBA/UNLocAvgBA/UNMLOutBA/UNStep1GoodC`, `inWindow_nonempty`, `inst_locAvg_domain` (domain nonempty at every `n`), `inst_ba_mean_ne_zero` (mean has a nonzero entry: drift is real).
- Kept hypotheses: the rows and consumed inputs (owed pins of UN/BA gates), `UNCoreC`, `UNL32` (authorized LSY input, §5), `UNGUELocal`, `UNGreenCorrAll`, and T2161's deterministic pins `BAmUniqReal 3`, `BAmExists 3` (other gates' pins, not yet proved; allowed by CLAUDE.md §4 step 2). No `N = 0`, empty index, collapsed window or `False` premise.
Auditor's own extreme-input check (`AuditCheck.lean` importing the probe, compiled in the audit worktree):
```
example (sz) (h : ∀ n, sz.lam n = 0) … :
  (UNEMCTE2k (UNKind.ba d) sz E 2 τU Cn ↔ UNEMCTE2k (UNKind.band d) (sz.withLam 0) E 2 τU Cn) ∧
  (UNJakk (UNKind.ba d) sz E 2 τU C c' ↔ UNJakk (UNKind.band d) (sz.withLam 0) E 2 τU C c') ∧
  (∀ n t ω, ouMat (UNModel.ba sz) n t ω = ouMat (UNModel.band (sz.withLam 0)) n t ω)
example … : ouMat (UNModel.band sz) n t ω = e^{-t/2} • H + √(1-e^{-t}) • Xmat …   (T2162 matrix)
$ lake env lean AuditCheck.lean > ac.out; echo exit=$?; grep -c error ac.out
exit=0
0
'RBM.Univ.un_claimAll_of_rowsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_claimAll_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_univ_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
```
At `λ = 0` the BA OU pins reduce to the band pins of `sz.withLam 0` (variance profile `S^{(B)}(0)`), and `BASelf_msc` gives `msc` as a solution of `(self_m)`; the reduction `BAm = msc` itself needs uniqueness and is listed as not compiled (report (d)6).

## 8. Hidden hypotheses, vacuity, cycles
- `UNModel` fields: law, probability, matrix, hermiticity, measurability, `mean`, `mean_herm` — data and structural facts only, no analytic hypothesis. `UNKind` is data (model, coupling, bulk set, `m`). No row is a field of a structure.
- No cycle: the rows consume `UNMLOutBA` (BA-V3), `UNLocAvgBA` (BA-M1), `UNQueBA` (BA-M3), none of which mentions `UNClaimAll`; `UNCoreC` consumes `UNClaimAll` and produces `UNUnivDilAt`.
- External input: only `UNL32` (LSY Thm 2.2, DECISIONS §5), unchanged from T2162; its limit check is in T2162 (a)(ii) and the BA regularity data `c ≤ Im m ≤ C` are printed in (a)(ii).

## 9. Paper-delta coverage
Lean/paper differences and their candidates: law of the BA pins `seqP (sz.withLam 0)` (T2173a, witness `seqGvar_ne_withLam_zero`); `BAGlueUniv` lacks QUE/flow outputs (T2173b); BA proof runs on the centred flow `(MBM)` where the paper says "as in the band case", `7_8:1835` (T2173c; covers A1, `UNCoreC`'s `UNTrLocalInit`, `UNStep1GoodC`); density regularity beyond `lem:propM` (T2173d); one-block `M_{y,α}` (T2173e); ρ-bulk form (DECISIONS §51, existing). `grep -c T2173 docs/paper-deltas.md` = 0: none appended yet (dispatcher numbers them). Coverage complete.

## 10. Observations (no effect on verdict)
- O1: `λ = 0` lies outside `Admissible` (`(eq:WO)` lower bound `λ ≥ W^{-3/2+𝔡}`), so the extreme check is at the level of the pin formulas, as above.
- O2: `UNLocAvgBA` ↔ `BAEnd_locSC` bridge (same threshold, `Prec` vs explicit `W^τ`, `∃z` inside the probability) is not compiled; it is assigned to BA-M1 in the split.
- O3: the generator identity with drift is numerical in the report (b.5) and exact above for `Tr H²`; its Lean proof is UN-15/UN-01b.

## Verdict
| target | verdict |
|---|---|
| 1 Interface (`un_claimAll_of_rowsBA`, BA rows, k-pins) | PASS |
| 2 Drift (centred flow, `drift_entry`, sizes) | PASS |
| 3 GUE phase classification | PASS |
| 4 Exponent table | PASS |
| 5 Split table, BA total on top | PASS (sign-off item 6.2) |
| 6 Instances at d = 3, non-vacuity | PASS |
Overall: **PASS — needs dispatcher sign-off** (section 6: A1 amendment of merged `UNModel`/`ouMat`; model-generic UN-25..52 for BA total ≤ 70).
