Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 13:25:43 UTC 2026

Scope: mathematics only (no Lean written). Ticket items (iii)-(viii) and the X1-C5 measurements (`g`, `f_sem`) need compiled generic text, so they belong to the `prover-max` probe step and the 1a-audit, not to this section.

### (i) Exponent table (`N = (W L)^d`, `ℓ_u = ellT L lam u`, `G = log W`, `w = G³ ℓ_s`)

| # | quantity | value / source | constraint | slack |
|---|---|---|---|---|
| 1 | spectral margin `κ` | generic `κ ≤ (C.m n).im`; band passes `cltCk(κ/2)` (`CltStep:783`); BA: `Im m ≥ (πκ)^5/2048` (`T2449-design.md` §1.4, `BAFlow`) | `0 < κ ≤ m.im` (replaces `|E| ≤ 2-κ`) | band `0.2222 ≤ 0.9682`; the generic reading covers T2449's margin, no stop rule |
| 2 | E4 `T2455_CltEtaLowerOf` | `N^{-1+δ} ≤ 1-u` ⇒ `κ/N ≤ (ztOf m E u).im = (1-u) m.im` (`ztOf_im`, `GLoopFlow:64`) | only `N ≥ 1`, `δ ≥ 0` (`N^{-1} ≤ N^{-1+δ} ≤ 1-u`) and `κ ≤ m.im`; no `‖m‖ = 1`, no `E` | `1.2e-44 ≤ 3.8e-15` at `u = tCL`; `N = 0` corner: goal `0 ≤ (1-u) m.im`, true (band `cltEta_lower` `:610`) |
| 3 | M5 base `2N³/κ` | `‖F.eval‖ ≤ (K+1) N^{C'} (2N³/κ)^K` | the step `1 ≤ 2N²η⁻¹`, `η = κ/N` (`cltres_eval_le` `hΘ`, `CltResolvent:649-652, :707`) needs `κ ≤ 2N³`; band uses `cltCk κ ≤ 1` (`:600`). **Generic premise needed: `κ ≤ 1` (or `κ ≤ 2N³`)**; E4 alone does not give it | BA: `κ ≤ Im m ≤ ‖m‖ ≤ 1` (`EMn2BA:98-103`, `BAm_norm_le_one`); instance `6.2e130 ≥ 1` |
| 4 | `‖C.M n x y‖ ≤ 1` (input (d)) | `norm_mE` (`CltGood:433`), BA `BAMB_ward_row` | E2: entries `≤ ‖G-M‖ + ‖M‖ ≤ 1 + 1 = 2`, `a = min(2𝔠𝔡, ε/2)` (`CltGood:420`), `q = N^{a/2} ≥ 2` | band `a = 1/30` at `(𝔠,𝔡,ε) = (1/6,1/10,1/10)`; eventual |
| 5 | isolation window / separation | `w = G³ℓ_s`, pair spread `≤ w`, separation `10w` (`T2455_STCltIsoConclgL`) | `10 w ≤ ⌊L/2⌋` for non-vacuity | `46,037 ≤ 7,962,624` (`ℓ_0 = 1`) |
| 6 | CltStep geometry | `θ = max(3w-2, w)`, radius `ρ = w+1`, `R = 8w` (`CltStep` `hθR`) | `θ ≤ R/2-ρ-1 = 3w-2` | **0** (equality, `w ≥ 1`); no room to change `8w`, `ρ` |
| 7 | CltStep exponents | `a = C'+3K+2`, `D'' = a(2p+2)+D+4`, `D' = D''/𝔠` | absorb `A ≤ N` into `N^{x+1} ≤ N^a`: `C'+3K+1 ≤ a` | slack 1; `(K,C',p,D) = (2,2,1,1)`: `a=10`, `D''=45`, `D'=270` at `𝔠 = 1/6` |
| 8 | CltStep size thresholds | `C1 = 2(K+1)(2/κ)^K`, `C2 = 4(K+1)2^K K 4^K`, `4p+16`, `W^{1/2} ≥ 16` | `≤ N`, `W ≥ 256` | `486 / 1536 / 20` (band `κ = cltCk(0.05)`); `W^{1/2} = 4096` |
| 9 | isolation closing | `2N² · N^{-D-3} ≤ N^{-D} ≤ W^{-D}` (`cltStep_exponent`, `CltStep:1277`) | `N ≥ 2`, `W ≤ N` | factor `N/2` |
| 10 | flow facts (f) | `N^{-1+ε} ≤ 1-t n`, `t n < 1`, `κ ≤ Im m`, `Admissible 𝔠 𝔡` | `W ≥ N^𝔠`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` | band: `N^{-0.9} = 1.1e-39 ≤ Im z = 2.0e-15 ≤ 1` |
| 11 | FarEntry `KfargL` | `‖C.K‖ ≤ W^{-D}` beyond `δ G^{3/2} ℓ_u`, `δ = 1`, `D = 2D'` (`farEntry_neighbour`) | `c G³ - 2 ≥ G^{3/2}` and `exp(-√(cG³-2)) ≤ W^{-K1}`: exponent `3/2 > 1`; `X0 = max(1,(K1²+4K1+10)/c)`, `K1 = (max(Cd,0)+2)/𝔠+2D'` | `K1 = 20`, `X0 = 490` vs `G(n=0) = 16.6`: conclusion is eventual from `n* = 683` (`W = 2^707`); hypotheses hold at `n = 0` |
| 12 | far-set non-vacuity | `c G³ ℓ_τ ≤ ⌊L/2⌋` (FarEntry), `G^{3/2} ℓ_u ≤ ⌊L/2⌋` (KfargL) | else conclusion vacuous | `τ = sCL = 0`: `4604`, `67.9 ≤ 7.96e6`. `τ = tCL`: `ℓ = L`, `7.3e10 > ⌊L/2⌋`: **vacuous**, so instances of `stFarEntryAtLoggL` use `τ = 0` |
| 13 | `f^{far}` region (`STfFarg`) | `G⁵ℓ_s ≤ ℓ_t`; cap `½G^{3/2}ℓ_t + G^{5/2}ℓ_s`; sum from `G⁴ℓ_s` | region nonempty | `1.27e6 ≤ 1.59e7`; cap `5.4e8 > ⌊L/2⌋` (non-binding at `tCL`); `G⁴ℓ_s = 76,585 < ⌊L/2⌋` |
| 14 | `GijDecgL` windows | `Φ ≤ W^{-ε₀}`, `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` | window nonempty iff `ε₀ ≤ d/2` | `ε₀ = 1/10`: `1.5e-11 ≤ 0.19` |
| 15 | pin scale `𝗕_b` | `(lam² W^d)^{6/5}`, `STAI^{-6/5}` | `lam² W^d ≥ W^{2𝔡}` (`lam_sq_mul_pow_ge`, `Sizes:193`) | `WO` at `n=0`: `W^{-1.4} = 7.7e-11 ≤ 1 ≤ 10` |
| 16 | coupling `g₀` (record) | `baFMz sz z = baFM sz (BAflowLam0 sz z) (BAflowEs sz z)` (`FlowPins:393`); `T2455_*` read `sz.lam` only in `ellT`, `STAI`, `STcltBg` | the BA instance keeps `sz.lam = g`; `g₀ = √t₀ g` enters only the matrix (`H₀ = g₀Ψ`, `CltRepg`) and the law is `seqP (sz.withLam 0)` | `Admissible`/`WO` is then asked of `g`, not of `g₀` |

Findings: (F1) row 3 adds the premise `κ ≤ 1` to M5 (not to E4). (F2) At BA, `C.K = W^{-d}(BATheta · BAMss)_{a₁a₂}` (`BAKsolve`, `BA/KSolve:57-71`), while T2452's D4 `BAKellStarEv` has the content of `KellStarEv`, bounds on `Theta` and `ukerMat` (`T2452-prove.md:5`, `KellStar:54-70`); the BA producer of `T2455_KfargL` therefore also needs decay of `BAMss` (input (e): `baPropM_holds`, `baOffDiag_holds`), not only D4. No statement here changes. (F3) The slack-0 row 6 and the vacuity of row 12 at `tCL` are properties of the merged proofs/instances, recorded for the probe.

### (ii) One concrete nondegenerate instance

Band witness `szCL`, `n = 0` (`Step5Pins:642-754`: `d = 3`, `L = 2·24⁵`, `W = 2^24`, `lam = 1`; `flow_zCL`: `κ = ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`; `s = sCL = 0`, `t = tCL = 1 - L⁻²`, `z = zCL = 1/2 + i/(2L²)`), spectral value `m = mE(lemE z)`; part B: a non-semicircle `m = 0.3+0.6i` (`‖m‖ = 0.67`), `d=3, L=3, W=4`, `κ = 1/2`, `δ = 1/10`, to show E4/M5 need no `‖m‖ = 1`. External hypotheses: none read from other tickets (Step 2 pins stay hypotheses of the carrier statements). Limit computations: `n*=683` (row 11), `N→∞` is `SizeTendsto` of `szCL` (`szCL_tendsto`).

```
$ cd <scratchpad>/T2455 && python3 inst.py
L=15925248 W=16777216 log10 N=43.2804 logW=16.6355
Bandwidth N^c <= W                                         OK  1.635e+7 16777216
WO W^(-d/2+dd) <= lam <= 1/dd                              OK  7.681e-11
locDomain |Re z|<=2-kap                                    OK  0.5
locDomain N^(-1+eps) <= Im z <= 1                          OK  1.116e-39 1.972e-15
t=tCL <= lemT(z), t<1                                      OK  1.907e-15 3.943e-15
0 <= s=0 <= t                                              OK 
|lemE| <= 2-kap/2 (band CltStep:1)                         OK  0.5
|m|=1 (norm_mE)                                            OK 
kappa' = cltCk(kap/2) <= Im m                              OK  0.2222 0.9682
kappa' <= 1  (M5 step Theta>=1)                            OK  0.2222
E4 hyp N^(-1+eps/2) <= 1-u, u=s=0                          OK  7.649e-42 1.0
E4 concl kappa'/N <= Im ztOf, u=s=0                        OK  1.165e-44 0.9682
E4 hyp N^(-1+eps/2) <= 1-u, u=t=tCL                        OK  7.649e-42 3.943e-15
E4 concl kappa'/N <= Im ztOf, u=t=tCL                      OK  1.165e-44 3.818e-15
M5 base 2N^3/kappa' >= 1: 6.24498e+130
ell_0=1, ell_t=L (to 1e-30)                                OK  1.0 1.593e+7
isolation: w <= 10w <= floor(L/2) (set nonempty)           OK  4.604e+4 7.963e+6
CltStep theta=max(3w-2,w)=3w-2 <= 8w/2-(w+1)-1             OK  slack 0.0
CltStep W^(1/2) >= 16                                      OK  4096.0
STfFar U: log^5 ell_s <= ell_t                             OK  1.274e+6 1.593e+7
STfFar sum range: log^4 ell_s < floor(L/2)                 OK  7.659e+4 7.963e+6
STfFar dist cap  1/2 log^1.5 ell_t + log^2.5 ell_s = 5.40272e+8  vs floor(L/2) = 7962624.0 (non-binding at t=tCL)
far set nonempty, tau=0: FarEntry log^3*ell=4603.73  KfargL log^1.5*ell=67.8508  floor(L/2)=7962624.0 -> True True
far set nonempty, tau=tCL: FarEntry log^3*ell=7.33156e+10  KfargL log^1.5*ell=1.08054e+9  floor(L/2)=7962624.0 -> False False
GijDecgL: W^(-3/2) <= W^(-eps0), eps0=1/10 < 3/2           OK  1.455e-11 0.1895
FarEntry X0(c=1,K1=20.0) = 490.0 > logW(n=0)=16.636: conclusion eventual, first n with logW>=X0: n*=683 (W=2^707)
CltStep: a=10 D''=45 D'=270.0 C1=486.076 C2=1536 4p+16=20  N(n=0) >= max: True
Iso closing 2N^2 N^(-D-3) <= N^(-D) (N>=2) <= W^(-D)       OK  slack N/2 = 9.536e+42
--- B
N=1728.0  |m|=0.6708 (not 1)  kappa=0.5 <= Im m=0.6: True
E4 hyp N^(-1+delta)<=1-u, u=0.0                            OK 
   concl kappa/N <= Im ztOf = (1-u) Im m                   OK  0.0002894 0.6
E4 hyp N^(-1+delta)<=1-u, u=0.5                            OK 
   concl kappa/N <= Im ztOf = (1-u) Im m                   OK  0.0002894 0.3
E4 hyp N^(-1+delta)<=1-u, u=0.99878                        OK 
   concl kappa/N <= Im ztOf = (1-u) Im m                   OK  0.0002894 0.0007317
M5 base 2N^3/kappa >= 1 (kappa<=1)                         OK  2.064e+10
E4 at N=1,u=0                                              OK 
```

All hypothesis checks print OK at `n = 0` (no FAIL line); the far sets of row 12 are empty at `u = tCL`, as printed. Conclusions flagged "eventual" (rows 8, 11) are `∀ᶠ n` conclusions, not hypotheses.

### Verdicts
- Target 1 (CltSwap): **PASS**. `measurePreserving_cltSwap`, `integral_eq_zero_of_cltSwap_neg` take the coupling `g` as an explicit argument (`CltSwap:255, :299`); `cltTransfer` (`:323`) is stated for `sz.lam`, so the BA law `seqP (sz.withLam 0)` needs no new statement.
- Target 2 (E4, M4, M5 generic): **PASS**, with premise `κ ≤ 1` added to M5 (F1).
- Target 3 (CltPath): **PASS** (no exponent of its own; reads rows 2-3).
- Targets 4-5 (FarEntry, CltGood): **PASS** (rows 4, 11-12; F2 is a U4-BA producer note, not a defect of the generic statement).
- Target 6 (CltStep, `STCltIsogL`): **PASS** (rows 5-9; `T2455_STCltIsoConclgL` is closed by `N^{-D-3}` per step, slack `N/2`).
- Target 7 (ExpInv, `T2455_STExpInvgL`): **PASS** (no exponent; needs `H₀` invariant under the lifted translation and negation, input (h)).
- Target 8 (`Chain/CltGen`): **PASS** (`T2455_STfFarg` is the band `STfFar` with `Step2Gen_Theta (Mss·S) t`; at the band `Mss = μ•1` by `Step2Kern_Mss_band`, `Step2Gen:268`).
- Layout (in place): no mathematical objection from this section.

### (a″) Probe compile (Mon Oct 12 14:30:50 UTC 2026)

Probe step of the 1a design gate: `prover-max`, model claude-sonnet-5-5. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2455`, branch `t/T2455`, base `04118b1`. Commits `4361ff5`, `62feb69`, `e0d436d`, `b981c85` (`RBM3D/Probe/T2455Pins.lean`) and `2ae617c` (`RBM3D/Probe/T2455Meas.lean`); `git diff --stat main...t/T2455` lists only these two files. At 14:24:23 `main` was `880c9d0` and `git diff --stat 04118b1..main -- RBM3D RBM3D.lean lakefile.toml lean-toolchain lake-manifest.json` was empty, so the compile at the base is the compile on `main`. Section (a) is not edited. `Pins:N` is line N of `T2455Pins.lean`, `Meas:N` of `T2455Meas.lean`.

```
$ lake env lean RBM3D/Probe/T2455Pins.lean   (Mon Oct 12 14:27:55 UTC 2026, b981c85)  exit=0  output lines 0  file lines 397
$ lake env lean RBM3D/Probe/T2455Meas.lean   (same run, 2ae617c)                        exit=0  output lines 0  file lines 392
$ grep -nE "sorry|admit|native_decide|^axiom" <both files>                             no match (grep exit 1)
$ git grep -nE "(def|theorem|lemma|structure|abbrev) (<the 41 new public names>)( |$)" <ref> -- RBM3D ":!RBM3D/Probe"
  main, t/T2449, t/T2450, t/T2451, t/T2452, t/T2453, t/T2454, t/T2456: 0 hits each (14:18:06; sanity: 2 hits for cltStep_win, HClt on main)
```
Scratch copy of `T2455Pins.lean` (397 of 400 lines used, so these lines are not in the file) plus the verbatim `T2455_*` definitions of the check file, nine `rfl` examples (`CltEtaLowerOf`, `STfFarg`, `STCltFarConclgL`, `STcltBg`, `STcltXg`, `STCltIsoConclgL`, `STExpInvgL`, `CltRepg` with the argument order of the check, `STGijDecgL` equal their `T2455_` namesakes; `T2455_KfargL` is superseded, F2), `#check`, `#print axioms`; exit 0 (14:28 UTC); output verbatim:
```
STCltIsogL : ℕ → Prop
STCltFargL : ℕ → Prop
@STExpInvgL : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Measure sz.SeqΩ → Prop
@HCltOf : {d : ℕ} →
  {sz : Sizes d} →
    FlowFM sz →
      Measure sz.SeqΩ →
        ((n : ℕ) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) →
          (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → (ℕ → ℝ) → Prop
@STThPropsg : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Prop
@STKpropsg : {d : ℕ} → {sz : Sizes d} → FlowFM sz → (ℕ → ℝ) → Prop
@STGijDecgL : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → Prop
@STKfargL : {d : ℕ} → {sz : Sizes d} → FlowFM sz → (ℕ → ℝ) → Prop
@STMfarg : {d : ℕ} → {sz : Sizes d} → FlowFM sz → (ℕ → ℝ) → Prop
@CltRepg : {d : ℕ} →
  {sz : Sizes d} →
    FlowFM sz →
      Measure sz.SeqΩ →
        ((n : ℕ) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
@CltInvg : {d : ℕ} → {sz : Sizes d} → ((n : ℕ) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) → Prop
CltEtaLowerOf : ℕ → ℕ → ℕ → Prop
cltEta_lowerOf : ∀ (d L W : ℕ), CltEtaLowerOf d L W
CltDerivEvalMultiOf : ℕ → (L W : ℕ) → ℕ → [NeZero L] → [NeZero W] → Prop
CltEvalDetLeMultiOf : ℕ → (L W : ℕ) → ℕ → [NeZero L] → [NeZero W] → Prop
CltPathBoundMultiOf : ℕ → (L W : ℕ) → ℕ → [NeZero L] → [NeZero W] → Prop
hCltOf_szCL : STLocalEntryUgL (bandFM szCL (STflowE zCL)) szCL.seqP sCL tCL →
  STGdecayWgL (bandFM szCL (STflowE zCL)) szCL.seqP sCL tCL 1 →
    STGijDecgL (bandFM szCL (STflowE zCL)) szCL.seqP sCL →
      STKfargL (bandFM szCL (STflowE zCL)) sCL →
        HCltOf (bandFM szCL (STflowE zCL)) szCL.seqP (fun x => 0) szCL.lam (STflowE zCL) (1 / 2) (1 / 10) (1 / 6)
          (1 / 10) 1 sCL tCL
@bandFM_STCltFarConcl : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  STCltFarConclgL (bandFM sz E) sz.seqP s t ↔ sz.STCltFarConcl E s t
@cltRepg_band : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), CltRepg (bandFM sz E) sz.seqP (fun x => 0) sz.lam E
@cltRepg_ba : ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  CltRepg (baFM sz lam0 E) (sz.withLam 0).seqP (fun n => ↑(lam0 n) • PsiI d (sz.L n) (sz.W n)) 0 E
'RBM.Evol.cltEta_lowerOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltCk_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.hCltOf_szCL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STCltFarConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STfFarg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STThg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltRepg_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltRepg_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STMfarg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_M_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Scratch copy of `T2455Meas.lean` plus `#check`, `#print axioms`: exit 0, output verbatim:
```
@lenv_of_rep : ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
  {H₀ : (n : ℕ) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ},
  CltRepg C μ H₀ g' E → ∀ {κ : ℝ}, 0 < κ → ∀ (n : ℕ), κ ≤ (C.m n).im → ∀ {u : ℝ}, u < 1 → LEnv C n u
@bandFM_KInv : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), (∀ (n : ℕ), |E n| < 2) → KInv (bandFM sz E)
'RBM.BA.lenv_of_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_KInv' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Candidate `Chain/CltGen` text (Part 2 of the probe from `STThg` to `STCltFargL`, imports `RBM3D.Chain.Step2Gen`, `RBM3D.Induction.Step5Pins` only): 155 lines, `lake env lean` exit 0, output lines 0 (14:28:13), no `BA.` name; cap 300.

**Probe line against the files.** Generic definitions `Pins:142-258` (`STThg`, `STfFarg`, `STCltFarConclgL`, `STcltBg`, `STcltXg`, `STCltIsoConclgL`, `STExpInvgL`, `CltRepg`, `CltInvg`); tier 1 `Pins:30-110`; premise block `HCltOf` `:265`, `STCltIsogL` `:272`, `STCltFargL` `:278`, target 7 `:284`. E4: def `:58`, **proved** `cltEta_lowerOf` `:74` for every `m : ℂ`. M4 `:44`, M5 `:64`, P1 `:100`, band corollaries `:122-:134`. X1-C3 forms `STGijDecgL` `:205`, `STKfargL` `:226`, `STMfarg` `:232`. BA readings `:380-:395`. `cltYOf` `:40`, `cltEvalAtOf` `:89`, `cltGoodAtOf` `:93`; the one-label forms `CltDerivEvalOf`, `CltEvalDetLeOf`, `CltPathBoundOf` and `cltYoOf` are the `k = 1` cases of the `Multi` forms and are not spelled out (400-line limit). X1-C5: `T2455Meas.lean`. Preflight items (iii)/(iv) tables are for the 1a-audit to write from this output; (v) is F6; (vi) is `CltRepg` `:195` with `cltRepg_band`, `cltRepg_ba`; (vii) is the bridge list below; (viii) is the X1-C5 block; no per-file line prediction is made here.

**Premise lists as compiled** ("proved" = compiled in the probes; "named" = a merged name, not compiled here).
| premise (block `HCltOf`) | band | BA |
|---|---|---|
| (f) `0<κ≤1`, `κ≤Im(C.m n)`, `0<δ`, `Admissible`, `0≤s<t<1`, `N^(-1+δ)≤1-t` | all discharged at `szCL, zCL, s=0, t=1-L⁻², κ=1/2, δ=1/10`: `hCltOf_szCL` `:328` (proved); general `abs E ≤ 2-κ`: `cltCk_facts` `:112` (proved) | `BAReal` (`MFixedPoint:432`), `BAdom` (`:435`) carry `κ≤Im m`; the margin `κ'=(πκ)^5/2048` of `T2449-design.md` §1.4 has this form; `κ≤1`: `BAm_norm_le_one` (named) |
| (g) `CltRepg` `:195` | `cltRepg_band` `:290` (proved, all `sz`, `E`) | `cltRepg_ba` `:297` (proved: `rfl`, `PsiI_isHermitian`) |
| (d) Ward row `Σ_y‖C.M n x y‖²≤1`; (e) `STMfarg` | `bandFM_M_le` `:303`, `bandFM_STMfarg` `:308` (proved) | `BAMB_ward_row` (`BA/Ward:108`), `baOffDiag_holds` (`BA/Ward:303`) (named) |
| (a) `STLocalEntryUgL`, `STGdecayWgL` | merged `bandFM_STStep2Concl` (`Step2Gen:569`) | T1-BA (named) |
| (b) `STGijDecgL` | `STGbEXPij -> STGijDecgL (bandFM ..)`: statement only `:387` | **proved** from merged `baGbEXPij'_holds` (`GreenOff:1289`) `:383` |
| (c) `STKfargL` | **proved** from merged `emn2Exp2_bandHK` `:390` | **proved** from merged `baEMn2ExpHK` `:393` |
| Far pin only: `STReg5I`; `STThPropsg` `:238`; `STKpropsg` `:251`; `STExpInvgL` | `STThg` = merged `Theta`: `bandFM_STThg` `:358` (proved); `STExpInvgL (bandFM ..)` for `abs (E n) < 2` `:376` (proved); invariance conjunct of `STKpropsg`: `bandFM_KInv` `Meas:373` (proved); not compiled: the decay/difference/symmetry conjuncts of `STThPropsg` (merged `prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`) and the bound of `STKpropsg` | `baProp5to8_holds` (`Prop6Path:1049`), `BAKsolve` (named) |
| target 7: (g), (h) `CltInvg` `:258` | `H₀ = 0` | `H₀ = λ₀Ψ`: (h) not compiled |

Instances. Iso pin applied at the band data of `Step5Inst` with (a)-(c) as hypotheses and every other premise discharged: `hCltOf_szCL` `:328`, application `:353`. ExpInv: conclusion at the band `:376`. Far pin: no applied instance (`STThPropsg`, `STKpropsg` are X1b's). Bridges (G1), proved: `STCltIsoConclgL <-> STCltIsoConcl` by `Iff.rfl` `:375`; `STCltFarConclgL <-> STCltFarConcl` `:371` through `bandFM_STfFarg` `:365`, `bandFM_STThg` `:358`, `Step2Kern_Mss_band`; tier-1 corollaries at `m = mE E` `:122-:134` (`zt_eq_ztOf`; M5 uses `cltCk κ ≤ 1`, P1 uses `H₀ = 0`).

**Findings** (from the files and the output above).
- **F1** E4 holds for every `m` (no `‖m‖ = 1`, no `E`); M5 needs the premise `κ ≤ 1` (`:64`) and P1 needs `H₀.IsHermitian` (`:100`). So (f) contains `κ ≤ 1` (section (a) F1) and `CltRepg` contains the Hermitian `H₀`.
- **F2** T2452 is on `main` (`6bdc5a3`, `docs/reports/T2452-design.md`): D4 `:164-173`, finding `:170`, says FarEntry's far field is K-level (`emn2ExpHK`, merged `emn2Exp2_bandHK`, `baEMn2ExpHK`). `STKfargL` is now that form (carrier, one time, `δ = 1`, bound `W^(-d) W^(-(D+d))`), not the check's proposal (all `δ`, all `u ≤ t`, bound `W^(-D)`); both models have a merged producer (`:390`, `:393`), which closes section (a) F2 (BA `K = W^(-d)(Θ·Mss)`).
- **F3** (d) is the Ward row bound, not the entry bound: the loop premise inside `STGijDecgL` is supplied inside FarEntry by `𝓛^(2)_((-,+),(a,b)) = W^(-2d) Σ_(x∈[a],y∈[b]) |G_xy|²` (`Eblk`, `Loop/GLoop:55`) and `Σ_(x∈[a],y∈[b]) |M_xy|² ≤ W^d`, hence `1_Ω 𝓛 ≤ 2‖G-M‖²_max + 2W^(-d)`: `Φ = W^(-ε₀)` for `|a-b| < ρ`, `W^(-D)` beyond (`STGdecayWgL`, `STKfargL`), so no premise beyond the ticket's. Mathematics, not compiled. The entry bound `|M_xy| ≤ 1` (E2) follows from (d).
- **F4** X1b reads the closed form of `𝒦^(2)` (`MeanFar:885-889` `meanFar_K_eq`, `:1499-1503` `meanFar_n_K`, `:1785-1796` `hKbound`). The Far pin therefore carries `STKpropsg` (invariance, and `c₁/STAI` at the time `s`) besides `STThPropsg`. If (i) is read narrowly this is a premise beyond (a)-(i) for `STCltFargL` only: a stop-rule item for the 1a-audit. The Iso and ExpInv pins do not carry it.
- **F5** The pins quote `HCltOf`, so the premise block is in `Chain/CltGen`, not in `CltGood` (ticket target 5). Candidate `CltGen`: 155 lines, no `BA/*` import.
- **F6** The Iso pin does not read `STReg5I`, `C.eta`, `C.S` or `C.K` (`K` cancels in `STcltXg`, `CltStep:1030`). Spectral reading (v): `ztOf (C.m n) (E n) u`, `κ ≤ (C.m n).im`, `κ ≤ 1`; T2449 MN0 (merged `T2449-design.md` §1.4) uses `Ed κ' = BAReal ..`, i.e. `κ' ≤ Im m`: covered, stop rule not triggered.
- **F7** X1-C1 grep `mE|zt E|zt \(|2 - κ|\|E\||cltCk|etaT|norm_mE|PropSpin|Theta d|mSigma|STmsig ` over `T2455Pins.lean` (14:28:46): hits at lines 29, 57, 63, 88, 110 (docstrings, comment), 112-131 (`cltCk_facts`, band corollaries), 302, 306 (`bandFM_M_le`), 335-337 (`hCltOf_szCL`), 360 (`bandFM_STThg`); none in the body of a generic definition (lines 30-285).

**X1-C5.** Blocks declaration-aligned: `MeanFar.lean:874-1026`, `CltMoments2.lean:791-929` (the ticket ranges end inside the next declaration). Commands and output: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2455/meas/rep/measure.txt` (14:15:51): band text `git show 04118b1:.. | sed -n`, generic text between the `-- BLOCK` markers of `T2455Meas.lean`, `git diff --no-index --numstat`.
```
$ wc -l band1.txt gen1.txt band2.txt gen2.txt                      153 127 139 136   (band1/2: sed -n 874,1026p and 791,929p of the base files)
$ git diff --no-index --numstat band1.txt gen1.txt                 59	85	band1.txt => gen1.txt
$ git diff --no-index --numstat band2.txt gen2.txt                 47	50	band2.txt => gen2.txt
block     lines  added removed   g=(a+r)/lines    f_sem: lines moved to the band instance (band text lines)   f_sem
MeanFar     153     59      85   144/153 = 0.941  24 (11-19 K_eq, 36-38 and 51-56 Θ steps, 117-122 shift)    0.157
CltMom2     139     47      50    97/139 = 0.698  0                                                           0
both        292    106     135   241/292 = 0.825  24                                                          0.082
```
The 24 moved lines are the content of the compiled band instance `bandFM_KInv` (`Meas:373-391`, 19 lines with the statement). `lenv_of_rep` (`Meas:72`) derives the loop envelope `LEnv` (measurable, bounded by `η⁻²`) from `CltRepg` and `κ ≤ Im m`; `LEnv` and `KInv` replace `hE : |E| < 2`, `hu : u < 1`. No segment reaches `f_sem > 0.30`. `grep -cE 'mE|zt E|2 - κ|cltCk|etaT|mSigma|STmsig|\|E\|'` gives 19 and 14 on the aligned blocks (20 and 14 on the ticket ranges; the ticket quotes 21 and 14). Lines with any band token, pattern `mE|zt E|2 - κ|cltCk|etaT|seqP|seqHflow|Lloop|STLKM|STKloop|Theta d|STfFar|STcltX|STcltB|STmsig|mSigma|stExpInv_holds|STGdecayW |hE`: 55 and 37, i.e. 2.62 changed lines per band-token line in both blocks. The four X1b files have 475 such lines (29, 149, 141, 156): an extrapolation (not a measurement) is about 1.2k changed lines, about 0.5k added.
**g₀.** `sz.lam` enters the generic statements as `ellT` (`Pins:149-234`), `lam²W^d` (`STAI` in `STCltFarConclgL`, `:170` in `STcltBg`), `Bparam` and `lam²` (`:242-247`) and, through `Admissible`, `(eq:WO)`; the law's coupling is the separate `g'` of `CltRepg`. BA passes `sz.lam = g`, `g' = 0`, `H₀ = λ₀Ψ`, `λ₀ = BAflowLam0 = sqrt(t₀) g`; `cltRepg_ba` `:297` takes any `lam0`, and `lam0` occurs only there and at `:382`. No premise asks `λ₀ ≤ W^(-ε)` or smallness of `M - m₀ I` (C1).

**Open for the 1a-audit.** (1) F4: rule on `STKpropsg` for `STCltFargL`. (2) `HCltOf` placed in `Chain/CltGen` (F5). (3) `STKfargL` follows T2452 D4 (F2); the check's `T2455_KfargL` is superseded. (4) Not compiled: (h) at BA, the bound conjunct of `STKpropsg`, a Far-pin instance, the decay/difference/symmetry conjuncts of `STThPropsg`, the band implication `STGbEXPij -> STGijDecgL`, the F3 arithmetic. (5) Paper-delta candidates: none from this step.

**R1 repair (rule B; 1a-audit D1), Mon Oct 12 15:05:43 UTC 2026** (repairer, claude-opus-5-5). Option taken: the loop premise of `STGijDecgL` covers **both mixed charges**; `Φ` stays arbitrary (no symmetry premise). Commit `46fc313` on `t/T2455`, hunks at Pins:204 (docstring), 211-213 (premise), 386 (BA reading); the file keeps 397 lines, so the `Pins:N` references above stay valid. This block supersedes row (b) of the premise table ("statement only `:387`"), item (4) "band implication not compiled", and the `rfl` of `STGijDecgL` with the check's `T2455_GijDecgL` (a proposal, not binding; see the end of this block). `<scratch>` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad`.
```
$ git diff --stat b981c85 46fc313            RBM3D/Probe/T2455Pins.lean | 10 +++++-----
$ sed -n 211,213p RBM3D/Probe/T2455Pins.lean
      PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (t n) p.1.1 ![p.2.1, p.2.2] ω‖)
        (fun n p _ => Φ n p.2.1 p.2.2 ^ 2) →
$ lake env lean RBM3D/Probe/T2455Pins.lean; lake env lean RBM3D/Probe/T2455Meas.lean   (Mon Oct 12 15:04:03 UTC 2026, 46fc313)
  pins exit=0 output lines 0 (contains the BA reading :383-386 and hCltOf_szCL :328);  meas exit=0 output lines 0
$ grep -nE "sorry|admit|native_decide|^axiom" <both probes>    grep exit=1;   wc -l: 397, 392
$ git diff --stat 04118b1 main -- RBM3D RBM3D.lean lakefile.toml lean-toolchain lake-manifest.json   (main = c0ea2d6)   -> empty
$ diff <(sed -n 11,153p <scratch>/T2455/repair/cltgen_R1.lean) <(sed -n 141,283p RBM3D/Probe/T2455Pins.lean)   exit=0
  cltgen_R1.lean (candidate Chain/CltGen): imports RBM3D.Chain.Step2Gen, RBM3D.Induction.Step5Pins; 155 lines; lake env lean exit=0, output lines 0; grep -cE "BA\.|baFM" -> 0
```
BA reading (Pins:386): `GreenCore_loopPrem` is the restriction of the two-charge premise to `σ = ![false, true]`, `StochDomAt.precomp_param h4 fun n p => (⟨![false, true], _⟩, p.1, p.2)` (`Defs/StochDomAt:335`). The derivation of `STGbEXPij d → … → STGijDecgL (bandFM sz (STflowE z)) (seqP sz) t` (the Pins:387 statement) is compiled in a scratch copy, probe + 181 lines (`<scratch>/T2455/repair/derive.lean`; not in the probe: 397 of 400 lines used). Statements in that file: `T2455_gijDec_of_gex (C) (μ) (t) (hsize : Tendsto sz.size atTop atTop) (h : ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEXgL C μ t ε₀) : STGijDecgL C μ t` (every carrier, `c = 1`); `T2455_stGijDecgL_band (hG : STGbEXPij d) … (hf : STFlow sz κ ε 𝔠 𝔡 z) … : STGijDecgL (bandFM sz (STflowE z)) (Sizes.seqP sz) t`; `T2455_stGijDecgL_band3` (`3 ≤ d`, `hG := stGbEXPij_of_v3 (gbEXPV3 hd)`); `example : <Pins:387 statement>`.
```
$ lake env lean <scratch>/T2455/repair/derive.lean    exit=0; output: 2 deprecation warnings (if_neg, if_pos) and
'RBM.BA.T2455_gijDec_of_gex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_stGijDecgL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_stGijDecgL_band3' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Steps (Lean names). (1) `stGbEXPij_of_v3 (gbEXPV3 hd)` (Green/Pins:1137, Green/GbEXP:806) gives `STGijGEX sz (STflowE z) t ε₀` for every `ε₀ > 0`; `bandFM_STGijGEX` (Step2Gen:792) restates it as `STGijGEXgL (bandFM …) (seqP sz) t ε₀`. This is the step `ind·‖G_xy‖ = ind·‖(G−M)_xy‖` for `x ≠ y` (band `M` diagonal); `STindMax = STindMaxg` is `rfl` (`bandFM_STindMax`).
(2) `StochDomAt.of_subset_union` (Defs/StochDomAt:355) with `τ' = τ/4`, `q = N^{τ/4}`: off both bad sets, `ind·‖GM_xy‖² ≤ q·STgexRHSg` and `ind·‖L_σ(a',b')‖ ≤ q·Φ(a',b')²` for both `σ` of `STgexRHSg`. The loop transpose `𝓛_{(σ₁,σ₂),(a,b)} = 𝓛_{(σ₂,σ₁),(b,a)}` is not needed: the premise bounds both charges at the same `(a',b')`.
(3) On `ind = 1`: `STgexRHSg ≤ 2q·X² + Ψ²·1_{|a−b|≤1}` with `X = Σ_{|a'−a|≤1,|b'−b|≤1} Φ(a',b')` (`ΣΦ² ≤ X²`); `W^{-d}1_{|a−b|≤1}` is absorbed by `W^{-d} = (W^{-d/2})² ≤ Ψ²`. (4) The right side `R ≥ (X + Ψ·1_{|a−b|≤1})/8` (`e^{-2} ≥ 1/8` from `Real.exp_one_lt_d9`; the weights are `≥ e^{-2}` on the neighbours, `Ψe^{-|a−b|} ≥ Ψ/8` when `|a−b| ≤ 1`). The `Prec` square root is a comparison of squares (`pow_le_pow_iff_left₀`): `‖GM_xy‖ ≤ 16q·R ≤ N^τ·R` once `N^{3τ/4} ≥ 16`. On `ind = 0` it holds since `R ≥ 0`.
The check's one-charge `T2455_GijDecgL` implies the repaired `STGijDecgL` (`<scratch>/T2455/repair/weaker.lean`: probe + check lines 241-266 + one `example` by `StochDomAt.precomp_param`; `lake env lean` exit=0, output `'RBM.BA.hCltOf_szCL' depends on axioms: [propext, Classical.choice, Quot.sound]`): the repaired input is weaker, as D1 says.

### (a‴) 1a repair (rule B) — Mon Oct 12 15:05:43 UTC 2026
Repairer claude-opus-5-5: items R2, R3 of `T2455-1a-audit.md` §8 (R1 is the last block of (a″)); scripts and outputs in `<scratch>/T2455/repair/`. **R2. X1-C2 table.** `STThPropsg` is for mixed pairs (`σ 0 ≠ σ 1`, Pins:240); the producers cover all four pairs.
| band fact (X1 reader) | generic hypothesis | band producer | BA producer |
|---|---|---|---|
| `‖mE E‖ = 1` (`norm_mE`, CltGood:433) | (d) `Σ_y ‖C.M n x y‖² ≤ 1` (Pins:268) | `bandFM_M_le` (Pins:303) | `BAMB_ward_row` (BA/Ward:108) at real `E`, with `BAMfine_eq` (BA/GreenSchur:93); `BAPropM` item 3 (MFixedPoint:567) |
| `KLK_two`, `m(σ)m(−σ) = 1`, `kellStarEv` (FarEntry:417-445, 712) | (c) `STKfargL` (Pins:226) | `emn2Exp2_bandHK` (Induction/EMn2Exp2:945) | `baEMn2ExpHK` (BA/EMn2BA:637) |
| `Theta d L g (t m m)` in `STfFar` | `STThg` (Pins:142) | `bandFM_STThg` (Pins:358) | `T2455_baFM_STThg` (scratch below, via `Step2Kern_Mss_BA`, Step2Kern:73) |
| shift `Θ_xy = Θ_{0,y−x}` (`meanFar_Theta_shift`, MeanFar:991); symmetry (MeanFar:928) | conj. 1, 2 of `STThPropsg` | `meanFar_Theta_shift` (private; copy); `Theta_transpose_of_three_le` (Propagator/Props4:95) | `baP8_BATheta_shift` (BA/Prop6Path:497); `BATheta_isSymm` (BA/KBase:371; `BAReal`, `0 ≤ t < 1`) |
| `(prop:ThfadC)`: `prop5Decay_holds` (CltMoments1:944, CltFar:1171, MeanFar:1994) | conj. 3 | `prop5Decay_holds` (Propagator/Prop5Hold:784) | `(baProp5to8_holds d Λ κ c).decay` = `BAProp5` (BA/FlowPins:173) |
| `(prop:BD1)`, `(prop:BD2)`: `prop6Diff1_holds d Λ κ (1/2)` (CltMoments1:981), `prop7Diff2_holds d Λ κ' (1/2)` (MeanFar:1995) | conj. 4, 5 | `prop6Diff1_holds` (Prop6Hold:353), `prop7Diff2_holds` (:384) | `.diffOne`, `.diffTwo` = `BAProp6`, `BAProp7 d Λ κ (1/2)` (FlowPins:194, 205) |
| closed form of `𝒦^{(2)}` ((a″) F4) | `STKpropsg` (Pins:251) | X1b (audit F4) | `BAKsolve` (BA/KSolve:58) via `Step2Kern_BAKsolve_form` (Step2Kern:104); U4-BA |

**Premises compared.** `|r| ≤ ½|a|`: conj. 4-5 have `zdistD r ≤ 1/2 * zdistD a` (Pins:244, 246); `Prop6Diff1`, `Prop7Diff2`, `BAProp6`, `BAProp7` have `zdistD r ≤ c * zdistD a` with `0 < c < 1` and are read at `c = 1/2` (CltMoments1:981, MeanFar:1995; BA `inst_bundle`, Prop6Path:1065). Same premise; `zdistD` is the periodic `L¹` sum (Defs/Lattice:71).
- Stage P's `max τ 1`: only inside the BA proofs. `grep -c "max τ 1" RBM3D/BA/PropUnit.lean` → 11 (the factor `(1 + A²/max τ 1)^{-M}`, PropUnit:125); `sed -n 173,215p RBM3D/BA/FlowPins.lean | grep -c max` → 0. No factor or premise reaches `STThPropsg`.
- Constants: `BAProp5` (`∃ C c`), `BAProp6/7` (`∃ C`) are fixed after `(d, Λ, κ[, c])`, before `L, g, E, m` (FlowPins:173-215); band `Prop5Decay d Λ`: `(d, Λ)`; `Prop6Diff1`, `Prop7Diff2 d Λ κ c`: `(d, Λ, κ, c)` (Propagator/Pins:34-80). `STThPropsg` asks `∃ C₅ c₅ C₆ C₇` per carrier before `∀ᶠ n` (Pins:239): covered with `Λ = 𝔡⁻¹`, `c = 1/2`; `0 < g₀ ≤ 𝔡⁻¹` eventually is `BAflow_lam0_window` (GreenSchur:72).
- C1: the BA statements read take `BAReal`, `0 < g ≤ Λ`, `3 ≤ L`, `0 ≤ t < 1` (and `0 < c < 1`) only; no `g₀ ≤ W^{-ε}`, no smallness of `‖M − m₀I‖`.

**Coupling.** `baFMz sz z = baFM sz (BAflowLam0 sz z) (BAflowEs sz z)` (FlowPins:393), so `STThg` there is `BATheta d L g₀ E m` with `g₀ = BAflowLam0 sz z n = √t₀ · sz.lam n` (FlowPins:386), and `BAflow_real` (GreenSchur:59) gives `BAReal d L g₀ κ E m`: `baProp5to8_holds` is read at `g₀`, while `STThPropsg` reads `Bparam`, `ellT`, `(g² + |1−t|)⁻¹` at `sz.lam n = g`. The conversion is needed: `g₀² ≤ g² ≤ ((κ+1)/κ)g₀²` (`TwistStep2_lam0_sq`, BA/TwistStep2:740, from `κ/(κ+1) ≤ t₀`, `TwistStep2_T0_ge` :731) gives `(g₀²+x)⁻¹ ≤ ((κ+1)/κ)(g²+x)⁻¹` and `Bparam(g₀) ≤ ((κ+1)/κ)Bparam(g)`; `g₀ ≤ g` gives `ellT(g₀) ≤ ellT(g)`, so `e^{-c|a|/ellT(g₀)} ≤ e^{-c|a|/ellT(g)}`. Constants: `C₅ = ((κ+1)/κ)C`, `c₅ = c`, `C₆, C₇` times `(κ+1)/κ`; still `(d, 𝔡⁻¹, κ)` only. `grep -rn "theorem ellT_mono\|theorem ellT_le\|theorem Bparam_le\|theorem Bparam_mono" RBM3D` finds `ellT_mono` (Kernel/PropT:58, in `t`), `ellT_mono_instance` (NQGood1:1359, in `t`), `ellT_le_L`: no conversion in `g` is merged; U4-BA adds it. Scratch `T2455_P5_conv`: P5 at `g₀` gives P5 at `g` with `C ↦ ((κ+1)/κ)C`, same `c` (given `g₀ ≤ g`, `g² ≤ ((κ+1)/κ)g₀²`, `t < 1`; with `T2455_inv_conv`, `T2455_ellT_conv`). `T2455_baFM_STThg : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 → STThg (baFM sz lam0 E) n σ σ' t = BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t σ σ'`.
```
$ lake env lean <scratch>/T2455/repair/conv.lean     (probe + 62 lines)    exit=0, output:
'RBM.BA.T2455_baFM_STThg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_Bparam_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_P5_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**R3. X1-C3 table.** Code lines (comments stripped) of the seven files naming each public declaration of the source module; worktree `46fc313`:
```
$ sh <scratch>/T2455/repair/x1c3_compact.sh       (runs x1c3.py; drops the Step5Pins instance-data rows szCL… and InstIng5Concl)
KDecay: 16 public, used: 0
Step34Pins: 127 public, used: 1 | STStep2Concl 0/0/0/4/5/2/0
Step5Pins: 108 public, used: 23 | STcltB 0/0/0/0/0/7/0 | STcltX 0/0/0/0/0/4/0 | STCltIsoConcl 0/0/0/0/0/1/0 | STCltIso 0/0/0/0/0/2/0 | STExpInv 0/0/0/0/0/0/2
Green/Pins: 79 public, used: 2 | v3_premises_of_stFlow 0/0/0/1/2/2/0 | stGbEXPij_of_v3 0/0/0/1/0/0/0
Green/GbEXP: 20 public, used: 1 | gbEXPV3 0/0/0/1/0/0/0
Green/EntryCore: 56 public, used: 1 | green 0/46/15/0/0/0/0
KellStar: 3 public, used: 1 | kellStarEv 0/0/0/1/0/0/0
columns: CltSwap CltResolvent CltPath FarEntry CltGood CltStep ExpInv
filtered rows: 18; KDecay decls: 52, private: 36
```
KDecay confirmed: none of its 16 public names occurs in the code of the seven files (its 36 privates are not reachable). `InstIng5Concl` occurs once, in a band `example` (CltStep:1509).
| fact (file) | generic form | band, here | BA producer / layer |
|---|---|---|---|
| `STStep2Concl` `.1` = `STLocalEntryU`, `.2.2` = `STGdecayW` (FarEntry:702-703; CltGood, CltStep) | (a) `STLocalEntryUgL`, `STGdecayWgL` (Step2Gen:497-512) | `bandFM_STStep2Concl` (Step2Gen:569) | T1-BA (U-D layer) |
| `STcltB`, `STcltX`, `STCltIsoConcl`, `STCltIso` (CltStep), `STExpInv` (ExpInv) | `STcltBg`, `STcltXg`, `STCltIsoConclgL`, `STCltIsogL`, `STExpInvgL` (CltGen) | bridges Pins:371-377 | U4-BA |
| `v3_premises_of_stFlow` (FarEntry, CltGood, CltStep) | (f) in `HCltOf` (Pins:266-267) | `hCltOf_szCL` (Pins:328) | `BAflow_real`, `BAflow_lam0_window`, `TwistStep2_T0_ge`, `EMn2BA_T0_lt_one` (merged) |
| `stGbEXPij_of_v3`, `gbEXPV3` (FarEntry) | (b) `STGijDecgL` (Pins:205) | `T2455_stGijDecgL_band3` (R1 scratch) | `baGbEXPij'_holds` (GreenOff:1289; Pins:383-386) |
| `kellStarEv` (FarEntry) | (c) `STKfargL` (Pins:226) | `kellStarEv` + `farEntry_K_le` (FarEntry:417) | `baEMn2ExpHK` (EMn2BA:637) |
| `green` (CltResolvent, CltPath); Step5Pins instance data (18 rows) | unchanged (tier 1, any matrix); none | —; band instances | `green` at `H₀ + Hflow`; U4-BA data |

Import finding (`<scratch>/T2455/repair/closure.py`): the closure of `RBM3D.Induction.EMn2Exp2` contains `RBM3D.BA.FlowPins` and `RBM3D.BA.MFixedPoint`; those of `RBM3D.Evolution.FarEntry` and `RBM3D.Induction.EMn2Exp1` contain no `BA/*`. So FarEntry's band (c) (and the `hK` of the 1b instances) should follow `emn2Exp2_bandHK`'s route (`emn2Exp_kellStar_far`, EMn2Exp1:1762, or `kellStarEv` with `farEntry_K_le`), without importing `EMn2Exp2`.

**Privates reused** (signature = declaration line to `:=`; S = X1-C1 token, B = band-model token, R = model-free):
```
$ sh <scratch>/T2455/repair/privs_compact.sh
CltSwap 4 (S 0, B 0, R 4);CltResolvent 46 (S 9, B 0, R 37);CltPath 33 (S 4, B 13, R 16);FarEntry 22 (S 2, B 4, R 16);CltGood 9 (S 0, B 2, R 7);CltStep 26 (S 2, B 0, R 24);ExpInv 35 (S 0, B 2, R 33)
total 175 {'S': 17, 'B': 21, 'R': 137}
```
The script counts 175 privates (the ticket: 172). The 137 model-free ones are reused unchanged. Plan for the 38 others (none deleted, §153 (1)). Generalized in place (13): `cltres_zs_im`, `cltres_gEntry_le`, `cltres_eval_le`, `cltpath_zs_im`, `cltpath_gEntry_le`, `cltpath_deriv`, `cltpath_gEntry_zero`, `farEntry_indMax_eq_one`, `cltGood_P_le_of_seqP`, `cltGood_STWB_le`, `cltStep_core`, `expInv_seq`, `expInv_integral_eq`. Kept for band corollaries and checks (12): `cltres_ck_le_im`, `cltres_ck_pos`, `cltres_ck_le_one`, `cltres_chk_E4`, `cltres_chk_M5`, `cltres_chk_M5Multi`, `cltStep_ck_pos`, `farEntry_K_le` (band (c)), `farEntry_neighbour`, `farEntry_gexRHS_le`, `farEntry_norm_Gt_false`, `farEntry_core` (old band route). Band instance data, reused by the generic instances at `H₀ = 0`, `m = mE E` (13): `cltpath_chk_*` (7), `cpw_eq`, `cpS`, `cpS_pos`, `cpx`, `cpx_far`, `cpc`.

**Predicted lines per file** (estimate; stop line 2,000, binding).
| file | now | Δ central / high | predicted central / high |
|---|---|---|---|
| CltSwap | 365 | 0 / 30 | 365 / 395 |
| CltResolvent | 1,118 | 140 / 220 | 1,258 / 1,338 |
| CltPath | 551 | 80 / 130 | 631 / 681 |
| FarEntry | 940 | 410 / 560 | 1,350 / 1,500 |
| CltGood | 680 | 110 / 180 | 790 / 860 |
| CltStep | 1,594 | 115 / 200 | 1,709 / 1,794 (206 lines left at high) |
| ExpInv | 544 | 60 / 110 | 604 / 654 |
| Chain/CltGen (new; cap 300) | — | 180 / 230 | 180 / 230 |

Basis: probe sizes and the compiled scratch texts. CltResolvent: 8 generic defs (Pins:29-71 plus the one-label M4/M5 forms), 5 theorem statements, 5 band corollaries (pattern Pins:122-128) and `cltCk_facts` (9), endpoint instances. CltPath: 5 generic defs (Pins:88-108 plus one-label forms), 2 corollaries (Pins:129-133), instances. FarEntry: `STFarEntryAtLoggL` and its theorem (≈ 20), `T2455_gijDec_of_gex` with helpers (≈ 125, R1), band (c) (≈ 25), the new carrier core through (b)-(d), (g) (≈ 200; the band core FarEntry:682-826, 145 lines, stays), band corollary and instance (≈ 40). CltGood: 6 generic statements (band texts 29 lines), 3 theorem statements and corollaries, (d) in E2, instance. CltStep: `cltStepOf` (band statement 20 lines), loop forms (10), `stCltIsogL_holds` (CltStep:1312-1349 moves), 3 corollaries, instance (≈ 25). ExpInv: `stExpInvOf` (≈ 15), `stExpInvgL_of_rep` (≈ 30), band instance and example (≈ 15). CltGen: the candidate (155) plus bridges (Pins:357-377) and `cltRepg_band`. Observation: the central sum of Δ (1,095) exceeds the ticket's central (650) and is near its high (1,100); the high sum is 1,660; the excess is FarEntry's new carrier route ((b) with a constructed `Φ`, (c), (d), (g)), which FarEntry's 3 spectral lines do not show. No file is predicted past 2,000.

**Paper-delta candidate T2455a** (D1 fix, adopted). The generic input `STGijDecgL` (the primed `(GijGEX_BA)`, `lem_GbEXP_BA` (b), `7_8:1942-1944`) takes the loop premise `(eq:def_Psit)` (`7_8:1924`) for both mixed charges `(−,+)` and `(+,−)`, uniformly in `(a,b)`; the paper states `(−,+)` only. This is a Lean-only weakening of the input (one more premise). Reason: the band `(GijGEX)` (`3_5:24-26`) sums both charges and `Φ` is arbitrary, while `𝓛_{(+,−),(a,b)} = 𝓛_{(−,+),(b,a)}`. The BA producer `baGbEXPij'_holds` keeps the paper's one-charge premise and implies the Lean form (Pins:383-386).

### (a⁗) UBA-C1 correction of R2 (H250 (3)) — Mon Oct 12 15:24:30 UTC 2026
Stage 1b (restart), `prover-hard`, claude-sonnet-5-5; sections (a)-(a‴) are not edited. Rule (DECISIONS §269 (2), CONTROL H250 (3)): size-level quantities read `sz.lam`; Θ-profile facts are read at the kernel coupling `gK` through a profile hypothesis; the crossing is ONE comparison hypothesis `∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (band `gK = sz.lam`, `A = 1`; BA `gK = BAflowLam0`, `A = (κ+1)/κ` by `TwistStep2_lam0_sq`, TwistStep2:740). The pins `STCltFargL`, `STCltIsogL`, `STExpInvgL` stay as the 1a-audit round 2 fixed them (Pins:265-284): `gK`, `A`, the profile hypothesis and the comparison hypothesis occur in no pin and in no premise of `HCltOf`; they occur only in the U4-BA conversion that produces `STThPropsg C`, `STKpropsg C s` (so no premise beyond (a)-(i), stop rule not hit). R2 rows, restated:
| X1-C2 row (fact read by X1) | level | generic hypothesis | band (`gK = sz.lam`, `A = 1`) | BA (`gK = g₀`, `A = (κ+1)/κ`) |
|---|---|---|---|---|
| `‖mE E‖ = 1` (`norm_mE`) | none (matrix) | (d) Ward row (Pins:268) | `bandFM_M_le` | `BAMB_ward_row` (as R2) |
| `KLK_two`, `kellStarEv` | `sz.lam` (`ellT (sz.L n) (sz.lam n) (t n)` in `STKfargL`) | (c) `STKfargL` (Pins:226) | `emn2Exp2_bandHK` | `baEMn2ExpHK` (EMn2BA:637) states it at `baFMz sz z`, `sz.lam`; decay shown at `ℓ(g₀)` is read at `ℓ(g)`, `ℓ(g₀) ≤ ℓ(g)`: no conversion here |
| `Theta d L g (t m m)` in `STfFar` | none (carrier object) | `STThg` (Pins:142) | `bandFM_STThg` (Pins:358) | `T2455_baFM_STThg` (scratch of R2): `BATheta d L g₀ E m` |
| shift `Θ_xy = Θ_{0,y-x}`, symmetry | scale-free | `STThPropsg` conj. 1, 2 | `meanFar_Theta_shift`, `Theta_transpose_of_three_le` | `baP8_BATheta_shift`, `BATheta_isSymm`: no `A` |
| `(prop:ThfadC)`, `(prop:BD1)`, `(prop:BD2)` | profile at `gK`; the statement reads `Bparam`, `ellT`, `(sz.lam² + |1-t|)⁻¹` at `sz.lam` | profile hypothesis (`BAProp5-7`-shape at `gK`) + the comparison hypothesis | `gK = sz.lam`: `prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds` directly | `baProp5to8_holds` at `g₀` (`BAReal` of `BAflow_real`); constants `C₅,C₆,C₇ ↦ A·C` (R2 scratch `T2455_P5_conv`, `T2455_inv_conv`: `(g₀²+x)⁻¹ ≤ A (g²+x)⁻¹`, `Bparam g₀ ≤ A Bparam g`, `ℓ(g₀) ≤ ℓ(g)`); owner U4-BA (a), not X1a |
| closed form of `𝒦^{(2)}`: invariance, `‖K‖ ≤ c₁/STAI` | `STAI = sz.lam² W^d` (Step34Pins:79) at `sz.lam` | `STKpropsg` (Pins:251) | X1b | `BAKsolve` at `g₀`; `STAI sz n ≤ A·(g₀² W^d)` is the second conjunct of the comparison hypothesis; owner U4-BA (a) |
| windows `Admissible`/`WO`, isolation `10w`, `STcltBg` scale `(sz.lam² W^d)^{6/5}`, `STfFarg` regions | `sz.lam` | `HCltOf` (f), `STCltIsoConclgL`, `STCltFarConclgL` | `szCL` | BA passes `sz` (lam `= g`); `0 < g₀ ≤ 𝔡⁻¹` eventually: `BAflow_lam0_window` (GreenSchur:72) |
C1: `A = (κ+1)/κ` depends on `κ` only; no `g₀ ≤ W^{-ε}`, no smallness of `‖M - m₀I‖`. Supersedes only the "Coupling" paragraph of (a‴) (conversion "U4-BA adds it" becomes: one comparison hypothesis, owner U4-BA (a)); the other R2 rows stand.

## (b) Script output (stage 1b, `prover-hard`, claude-sonnet-5-5) — Mon Oct 12 16:40 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2455`, branch `t/T2455` at `8eb4ff2` (11 commits since `46fc313`; `git status --short` empty).
```
$ lake build        (whole library, started 16:33:48 UTC, finished by 16:38:32 UTC; log scratchpad/T2455/fullbuild3.log)
info: RBM3D.lean:514:0: axiom audit: 13321 theorems, 4208 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 120 (borrowed 1, owed 55, structural 45, refuted 6, superseded 13).
Build completed successfully (4282 jobs).        grep -c error: 0   grep -nE "sorry|admit|native_decide|^axiom" <8 files>: exit 1
$ wc -l (stop line 2,000 per file; 1a high prediction in brackets)
 365 CltSwap (unchanged)   1285 CltResolvent [1338]   708 CltPath [681]   1865 FarEntry [1500]   1080 CltGood [860]   1823 CltStep [1794]   634 ExpInv [654]   267 Chain/CltGen [230; cap 300]
$ git diff --stat main...t/T2455 | tail -1      11 files changed, 3510 insertions(+), 476 deletions(-)    (7 Lean files — CltSwap is unchanged —, RBM3D.lean, Test/Axioms.lean, the two never-merged probes)
$ git diff main...t/T2455 -- <CltMoments1 CltMoments2 MeanFar CltFar RBM3D/Induction Chain/Carrier Chain/Step2Gen Chain/Step2Kern> | wc -l      0
$ grep -n '^import' <the 8 files> | grep -c 'RBM3D.BA'      0 per file;   CltGen imports: RBM3D.Chain.Step2Gen, RBM3D.Induction.Step5Pins
$ lake env lean docs/tickets/checks/T2455-check.lean (copy in scratchpad; 16:38:44)      exit 0, errors 0
```
**G1** (`scratchpad/T2455/g1/g1.py 04118b1`: non-private declarations of the seven files, signature of theorems and full text of defs, whitespace-normalised):
`public decls on base: 100  missing: 0  changed: 0  new public: 45` (+ 25 in `Chain/CltGen` = 70 new public names). Private names: base 4/46/33/22/9/26/35 → 4/55/44/38/14/28/37 (CltSwap … ExpInv), none deleted (`comm -23` per file: 0). All band privates keep their names; `cltStep_STcltX_eq` and `cltStep_core`/`cltStep_assembly`/the `Xo`/`Gamma` helpers are generalised in place.
**Axioms** (`#print axioms` of the 70 new public names, `scratchpad/T2455/final/axioms.lean`, 16:38:44): `lines=70  standard three or none=70`.
**Statement diff against the check** (`final/stmt.lean` = check Parts 1-2 + `Iff.rfl`/`rfl` examples, exit 0): `CltEtaLowerOf ↔ T2455_CltEtaLowerOf`, `STfFarg = T2455_STfFarg`, `STCltFarConclgL ↔ T2455_STCltFarConclgL`, `STcltBg = T2455_STcltBg`, `STcltXg = T2455_STcltXg`, `STCltIsoConclgL ↔ T2455_STCltIsoConclgL`, `STExpInvgL ↔ T2455_STExpInvgL`. `diff <(sed -n 141,283p Probe/T2455Pins.lean) <(sed -n 28,170p Chain/CltGen.lean)`: blank lines only, so `HCltOf`, `STCltIsogL`, `STCltFargL`, `STExpInvgL` are the texts fixed at the 1a-audit.
**Spectral grep** (X1-C1, pattern `mE|zt E|zt \(|2 - κ|\|E\||cltCk|etaT|norm_mE|PropSpin|Theta d|mSigma|STmsig `, statements of the 45+25 new public declarations): 2 hits, both band material: `cltCk_facts` (the band margin `c_κ`, used by the band corollaries) and `bandFM_STThg` (bridge to the merged `Theta`). Lines matching `mE|zt E|2 - κ|cltCk|etaT`, base → now: CltSwap 0→0, CltResolvent 38→47, CltPath 15→13, FarEntry 3→7, CltGood 10→14, CltStep 18→16, ExpInv 3→3, CltGen 0→3 (band corollaries, bridges and band instances).
**Name clash**: `git grep -nE "(def|theorem|lemma|structure|abbrev|instance) (<70 names>)( |$)"` on `main` and 457 `t/*` branches (`t/T2455` excluded, `RBM3D/Probe` excluded): 0 hits (positive control, `cltStep_win|HClt` on main: 2 hits).
**Ports**: none from `../RBM1D`/`../RBM2D`. The two-loop-in-entries lemmas are copied from this project: `RBM3D/Green/Pins.lean:350-440` (private there; `git log -1 -- RBM3D/Green/Pins.lean` = `64bdfd3`) as `farEntry_gres_blockMat_true`, `farEntry_trace_pm_formula`, `farEntry_loopFine_pm`, `farEntry_loopFine_mp`.
**Targets** (extracted by script from the files; first 250 characters):
```
CltResolvent: cltEta_lowerOf (d L W) : CltEtaLowerOf d L W      cltDeriv_evalMulti_leOf (d L W k) : CltDerivEvalMultiOf d L W k      cltEval_detMulti_leOf (d L W k) : CltEvalDetLeMultiOf d L W k   (+ one-label cltDeriv_eval_leOf, cltEval_det_leOf)
CltPath:      cltPathMulti_boundOf (k) : CltPathBoundMultiOf d L W k      (+ cltPath_boundOf)
FarEntry:     stFarEntryAtLoggL {H₀ g' E s t τ 𝔠 𝔡 δ Cd} (hd : 3 ≤ d) (hadm : sz.Admissible 𝔠 𝔡) (hδ : 0 < δ) (hRep : CltRepg C μ H₀ g' E) (hWard : ∀ n x, ∑ y, ‖C.M n x y‖ ^ 2 ≤ 1) (hs) (hsτ) (hτt) (ht1) (hrange) (hLoc : STLocalEntryUgL C μ s t) (hDec : STGdecayWgL C μ s t Cd) (hGij : STGijDecgL C μ τ) (hK : STKfargL C τ) (hMf : STMfarg C τ) : STFarEntryAtLoggL C μ τ
              bandFM_STKfargL (hd : 3 ≤ d) {κ ε 𝔠 𝔡 z} (hκ) (hε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (ht0) (htT) : STKfargL (bandFM sz (STflowE z)) t      (+ stGijDecgL_of_gex, bandFM_STGijDecgL, bandFM_STGijDecgL_of_three_le)
CltGood:      cltGmax_whpOf (d) : CltGmaxWhpOf d      cltFarEntry_whpOf (d) : CltFarEntryWhpOf d      cltGood_whpOf (d) : CltGoodWhpOf d
CltStep:      stCltIsogL_holds (d) : STCltIsogL d      cltStepOf (C μ) (hH : HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t) (K C' hC' F hcoef hloc p hp D hD) : ∀ᶠ n, ∀ b i, window → isolated → ∀ e j hj, ‖∫ q, (cltStep_XoY (cltEvalAtOf (F n) (C.m n) (E n) (s n) (H₀ n)) (g' n) b i … - … (j+1)) * cltStep_GammaY … q.1 ∂(PF (g' n)).prod (PF (g' n))‖ ≤ N^(-D-3)
ExpInv:       stExpInvgL_of_rep (hRep : CltRepg C μ H₀ g' E) (hInv : CltInvg H₀) : STExpInvgL C μ      stExpInvgL_band (sz) (E) : STExpInvgL (bandFM sz E) (seqP sz)
```
**Compiled nonempty instances** (`d = 3`; Step 2 pins `STLocalEntryUgL`, `STGdecayWgL` are the only hypotheses; every other premise is discharged; `Probe` is not used):
| target | instance (file:line) | data |
|---|---|---|
| `cltEta_lowerOf`, `cltDeriv_(evalMulti_)leOf`, `cltEval_det(Multi)_leOf` | `cltres_chk_E4Of/M4Of/M4MultiOf/M5Of/M5MultiOf` (CltResolvent:1144-1190) | `m = 3/10 + (3/5) i` (`‖m‖² = 0.45`), `κ = 1/2 ≤ Im m`, `d = L = 3, W = 1`, `E = 0`, `u = 1/2` |
| `cltCk_facts` | `cltres_chk_ckfacts` | `κ = 1`, `E = 0` |
| `cltPath(Multi)_boundOf` | `cltpath_chk_szCLOf(_multi)` (CltPath:641, 663) | `szCL`, `m = 1/2 + i`, `H₀ = (1/3)·1`, `ω₀ = 0`, `ρ = w`, `R = 10 w`, `s = W^{-1/2}` |
| `stFarEntryAtLoggL`, `bandFM_STGijDecgL_of_three_le`, `bandFM_STKfargL` | `example` FarEntry:1815 | `bandFM szCL (STflowE zCL)`, `s = τ = sCL`, `t = tCL`, `Cd = 1`, `δ = 1/10`; `hGij` by `gbEXPV3`, `hK` by `kellStarEv`, `hMf`, Ward, `CltRepg` discharged |
| `cltGmax/cltFarEntry/cltGood_whpOf` | `cltGood_hCltOf_szCL` (CltGood:1002) and the three `example`s (:1037, :1044, :1053) | same band data, `κ = 1/2`; `c = 1`, `D' = 5`, `D = 10`; far set nonempty at every `n` |
| `stCltIsogL_holds`, `cltStepOf`, `cltStep_loopForm_evalOf`, `cltStep_pairForm_evalOf` | `example`s CltStep:1763, :1765, :1774, :1784, :1793 | band data as above; labels `cltStep_szCL_witness` (window `m² > 0`, isolated); `m = 1/2 + i` |
| `stExpInvgL_of_rep`, `stExpInvgL_band` | `example`s ExpInv:624, :628 | `szCL`, law `seqP (szCL.withLam 0)`, `m = 1/2 + i`, `H₀ = (1/3)·1`; band `E = STflowE zCL` |
| `CltGen` bridges | 7 `example`s (CltGen:239-253) | `szCL`, `n = 0`; the `bandFM_STExpInv` example (CltGen:253) keeps `STExpInv 3` as a hypothesis (proved by `stExpInv_holds` in ExpInv, which imports CltGen) |
The two Step 2 hypotheses are the same ones as in the merged `farEntry_szCL_stFarEntryAtLog` (FarEntry) and `cltStep` instances; they are the `STStep2Concl` components of the Step 2 gate.
**Registry** (`Test/Axioms.lean`, +9 lines): owedProps `STLocalEntryUgL`, `STGdecayWgL`, `STGijDecgL`, `STKfargL`, `STMfarg`, `CltInvg` (owners T1-BA / U4-BA); structuralProps `CltRepg`, `HCltOf`. The scan inside the full build above passed. `RBM3D.lean`: `import RBM3D.Chain.CltGen` after the last import.

Narrative (facts from the commits and files).
- Order as the ticket: CltSwap (no edit: `cltTransfer` is applied at `sz.withLam g'`), CltResolvent, CltPath, `Chain/CltGen`, FarEntry, CltGood, CltStep, ExpInv; each module built (`lake build RBM3D.<Module>`) before the next.
- Tier 1: the generic statements carry `m : ℂ` and `H₀` (`gEntryOf`, `LocalForm.evalOf`, `cltYOf`, `cltEvalAtOf`, `cltGoodAtOf`); their proofs are the old band proofs with `zt E u ↦ ztOf m E u`, `H₀ + Hflow`; the band pins `cltDeriv_evalMulti_le`, `cltEta_lower`, `cltEval_detMulti_le`, `cltPathMulti_bound`, `cltStep_loopForm_eval` are one-line corollaries (`zt = ztOf (mE E)` is `rfl`; `cltPathMulti_bound` through `0 + Hflow = Hflow`). M5 takes the premise `κ ≤ 1` ((a) F1).
- `Chain/CltGen` holds the pins verbatim, the inputs, `HCltOf` and the band bridges; `bandFM_STMfarg` takes `∀ᶠ n, 0 < log W` (the probe had `∀ n`), which `Admissible` gives.
- FarEntry: the scalar tail of `farEntry_neighbour` is now `farEntry_loop_le` (shared by the band route and the carrier route); `farEntry_indMax_eq_one` is stated over a carrier. The carrier route builds `Φ_n(a,b) = W^{-ε₀}` for `|a-b|_∞ < ρ_n = (c/2 (log W)³ - 2) ℓ_τ`, `W^{-D₁}` beyond, `Ψ = W^{-ε₀}`; the loop premise of `STGijDecgL` is proved from the entries identity (`‖𝓛‖ ≤ 2m² + 2W^{-d}`, Ward row), `STGdecayWgL` and `STKfargL`; the right side is `≤ 3 W^{-D'}` (`farEntry_rhs_le`). `stGijDecgL_of_gex` is `T2455_gijDec_of_gex` of the 1a repair (R1) with its helpers. The band `farEntry_core` route is kept.
- CltGood: items 3-5 over the carrier by the band proofs with `PF d L W (g' n)`, `H₀ n + Hflow`, `Σ_y ‖M_xy‖² ≤ 1` in place of `norm_mE`; `cltGood_STWB_leOf` is generic in the range exponent (the band `cltGood_STWB_le` calls it).
- CltStep: the helpers, `cltStep_core` and `cltStep_assembly` are abstract in the evaluation `Y` (band `Y = cltEvalAt F E u`, defeq to `cltStep_XoY`); the sequence-level body is `cltStep_seq` (abstract in `Y`, `Good`, with the spectral input `hYn` and the path bound `hP1`). The band `cltStep` keeps its `HClt` (non-strict `s ≤ t`) and calls `cltStep_seq`; `cltStepOf` (under `HCltOf`, strict `s < t`) calls it too; so the band `cltStep` is not a corollary of `cltStepOf`. `stCltIsogL_holds` is the old `stCltIso_holds` proof with `STcltXg`; the band `stCltIso_holds` is now its corollary at `bandFM sz (STflowE z)` (`HCltOf` built from the band premises, `κ ↦ cltCk (κ/2)`, `δ = ε/2`).
- ExpInv: `stExpInvgL_of_rep` reuses `expInv_integral_eq` at `sz.withLam g'` with `H₀` fixed by the lift (`CltInvg`); no separate `stExpInvOf`. Band `stExpInv_holds` is unchanged.
- UBA-C1: `gK`, `A`, the profile hypothesis and the comparison hypothesis occur in no declaration of this ticket (they belong to the U4-BA conversion, (a⁗)).

## (c) Verified Mathlib names (all compile in the build above)
`Real.rpow_le_one_of_one_le_of_nonpos`; `Real.rpow_def_of_pos`; `Real.one_le_rpow`; `Real.rpow_le_rpow_of_exponent_le`; `Real.exp_one_lt_d9`; `Real.exp_le_one_iff`; `Real.tendsto_log_atTop`; `Filter.Tendsto.const_mul_atTop`; `tendsto_pow_atTop`; `Measurable.of_eval`; `Matrix.conjTranspose_smul`, `Matrix.conjTranspose_one`, `Complex.conj_ofReal`; `Equiv.apply_eq_iff_eq`; `Finset.single_le_sum`; `Matrix.submatrix_add` exists but is a function-level equation, so `rw` at an applied term fails (used `ext` + `Matrix.submatrix_apply`). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Report length: sections (a)-(a⁗) alone are 310 lines; this file exceeds the 300-line limit of CLAUDE.md §6 (the 1a-audit already noted it; sections (a)-(a‴) were not edited).
- FarEntry (1865) and CltStep (1823) are above the 1a central predictions (1350 / 1709) and CltStep slightly above its high (1794); 135 and 177 lines remain to the stop line. CltGood is 220 above its high prediction.
- Band theorems kept with their own proofs (not re-derived from the generic ones, as in the (a‴) plan): `stFarEntryAtLog` (route `farEntry_core`), `cltGmax_whp`, `cltFarEntry_whp`, `cltGood_whp`, `cltCoord_tail` (E1 is used unchanged by `cltStepOf` at `sz.withLam g'`), `stExpInv_holds`, `cltStep` (shares `cltStep_seq`). Re-derived as corollaries: `cltDeriv_evalMulti_le`, `cltDeriv_eval_le`, `cltEta_lower`, `cltEval_detMulti_le`, `cltEval_det_le`, `cltPathMulti_bound`, `cltPath_bound`, `cltStep_pairForm_eval`, `cltStep_loopForm_eval`, `stCltIso_holds`.
- `STCltFargL` is stated (CltGen) and not proved here (X1b); `STThPropsg`, `STKpropsg` have no producer here. The conversion of the Θ-profile facts at `g₀` to `sz.lam` (comparison hypothesis, `A = (κ+1)/κ`) is U4-BA (a); no generic conversion lemma was added (scratch `T2455_P5_conv` of R2 exists).
- Hypotheses of the instances: `STLocalEntryUgL`, `STGdecayWgL` (Step 2 gate), at the band data they are the merged `STStep2Concl` components (`bandFM_STStep2Concl`, `Iff.rfl`).
- Main moved after the base (`04118b1` → `1debc23`: T2458 added `Chain/Step5Gen` and one line of `RBM3D.lean`); the branch was not rebased; `git diff main...t/T2455` lists only the sole writable files.
- Paper-delta candidates: **T2455a** (carried from (a‴): the loop premise of `STGijDecgL` for both mixed charges). **T2455b**: `STFarEntryAtLoggL` is stated for the charge `+` (`C.G`); the band `STFarEntryAtLog` has a `Bool` charge; the charge `-` is the transpose (`G(-) = G(+)ᴴ`, Hermitian `H₀ + H_u`) taken in `cltFarEntry_whpOf`. **T2455c**: the generic M5 (`CltEvalDetLeMultiOf`) has the premise `κ ≤ 1` in place of the band `cltCk κ ≤ 1` (no change of the paper's statement).
