Prover model: claude-sonnet-5-5
## (a) Math preflight — Wed Oct 14 07:45:29 UTC 2026

Targets 1–12 of `docs/tickets/T2504.md`, pins `docs/tickets/checks/T2504-check.lean` (`T2504_*`); BA tuple `(seqP(sz.withLam 0), BAFlow, baFMz, BAflowT0)`; instance data `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^-6`, `N_n = (W_n L_n)^3 = 2^21 (n+1)^18`).

### (i) Exponent table
| # | quantity | value (instance) | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `κ, ε, 𝔡, 𝔠` | `1/4, 1/10, 1/10, 1/6` | `0<κ,ε,𝔡` (pins 3, 6, 9, 10, 11); `BAFlow`: `κ ≤ Im m(z_n,lam_n)`, `N^{-1+ε} ≤ Im z_n ≤ 1`, `Admissible 𝔠 𝔡` | `Im m_S ≥ 0.83249` vs `1/4`; `N^{-0.9} ≤ 2^{-18.9}` vs `Im z ≥ 0.3667` |
| 2 | `Admissible`: `N^{𝔠} ≤ W`, `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`Defs/Sizes.lean:164-178`) | `N^{1/6} = 2^{3.5}(n+1)^3 ≤ 32(n+1)^5`; `W^{-7/5} = (2(n+1))^{-7} ≤ lam_n = (2(n+1))^{-6} ≤ 1/64 ≤ 10` | holds at every `n ≥ 0` (script rows `band`, `WO`) | factor `2(n+1)` at `WO`; `10` vs `1/64` |
| 3 | `c₁` (step pin, targets 3, 6) | `1/3` | `0<c₁≤1/2`; window `BAWinBulk sz z c₁ κ`: `κ ≤ Im m(g',E_n)`, `g' ∈ [√(1-c₁) g₀, g₀]`; probe `sz0_win_third` is at `κ=1/2` | numerics: `min Im m(g',E) = 0.99949` (n=0) vs `1/4`; limit `Im m(0,0)=1` |
| 4 | `T0_n = Im m/(Im m+Im z)`, times `s ≡ 1/10 < t ≡ 1/2`, member `u = 17/25` | `T0_n ∈ [0.69374, 25/36=0.69444]` | `s<t≤T0`; `u ≤ max(T0, 1-c₁=2/3)`: needs `T0 ≥ 17/25` (`t0_sz0_ge`) | `T0 - 17/25 ≥ 0.0137`; `T0 - 1/2 ≥ 0.19`; closed form `T0 ≥ 0.68699` at n=0 |
| 5 | target 2 (`BAFlowMember_holds`, `Step1Fam:624`): `κ' = c_κ(κ)κ`, `c_κ = √min(κ/(κ+1),1/2)` (`Step1Fam:488`); `ε' = ε/2` | `c_κ = √(1/5) = 0.447214`, `κ' = 0.111803`, `ε' = 1/20` | `κ' ≤ κ`, `ε' ≤ ε`, `0<κ',ε'` | `κ' = 0.4472 κ`; `ε'=ε/2` |
| 6 | `n₀` of the member modification (existential inside `BAFlowMember_holds`; V3 supplies none) | least `n₀` with `N_n^{-ε'} < κ'` for all `n ≥ n₀`: `5` (`N_4 = 8.0e18`, `N_5 = 2.13e20`) | `N > κ'^{-1/ε'} = 1.0737e19` | `N_5/1.0737e19 = 19.8`; the base-case data (`n=0`, `N=2^21`) is not affected: the modification only changes indices `< n₀` |
| 7 | step constant `𝔠d` (inside pin 1), `μ = min(2𝔠𝔡, ε/2)`, chain length `K` (`stChainSteps`, `MainIndChain:80`) | `𝔠d = 1/100`, `μ = 1/30`, `K = 6000` | `0<𝔠d≤1/100`; `2 ≤ K 𝔠d μ`; eventually `N^{𝔠d μ/2} ≥ 2^{𝔠d}` ⟺ `N ≥ 2^{2/μ} = 2^60 = 1.15e18` | `K 𝔠d μ = 2` (slack 0 at `K=6000`, any `K>6000` is positive); `sz0`: `N_n ≥ 2^60` from `n ≥ 4` (`N_4 = 8.0e18`, ratio 6.9) |
| 8 | horizon (target 10; `CltFlowBA_one_sub_T0`, `CltFlowBA:543`): `1 - T0 ≥ Im z/2` (`EMn2BA_one_sub_T0`, uses `Im m ≤ 1` `EMn2BA:99`, `Im z ≤ 1`) and `N^{ε/2} ≥ 2` | `N ≥ 2^{2/ε} = 2^20` | gives `N^{-1+ε/2} ≤ 1-T0` eventually; `0<T0<1` from `Im m, Im z > 0` | `N_0 = 2^21 = 2·2^20`; `1-T0 ≥ 0.3056` vs `N^{-0.95} ≤ 2^{-19.95}` |
| 9 | target 4: `c₁` of `BAWinBulk_of_dom_holds` at `(κ, Λ) = (1/2, 𝔡⁻¹ = 10)`, `c₁ = min(1/2, κ⁹/(64 d Λ))` (`CouplingWindow:692`) | `1/983040 = 1.0173e-6` | `0<c₁≤1/2`; needs `0<lam_n≤Λ` and `BAdom` at `κ=1/2` for all `n` (`flow_sz0`) | the output window is at `κ/2 = 1/4`; the window at `c₁ = 1/3` of row 3 contains the window at `c₁ = 1.0e-6` |
| 10 | target 4/5: tail `sz.comp(·+n₀)`, `n₀` from `WO` (`hflow.1.2.2.2.2`) | `n₀ = 3` (any `n₀ ≥ 0` works for `sz0`: row 2 holds at every `n`) | `lam_{j+n₀} ∈ (0, 𝔡⁻¹]`; flow at `κ/2 = 1/4 ≤ κ`: `(1/4) ≤ Im m ≥ 4/5` | `Im m ≥ 0.8325` vs `1/4` |
| 11 | target 7 `G_0 = M` (`Boot_GM_zero`, `Step1Boot:358`, `FlowFM.GM = G - M` `Chain/Carrier.lean:76`) | no constant | statement is `∀ (lam0 E n ω x y)`, no hypothesis | n/a |
| 12 | target 8 `𝓛_0 = 𝒦_0`, per index class (fill-in (iii)) | see below | see below | see below |
| 13 | `d` | instance `3`; pins for every `d` with `3 ≤ d →` | `BAMainIndFamTL d R` is a hypothesis of 6, 11; its `d>3` instances are outside V3 (Jun decision B, ticket) | n/a |

**Row 12, `STLK0` by index class** (`BAflow_real`, `GreenSchur:59`: `BAReal d L g₀ κ E m_F` at every `n`; `BAdom_real`, `MFixedPoint:479`, has no sign hypothesis on `κ`; `BASelf` carries `0 < m.im`, `MFixedPoint:193`).
- `g₀ n > 0`: `GridGoodBA_KI_init` (`GridGoodBA:603`, needs `0 < lam0 n`) would serve; not used.
- `g₀ n ≤ 0` (at finitely many `n` possibly: `BAFlow` gives `WO` only eventually, and `T2504_LK0` has no `0<κ`): `GridGoodBA_loopFine_init` (`:566`, hypothesis `0 < (BAmF ..).im` only), `GridGoodBA_BAMLoop_one_loop` (`:591`, hypothesis `BASelf` only), `CltFlowBA_Ksol_isKLoopS` (`CltFlowBA:362`, hypothesis `BAReal d L g κ E m` only; comment "no `0 < g`"). Every hypothesis of the three is available at every `n` from `BAflow_real`. No source is missing: the ticket's stop rule (answer (5)) does not trigger.

**Family-premise table** (fill-in (iv); guards read from the `T2504_*` pins): `BAMainIndFamTL`: guard `3 ≤ d`, `∃ 𝔠d` after `(κ, ε, 𝔡)`, `𝔠d ≤ 1/100`, inner `∀ c₁ ∈ (0,1/2]` (not `∃`); `STHorizonG`/`STBaseG`: `0<κ`, `0<ε` (`STBaseG` also `0<𝔡`, `MainIndBase:58`) `→ Flow →`; `STG0M`, `STLK0`: `Flow →`, no sign guard; `STKboundgL` (`BAKbound`): `0<κ,ε,𝔡`; `BATwistLoopBase`: `3 ≤ d`, `STG0M →`; no new `∃`, no `∀ n` drift.
**UBA-C1** (fill-in (v)): size level (`sz.lam`): `0<lam≤𝔡⁻¹` on the tail (row 10), `Im m(z,lam) ≤ 1`, `1-T0 ≥ Im z/2` (row 8); kernel level (`g₀`): `G_0=M`, `𝓛_0=𝒦_0` (rows 11, 12), window at `κ/2` (row 9), `STKboundgL`; crossing: none.
**Constants before/after `(sz, z)`** (fill-in (i)): before: `c₁` (`∃ c₁` of target 4 after `(κ, 𝔡)`; `∀ c₁` in pin 1), `κ', ε'` (after `(κ, ε, 𝔡)`), `𝔠d`; inside proofs: `n₀`, `K` (after `𝔠d, ε, 𝔠, 𝔡`; `K` depends on `𝔠d min(2𝔠𝔡, ε/2)`), `C`.
**M/N shape** (fill-in (x), closing (iii)): `grep -n '∀ d : ℕ, UNMLOutBA d'` hits `BA/UNPins.lean:124, 143, 370, 1027, 1041, 1053, 1066`, `BA/EMCTE2BA.lean:943, 953, 961`, `BA/RandomLayerBGBA.lean:207`; `ba_mlout` (`RandomLayerBGBA:115`) and `inst_UNMLOutBA` (`UNPins:1015`) take `UNMLOutBA d` with `3 ≤ d` / at `3`. Only `UNMLOutBA 3` is unconditional under §316; reported, not a stop (answer (7)).
Moved to the 1b head (ticket fill-in (vi), (vii), (viii) and 0149 `:98`): registry scan preview, line counts, name-clash grep.

### (ii) One nondegenerate instance (`d = 3`, every `n`, no `N = 0`)
Hypotheses of every target at once: `sz0`, `zSeq n = z_S(L_n, lam_n)` (`z_S = w - m_w`, `w = 6i/5`, `m_w = L^{-3} tr(lam Ψ - w)^{-1}`, `Ψ` the ℓ¹ nearest-neighbour adjacency `Defs/Lattice.lean:108`); `(κ, ε, 𝔠, 𝔡) = (1/4, 1/10, 1/6, 1/10)`; `c₁ = 1/3`; `s ≡ 1/10`, `t ≡ 1/2`, `t ≡ 0`; non-main member `BAzSrc sz0 zSeq (2/3) (17/25)`; target 4 at `κ = 1/2`, `n₀ = 3`; target 5 at `n₀ = 3`, `τ ≡ 1/2`; targets 7–10 hypothesis-free; the family step the one hypothesis of 6, 11 and of the step-use examples. Script: spectrum of `Ψ` from `2Σcos(2πk_i/L)`, `m` at `(g', E)` by the fixed point of `(self_m)`; `n = 0..15` computed (`L ≤ 64`, `N ≤ 1e28`); `n > 15` by the closed forms `Im m_S ≥ 1.2/(1.44 + lam²L³)`, `lam²L³ = (n+1)^{-9}/64`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2504/inst.py`
```
n= 0 L=  4 W=32 N=2.097e+06 lam=1.562e-02 ImmS=0.83249 Imz=0.36751 T0=0.69374 minImm_win=0.99949 res=4.4e-16 fails=[]
n= 1 L=  8 W=1024 N=5.498e+11 lam=2.441e-04 ImmS=0.83333 Imz=0.36667 T0=0.69444 minImm_win=1.00000 res=4.4e-16 fails=[]
n= 2 L= 12 W=7776 N=8.125e+14 lam=2.143e-05 ImmS=0.83333 Imz=0.36667 T0=0.69444 minImm_win=1.00000 res=3.3e-16 fails=[]
n= 5 L= 24 W=248832 N=2.130e+20 lam=3.349e-07 ImmS=0.83333 Imz=0.36667 T0=0.69444 minImm_win=1.00000 res=2.2e-16 fails=[]
n=10 L= 44 W=5153632 N=1.166e+25 lam=8.820e-09 ImmS=0.83333 Imz=0.36667 T0=0.69444 minImm_win=1.00000 res=1.1e-16 fails=[]
n=15 L= 64 W=33554432 N=9.904e+27 lam=9.313e-10 ImmS=0.83333 Imz=0.36667 T0=0.69444 minImm_win=1.00000 res=1.8e-25 fails=[]
all checks n=0..15: True
n->inf: Im mS -> 5/6=0.83333, Im zS -> 11/30=0.36667, T0 -> 25/36=0.69444 >= 17/25=0.68000; Im m(0,0)=1 >= 1/4
n=0 bound Im mS >= 0.82439, T0 >= 0.68699 (17/25=0.68)
c_kappa=0.447214 kappa'=0.111803 eps'=0.050  kappa'^(-1/eps')=1.0737e+19
least n0 with N_n^(-eps') < kappa' for all n>=n0: 5  N_4=8.0000e+18  N_5=2.1299e+20
mu=1/30  K>=6000  K*cd*mu=2>=2; N>=2^(2/mu)=2^60=1.153e+18
sz0: N_n >= 2^(2/mu) for all n >= 4 (N_4=8.0000e+18)
horizon: N^(eps/2)>=2 <=> N>=2^(2/eps)=2^20=1048576; N_0=2097152=2^21 (slack factor 2)
target 4: c1 = min(1/2, (1/2)^9/(64*3*10)) = 1/983040 = 1.0173e-06; tail n0=3: lam_j=(2(j+4))^-6>0 and <=10, flow at kappa/2=1/4 <= Im m (>=4/5)
target 3 constants: c1=1/3<=1/2; s=1/10<t=1/2<=T0 (T0>=25/36*... min T0 above >=0.68); mem. u=17/25<=max(T0,2/3): T0>=17/25
```
Each `fails=[]` covers the script's checks: `L ≥ 3`, `N^{1/6} ≤ W`, `W^{-1.4} ≤ lam ≤ 10`, `1/4 ≤ Im m_S`, `N^{-0.9} ≤ Im z ≤ 1`, `17/25 ≤ T0 < 1`, `Im m ≤ 1`, `1-T0 ≥ Im z/2`, `N^{-0.95} ≤ 1-T0`, window at `c₁ = 1/3` (17 points `g'`, residual of `(self_m)` `< 1e-9`).
Scope of the script: it checks the numerical inequalities behind `flow_sz0`/`sz0_win_third`/`t0_sz0_ge` at the weakened `κ = 1/4`; the compiled Lean facts (`FlowPinsInst.flow_sz0 :1214`, `Step1FamInst.sz0_win_third :802`, `inst_BAFamZ_closed :820`, `half_lt_t0 :1254`) are the Lean witnesses of the same inequalities and are the ones the instances use (the probe `t/T2503:RBM3D/Probe/T2503Pins.lean:310-391` uses them at the premises above; the ticket states that it compiled).
External hypothesis (the family step `BAMainIndFamTL`, another gate's pin, not yet proved): its limit data at the instance are rows 7–8: `𝔠d = 1/100`, `K = 6000`, `N_n^{1/6000} ≥ 2^{1/100}` (`N_n ≥ 2^60`) for `n ≥ 4`, `N_n^{-0.95} ≤ 1-T0_n` for all `n ≤ 15` (closed form for larger `n`: `N_n^{-0.95} ≤ 2^{-19.95}` vs `1-T0 ≥ 0.3056`), `T0 → 25/36`, `Im m_S → 5/6`, `Im z_S → 11/30` as `n → ∞` (script output: `all checks`, `n->inf`, `mu=1/30`, `sz0: N_n >= 2^(2/mu)` lines); the step is a hypothesis of the instances, as the ticket and CLAUDE.md §4 step 2 allow.

### Verdict per target
1 (`BAMainIndFamTL` def): PASS (statement = T2503 binding text via `T2504_BAMainIndFamTL`; no hypothesis set involved).
2 (`BATwistLoopLaw_congr`, `baFamMember_flow`): PASS (rows 5–6).
3 (`baFamMember_base`): PASS (rows 1, 3–6, 11).
4 (`baTailPassage`): PASS (rows 9–10).
5 (`baConclShift`): PASS (row 10; no numerical constant).
6 (`baChainFamTL_holds`): PASS (rows 3–4, 7–8, 10; premises 1–7 of the family table).
7 (`baG0M_holds`): PASS (row 11).
8 (`baLK0_holds`): PASS (row 12: BAReal-only route at every `n`).
9 (`stBaseG_of_init'`, `baBaseG_holds`): PASS (`stBaseG_of_init`, `MainIndBase:110`, at the setting `0<ε ∧ 0<𝔡 ∧ Flow`; `STBaseG` supplies `0<ε`, `0<𝔡` as hypotheses, so the setting holds at every use).
10 (`baHorizonG_holds`): PASS (row 8).
11 (`baMLOutTL_of_famStep`, `unMLOutBA_of_BAMLOutTL`, `unMLOutBA_of_famStep`): PASS.
12 (instances): PASS at the numbers of (ii).
No target and no row changes: no 1a-audit needed. Overall verdict: PASS.

### (b) Script output (stage 1b, `Wed Oct 14 08:05:35 UTC 2026`; branch `t/T2504`, head 43f2230d, 4 commits on 41e55513; scripts and raw outputs in `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2504`)

**(1) Size.** `wc -l RBM3D/BA/MainIndOutBA.lean` = 430 (design 240 / 395 / 766; ticket central ≈ 435; stop line 766 not reached). Script, lines per section: header+imports+docstring+opens 1-54; §1 def 21; §2 TL2 congruence + member flow 32; §3 member base, tail passage, shift 67; §4 chain 72; §5 `G_0 = M`, `𝓛_0 = 𝒦_0`, base, horizon 65; §6 terminal outputs 17; §7 instances 102.

**Build.** `lake build RBM3D.BA.MainIndOutBA` (tail): `Build completed successfully (4154 jobs).`  Full `lake build` after all edits (started 07:54:21Z, ended 08:00:06Z, exit 0; the tree built is the content of commit 43f2230d: `git status --short` in the worktree is empty after the commit and no file changed between build and commit), tail and `#assert_rbm_axioms` lines:
```
Build completed successfully (4386 jobs).
exit 0 (and: "info: RBM3D.lean:616:0: axiom audit: 15184 theorems, 4697 definitions, 0 axioms in `RBM`")
```
**Axioms** (`lake env lean $S/axioms.lean | sed "s/ depends on axioms:/:/"`, a `#print axioms` of the 15 new public declarations):
```
'RBM.BA.BAMainIndFamTL': [propext, Classical.choice, Quot.sound]
'RBM.BA.BATwistLoopLaw_congr': [propext, Classical.choice, Quot.sound]
'RBM.BA.baFamMember_flow': [propext, Classical.choice, Quot.sound]
'RBM.BA.baFamMember_base': [propext, Classical.choice, Quot.sound]
'RBM.BA.baTailPassage': [propext, Classical.choice, Quot.sound]
'RBM.BA.baConclShift': [propext, Classical.choice, Quot.sound]
'RBM.BA.baChainFamTL_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.baG0M_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.baLK0_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.stBaseG_of_init'': [propext, Classical.choice, Quot.sound]
'RBM.BA.baBaseG_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.baHorizonG_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.baMLOutTL_of_famStep': [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_BAMLOutTL': [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_famStep': [propext, Classical.choice, Quot.sound]
```
**Targets, statements extracted from the file by script** (`python3 -I $S/stmts.py`; `line: statement`, whitespace collapsed):
```
60: def BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t → (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' → let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0) STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) → sz.STConStInd 𝔠d s t → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0) STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t
79: theorem BATwistLoopLaw_congr (d : ℕ) (sz : Sizes d) (C C' : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) (h : FlowFM.EvEq C C') : BATwistLoopLaw C μ τ ↔ BATwistLoopLaw C' μ τ
90: theorem baFamMember_flow (d : ℕ) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → (∀ n, t n ≤ BAflowT0 sz z' n) ∧ ∃ z'' : ℕ → ℂ, BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧ (∀ n, t n ≤ BAflowT0 sz z'' n) ∧ FlowFM.EvEq (baFMz sz z'') (baFMz sz z')
112: theorem baFamMember_base (d : ℕ) (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' → STConclgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 0) ∧ BATwistLoopLaw (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 0)
128: theorem baTailPassage (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∃ n₀ : ℕ, BAFlow (sz.comp (· + n₀)) (κ / 2) ε 𝔠 𝔡 (fun j => z (j + n₀)) ∧ (∀ j, 0 < (sz.comp (· + n₀)).lam j) ∧ BAWinBulk (sz.comp (· + n₀)) (fun j => z (j + n₀)) c₁ (κ / 2)
155: theorem baConclShift {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (n₀ : ℕ) : let C₁ := baFMz (sz.comp (· + n₀)) (fun j => z (j + n₀)); let μ₁ := seqP ((sz.comp (· + n₀)).withLam 0) let τ₁ : ℕ → ℝ := fun j => τ (j + n₀) (STLKgL C₁ μ₁ τ₁ ∧ STLmaxgL C₁ μ₁ τ₁ ∧ STDecaygL C₁ μ₁ τ₁ ∧ STExp2gL C₁ μ₁ τ₁ ∧ STLocalEntrygL C₁ μ₁ τ₁ ∧ STDecayStronggL C₁ μ₁ τ₁ ∧ BATwistLoopLaw C₁ μ₁ τ₁) → let C := baFMz sz z; let μ := seqP (sz.withLam 0) STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧ STDecayStronggL C μ τ ∧ BATwistLoopLaw C μ τ
216: theorem baChainFamTL_holds (d : ℕ) (hmain : BAMainIndFamTL d STAny) (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z)) (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) (hTL : BATwistLoopBase d) (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : BAMLOutTL d
250: theorem baG0M_holds (d : ℕ) : ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)
268: theorem baLK0_holds (d : ℕ) : ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STLK0 (baFMz sz z)
286: theorem stBaseG_of_init' {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} (hprob : ∀ sz, IsProbabilityMeasure (law sz)) (hL : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STLK0 (mk sz z)) (hG : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STG0M (mk sz z)) (hK : 3 ≤ d → ∀ κ ε 𝔠 𝔡 sz z, 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) : STBaseG d law Flow mk
300: theorem baBaseG_holds (d : ℕ) : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz
307: theorem baHorizonG_holds (d : ℕ) : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z)
315: theorem baMLOutTL_of_famStep (d : ℕ) (hmain : BAMainIndFamTL d STAny) : BAMLOutTL d
320: theorem unMLOutBA_of_BAMLOutTL (d : ℕ) (h : BAMLOutTL d) : Univ.UNMLOutBA d
326: theorem unMLOutBA_of_famStep (d : ℕ) (hmain : BAMainIndFamTL d STAny) : Univ.UNMLOutBA d
```
**Statements against the pins** (check compiles on the branch: `lake env lean docs/tickets/checks/T2504-check.lean` exit 0, 0 error lines; uncommitted scratch = the check + `import RBM3D.BA.MainIndOutBA` + the `example` lines below (prefix `RBM.BA.` stripped, `example` dropped, lines joined by `;` and folded to 180 columns), `lake env lean $S/pins_scratch.lean` exit 0, 0 error lines):
```
: T2504_TL2Congr := BATwistLoopLaw_congr;(d : ℕ) : T2504_MemberFlow d := baFamMember_flow d;(d : ℕ) : T2504_MemberBase d := baFamMember_base d;(d : ℕ) : T2504_TailPassage d := 
baTailPassage d;: T2504_ConclShift := @baConclShift;(d : ℕ) : T2504_BAChainFamTL d := baChainFamTL_holds d;(d : ℕ) : T2504_G0M d := baG0M_holds d;(d : ℕ) : T2504_LK0 d := 
baLK0_holds d;: T2504_BaseGInit' := @stBaseG_of_init';(d : ℕ) : T2504_BaseGBA d := baBaseG_holds d;(d : ℕ) : T2504_HorizonGBA d := baHorizonG_holds d;(d : ℕ) : T2504_MLOutOfStep d 
:= baMLOutTL_of_famStep d;(d : ℕ) : T2504_UNOfMLOut d := unMLOutBA_of_BAMLOutTL d;(d : ℕ) : T2504_UNOfStep d := unMLOutBA_of_famStep d;(d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → 
(ℕ → ℝ) → (ℕ → ℝ) → Prop) :     T2504_BAMainIndFamTL d R ↔ BAMainIndFamTL d R := Iff.rfl;: Prop := T2504_BAMainIndFamTL 3 RBM.Gauss.Sizes.STAny
```
Text diff of the def (script `$S/bind.py`, prefixes `RBM.BA.`, `RBM.Gauss.`, `Sizes.` stripped, whitespace collapsed): `BAMainIndFamTL` vs `T2504_BAMainIndFamTL` (T2504-check): 15 vs 15 lines, 0 diff lines; vs `T2503_BAMainIndFamTL` (T2503-check): 0 diff lines; vs the probe `t/T2503:RBM3D/Probe/T2503Pins.lean` `def T2503_BAMainIndFamTL` (probe lines 33-47, 15 lines): 0 diff lines.  Differences from the probe statements: the probe `T2503_TL2Congr`, `T2503_MemberFlow`, `T2503_BAChainFamTL` defs are unfolded into the theorem statements (new file has one def); names `T2503_*` → pinned names; the probe's `T2503_baChainFamTL : T2503_BAChainFamTL d` is stated here with the explicit hypotheses of the pin (no `BAChainFamTL` def).

**Compiled nonempty instances** (target 12; `python3 -I $S/inst.py`, section 7 of the file, one line per `example`/helper; `μ0`, `mem0` are `local notation` for `Sizes.seqP (sz0.withLam 0)`, `BAzSrc sz0 zSeq (fun _ => 2/3) (fun _ => 17/25)`):
```
343: private theorem MainIndOutBA_flow : BAFlow sz0 (1 / 4) (1 / 10) (1 / 6) (1 / 10) zSeq := ⟨flow_sz0.1, fun n => ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (flow_sz0.2 n).1, (flow_sz0.2 n).2⟩⟩
346: private theorem MainIndOutBA_win : BAWinBulk sz0 zSeq (1 / 3) (1 / 4) := fun n g h1 h2 => (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans (sz0_win_third n g h1 h2)
349: private theorem MainIndOutBA_mem (u : ℝ) (hu : max u (1 - 1 / 3) ≤ max (2 / 3) (1 - 1 / 3)) : BAFamZ sz0 zSeq (1 / 3) (fun _ => u) mem0 := BAFamZ_mono_max sz0 zSeq (1 / 3) _ (fun _ => 2 / 3) _ (fun _ => hu) inst_BAFamZ_closed
353: -- targets 7, 8: `G_0 = M` and `𝓛_0 = 𝒦_0` at `zSeq` (hypothesis-free)
354: example : STG0M (baFMz sz0 zSeq) := baG0M_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq MainIndOutBA_flow
355: example : STLK0 (baFMz sz0 zSeq) := baLK0_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq MainIndOutBA_flow
357: -- target 9 (a): the generic `stBaseG_of_init'` at the BA data and at `zSeq`
358: example : STConclgL (baFMz sz0 zSeq) μ0 (fun _ => 0) := stBaseG_of_init' (law := fun sz => Sizes.seqP (sz.withLam 0)) (Flow := fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (mk := baFMz) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baLK0_holds 3) (baG0M_holds 3) (fun hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hf => baKbound_holds 3 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow
364: -- target 9 (b): the six conclusions at the zero sequence at `zSeq`
365: example : STConclgL (baFMz sz0 zSeq) μ0 (fun _ => 0) := baBaseG_holds 3 le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow
368: -- target 10: admissible sizes, `0 < T₀ < 1`, `N^{-1+ε/2} ≤ 1 - T₀` eventually, at `zSeq`
369: example : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, 0 < BAflowT0 sz0 zSeq n ∧ BAflowT0 sz0 zSeq n < 1) ∧ ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-1 + (1 / 10 : ℝ) / 2) ≤ 1 - BAflowT0 sz0 zSeq n := baHorizonG_holds 3 (1 / 4) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) (by norm_num) MainIndOutBA_flow
373: -- target 2 (a): TL2 at `zSeq` and at its finite modification `zMod` (`zMod_ev`: equal for `n ≥ 3`)
374: example (μ : Measure sz0.SeqΩ) (τ : ℕ → ℝ) : BATwistLoopLaw (baFMz sz0 zSeq) μ τ ↔ BATwistLoopLaw (baFMz sz0 zMod) μ τ := BATwistLoopLaw_congr 3 sz0 _ _ μ τ (zMod_ev.mono fun n hn => baFMz_eqAt sz0 hn)
378: -- target 2 (b): the non-main member of `Fam(1/2)` as a flow at `(κ', ε')` after the finite modification, horizon `≥ 1/2`, `EvEq`
379: example : ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ 1 / 4 ∧ 0 < ε' ∧ ε' ≤ 1 / 10 ∧ (∀ n, 1 / 2 ≤ BAflowT0 sz0 mem0 n) ∧ ∃ z'' : ℕ → ℂ, BAFlow sz0 κ' ε' (1 / 6) (1 / 10) z'' ∧ (∀ n, 1 / 2 ≤ BAflowT0 sz0 z'' n) ∧ (baFMz sz0 z'').EvEq (baFMz sz0 mem0) := by obtain ⟨κ', ε', h1, h2, h3, h4, H⟩ := baFamMember_flow 3 (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) exact ⟨κ', ε', h1, h2, h3, h4, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) mem0 (MainIndOutBA_mem _ (by norm_num))⟩
385: -- target 3: the per-member base at the non-main member of `Fam(0)` (hypothesis-free; `baBaseG_holds`, `baG0M_holds` discharge `hbase`, `hG`)
386: example : STConclgL (baFMz sz0 mem0) μ0 (fun _ => 0) ∧ BATwistLoopLaw (baFMz sz0 mem0) μ0 (fun _ => 0) := baFamMember_base 3 (baBaseG_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win mem0 (MainIndOutBA_mem 0 (by norm_num))
390: -- target 4: the tail of `sz0` along `zSeq` at `κ = 1/2` (`flow_sz0`): flow at `κ/2`, window at `κ/2`
391: example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ n₀ : ℕ, BAFlow (sz0.comp (· + n₀)) (1 / 2 / 2) (1 / 10) (1 / 6) (1 / 10) (fun j => zSeq (j + n₀)) ∧ (∀ j, 0 < (sz0.comp (· + n₀)).lam j) ∧ BAWinBulk (sz0.comp (· + n₀)) (fun j => zSeq (j + n₀)) c₁ (1 / 2 / 2) := by obtain ⟨c₁, h0, h1, H⟩ := baTailPassage 3 le_rfl (1 / 2) (1 / 10) (by norm_num) (by norm_num) obtain ⟨n₀, hf, hl, hw⟩ := H (1 / 10) (1 / 6) sz0 zSeq flow_sz0 exact ⟨c₁, h0, h1, n₀, hf, hl, hw⟩
397: -- target 5: the seven conclusions along the tail (`n₀ = 3`, `τ ≡ 1/2`) give the seven along `sz0`; the seven at the tail are the hypothesis
398: example (h : let C₁ := baFMz (sz0.comp (· + 3)) (fun j => zSeq (j + 3)); let μ₁ := Sizes.seqP ((sz0.comp (· + 3)).withLam 0) STLKgL C₁ μ₁ (fun _ => 1 / 2) ∧ STLmaxgL C₁ μ₁ (fun _ => 1 / 2) ∧ STDecaygL C₁ μ₁ (fun _ => 1 / 2) ∧ STExp2gL C₁ μ₁ (fun _ => 1 / 2) ∧ STLocalEntrygL C₁ μ₁ (fun _ => 1 / 2) ∧ STDecayStronggL C₁ μ₁ (fun _ => 1 / 2) ∧ BATwistLoopLaw C₁ μ₁ (fun _ => 1 / 2)) : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STExp2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STDecayStronggL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) := baConclShift sz0 zSeq (fun _ => 1 / 2) 3 h
407: -- target 6: `BAMLOutTL 3` at `t ≡ 1/2` and at `t ≡ 0` (the class mixed with the chain to `T₀/2`); the family step is the one hypothesis
412: example := baChainFamTL_holds 3 hm (baHorizonG_holds 3) (baBaseG_holds 3) (baTwistLoopBase_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
415: example := baChainFamTL_holds 3 hm (baHorizonG_holds 3) (baBaseG_holds 3) (baTwistLoopBase_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])
419: -- target 11: the terminal plug-in, the projection and the composite at the data
420: example := baMLOutTL_of_famStep 3 hm le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
422: example := unMLOutBA_of_BAMLOutTL 3 (baMLOutTL_of_famStep 3 hm) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
424: example := unMLOutBA_of_famStep 3 hm le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])
```
**Routes** (target@file line: merged names@file:line; `python3 -I $S/routes.py`; `open private` list = the 5 lines of the greps below):
```
BATwistLoopLaw_congr@79: PrecL_congr@BA/Step1Boot.lean:185, twL2'@BA/TwistPins.lean:70, twK@BA/TwistPins.lean:76, twMB@BA/TwistPins.lean:73
baFamMember_flow@90: BAFlowMember_holds@BA/Step1Fam.lean:624, BAFamZ_mono@BA/Step1Boot.lean:173, BAFamZ_horizon@BA/Step1Boot.lean:179, BAflowT0_congr@BA/Step1Fam.lean:74, baFMz_eqAt@BA/Step1Fam.lean:273
baFamMember_base@112: STLKgL_congr@BA/Step1Fam.lean:205, STDecayStronggL_congr@BA/Step1Fam.lean:223, baTwistLoopBase_holds@BA/TwistChain.lean:110, BAflow_T0_bounds@BA/Step1Trivial.lean:47
baTailPassage@128: BAWinBulk_of_dom_holds@BA/CouplingWindow.lean:836, comp_admissible@Induction/SizesComp.lean:93
baConclShift@155: stochDomAt_iff_comp_cover@Induction/SizesComp.lean:536, seqP_withLam_reindex_preimage@Induction/SizesComp.lean:239, integral_reindex@Induction/SizesComp.lean:253
baChainFamTL_holds@216: stChainTime_facts@Induction/MainIndChain.lean:62, stChainSteps@Induction/MainIndChain.lean:80, STLocalMaxgL_of_STLocalEntrygL@Induction/MainIndChain.lean:126, BAFamZ_main@BA/Step1Trivial.lean:56, TwistChain_LK_mix(private)@BA/TwistChain.lean:194, TwistChain_TL2_mix(private)@BA/TwistChain.lean:226
baG0M_holds@250: Boot_GM_zero(private)@BA/Step1Boot.lean:358
baLK0_holds@268: BAflow_real@BA/GreenSchur.lean:59, GridGoodBA_loopFine_init(private)@BA/GridGoodBA.lean:566, GridGoodBA_BAMLoop_one_loop(private)@BA/GridGoodBA.lean:591, CltFlowBA_Ksol_isKLoopS(private)@BA/CltFlowBA.lean:362
stBaseG_of_init'@286: stBaseG_of_init@Induction/MainIndBase.lean:110
baBaseG_holds@300: baKbound_holds@BA/KBound.lean:245, isProbabilityMeasure_seqP@Gauss/FineModel.lean:171
baHorizonG_holds@307: BAflow_T0_bounds@BA/Step1Trivial.lean:47, CltFlowBA_one_sub_T0(private)@BA/CltFlowBA.lean:543
baMLOutTL_of_famStep@315: baChainFamTL_holds@MainIndOutBA:216
unMLOutBA_of_BAMLOutTL@320: 
```
**Greps** (hypothesis rules; `$S/greps.out`):
```
$ grep -nE 'BAK_le_small|BAMB_upper_small|Mbound_AO|W\^\(-eps|BAm_im_lower_window|\|E\||norm_mE|mSigma|SB d|E2Hyp|STGridRepNgL' RBM3D/BA/MainIndOutBA.lean
(no hit)
$ grep -nE '^(noncomputable )?(def|abbrev|structure) ' RBM3D/BA/MainIndOutBA.lean | cut -c1-60
60:def BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ →
$ grep -nE '(def|abbrev|structure|theorem) (BAFamZ|BAFlowMember|BAStep1|STBaseG|STHorizonG|STConclgL|BAMLOutTL|UNMLOutBA|[A-Za-z_]*_zero)' RBM3D/BA/MainIndOutBA.lean | cut -c1-80
256:private theorem MainIndOutBA_hflow_zero {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ
$ grep -nE 'T250[34]_' RBM3D/BA/MainIndOutBA.lean
(no hit)
$ grep -n -A1 '^open private' RBM3D/BA/MainIndOutBA.lean | cut -c1-120
49:open private TwistChain_LK_mix TwistChain_Lmax_mix TwistChain_Decay_mix TwistChain_Exp2_mix TwistChain_LocalEntry_mix
50-  TwistChain_TL2_mix from RBM3D.BA.TwistChain
51:open private Boot_GM_zero from RBM3D.BA.Step1Boot
52:open private GridGoodBA_loopFine_init GridGoodBA_BAMLoop_one_loop from RBM3D.BA.GridGoodBA
53:open private CltFlowBA_Ksol_isKLoopS CltFlowBA_one_sub_T0 from RBM3D.BA.CltFlowBA
54-
$ grep -n withLam RBM3D/BA/MainIndOutBA.lean | grep -v 'seqP (' ; grep -n '\.comp' RBM3D/BA/MainIndOutBA.lean | grep -v 'comp (· + '
151:    (fun _ s => seqP_withLam_reindex_preimage sz _ 0 (MainIndOutBA_shift_mono n₀).inje
172:    (Sizes.integral_reindex (sz.withLam 0) (· + n₀) (MainIndOutBA_shift_mono n₀).injec
259:  have h : (sz.withLam 0).seqHflow n 0 ω i j = 0 := by
260:    have h0 : (sz.withLam 0).seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
138:    ⟨Sizes.comp_admissible sz _ 𝔠 𝔡 (tendsto_add_atTop_nat n₀) hflow.1, fun j => hflow.2 (j + n₀)⟩
```
Labels: the `*_zero` hit is `MainIndOutBA_hflow_zero`, a private helper under the stem, a copy of the inline `hH` step of `Boot_GM_zero` (`Step1Boot:360`), not one of `MainIndBase`'s private `*_zero`.  The `withLam` hits at 151, 172, 259-260 and the `comp` hit at 138 are in proofs (a lemma name; `(sz.withLam 0)` as an argument), not in statements; every `withLam` in a statement is `seqP (… .withLam 0)` and every `comp` in a statement is `(· + n₀)`.

**Name clash** (`$S/clash.sh`: `grep -rwF --include=*.lean` of the 15 public names and of the stem `MainIndOutBA_` over `RBM3D RBM3D.lean`, excluding the new file and `Test/Axioms.lean`): 0 hits for each, except `BAMainIndFamTL`: 1 hit, the comment `RBM3D/BA/TwistPins.lean:168`.

**Diff scope** (`git diff --name-only main...t/T2504`): `RBM3D.lean`, `RBM3D/BA/EMn2BA.lean`, `RBM3D/BA/LWPinsBA.lean`, `RBM3D/BA/MainIndOutBA.lean`, `RBM3D/Test/Axioms.lean` (merge-base 41e55513).  `git diff --stat main...t/T2504 -- RBM3D/Chain RBM3D/Induction RBM3D/Graph` empty; no other `RBM3D/BA/*` file changed; `grep -rln RBM3D.BA.MainIndOutBA RBM3D RBM3D.lean` = `RBM3D.lean` only.  Script `$S/scope.py` (comments stripped from the merge-base and branch versions): `LWPinsBA.lean`: changed lines [20, 50, 52], code identical after stripping comments: True, line count 112 = 112; `EMn2BA.lean`: changed line [124], code identical: True, 1091 = 1091 (counts of `split("\n")`).  `RBM3D.lean`: +1 import line after the last import (`import RBM3D.BA.MainIndOutBA`).

**Registry** (`RBM3D/Test/Axioms.lean`; diff of `git diff -U0 main...t/T2504`, cut to 118 columns; scan output `$S/reg.py` on the full builds before (unedited tree, `lake build` finished 07:53:28Z by file mtime) and after):
```
-   -- T2340 (ST-6 R1-R3, DECISIONS §151): carrier facts of the final assembly; the band instances are proved there (`
-   `RBM.BA.STLK0, -- `𝓛_0 = 𝒦_0` (`1_2:1240-1243`) over a flow carrier; band: `azumaProxy_loopFine_sub_STKloop`; BA: 
-   `RBM.BA.STG0M, -- `G_0 = M` (`1_2:1240`) over a flow carrier; band: `lwExpTerm3_Gt_zero`; BA: BA-V `GLoopAtT0`
-   `RBM.BA.STBaseG, -- the six conclusions of `lem:main_ind` at the zero sequence over a carrier; band: `stBase_band`
-   `RBM.BA.STHorizonG, -- admissible sizes, `0 < T0 < 1` and `N^{-1+ε/2} ≤ 1 - T0` eventually; band: `stHorizon_band`
+   -- T2340 (ST-6 R1-R3, DECISIONS §151): carrier facts of the final assembly; the band instances are proved there (`
-   `RBM.BA.STMainIndG, -- `lem:main_ind` over a carrier `(law, Flow, mk, T0)` (`BA/FlowPins.lean:434`), hypothesis of
+   `RBM.BA.STMainIndG, -- `lem:main_ind` over a carrier `(law, Flow, mk, T0)` (`BA/FlowPins.lean:434`), hypothesis of
+   `RBM.BA.BAMainIndFamTL, -- the family step of the BA main induction (`lem:main_ind_BA` on `Fam(u)`, `7_8:1954-1990
-   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`)
+   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`); `UNMLOutBA` left this 
-   `RBM.Univ.UNMLOutBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-V3, `lem:main_ind_BA` out
before: registry: 2 borrowed + 122 owed + 138 structural + 7 refuted + 19 superseded; 144 registered premise(s) carry nothing yet   (premises found by scanning: 144; owed found 65)
after : registry: 2 borrowed + 118 owed + 138 structural + 7 refuted + 19 superseded; 141 registered premise(s) carry nothing yet   (premises found by scanning: 144 → 143; owed found 65 → 64)
diff of the "carry nothing" lists (before vs after): 22,23d21 < RBM.BA.STBaseG < RBM.BA.STHorizonG ; 43d40 < RBM.Univ.UNMLOutBA   (the other 141 names unchanged)
ledger lines before: STLK0: 1, STG0M: 1, STBaseG: 5, STHorizonG: 4, UNMLOutBA: 11 theorems resting; after: none of the five; new: RBM.BA.BAMainIndFamTL: 3 [no certificate]
```

**(5) `STLK0` per index class.**  `baLK0_holds` has no index split: the statement is `BAFlow sz κ ε 𝔠 𝔡 z → STLK0 (baFMz sz z)` (no `0 < κ`, no `0 < sz.lam`; every `n`), and its proof (lines 268-284) uses `BAflow_real` (`GreenSchur:59`) at the given `n`; `grep -c "lam_pos\|hg\b\|0 < sz.lam\|0 < lam0"` on lines 268-283 = 0.  The hypotheses of the three opened private lemmas: `GridGoodBA_loopFine_init (hm : 0 < (BAmF sz lam0 E n).im)` (`GridGoodBA:566`), `GridGoodBA_BAMLoop_one_loop (h : BASelf d L g z m)` (`:591`), `CltFlowBA_Ksol_isKLoopS (hr : BAReal d L g κ E m)` (`CltFlowBA:362`): each follows from `BAflow_real` at every `n`.  So `g₀ n > 0` and `g₀ n ≤ 0` take the same route; the stop rule (answer (5)) did not trigger.

**(10) M/N shape** (`grep -n "∀ d : ℕ, UNMLOutBA d"`): `BA/UNPins.lean:124, 143, 370, 1027, 1041, 1053, 1066`; `BA/EMCTE2BA.lean:943, 953, 961`; `BA/RandomLayerBGBA.lean:207, 210`.  `ba_mlout (d) (hd : 3 ≤ d) (h : UNMLOutBA d)` (`RandomLayerBGBA:115`), `inst_UNMLOutBA (h : UNMLOutBA 3)` (`UNPins:1015`).  N's readers take `∀ d : ℕ, UNMLOutBA d`; under §316 only `UNMLOutBA 3` is unconditional (V2b).  Reported, not a stop (answer (7)); no N file edited.

**(9) Plug-in recipe for V2a / V2b** (`#check`, `$S/recipe.lean`): V2a/V2b prove `BAMainIndFamTL d R` per regime / at `STAny` and pass it to the terminal theorems by name.
```
RBM.BA.BAMainIndFamTL : ℕ → ({d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) → Prop
RBM.BA.baMLOutTL_of_famStep : ∀ (d : ℕ), (RBM.BA.BAMainIndFamTL d fun {d} => RBM.Gauss.Sizes.STAny) → RBM.BA.BAMLOutTL d
RBM.BA.unMLOutBA_of_famStep : ∀ (d : ℕ),
  (RBM.BA.BAMainIndFamTL d fun {d} => RBM.Gauss.Sizes.STAny) → RBM.Univ.UNMLOutBA d
RBM.BA.unMLOutBA_of_BAMLOutTL : ∀ (d : ℕ), RBM.BA.BAMLOutTL d → RBM.Univ.UNMLOutBA d
RBM.BA.BATwistLoopLaw_congr : ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (C C' : RBM.BA.FlowFM sz)
  (μ : MeasureTheory.Measure sz.SeqΩ) (τ : ℕ → ℝ),
  C.EvEq C' → (RBM.BA.BATwistLoopLaw C μ τ ↔ RBM.BA.BATwistLoopLaw C' μ τ)
```
**(4) Tables as used.** Family-premise table and UBA-C1 table of (a) hold as the statements above read: guards `3 ≤ d`, `0 < κ`, `0 < ε`, `0 < 𝔡` as in (a) (`STBaseG`, `STHorizonG` guards unchanged; `stBaseG_of_init'` `hK` under `0 < κ → 0 < ε → 0 < 𝔡 → Flow →`); `baG0M_holds`, `baLK0_holds` under `BAFlow` only; `∃ c₁` after `(κ, 𝔡)` in `baTailPassage`, `∀ c₁ ∈ (0, 1/2]` in `BAMainIndFamTL`; `n₀`, `K`, `κ'`, `ε'` inside proofs or existential after the guard; no `∀ n` drift premise; UBA-C1 crossing: none.  Ports: from `t/T2503:RBM3D/Probe/T2503Pins.lean` (last commit 93bd54cd) lines 33-47 (target 1), 95-261 (targets 2-6), from `t/T2449:RBM3D/Probe/T2449Pins.lean` (last commit 921369b2) :259 (target 11 (b)); read with `git show` only, never imported or merged.  No RBM1D/RBM2D port in this ticket (no diff-stat).

**Narrative.**  Targets 1-6 and 11 (b) are the compiled probe pieces re-declared under the stem `MainIndOutBA_` (privates) with the pinned public names; targets 7-10 and 11 (a), (c) are new here.  `baG0M_holds` reads `Boot_GM_zero` (`G - M = 0`).  `baLK0_holds` splits on the loop length: length ≥ 2 by the initial clause of `IsKLoopS`, length 1 by its one-loop clause with `GridGoodBA_BAMLoop_one_loop`; `𝓛_0` by `GridGoodBA_loopFine_init` after `H_0 = g₀ Ψ`.  `stBaseG_of_init'` is `stBaseG_of_init` at the setting `0 < ε ∧ 0 < 𝔡 ∧ Flow` (no edit of `MainIndBase`).  `baHorizonG_holds` is `hf.1`, `BAflow_T0_bounds`, `CltFlowBA_one_sub_T0`.  The chain `baChainFamTL_holds` runs the family induction over `stChainTime`/`stChainSteps` at the tail `sz.comp (· + n₀)` (`κ/2`), shifts back with `baConclShift`, mixes at `t_n = 0` with the merged `TwistChain_*_mix`.  No merged statement, merged private or other module changed; the only comment edits are the four lines of `LWPinsBA`/`EMn2BA` (script above).  The instances apply every target at `d = 3`, `sz0`, `zSeq`, `(κ, ε, 𝔠, 𝔡) = (1/4, 1/10, 1/6, 1/10)`, `c₁ = 1/3`, member `BAzSrc sz0 zSeq (2/3) (17/25)`, `t ≡ 1/2` and `t ≡ 0`, tail `n₀ = 3` with `τ ≡ 1/2`, window at `κ = 1/2`; the existentials `κ'`, `ε'`, `c₁`, `n₀`, `K` of the theorems are not instantiated in Lean (their values are in (a), rows 5-10).  Hypotheses of the instances: the family step `BAMainIndFamTL 3 STAny` (6, 11) and the seven tail conclusions (5); targets 2, 3, 4, 7-10 have none.

### (c) Verified Mathlib names (`#check`, `$S/names.lean`)
`sub_eq_zero`, `List.ofFn_succ`, `List.length_ofFn`, `Nat.lt_or_ge`, `le_antisymm`, `one_pos`, `Real.rpow_pos_of_pos`, `Nat.pos_of_ne_zero`, `exists_nat_ge`, `div_le_iff₀`, `half_le_self`, `half_pos`, `Filter.tendsto_add_atTop_nat`, `tendsto_natCast_atTop_iff`, `Filter.eventually_atTop`, `inv_pos`, `lt_min`, `mul_pos`: all present (checked in this session).  No name verified absent; none invented.

### (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (D536, D538, D723 cover the family form, the tail at `κ/2` and the `d > 3` scope).  `stBaseG_of_init'` (premise `0 < ε → 0 < 𝔡 →` under `hK`) is a Lean-side form of a merged lemma, not a paper-statement difference.
- Registry numbers differ from the ticket text by one: build before/after reports owed 122 → 118 (ticket: 121 → 117); the change is the planned -5 +1.  `BAMainIndFamTL` is to leave the list at V2b's merge when a theorem concludes it at `d = 3`.
- Merge: `main` is now 051e596f (T2498 row b added `import RBM3D.Chain.QEndGridGen` after the last import of `RBM3D.lean`); `git merge-tree --write-tree --name-only main t/T2504` reports a content conflict in `RBM3D.lean` only (two adjacent import insertions: union); `Test/Axioms.lean` merges without conflict.
- M/N shape (closing (iii)): see (10) above; the restatement of N's readers at `d = 3` belongs to M/N (flag in V's closing REQ).  Not a stop.
- `baChainTL_holds` and `unMLOutBA_of_pins` stay unused (F2, REQ `:44`); not touched.
