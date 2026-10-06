Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 14:25:48 UTC 2026

### (i) Exponent table (`d = 3`, `k = m+2`, `m ≥ 1`; `C4 = qProxy4C d k Λg κ' KL`, `Cn = qProxyCn d (m+1) …`, `CQ = 2Cn+2` are `Classical.choose` constants, only `> 0` is known: `QProxy.lean:458-473`; tested on a grid)
| # | quantity | value / choice | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `ε₀'`, `ε₀''` | `ε₀' = min ε₀ 1`, `ε₀'' = ε₀'/2` (budget run here) | final `(3/2)N^{ε₀''} + N^{τN} ≤ N^{ε₀}` ⇐ `N^{ε₀/2} ≥ 3` | crossover `log₁₀N ≥ 9.54` (`ε₀ = 1/10`), `0.95` (`ε₀ = 1`) |
| 2 | `Λg, κ', KL` | `𝔡⁻¹`, `min κ (4/5)`, `1/𝔠` | `κ' ≤ Im m(E)` (`nqGood1_mE_im_ge` `NQGood1:404`); `L^d ≤ N ≤ W^{1/𝔠}` from `Bandwidth` | exact |
| 3 | `ε`, `ε'` | `ε = min(ε₀''/(8 max(C4,Cn)), 1/2)`, `ε' = ε/2` (class exponent of `altClsQN`) | `C4ε, Cnε ≤ ε₀''/8`, `Cnε' ≤ ε₀''/16`, `ε ≤ 1/2` (`altBudgetExpQN_of_choice` `QBudgetB:711`) | `ε'`: factor 2 |
| 4 | `ε₁ = εq`, `τN` | `ε₀''/40`, `ε₀''/8` | each `≤ ε₀''/8` (same lemma) | `ε₁, εq`: factor 5 |
| 5 | `τ'` (`GoodSetN`) | `min(ε/4, ε₀''/(40dm))` | `dW^{τ'} ≤ W^{ε'}`, `dW^{ε'} ≤ W^{ε}`, `4 ≤ W^{ε'}, W^{ε}`, `log L ≤ W^ε`: eventual (`W ≥ N^𝔠`) | thresholds in (ii) rows `hdW1, hdW2, hWeps, hlog` |
| 6 | `ν = N^{ε₁}W^{τ'dm}` | `hνt` equality; `Yl = N^{ε₁}X ≤ νX` | `hνN`: `ε₁ + τ'dm ≤ ε₀''/20 ≤ 1/40 ≤ 1` | `≥ 0.97` |
| 7 | `hMΛ` | `(2m+5)·3·4^{dm}(2/√κ)C₁ν² ≤ N^{τN}`, `C₁ = (1+40d(m+1))6^{d(m+1)}` | slope `τN−2ε₁−2τ'dm = ε₀''/40` (`W ≤ N`), `7ε₀''/120` (`W ≤ N^{1/3}`) | `ε₀ = 1/10`: `0.00125`, `0.00292`; crossovers `log₁₀N ≈ 8384/11924/18854` (`m = 1/2/4`, `W ≤ N`) |
| 8 | `D''` | `2Cn+2+2C4+k+(4k+1)/𝔠` | `altBudgetExpQN_of_choice`; C2 `hD`: `m+3+CQ < D''+1` | `hD` slack `2C4+(4m+9)/𝔠 > 0` (`≥ 102` at `m=2, 𝔠=1/6`) |
| 9 | `D'`, `Dc` | `D' = D''+2`, `Dc = D'−1 = D''+1` | `D' ≥ C4+Cn+(2k+1)/𝔠`; `hFv` `𝔠D' ≥ 2m+4` (have `≥ 4m+9`); `1 < Dc`; `2W^{-D'}, 4W^{-D'} ≤ W^{-Dc}` (`W ≥ 4`) | `hFv`: `2m+5` |
| 10 | shift | `W^{-D'} + eeShiftErrN ≤ W^{-(D''+1)}` = `altEnd_shift_fixed` (`QEndA:1302`) at `D''+1` | `C_K ≥ D''+2k+6`, `W ≥ 2`, `N ≥ 2k(2k+2)`, `η_v⁻¹ ≤ N` | `C_K − (D''+2k+6) = D₁+2C_P+6k+14` |
| 11 | `D_Y = D_t = k+1`, C1b | `‖aTrueQN(K)‖ ≤ budget + N^{−D_t}` | `N^{−(k+1)} ≤ ½N^{ε₀''}B_v^k` ⇐ `N^{1+ε₀''} ≥ 2`, `B_v ≥ N⁻¹` (`expDr_Bctl_ge` `ExpEtermsB:134`), `Λ ≥ 1` | `log₁₀N ≥ 0.29` |
| 12 | `C_K` | **`D₁ + 2C_P* + 8k + 20 + D''`** (`C_P* ≥ 0` from `yMomentsQUnifN`) | `AssembledN`: `(D₁+1)+4(k+1)+k+2C_P+8 ≤ C_K` (slack `3k+7+D''`); `sum_weighted_qErrQN_le` at `m↦m+1`, `D_t=k+1`, `τK=1`, `θ=1−τR ≤ 1`: `h1 < 8k+18`, `h2 < 7k+8`, `h3 < 4k+4`, `h4 < 1`; `nqBudget_merged_inputs` `6k+18`; shift row 10 | **F5**: ticket's `6k+20` closes `h1` only if `D'' > 2k−2` (true for `𝔠 ≲ 4`, g1); `8k+20` is `𝔠`-free |
| 13 | union | `D₁' = D₁+1` | `2^k N^{−(D₁+1)} ≤ N^{−D₁}` ⇐ `N ≥ 2^k` (`nqEnd_ev_union` `NQEndLin:1011`) | eventual |
| 14 | regime | `η_v⁻¹ ≤ N` (`nqEnd_ev_hη` `:503`, `RangeCond τR v`, `τR = min τ 1`, `N^{τR} ≥ κ'⁻¹`); `N⁻¹ ≤ 1−v` from `Im m ≤ 1` (`st5_mE_im_le_one` `Step5Kit:351`); `hΔη`: `ΔN ≤ N^{1−C_K} ≤ 1` | `STCaseI` + `v ≤ t` gives `v ≤ 1−g²/L²`; `W⁻¹ ≤ (1−t)/(1−s) ≤ (1−v)/(1−s)` | eventual |
| 15 | G2 crude (`N`-exponents) | `‖STLKM_u(H)‖ ≤ η_u^{-k} + MK ≤ (1+N)η_v^{-k} ≤ N^{k+2}` (`N ≥ 2`): `STmaxLKM_crudeN` `NQGood1:941`, `MK = N·η_v^{-k}` from `exists_norm_Kcal_le_win` `GridDriftN:1098` (`τ = 1`, `STKbound` from `stKbound_holds` `KLFinal:243`); `C_cr = k+2`, `C_big = 2k+2` | case `𝔏 ≥ N^{C_big}`: RHS `≥ N^{ε₀}𝔏B_v^k ≥ N^{C_big−k} = N^{k+2}`, `B_v ≥ N⁻¹` | exact |
| 16 | G2 `C₀` (`W`-exponent) | **`C₀ = (8k+7)/𝔠`** | case `𝔏 < N^{C_big}`: `Λ < N^{2C_big}`, `Φ_i, X < N^{C_big}`; `hMee ≤ 2N^{2ε₁+2C_big+4k+1} ≤ N^{8k+7}`, `dDriftLinN ≤ N^{4k+4+2ε₁}`, crude `N^{k+2}`; `N ≤ W^{1/𝔠}` | **F6**: `B_u ≤ 1` is false (`B ≈ 1.001` at `1−u = 1/N`, g2); source is `B_u ≤ 2(1−u)⁻¹ ≤ 2N` (private `gdn_Bctl_le` `GridDriftN:987`, copy), so ticket's `(2ε₁+2C_big+2)/𝔠 + C_cr` is too small |
| 17 | `lam` patch | `ϑ = δ` (1 on constant labels, else 0) when `lam n ≤ 0` | `ellT L g t = 1` for `g ≤ 0`; (i) one constant label per `a₁`; (ii) `1 ≤ C₁·1·e^{−c·0}` (`zdistD_zero` `Lattice.lean:80`, `C₁ ≥ 1`), `0 ≤ RHS` elsewhere; (iii) constant in `t`; (iv) `deriv = 0 ≤ RHS` | `STMollifierProps` holds at every `n`; `C₁ ≥ 1` |

### (ii) One concrete instance: `sz0` (`d=3`, `L=4x`, `W=(2x)^5`, `lam=(2x)^{-6}`, `x=n+1`) at `n = 4`, `m = 2` (`k = 4`), `E ≡ 0`, `κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/2`, `s ≡ 0`, `t ≡ v ≡ 1/2` (non-collapsed; collapsed: `s ≡ v ≡ 0`), `Λ ≡ Φ_i ≡ X ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`; `C4 = Cn = 10`, `C_P = 50` are test values for the opaque constants
Target hypotheses = the pin's premises (structural, discharged for all `n`); the rows of (i) are eventual (`∀ᶠ n`), so each row's own crossover is printed, not assumed.
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2302 && python3 g2.py`
```
sz0 n=4: L=20 W=100000 N=8000000000000000000 lam=1.0e-6 ; log10 N=18.903
  pin hyps at n=4: 3<=d,0<kap,0<c,0<tau,0<dd=True; Bandwidth N^c<=W=True; WO W^(-d/2+dd)<=lam<=1/dd=True; |E|<=2-kap=True; 0<=s<=v<=t<1=True; STCaseI lam^2/L^2<=1-t=True; RangeCond N^(-1+tau)<=1-t=True; W^-1<=(1-t)/(1-s)=True; 1<=Lam, 0<=Phi_i, 1<=X (all =1)=True; s<v (non-collapsed Delta>0)=True
  all-n structural pin hyps for n=0..20000: True
consts: e0''=0.05 eps=0.000625 eps'=0.0003125 tau'=0.00015625 e1=eq=0.00125 tauN=0.00625 D''=148.0 D'=150.0 Dc=149.0 C_K=301.0
  grid K=ceil(N^C_K): log10 K = 5690 (inherent to the pin: N^{C_K}<=K)
  row hdW1  d*W^tau' <= W^eps'           n=4:False  first n for sz0: n*=10^610 (log10 N=10993.8)
  row hdW2  d*W^eps' <= W^eps            n=4:False  first n for sz0: n*=10^305 (log10 N=5497.3)
  row hWeps 4<=W^eps'                    n=4:False  first n for sz0: n*=10^385 (log10 N=6936.6)
  row hlog  log L <= W^eps               n=4:False  first n for sz0: n*=10^1087 (log10 N=19578.1)
  row hMLam K_c nu^2 <= N^tauN           n=4:False  first n for sz0: n*=10^256 (log10 N=4615.8)
  row final N^(e0/2)>=3                  n=4:True   first n for sz0: n*=1 (log10 N=11.7)
  row ha1   W^(C4 eps)N^e1<=N^e0pp/6     n=4:True   first n for sz0: n*=3 (log10 N=17.2)
  row C1b   2<=N^(1+e0pp)                n=4:True   first n for sz0: n*=1 (log10 N=11.7)
  row hFv   W^-D' <= nu N^-(2m+4)        n=4:True   first n for sz0: n*=1 (log10 N=11.7)
G2 n=4: eta_v=0.5 B_v=2.00025e-15 (>=1/N: True) ; crude=(1+N)*eta^-k <= N^(k+2): True ; C_cr=k+2=6 C_big=2k+2=10 C0=(8k+7)/c=234.0 (W-exponent)
  B_u at 1-u=1/N (lam^2=1e-12): B=1.001  -> B_u<=1 is FALSE in general; B_u<=2(1-u)^-1=1.6e+19
  small case frakL=5 < N^C_big: True ; hMee=5.71429e-118 <= W^C0: True ; dDriftLinN=1.42786e-58 <= W^C0: True
  big case frakL=2N^C_big: N^e0*frakL*B_v^k=2.6704e+132 >= crude=1.28e+20 : True
  collapsed s=v=0: N^e1+N^tauN=2.3685508 <= N^e0=77.679961 : True
limit check H=0,u=0: ||STQop(STLKM)||=0 <= N^e1*B_0^k=1.05644e-60 (B_0=1.00012e-15)
```
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2302 && python3 g1.py` (exact `Fraction` grid: `ε₀ ∈ {1/10,1,5}`, `m ∈ {1,2,3,4,6,10}`, `𝔠 ∈ {1/100,1/6,1/3}`, `C4,Cn ∈ {1e-3,1,10,1e3}`, `C_P ∈ {0,50}`, `D₁ ∈ {1/100,1}`; `ck` = coefficient in `C_K`)
```
CK=D1+2CP+8k+20+D": 10 rows (budget_of_choice 15 premises, hD, hFv, hnuN, Dc>1, AssembledN, sum_weighted h1-h4, nqBudget h1-h4, shift) x 3456 grid pts, all true: True
CK=D1+2CP+6k+20+D": 10 rows (…same…) x 3456 grid pts, all true: True
ck=6 at m=6,c=9,C4=Cn=1/100,D1=1/100,CP=0: CK=81.72 need >8k+18=82 -> False
ck=8 at m=6,c=9,C4=Cn=1/100,D1=1/100,CP=0: CK=97.72 need >8k+18=82 -> True
 ck=6 m=60 c=4: CK=518.3 need>514 -> True
 ck=6 m=60 c=5: CK=505.8 need>514 -> False
hMLambda: slope tauN-2e1-2tp*d*m (e0=1/10: e0pp=1/20); crossover log10N = log10(K_c)/slope; K_c=(2m+5)*3*4^(dm)*2*C1
 e0=1/10 m=1 K_c=3.022e+10 slope(W<=N)=1/800=0.00125 cross=8384 | slope(W<=N^(1/3))=0.00292 cross=3593
 e0=1/10 m=2 K_c=8.047e+14 slope(W<=N)=1/800=0.00125 cross=11924 | slope(W<=N^(1/3))=0.00292 cross=5110
 e0=1/10 m=4 K_c=3.698e+23 slope(W<=N)=1/800=0.00125 cross=18854 | slope(W<=N^(1/3))=0.00292 cross=8080
e0=1/10: final absorption crossover log10N>=log10(3)/(e0/2)=9.54 ; ha1 (W<=N) log10N>=log10(6)/(e0pp*(1-1/8-1/40))=18.31 ; C1b log10N>=0.29
e0=1: final absorption crossover log10N>=log10(3)/(e0/2)=0.95 ; ha1 (W<=N) log10N>=log10(6)/(e0pp*(1-1/8-1/40))=1.83 ; C1b log10N>=0.20
```
External hypothesis (projected initial bound, S3-18b1): limit line above; `(𝓛−𝒦)(0) = 0` at `u = 0` is `AzumaProxyN.lean:600-621` (private, copy). The good-walk antecedent is a statement on `ω` (probability `≥ 1−N^{−D}`, S3-18b1); I did not evaluate it at a concrete matrix beyond `H = 0 ∈ altYSetN`.

### Gates and verdicts
`bash <scratch>/T2302/chk_lines.sh` → `G3 citations (file:line:name) checked: 109 mismatches: 0` (every `file:line` of the ticket's premise table and dependency list names the cited declaration at `2cf288c`).
- **§95 (3) level check: PASS.** `GoodSetN` at crude `Φc` is used only through Herm, Dec (`goodSetN_LKM_far`), (D4), (Vb); its (G2) is `1 ≤ m < k` (`GridGoodN.lean:127`), never length `k`. `GoodLinN` at `Φ₁,Φ₂,Φ₃`; `altYSetN` at length `m+1 = k−1` with `N^{ε₁}X`; `cQVAltQN` at `Λ`; the level split compares deterministic levels with `N^{C_big}` only. No set or hypothesis needs `Ξ̂` at length `k`.
- **§29: PASS.** (1) `0 ≤ s ≤ v ≤ t < 1` explicit, no `t ≤ lemT`. (2) case (i) only via `STCaseI`, `v ≤ t`, `W⁻¹ ≤ (1−t)/(1−s)`; `N⁻¹ ≤ 1−v` derived (row 14). (3) `KL = 1/𝔠` from `Bandwidth` (row 2). (4) all numerical rows `∀ᶠ n` from `SizeTendsto`, `Bandwidth`, `WO`, `RangeCond`; level split per `n` inside `∀ᶠ`. (5) per-path, stopping family on the grid, no `Prec`. (6) constants depend on `(d,m,𝔠,𝔡,κ,ε₀,D₁)` and, through `C_P*`, on `(τ,E,s,v)` (all quantified before the `∃`); `C_K` before `Φc, K`. (7) scale `N`, levels at `B_{u_j}^k`.
- **G1 PASS** (rows 1-16; `C_K` and `C₀` corrected: F5, F6). **G2 PASS with F6** (constants in rows 15-16; both cases and the collapsed window checked at `n = 4`, `m = 2`).
- **G3 PASS, no slip-class (3) row.** Verified against the sources: `hker ← alt_hkerGridQN` needs `W⁻¹ ≤ (1−v)/(1−s)` (from the pin with `v ≤ t`) and `v ≤ 1−g²/L²` (`STCaseI`); `hdrift ← alt_hdriftGridQN` bounds `dDriftAltLinQN` at class exponent `ε'`; `hA0cls, hDcls` need the `W^{C₀}` crude sups (`altEnd_crudeSup`, `altEnd_driftSup`, under the level split, not from `GoodSetN`); `hc_pos`: `qvBdAltQN ≥ W^{C4}W^{k}W^{−D''+CQ} > 0`, `Δ > 0` iff `s < v`, so the non-collapsed branch only; `budgetAltQN.hdd ← dDriftAltLinQN_le_shape` has `Pa = W^{Cnε'}Γ²k + N^{τN}`, `Φd = Φ₁+Φ₂+Φ₃+X` (`QBudgetA:419`), matching `altBudgetNumQN`; `C1b.hsum ← sum_weighted_qErrQN_le` at `m↦m+1` has the same `qErrQN`/exponent `(m+1+1)` text; `AssembledN`'s `D` is `D_Y`, `ε` is `εq`. Only unproduced premise: the projected initial bound (S3-18b1, scoped in T2294).
- **`lam` patch (Design (c)): PASS** (row 17; `ellT` identity is the check file's `example`). Fibre-sum: the only `a` with `a 0 = a₁` and `δ ≠ 0` is the constant tuple, sum `= 1`.
- **Findings for stage 1b.** **F5:** `C_K = D₁+2C_P*+8k+20+D''` (not `6k+20`), `𝔠`-free. **F6:** `B_u ≤ 1` has no source; use `B_u ≤ 2(1−u)⁻¹ ≤ 2N` and `C₀ = (8k+7)/𝔠`; crude bound is in `N`-exponents (`N^{k+2} ≤ W^{(k+2)/𝔠}`). **F7:** the docstring of `yMomentsQUnifN` names an explicit `C_P`, but the statement gives only `∃ C_P, 0 ≤ C_P`; row 12 uses `C_P* ≥ 0` only.
- **Targets.** 1 helpers §0-§4 incl. `lam` patch and level split: PASS (with F5-F7). 2 `altGrid_assembly`: PASS. 3 `altGridEndQN` (`T2302_altGridEndQN` unchanged, check file exit 0 at `14:13:58`): PASS.

## (b) Script output (stage 1b, written Tue Oct  6 15:13:37 UTC 2026 per `date -u`; commit `67d3d42` on `t/T2302`, committer date 2026-10-06T08:09:53-07:00)
Section (a) was not edited; no correction of (a) is needed (no verdict changes).

Build, axioms of the public declarations, hygiene (`cd /Users/junyin/Lean_proof/RBM3D-wt/T2302`):
```
$ lake build RBM3D.Induction.QEndGrid 2>&1 | grep -E "^(info|error|warning): RBM3D/Induction/QEndGrid.lean.*(depends on axioms|error|declaration uses)|Build completed"
2147:0: 'RBM.Ind.altGridEndQN' : [propext, Classical.choice, Quot.sound]
2148:0: 'RBM.Ind.QEndGridInst.agCaseI' : [propext, Classical.choice, Quot.sound]
2149:0: 'RBM.Ind.QEndGridInst.agWt' : [propext, Classical.choice, Quot.sound]
2150:0: 'RBM.Ind.QEndGridInst.window_nondegenerate' : [propext, Classical.choice, Quot.sound]
2151:0: 'RBM.Ind.QEndGridInst.window_collapsed' : [propext, Classical.choice, Quot.sound]
2152:0: 'RBM.Ind.QEndGridInst.altGrid_instance' : [propext, Classical.choice, Quot.sound]
2153:0: 'RBM.Ind.QEndGridInst.altGrid_instance_collapsed' : [propext, Classical.choice, Quot.sound]
2154:0: 'RBM.Ind.QEndGridInst.lam_patch_instance' : [propext, Classical.choice, Quot.sound]
2155:0: 'RBM.Ind.QEndGridInst.lam_patch_values' : [propext, Classical.choice, Quot.sound]
2156:0: 'RBM.Ind.QEndGridInst.levels_small_instance' : [propext, Classical.choice, Quot.sound]
2157:0: 'RBM.Ind.QEndGridInst.levels_big_instance' : [propext, Classical.choice, Quot.sound]
2158:0: 'RBM.Ind.QEndGridInst.levels_crude_instance' : [propext, Classical.choice, Quot.sound]
Build completed successfully (3865 jobs).
$ grep -c "sorry\|admit\|native_decide\|axiom \|maxHeartbeats" RBM3D/Induction/QEndGrid.lean
0
$ git diff --name-only main...t/T2302 ; wc -l RBM3D/Induction/QEndGrid.lean ; git log -1 --format=%h
RBM3D/Induction/QEndGrid.lean
    2158 RBM3D/Induction/QEndGrid.lean
67d3d42
```
Statement of `altGridEndQN` (target 3; extracted by script) and its diff against the pin `T2302_altGridEndQN` of the check file:
```
$ sed -n "/^theorem altGridEndQN :/,/:= by$/p" RBM3D/Induction/QEndGrid.lean
theorem altGridEndQN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
$ python3 <scratch>/T2302/stmt_diff.py
statement lines: check 35 file 35 ; unified-diff lines: 0
$ <scratch>/T2302/mk_stmt_script.sh   (check file + `import RBM3D.Induction.QEndGrid` + `example : RBM.Ind.T2302Check.T2302_altGridEndQN := @RBM.Ind.altGridEndQN`; `lake env lean`)
exit: 0
$ grep -n "^private theorem altGrid_assembly\|^theorem altGridEndQN\|^private structure AltGridArith" RBM3D/Induction/QEndGrid.lean
831:private theorem altGrid_assembly {κ : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m)
1188:private structure AltGridArith (d m : ℕ) (𝔠 C₄ Cn e2 D₁ Cmax ε ε' τ' ε₁ τN D'' D' Dc C_K : ℝ) : Prop where
1326:theorem altGridEndQN :
```
Compiled nonempty instances (all in `RBM.Ind.QEndGridInst`; data of the header of §7: `sz0`, `d = 3`, `E ≡ 0`, `κ = 1`, `s ≡ 0`, `t ≡ 1/2`, `v ≡ 1/2`
(`s < v`, `Δ > 0`: `window_nondegenerate`) or `v ≡ 0` (collapsed: `window_collapsed`), levels `≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, every `m ≥ 1`; no hypothesis is left):
```
$ sed -n "/^theorem altGrid_instance (m/,/^  exact ⟨n, G, hG, hGb⟩/p" RBM3D/Induction/QEndGrid.lean | head -3 ; then the proof part
theorem altGrid_instance (m : ℕ) (hm : 1 ≤ m) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
  ...
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := altGridEndQN sz0 1 (1 / 6) (1 / 2) (1 / 10)
    agE agS agT (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    sz0_bandwidth sz0_WO agE_abs agS_nonneg agS_le_agT agT_lt_one agCaseI rangeCond_half agWt m hm
    agOne agOne agOne agOne agOne (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) agV
    agS_le_agV agV_le_agT (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend agOne (agK C_K) (agK_ne_zero C_K)
    (Eventually.of_forall (agK_low C_K)) (Eventually.of_forall (agK_up C_K))).exists
  exact ⟨n, G, hG, hGb⟩
$ grep -n "^example\|^theorem \(altGrid_instance\|lam_patch\|levels_\)" RBM3D/Induction/QEndGrid.lean | cut -c1-90
1947:example : T2302_altGridEndQN := @altGridEndQN
1958:theorem altGrid_instance (m : ℕ) (hm : 1 ≤ m) :
1993:theorem altGrid_instance_collapsed (m : ℕ) (hm : 1 ≤ m) :
2027:example := altGrid_instance 1 le_rfl
2030:example := altGrid_instance 2 (by norm_num)
2033:example := altGrid_instance 3 (by norm_num)
2036:example := altGrid_instance_collapsed 2 (by norm_num)
2043:theorem lam_patch_instance (m : ℕ) :
2051:theorem lam_patch_values (t : ℝ) :
2091:theorem levels_small_instance :
2115:theorem levels_big_instance :
2123:theorem levels_crude_instance (σ : Fin (2 + 1 + 1) → Bool) :
```
Registry pre-check (`Test/Axioms.lean` unchanged; `<scratch>/T2302/reg_before.lean` = `import RBM3D` + `#assert_rbm_axioms`; `reg_after.lean` adds `import RBM3D.Induction.QEndGrid`):
```
$ lake env lean <scratch>/T2302/reg_before.lean ; echo $?   ->  0 ;  line 1: axiom audit: 8627 theorems, 2825 definitions, 0 axioms in `RBM`
$ lake env lean <scratch>/T2302/reg_after.lean  ; echo $?   ->  0 ;  line 1: axiom audit: 8650 theorems, 2832 definitions, 0 axioms in `RBM`
$ diff reg_before.out reg_after.out   -> only line 1 differs (273 lines each; the owed/borrowed premise counts are unchanged)
$ lake build   (whole library, worktree, before the hub adds the root import)  ->  exit 0, "Build completed successfully (4107 jobs)."
```
Sizes, sources of the copies, ports, name clashes:
```
$ awk (lines per section of RBM3D/Induction/QEndGrid.lean)
   12  ## 0. Asymptotic helper (copy of `NQEndLin.lean:56`) -/
  318  ## 1. Elementary facts on the sizes and the grid (copies of 
  125  ## 2. The `lam` patch (paper-delta candidate `T2302c`)
  239  ## 3. The level split (F1/`T2294c`/`T2294e`, F6): determinis
  359  ## 4. The assembly at the alternating exit time, for one sig
  197  ## 5. Helpers of the endpoint: `W`-powers, the logarithm of 
  491  ## 6. The grid endpoint `altGridEndQN`
  361  ## 7. Compiled nonempty instances (namespace `QEndGridInst`)
$ sources of the copies: git --no-optional-locks log --oneline -1 -- <file>   (RBM3D files at the base 2cf288c)
Induction/NQEndLin         cef761a T2199: merge S3-12b Induction/NQEndLin
Induction/QEndA            8a0c4cd T2294: merge S3-18a1 Induction/QEndA
Induction/GridDriftN       14137ce T2111: merge ST2-29 Induction/LoopC2N + Induction/GridDriftN
Induction/QBudgetA         b39ac53 T2279: merge S3-17a Induction/QBudgetA
$ RBM1D / RBM2D: no text copied in this ticket (ports are of merged RBM3D files only); git -C ../RBM2D --no-optional-locks log -1 --format=%h:
9e0f275
$ name clash: grep -rn -F <new public name> RBM3D RBM3D.lean (main worktree HEAD 4686e08 at the time of the grep, `git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks log -1 --format=%h`)
altGridEndQN             0 hits
altGrid_                 0 hits
QEndGrid                 0 hits
QEndGridInst             0 hits
lam_patch_instance       0 hits
levels_small_instance    0 hits
altGrid_instance         0 hits
```

Narrative (facts from the files and the tool log above):
1. Deliverable: `RBM3D/Induction/QEndGrid.lean` (2158 lines, one file, commit `67d3d42` on `t/T2302`, based on `2cf288c`): the pinned theorem `altGridEndQN`
   (statement diff 0 lines, statement script exit 0), the private assembly `altGrid_assembly`, private helpers (prefix `altGrid_`), instances in `QEndGridInst`.
   Axioms: the three standard ones for every printed declaration. No `set_option maxHeartbeats`: every declaration passes at the default limit.
2. Proof shape of `altGridEndQN`: constants of Design (b) (one private lemma `altGrid_arith` packages every inequality between them); the eventual rows
   (`hη`, `hδ` at `D''+1`, `hlog`, `hdW`, `hFv`, `hMΛ`, `hfin`, the union bound, `hKcal`, `hlogR`, `altBudgetNumQN_eventually`); then per `n` three cases:
   (i) `N^{2k+2} ≤ 𝔏 n` (big levels): `G = univ`, conclusion from the level-free crude bound `N^{k+2}` (`altGrid_crude_N`, `altGrid_big_case`);
   (ii) small levels and `s_n = v_n`: `G = univ`, `altEnd_unQ` at `u = s_n = v_n`; (iii) small levels and `s_n < v_n`: `G = ⋂_σ G_σ` from `altGrid_assembly`
   (`assembledN` at `altExitTauN` + C1b), then `budgetAltQN`, `altEnd_unQ` at `v`, `altGrid_final_arith`.
3. Deviations from Design (b)/(a), all internal; no pin, merged signature or file scope is touched: (i) `ν = N^{ε₁}`, not `N^{ε₁} W^{τ'dm}`
   (`(W^{τ'})^{dm} ≤ N^{ε₁}` from `W ≤ N`, `τ' d m ≤ ε₁`), so `hMΛ` is `K_c N^{2ε₁} ≤ N^{τ_N}`, slack `τ_N - 2ε₁ = 3e₂/40` (better than (a) row 7);
   (ii) `C₀ = (8k+8)/𝔠` for `(8k+7)/𝔠` of (a) row 16 (the `+1` absorbs `W^{-(D''+1)} ≤ 1` in `hMee`); (iii) `C_K = D₁ + 2C_P* + 8k + 20 + D''` (F5);
   (iv) `B_u ≤ 2(1-v)⁻¹ ≤ 2N` (F6, copy `altGrid_Bctl_le`), crude constants in `N`-exponents (`C_cr = k+2`, `C_big = 2k+2`), moved to `W`-powers by `W ≥ N^𝔠`;
   (v) the level split enters the assembly as three eventual hypotheses (`hMee`, `hDr`, conditional on `altGrid_small`; `hCr`, level-free), proved in the endpoint.
4. F7: only `0 ≤ C_P*` of `yMomentsQUnifN` is used (via `altGrid_yMomentsMax`, over the patched family `altGrid_mol`, `T2294d` resolved in-ticket).
5. Size: 2158 lines against the ticket's 1200 / 1400 / 1650 (lo / central / hi). §1 (318 lines of the awk table) is copies of private `NQEndLin` helpers
   (ticket §0+§1: 320), §7 instances 361 (ticket 200), §6 the endpoint 491 (ticket §6: 200); the rest as in the table. Section (a) records no size estimate,
   so the preset cut ("Hi > 1500: stop at 1a") was not triggered at stage 1a.
6. Not done / limits: no separate instance of the private `altGrid_assembly` (it is used by `altGridEndQN`, whose instance is `altGrid_instance`);
   the good-walk and initial hypotheses of the conclusion stay hypotheses of the instances (S3-18b1's, as in `nqEndLin_instance`); the eventual
   statements are unfolded at one size index (`Filter.Eventually.exists`); `D₁`-exponent `P(Gᶜ) ≤ N^{-1}` is the theorem's output at `D₁ = 1`.
7. Ports: none from RBM1D/RBM2D in this ticket (the copies are of merged RBM3D files, commits in the table); the registry and `Test/Axioms.lean` are unchanged.

## (c) Verified Mathlib / core names used (all `#check`ed by `<scratch>/T2302/names_check.lean`: 50 names, exit 0)
`Real.log_le_rpow_div` (`0 ≤ x → 0 < ε → log x ≤ x^ε/ε`), `Real.rpow_le_rpow_of_exponent_le` (`1 ≤ x`), `Real.one_le_rpow`, `Real.rpow_natCast`, `Real.rpow_add`,
`Real.rpow_add'` (`0 ≤ x`, `y + z ≠ 0`), `Real.rpow_neg`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_le_rpow_of_nonpos`,
`Real.rpow_nonneg`, `Real.rpow_one`, `Real.rpow_zero`, `Fintype.card_subtype_le`, `MeasureTheory.measureReal_iUnion_fintype_le`, `MeasureTheory.measureReal_empty`,
`Finset.sum_eq_single`, `Finset.sup'_le`, `Finset.le_sup'`, `Finset.sum_pos`, `ite_eq_left`, `ite_eq_right`, `le_self_pow₀`, `inv_le_comm₀`, `inv_anti₀`,
`Nat.lt_two_pow_self` (implicit `{n}`), `Real.toNNReal_pos`, `NNReal.coe_pos`, `one_le_mul_of_one_le_of_one_le`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`,
`deriv_const`, `differentiableOn_const`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `mul_le_of_le_one_right`, `le_mul_of_one_le_left`, `le_mul_of_one_le_right`,
`div_le_div_of_nonneg_right`, `div_nonpos_of_nonpos_of_nonneg`, `min_eq_left`, `max_eq_right`, `lt_max_of_lt_left`, `Set.compl_iInter`, `Set.mem_iInter`,
`Filter.eventually_all`, `Matrix.isHermitian_zero`.  Absent / changed: unqualified `measureReal_iUnion_fintype_le` and `measureReal_empty` are unknown (need `MeasureTheory.`);
`if_pos` / `if_neg` are deprecated in this toolchain (build warning: use `ite_eq_left` / `ite_eq_right`).

## (d) Open issues and paper-delta candidates
- `T2302a`: the alternating endpoint's right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃ + X) B_v^k` carries the lower-length level `X = XLK(n_−1)` additively (from the
  de-`𝒬` step `(normQA)` at `v` and the drift); it is absorbed by the length induction (DECISIONS §62 (1)).
- `T2302b`: the endpoint needs a level-free crude fallback when the deterministic levels exceed `N^{2k+2}` (case (i) above: `‖(𝓛-𝒦)^{(k)}‖ ≤ N^{k+2}` on the good
  walk, `B_v ≥ N⁻¹`); the paper assumes polynomial levels.
- `T2302c`: the mollifier family must be defined at every size index (`lam` patch: delta family on constant labels where `lam n ≤ 0`; `ellT = 1` there); the paper has `ilambda > 0`.
- `T2302d`: the budget runs at `ε₀/2` (C1b absorption) and the final loss needs `N^{ε₀/2} ≥ 3` (large `N`); the shift is `D' = D'' + 2`, i.e. `W^{-D'} + eeShiftErrN ≤ W^{-(D''+1)}`
  (T2294c). Eventual only; no instance reaches these crossovers (the instances unfold the eventual statement at one `n`).
- Open issues: (1) file size 2158 lines against the ticket's hi estimate 1650 (see narrative 5); (2) the projected initial bound, the good walk `GoodSetN ∩ GoodLinN ∩ altYSetN`
  and `STOeqQt'` remain S3-18b1/S3-18b2 inputs, none is produced here; (3) `T2294d` is resolved in-ticket (the `lam` patch), no pin change; (4) cosmetic (supervisor 1356 O5) untouched.
