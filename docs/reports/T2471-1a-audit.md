Auditor model: claude-opus-5-5
# T2471 1a-audit (design gate), Mon Oct 12 20:21:20 UTC 2026
Inputs: ticket `docs/tickets/T2471.md`, check `docs/tickets/checks/T2471-check.lean`, report `docs/reports/T2471-prove.md` (a) + (a″),
branch `t/T2471` 3044b47e (probe only). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471-1a-audit` (detached at 3044b47e).
Binding note applied: CONTROL H256 (3) / supervisor 1852 UN-C5. Scratch: scratchpad `T2471/audit1a/`.

## 1. Branch scope and probe compile
```
$ git diff --stat main...t/T2471
 RBM3D/Probe/T2471Pins.lean | 400 +++++++++++++++++++++++++++++++++++++++++++++
$ cd RBM3D-wt/T2471-1a-audit && lake env lean RBM3D/Probe/T2471Pins.lean   (20:15:04 UTC)
exit=0            (no output: no error, no warning)
$ lake env lean audit1a/PinsAx.lean     # probe + #print axioms of its 10 theorems; exit=0
'RBM.BA.T2471_bandStep2_STGridWTail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_ker_band' / '_ker_BA' / '_window_BA' / '_STgAg_eq' / '_STgDriftg_eq' / '_STEEMg_eq' / '_F1_ba' / '_F2_ba' / '_clause1':
   each [propext, Classical.choice, Quot.sound]   (10 lines, verbatim form as the first)
$ lake env lean audit1a/unc5.lean       # prover's UN-C5 scratch (unc5_inc, unc5_mart, unc5_rem), copied; exit=0
'RBM.BA.unc5_inc' / 'RBM.BA.unc5_mart' / 'RBM.BA.unc5_rem' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean audit1a/d2_chain_only.lean   # D2 texts + T2471_WTail2, imports only Chain.GridDuhamelGen, Path.DifREP3; exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2471Pins.lean   -> no hit
```

## 2. Statements: check file vs probe (own script `audit1a/stmtdiff.py`, whitespace-normalised)
```
def T2471_GridRepN2: check==probe True (156 chars)
def T2471_Bridge: check==probe True (886 chars)
def T2471_WTail2: check==probe True (1110 chars)
Ker shape body: check==probe True
5a check==probe True
5b check==probe True
5c check==probe True
```
`T2471_WTail2` vs clause 4 of `STGridRepNAtgL` (`Chain/Step2Gen.lean:994-1035`, read): same binder order
(flow datum, window, `D`, `∃ CK`, `∀ K`, `∀ ε'`, `∀ᶠ n`, `∀ i`), same event, with `Mart n (i.1,b) (j+1) − Mart n (i.1,b) j`
replaced by the `martIncNg` partial-sum difference; probe l.388 proves that replacement is `rfl` for the canonical `Mart`.
`BAGridBridge d = T2471_Bridge d := rfl` (l.363) and `∀ d, T2471_Bridge d := baGridBridge_holds` (l.364) compile.
T2460 merged: `git merge-base --is-ancestor ad52b370 main` true; `baGridBridge_holds` at `BA/GridMartBA.lean:538`.

## 3. Numerics rerun (prover's scripts, unchanged; `python3 inst.py; thr.py; band.py; qv.py; lists.py; crude.py`, 20:16:29 UTC)
```
m=2 D=1 eps'=1/10: CK=9m+3D+22=43, C'=4m+D+6=15, P=ceil(N^15), TL one-slot CK=3D+40=43
constants at N=1: cShift=3.378e+15 c3=4.504e+15 VQ=3.518e+13 PY=3.243e+20  N0(m)=Cbig=4.981e+23 (log2=78.7)
n= 0 L=4 W=32 lam=1/64 N=2097152 (2.097e+06) lam0 in [1.276e-02,1.302e-02]>0 K_n=ceil(N^43)+1 has 272 digits
      fail: ['N>=Cbig (budgets, eventual)']
n= 1 L=8 W=1024 lam=1/4096 N=549755813888 (5.498e+11) lam0 in [1.993e-04,2.035e-04]>0 K_n=ceil(N^43)+1 has 505 digits
      fail: ['N>=Cbig (budgets, eventual)']
n=10 L=44 W=5153632 lam=1/113379904 N=11659991713824860234842112 (1.166e+25) lam0 in [7.201e-09,7.350e-09]>0 K_n=ceil(N^43)+1 has 1078 digits
      fail: []
budget slacks (N-exponent beyond N^-D): shift 30  f2 2  f1 8.0  Y 2;  2cShift=6.76e+15 4c3(1)=1.80e+16 1536PY(1)=4.98e+23
eventual budgets (N>=Cbig, Z budget; D=1, eps'=1/10) first hold at n=21, N=3.057e+30; n=10 (N=1.2e25) is below
n= 0 N=2.097e+06 Im z0=8.764e-06  msc(z0)=-0.249999+0.968241j  lemT=|msc|^2=0.999991 >= 1/16: True  t=1/16<=lemT, Delta=(1/16-0)/4=0.015625
n= 1 N=5.498e+11 Im z0=4.054e-10  msc(z0)=-0.250000+0.968246j  lemT=|msc|^2=1.000000 >= 1/16: True  t=1/16<=lemT, Delta=(1/16-0)/4=0.015625
n=10 N=1.166e+25 Im z0=8.844e-21  msc(z0)=-0.250000+0.968246j  lemT=|msc|^2=1.000000 >= 1/16: True  t=1/16<=lemT, Delta=(1/16-0)/4=0.015625
cases (sigma x labels, half with a1'!=a1): 960
per-cut cross-label identity max |lhs-rhs| (k=1,2, all 4 charge pairs): 2.97e-16
derivative formula d loop = -sum (Q1+Q2)^T X, max err (finite diff 1e-6): 5.05e-10
exact QV == sum of cut terms (no cross term) in 0 of 960 cases
CS bound  sum_c gvar|sum kap dL|^2 <= 2 Re sum kap kap* STeeMg: violations 0  min slack 3.156e-04  max ratio 0.999
STEEkMg k=0 list == STeeLoop k=1 (a'=a): True ; k=1 list == STeeLoop k=2: True
cutGlueL 1 2 x == (s, [x,a1]): True ; cutGlueR 1 2 y == (s, [a0,y]): True
Icc 1 2 pairs (k,l'>k): only (1,2) -> [(1, 2)] ; Icc 3 2 empty: True
1200 cases; max |STeeMg|/(m N (16N)^6) = 8.20e-10 (<=1); max |shift|/(m(2m+2)16^7 N^8 (u'-u)) = 2.14e-11 (<=1)
```
Exponents re-read in merged files: `gridRepWTailQN_holds` CK `9m+3D+22` (`DifREP3:2346`); `baTwistGridWTail_holds` `3D+40`
(`TwistGridWTail2:1236`); `baTwistGridRem_holds` C₀ = 11, CK = 6 (`TwistGridRem2:395-397`); `baTwistGridTail_holds` `2D+20`
(`TwistGridTail2:306`). Assembled CK = max = 3D+40: matches (a) row (i).

## 4. Mathematics of the plan (read against merged signatures)
- **Cross-label QV is of the band's form.** Band: `difRepTail_condMGF_Z` (`DifREP2:1404-1420`) has proxy
  `Δ·(k·Re ΣΣ κ_b κ̄_{b'} STeeM(σ,b,b'))` from `QVPropagatedN` (`QVN:799`, inequality with factor `k`). D2 `Inc` (probe l.59-70)
  has `Δ·(2·Re ΣΣ κ κ̄ STeeMg(σ,b,b'))` at `u_{j+1}`, `H_j`: the same shape at k = m = 2. TL's `TwistGridWTail_condMGF_generic`
  (`TwistGridWTail:1333`) takes any bound `linTrVar(AbCN) ≤ v ω`; `linTrVar(A) = Σ_c gvar_c (Re tr(A X_c))² ≤ Σ_c gvar_c|Σκ∂_cL|²`,
  which the CS bound above controls (0 violations, b₁ ≠ b₁′ in half the cases). Equality fails (cross-cut terms), as in the band;
  that delta is already recorded (`docs/paper-deltas.md:821`, factor `k`). No counterexample shape: no stop line.
- **Target 5.** Proved in the probe at `baStep2Mat` for every `d`, `sz`, `lam0`, `E` (l.324-337), statements equal to the check (§2);
  `filt (sz.withLam 0) j = filt sz j := rfl` compiles (l.340).
- **Target 6 under UN-C5.** Clause 1: `Rem` := residual at every `n` (`T2471_Rem`, l.376), `T2471_clause1` by `ring` (l.381),
  no bridge, no target 5 (the ticket's "telescoping using target 5" is superseded by UN-C5; (a) l.77 says so). Eventual clauses:
  `unc5_mart` (Σ martIncNg = `twMart (σ, a 0, a 1, a 1)` for every ω under H1), `unc5_rem` (residual = `twRem` under H1, H2, 5a, 5b)
  compile (§1). Clause 3: `STGridRepNAtgL` clause 3 reads `STeeMg … i.2 i.2` = `STEEMg` by 5c; with H3′ `‖twEEk‖ ≤ 2‖STEEMg‖`,
  `N^{ε'/2}(ΣΔ‖twEEk‖+N^{-D})^{1/2} ≤ √2·N^{ε'/2}(ΣΔ‖STeeMg‖+N^{-D})^{1/2} ≤ N^{ε'}(…)^{1/2}` once `N^{ε'/2} ≥ √2`; then
  `BATwistGridTail` (`TwistGrid2:239`, CK before ε') at ε'/2. Clause 2: `BATwistGridRem` (`TwistGrid2:227`). Clause 4: target 4.
  CK = max(6, 2D+20, 3D+40). Matches the UN-C5 note item by item.
- **Kernel class.** K1-K4 discharged at band (`T2471_ker_band`, hyp `|E n| ≤ 2`) and BA (`T2471_ker_BA`, hyps `BAReal`, `0<κ`);
  BA window `T2471_window_BA`. Instances at `d = 3`, every `n`: band Ker at `bandStep2Mat sz0 (STflowE z0)` (l.221), BA Ker at
  `baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)` (l.228), BA window at `t ≡ 1/2` (l.394). Nondegenerate (`sz0`, `L ≥ 4`).
- **Hidden hypotheses / vacuity.** `GridRepTailGen_Hyp` is a premise of `stGridWTail2gL_of` only; it is concluded by target 4
  (`gridRepTailGen_hyp_BA`), so no `Prop` premise stays open; registry none. `Inc` at BA is not compiled at 1a (the ticket does not
  require it in the probe; dispatcher answer (5) makes target 4 the non-vacuity check).

## 5. Census sources and greps
```
$ for n in <15 cited BA/band sources>; grep -rnE "(theorem|lemma|def) $n\b" RBM3D | head -1
TwistGridWTail_Y_fields -> BA/TwistGridWTail.lean:1419   TwistGridWTail_hermTestFun -> :848   TwistGridWTail_twEEM_norm_le -> :381
TwistGridWTail_Y_tail -> :1742   TwistGridWTail_svarF_zero -> :1117   LoopC2N_second_deriv_bound -> Induction/LoopC2N.lean:424
norm_loopL_zshiftN_le -> Induction/NQGood1.lean:676   norm_loopM_le_sharp -> Loop/GLoopFlow.lean:903   PsiI_isHermitian -> Gauss/BlockAnderson.lean:65
EMn2BA_one_sub_T0 -> BA/EMn2BA.lean:111   EMn2BA_mF_data -> :125   BAm_norm_le_one -> BA/Ward.lean:136   twU_eq_uKer -> BA/TwistGrid.lean:214
difRepTail_condMGF_Z -> Path/DifREP2.lean:1404   difRep2_peel -> Path/DifREP2.lean:478      (0 MISSING)
$ name clash, pattern GridRepTailGen|GridRepTailBA|TwistGridQTail|STGridWTail2gL|stGridWTail2gL_of|bandStep2_STGridWTail2|
  gridRepTailGen_hyp_|baGridWTail2_holds|baGridRepNAt2_of_bridge|baGridRepNAt2_holds|T2471_   (pathspec RBM3D RBM3D.lean)
main d0d9fe0f:        0 hits
t/T2460 79339380:        0 hits
other t/* branches scanned: 469; with hits: none
$ probe greps: UBA-C1 sz.lam hits: 0 | lam0|withLam|BAflowLam0 in l.37-127: l.127 only (target-4 statement, BA leaf)
  X1-C1/BA pattern over l.37-120 (D2 texts, T2471_WTail2): 0 | Ring.inverse|Matrix.of|cycProd|Ugen: 0 | STGridRepNgL: 0
$ grep -n scanPremises RBM3D/Test/Axioms.lean -> 447 (report cites :447; ticket :437)
```

## 6. H250 (4) deliverables table
| # | met? | evidence |
|---|---|---|
| (i) exponents | yes | (a) l.5-19; CK/C₀/tail exponents re-read (§3) |
| (ii) instance + script | yes | §3 rerun reproduces (n = 0, 1, 10; band DifREP3Inst); compiled d = 3 instances l.221, 228, 394 |
| (iii) D1 census, route | yes | route (i); sources exist (§5). Grouped per section with decl counts (observation O2) |
| (iv) D2 texts compiled | yes | probe exit 0; Chain-only compile exit 0; band and BA per-field discharges compiled |
| (v) target 5, cross-label QV | yes | §3 numerics; 5a-5c and `filt` proved in probe |
| (vi) target 6 | yes | §4; UN-C5 Mart/Rem identities compile; T2460 merged |
| (vii) UBA-C1 | yes | §5: no crossing, not triggered |
| (viii) hypothesis table | yes | (a) l.51-61 + (a″) row (viii) |
| (ix) premise scan | yes | no open `Prop` premise; registry none |
| (x) open private | yes | probe uses exactly `difRep3_sum_norm_uKer_sub_one`, `difRep3_conj_uKer` (l.27); 1b list (a) l.90 |
| (xi) layout | yes | no `BA/*` in Chain texts (§1 Chain-only compile); imports listed |
| (xii) sizes, split | yes | central 2,960 (Chain 790 + 740, BA 1,430) |
| (xiii) name clash | yes | §5: 0 hits on main, t/T2460, 469 other t/* branches |

## 7. Decisions asked of the 1a-audit
- **Split (pre-signed, H255 (4)): CONFIRMED.** Central 2,960 > 1,950. P1b-1 = `Chain/GridRepTailGen.lean` + `Chain/GridRepTailGen2.lean`
  (targets 1-3); P1b-2 = `BA/GridRepTailBA.lean` (targets 4-7; reserve `GridRepTailBA2` only if the leaf passes 1,800).
  Each half < 1,950. **No third row** (central 2,960 ≤ 3,900): no REQ.
- **Condition (7) (switch 1b to prover-max): does NOT hold.** D1 picks route (i), and the BA cross-label QV has the band's form (§4).
  The 1b stays `prover-hard`.
- **Target 2 text:** D2 keeps the canonical `Mart = Σ martIncNg`; `T2471_WTail2` stands as pinned.
- **Stop lines:** none hit (no false identity; no D2 field predicted > 400 lines at BA; no `STGridRepNgL`, `m > 2`, second kernel,
  spectral premise or `BA/*` import in Chain; no merged-file edit; no unproved public `Prop` premise). No dispatcher sign-off needed.

## 8. Observations (no effect on statements, instances, builds, axioms or delta coverage)
- O1. (a) l.33-35 pastes `band.py` output without the fields `lemT=|msc|^2=` and `t=1/16<=lemT, Delta=…` that the script prints now
  (§3); the values agree. Not verbatim.
- O2. D1 census is per section (with declaration counts and named key declarations), not one row per declaration.
- O3. Risk for 1b: the 2.6× references exceed 2,000 for every file (2,054 / 1,924 / 3,718); `Chain/GridRepTailGen` has no reserve file,
  so an overrun there is a ticket stop. The BA cross-label QV (≈ 300 predicted, stop at 400) is uncompiled; the private H3′ machinery of
  `BA/GridMartBA.lean:292-536` (`GridMartBA_Q1/_Q2/_Phi_add_le/_loop6_*`) is a reuse candidate by `open private`, not listed in (a) (x).
- O4. Paper deltas: none new; the factor-2 QV inequality is the recorded `paper-deltas.md:821` entry, H3′ is `T2460a`.

## Verdict
Design gate (stage 1a): **PASS**. Split P1b-1 / P1b-2 confirmed; 1b role `prover-hard` (condition (7) not met); no sign-off.
