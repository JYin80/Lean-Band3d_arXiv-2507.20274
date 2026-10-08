Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 04:04:22 UTC 2026 (date -u, start of stage; scripts run after)

Notation (merged definitions, read from the files): `x_u = 1-u`, `a = L^{-d}`, `W^d·Bctl n u = (g²+x_u)⁻¹ + (L^d x_u)⁻¹` (`Bparam d L g u 0`, `K=0`, `g = sz.lam n`), so `x·W^d·Bctl = x/(g²+x) + a`. `ρ = η_s/η_u = (1-s)/(1-u)`. `(lRB1)` = `1_2:1321` (STStep1Loop, with `Bctl n (s n)`), target `(Eq:LGxb)` = `1_2:1361` (STLmaxU).

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | R3 ratio `ρ B_s/B_u` (regime iii: `g² ≤ x_u ≤ x_s ≤ 1`) | `≤ (1+a)/(1/2+a) < 2` (`x_s/(g²+x_s) ≤ 1`, `x_u/(g²+x_u) ≥ 1/2`); holds also for `g = 0` | `≤ 4` (ticket constant `4^{k-1}`); only `k` fixed is needed since `≺` absorbs constants | factor 2 (grid max 1.99999798, script 1) |
| 2 | R3 control `x_u < g²` | ratio unbounded (`→ (1+a)/a`, `x_u→0`) | regime hypothesis `g² ≤ 1-t` is necessary for the constant | grid max 4.5e6 > 4 (script 1) |
| 3 | `𝔠d`, regime (iii) | `1/100` (not used by the proof) | `0 < 𝔠d ≤ 1/100` (pin) | 0 |
| 4 | `𝔠d`, regime (i) | `min(c_Qt, 1/100)`, `c_Qt ∈ (0,1/100]` opaque `∃` of `stOeqQt'_holds`; `stIterations'_holds` returns exactly `1/100` (`IterationsB.lean:572`) | `≤ 1/16` (`iterationsA_scale_I`), `≤ 1/100` (pin), `> 0`; `(con_st_ind)` at `𝔠d` passes down to `c_Qt`, `1/100` by `st5_conStInd_mono` (needs `0<𝔠d ≤ c'`, `t<1`) | `1/16 - 1/100 = 0.0525` |
| 5 | `𝔠d`, case (ii) | `min(c_NZ, 1/100)`, `c_NZ ∈ (0,1/100]` of `stOeqQtNZ'_holds`; `stIterationsII'_holds` returns `1/100` (`IterationsB.lean:583`) | `≤ 1/24` (`iterationsA_scale_II`), `≤ 1/4` (`st_hBA_II`) | `1/24-1/100 = 0.0317`; `1/4-1/100 = 0.24` |
| 6 | `Ψ` exponents | `3/4` (`A^{3/4}`), `1/8` (`A^{1-k/8}`), level `l=0`: `Ψ(r,0) = A^{3/4}+ρ^{r-1}A` | `k ≥ 2+8𝔠d(r-1)` (hscale): `ρ^{r-1}A^{1-k/8} ≤ c A^{3/4}` needs `𝔠d(r-1)+1-k/8 ≤ 3/4` | `st_kmin = ⌊2+8𝔠d(r-1)⌋+1`; at `𝔠d=1/100`: `r=2..7` bound `2.08..2.48`, `k_min=3` (script 1); slack `k_min - bound ∈ (0,1]` |
| 7 | `ρ` bound in hscale | (i) `ρ ≤ (1-s)/(1-t) ≤ B_t^{-𝔠d} ≤ (2A)^{𝔠d}` (`B_t ≥ (2A)⁻¹` since `x_t ≤ g²`, `A = g²W^d`); (ii) `ρ ≤ B_t^{-𝔠d} ≤ B_s^{-𝔠d} = A^{𝔠d}` (`B_s ≤ B_t`) | `(con_st_ind)` `B_t^{𝔠d} ≤ (1-t)/(1-s)` | exact in (ii); factor `2^{𝔠d(r-1)}` absorbed into `c` in (i) |
| 8 | `hBA` `B_v A^{3/4} ≤ c` | (i) `c=2`: `B_v ≤ 2/A` (`(g²+x)⁻¹ ≤ g⁻²`, `(L^d x)⁻¹ ≤ L^{2-d}g⁻² ≤ g⁻²`, `x ≥ g²/L²`, uses `d ≥ 2`), `A ≥ 1`; (ii) `c=1`: `B_v ≤ B_s^{1-𝔠d}`, `B_s ≤ 1`, exponent `1-𝔠d-3/4` | (ii) `𝔠d ≤ 1/4`; (i) `A = g²W^d ≥ W^{2𝔡} ≥ 1` from `(eq:WO)` (eventually) | (ii) exponent `1/4-𝔠d ≥ 0.24`; script 2: max `B_v A^{3/4}` = 0.42 (i), 0.46 (ii) at `n=0` |
| 9 | `hbase`, level `l=0` | `Ξ̂^{(L-K)}_{v,r} ≤ 1+(maxL+maxK)/B_v^r ≲ A(1+ρ^{r-1})` using `(lRB1)`, `(eq:bcal_k)` and `1/B_v ≤ 2A` (i) resp. `1/B_v ≤ 1/B_s = A` (ii) | `≤ Ψ(r,0)` since `ρ ≥ 1` (`(sef8w483r324)`, `3_5:1391`) | constant `2(1+…)` absorbed |
| 10 | `A ≥ 1` | (i) from `(eq:WO)`; (ii) `A = 1/B_s ≥ 1/B_t > 1` (`B_s ≤ B_t`, and `B_t<1` from `(con_st_ind)`: `B_t^{𝔠d} ≤ (1-t)/(1-s) < 1`) | eventually in `n` | script 2 (`A=64` at `n=0`) |
| 11 | time domain | `0 ≤ s < t ≤ lemT z < 1`; `lemT_lt_one` needs `Im z>0`, supplied by `STFlow` (`z.im ≥ N^{-1+ε} > 0`) | `t<1` so `1-u>0` on `[s,t]` | `x_u ≥ 1-t > 0` |
| 12 | `(con_st_ind)` | `B_t^{𝔠d} ≤ (1-t)/(1-s) < 1`, `∀ᶠ n` | eventual, not `∀ n` | data A holds at `n=0`; data B threshold `n ≈ 1.1e10` (limit statement, script 2) |

### (ii) One concrete nondegenerate instance (`d = 3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `C_d=1`)

Data are the merged ones: A = `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`), `z0 = 1/2 + i N^{-4/5}`, `(s,t)=(0,1/16)`: regime (iii) `lam² ≤ 15/16`. B = `szB` (`L=4`, `W=n+4`, `lam=1`), `zB = 1/2 + i/64`; regime (i) `(s,t)=(7/8,15/16)` (`g²/L² = 1/16 = 1-t`, `1-s = 1/8 ≤ g² = 1`), case (ii) `(s,t)=(15/16,31/32)` (`1-s = 1/16 = g²/L²`). Regime (i) is not available at `sz0` (`1-s ≤ g² ≤ 4096⁻¹` needs `s_n ≥ 1-4096⁻¹` and `t_n` beyond it, while the merged files prove only `lemT z0 ≥ 1/16`), regime (iii) cannot be met at `szB` (`g² = 1 > 1-t`); so two data sets. Stochastic premises (`STLK s`, `STStep1Loop`, `STStep2Concl`) are other gates' pins and stay hypotheses; `STKbound`, `STKward`, `STFlow`, regimes, `s<t≤lemT`, `(con_st_ind)` are deterministic and discharged.

Script 1 (R3 grid `g² ∈ [1e-6,1]` log-spaced, `L ∈ {3,10,100}`, `d ∈ {3,4}`, `x_u,x_s` log grid with `x_u ≤ x_s ≤ 1`; constants of (C)):
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2320/pre.py   # (source: /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2320/pre.py)
R3 regime(iii) points 73260  max ratio 1.9999979800020404  at (d,L,g2,x_u,x_s) (4, 100, 1e-06, 1e-06, 1.0)
   (1+a)/(1/2+a), a=L^-d, at worst (d=3,L=3): 1.9310344827586208   <= 2 < 4 : True
control 1-u<g^2: points 210024  max ratio 4545455.049586782  at (4, 100, 1.0, 1e-07, 1.0)  exceeds 4: True
c_Qt/c_NZ = 1/100 -> c_d = 1/100  positive: True  <=1/100: True  slack to 1/16,1/24,1/4: [0.0525, 0.03166666666666667, 0.24]
c_Qt/c_NZ = 1/1000000 -> c_d = 1/1000000  positive: True  <=1/100: True  slack to 1/16,1/24,1/4: [0.062499, 0.04166566666666666, 0.249999]
c_d = 1/100 [(2, 2.08, 3), (3, 2.16, 3), (4, 2.24, 3), (5, 2.32, 3), (6, 2.4, 3), (7, 2.48, 3)]
c_d = 1/1000 [(2, 2.008, 3), (3, 2.016, 3), (4, 2.024, 3), (5, 2.032, 3), (6, 2.04, 3), (7, 2.048, 3)]
```

Script 2 (instances A, B: regime inequalities, `lemT` numerically as `‖m_sc(z)‖²`, `m²+zm+1=0`, `Im m>0`; R3 ratio at the data; `(con_st_ind)`, `hBA`, `(eq:WO)`):
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2320/inst.py   # (source: /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2320/inst.py)
A (iii): N = 2097152  lam^2 = 0.000244140625  1-t = 0.9375  lam^2 <= 1-t: True  lemT(z0) = 0.999991 >= t: True < 1: True
   check n=0..10^6 sample: lam_n^2 <= 1/4096 <= 15/16: True
   u = 0  ((1-s)/(1-u)) B_s / B_u = 1.0  <= 4: True
   u = 1/32  ((1-s)/(1-u)) B_s / B_u = 1.0000077524196864  <= 4: True
   u = 1/16  ((1-s)/(1-u)) B_s / B_u = 1.0000160216652811  <= 4: True
   con_st_ind at n=0, c=1/100:  B_t^c = 0.9019698242288372  <= (1-t)/(1-s) = 0.9375
lemT(zB) = 0.983992 >= 31/32 = 0.96875 : True
B(i) : s,t = 7/8 15/16  lam^2/L^2 = 1/16  1-t = 1/16  1-s = 1/8
   regime I: lam^2/L^2 <= 1-t: True  1-s <= lam^2: True  (STRegIterI = same two)
   (1-t)/(1-s) = 0.5 ; (con_st_ind) at c_d=1/100 holds iff W^3 >= 1.510e+30, i.e. W >= 1.147e+10 (n >= 1.147e+10); B_t -> 0 so B_t^c -> 0 < 1/2 (limit)
   n = 0  A = 64.0  max_v B_v A^{3/4} = 0.42114447997139964 <= c (c=2 case i, 1 case ii): True
   n = 1000  A = 1012048064.0  max_v B_v A^{3/4} = 0.0066784521944976485 <= c (c=2 case i, 1 case ii): True
   (eq:WO) n=0: W^{-1.4} = 0.1435872943746294 <= lam = 1 <= 10
B(ii) : s,t = 15/16 31/32  lam^2/L^2 = 1/16  1-t = 1/32  1-s = 1/16
   case II: 1-s <= lam^2/L^2: True
   (1-t)/(1-s) = 0.5 ; (con_st_ind) at c_d=1/100 holds iff W^3 >= 1.863e+30, i.e. W >= 1.230e+10 (n >= 1.230e+10); B_t -> 0 so B_t^c -> 0 < 1/2 (limit)
   n = 0  A = 64.0  max_v B_v A^{3/4} = 0.455722766988491 <= c (c=2 case i, 1 case ii): True
   n = 1000  A = 1012048064.0  max_v B_v A^{3/4} = 0.007226789992554375 <= c (c=2 case i, 1 case ii): True
   (eq:WO) n=0: W^{-1.4} = 0.1435872943746294 <= lam = 1 <= 10
```

External-hypothesis limit check: the only asymptotic hypothesis is `(con_st_ind)` (and `(eq:WO)`, `A ≥ 1`), all `∀ᶠ n`: at data B `Bctl n t = W^{-3}·O(1) → 0` so `Bctl^{𝔠d} → 0 < 1/2 = (1-t)/(1-s)` for every `𝔠d > 0`; threshold for `𝔠d=1/100` is `W ≥ 1.15e10` (i), `1.23e10` (ii) (script 2). The statement is eventual, so no witness `n` is needed; the instance is the limit, not a value. At data A the inequality already holds at `n=0` (0.902 ≤ 0.9375).

### Consumer / §29 one-liners
(1) `0 ≤ s`, `t ≤ lemT z <1`: hypotheses of `STStep3R`, `t<1` from the flow (row 11). (2) case (ii) boundary `1-s ≤ g²/L²` is the hypothesis `STCaseII`; if `g² ≥ L²` it holds for every `s ≥ 0` and is non-restrictive; no argument uses the time `1-g²/L²`. (3) `L^d ≤ W^K` is not used (only `L^d ≥ L²`, `d ≥ 2`, row 8). (4) regimes are `∀ n` hypotheses (stronger premise), `(con_st_ind)`, `(eq:WO)` `∀ᶠ n`; conclusions are `Prec` (asymptotic). (5) all conclusions are `Prec` uniform in `u ∈ [s,t]` (union inside the probability), as `STLmaxU`. (6) `0 < lam`, `A ≥ 1` come eventually from `(eq:WO)` inside `STFlow.Admissible`; regime (iii) uses no lower bound on `lam` (`g = 0` is fine, row 1). (7) scale `N` vs `W`: `Bctl` is a deterministic factor, no `W^τ` loss enters.

### Checks of the mathematics against the paper
* (R3) `3_5:1384` ("`B_{u,0} ≍ |1-u|⁻¹` … `(Eq:LGxb)` follows directly from `(lRB1)`") is proved with explicit constant 2 on the whole of `[s,t]` when `1-t ≥ g²`; the paper states it for `1-s > g²`, `u ≤ 1-g²`, which is covered. `(lRB1)` (`1_2:1321`) has `(W^{-d}B_{s,0})^{n-1}`, which is what `STStep1Loop` has.
* (R1) `3_5:1422-1431` and (R2) `3_5:1575-1595`: the induction passes through `Ψ` with `A = g²W^d` resp. `A = (W^{-d}B_{s,0})⁻¹` (`(adsyzz0s8d6)`, `(eq:psipara_smalletacase)`); the exponent count is row 6-8; the closing step "`(η_s/η_t)^{n-1}A^{1-k/8} ≪ A^{3/4}`" is row 6/7. The paper's `Ξ̂^{(L-K)} ≺ Ψ ≲ A^{3/4}` and `(rela_XILXILK)` then give `Ξ̂^{(L)} ≺ 1 + B·A^{3/4} ≲ 1` (row 8). Both match the Lean skeleton.
* `k = 1` (`3_5:1385`): `Ξ̂^{(L-K)}_{u,1} ≺ 1` is `STAvgU`; `Ξ̂^{(L)}_{v,1} ≺ 1 + B_v·1 ≲ 1` follows from `(rela_XILXILK)` at `m = 1` (`iterationsA_rela_of_K` is stated for `1 ≤ m`) and `B_v ≤ c` (row 8, `A ≥ 1`); the ticket's `|m| ≤ 1` route is not needed.

### Verdict per target
* Target 1 `STStep3R d STReg5III`: **PASS** (R3, constant 2; no iteration, no `STXiBoot'`).
* Target 2 `STStep3R d STReg5I`: **PASS** (rows 4, 6-10; every input merged: `stOeqQt'_holds` at `STCaseI ⊇ STReg5I`, `stIterations'_holds` at `STRegIterI ⇔ STReg5I` conjunct-wise).
* Target 3 `STStep3II d`: **PASS** (rows 5-10).
* Findings for stage 1b (not defects of the statements): (f1) `hbase` (row 9) is not literally `iterationsA_apriori_of_lRB1` (that gives `Ξ̂^{(L)}`); it needs also `hK` (uniform in pairs) and `st5_Bctl_ge`/`B_s ≤ B_v`; (f2) `iterationsB_K_pairs` and `iterationsB_setting` are `private` in `IterationsB.lean:525,542`, so `hK` (pair-uniform `𝒦` bound) must be rebuilt in `Step3.lean` from the public `stKbound_timeIcc` (`KDecay.lean:1062`) by the same reindexing; the pin's own `STKbound` hypothesis (a per-time-sequence statement) is not that form; (f3) `(con_st_ind)` must be passed down to `c_Qt`/`1/100`/`c_NZ` by `st5_conStInd_mono`, with `0 < min`.
Overall verdict: PASS

### (a′) Preflight corrections
None: no statement of section (a) was found wrong while proving (findings f1-f3 of (a) are handled as listed in the narrative).

## (b) Script output (stage 1b by claude-sonnet-5-5; times `date -u` 2026-10-08; stage 1b started 04:10:04 UTC; commit `10258f1` at 04:27:28 UTC)
```
$ git log -1 --format="%h %s" t/T2320; git status --short
10258f1 T2320: Step 3 of lem:main_ind at regimes (iii), (i) and case (ii) (S3-25)

$ lake build RBM3D.Induction.Step3 2>&1 | tail -7 | cut -c1-200
info: RBM3D/Induction/Step3.lean:547:0: 'RBM.Ind.stStep3RegIII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:548:0: 'RBM.Ind.stStep3RegI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:549:0: 'RBM.Ind.stStep3II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:550:0: 'RBM.Ind.Step3Inst.inst_regIII' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:551:0: 'RBM.Ind.Step3Inst.inst_regI' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/Step3.lean:552:0: 'RBM.Ind.Step3Inst.inst_II' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3908 jobs).

$ git diff --stat main...t/T2320
 RBM3D/Induction/Step3.lean | 552 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   1 -
 2 files changed, 552 insertions(+), 1 deletion(-)

$ git diff main...t/T2320 -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-110
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STStep3II, -- Step 3, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelle

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Step3.lean | wc -l
       0

$ wc -l RBM3D/Induction/Step3.lean; grep -n "^/-! ##" RBM3D/Induction/Step3.lean   # line count after each section
     552 RBM3D/Induction/Step3.lean
57:/-! ## 1. Regime (iii): `ilambda² ≤ 1 - t`, directly from `(lRB1)` -/
97:/-! ## 2. The skeleton (probe `st_step3_skeleton`) and its inputs -/
326:/-! ## 3. The assembly at a `lem:iterations` regime -/
368:/-! ## 4. The targets -/
452:/-! ## 5. Compiled nonempty instances at `d = 3`

$ grep -n "^import" RBM3D/Induction/Step3.lean
6:import RBM3D.Induction.QtXiRoundLift
7:import RBM3D.Induction.IterationsB
```
`#print axioms` of the three targets and the three instances are the last six `info:` lines of the build above.
```
$ grep -n "^theorem stStep3" RBM3D/Induction/Step3.lean   # target statements (committed file)
377:theorem stStep3RegIII_holds : ∀ d : ℕ, STStep3R d STReg5III := by
408:theorem stStep3RegI_holds : ∀ d : ℕ, STStep3R d STReg5I := by
432:theorem stStep3II_holds : ∀ d : ℕ, STStep3II d := by
$ grep "^def T2320_" docs/tickets/checks/T2320-check.lean   # the pinned texts, main worktree
def T2320_stStep3RegIII : Prop := ∀ d : ℕ, STStep3R d STReg5III
def T2320_stStep3RegI : Prop := ∀ d : ℕ, STStep3R d STReg5I
def T2320_stStep3II : Prop := ∀ d : ℕ, STStep3II d
$ tail -3 checkeq.lean; lake env lean checkeq.lean   # check file + `import RBM3D.Induction.Step3` + 3 examples
example : RBM.Ind.T2320Check.T2320_stStep3RegIII := RBM.Ind.stStep3RegIII_holds
example : RBM.Ind.T2320Check.T2320_stStep3RegI := RBM.Ind.stStep3RegI_holds
example : RBM.Ind.T2320Check.T2320_stStep3II := RBM.Ind.stStep3II_holds
exit=0  (lines containing 'error': 0)

$ sed -n 490,495p;500,509p;514,523p RBM3D/Induction/Step3.lean   # the compiled instances (statement + the application of the target)
theorem inst_regIII (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd → STLmaxU sz0 (STflowE z0) sInst tInst) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STReg5III (stStep3RegIII_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_regIII sz0_con Cd hCd
theorem inst_regI (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK szB (STflowE zB) (fun _ => 7 / 8) →
        STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
        STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd →
        STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STReg5I (stStep3RegI_holds 3) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨szB_regIterI.1 n, szB_regIterI.2 n⟩)
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd
theorem inst_II (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK szB (STflowE zB) (fun _ => 15 / 16) →
        STStep1Loop szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
        STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) Cd →
        STLmaxU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STCaseII (stStep3II_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

$ sed -n 530,535p RBM3D/Induction/Step3.lean   # (R3) comparison at concrete numbers (`norm_num`)
example : (1 - (0 : ℝ)) / (1 - 1 / 32) * sz0.Bctl 0 0 ≤ 4 * sz0.Bctl 0 (1 / 32) := by
  obtain ⟨hL, hW, -, hlam⟩ := sz0_values
  unfold Sizes.Bctl Bparam
  rw [hL, hW, hlam]
  norm_num [abs_of_pos]
```
```
$ python3 -I imp.py   # which of the six ticket imports are transitive (kept: the two not imported by another)
RBM3D.Induction.QtXiRoundLift: transitively imported by []
RBM3D.Induction.QtNonzeroBoot: transitively imported by ['QtXiRoundLift']
RBM3D.Induction.IterationsB: transitively imported by []
RBM3D.Induction.ScaleFacts3: transitively imported by ['QtXiRoundLift', 'QtNonzeroBoot', 'IterationsB']
RBM3D.Induction.Step5Pins: transitively imported by ['QtXiRoundLift', 'QtNonzeroBoot']
RBM3D.Loop.KLFinal: transitively imported by ['QtXiRoundLift', 'QtNonzeroBoot', 'IterationsB', 'Step5Pins']

$ name-clash grep: for n in <new public + private names>; grep -rnw "$n" RBM3D --include="*.lean" | grep -v /Probe/ | grep -v Induction/Step3.lean | wc -l
stStep3RegIII_holds:0  stStep3RegI_holds:0  stStep3II_holds:0  Step3Inst:0  inst_regIII:0  inst_regI:0  inst_II:0  sz0_regIII:0  step3_xB:0  step3_finish:0  step3_skeleton:0  step3_psi0_le:0  step3_hbase:0  step3_K_pairs:0  step3_flowLam:0  step3_assemble:0  
control: grep -rnw "stIterations'_holds" (merged, must be >0): 9
$ git ls-tree -r main --name-only | grep -c Induction/Step3.lean   (file absent on main): 0

$ grep -c "RBM1D\|RBM2D" RBM3D/Induction/Step3.lean   # no RBM1D/RBM2D text used
0

$ registry pre-check: precheck.lean = import RBM3D / import RBM3D.Induction.Step3 / #assert_rbm_axioms (RBM3D.lean temporarily had the Step3 import; restored afterwards)
precheck exit=0 (04:28:25 UTC run, committed content); full `lake build` with the temporary root import: exit=0, "Build completed successfully (4128 jobs)"
1:axiom audit: 9085 theorems, 2945 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
2:All within [propext,
21:  RBM.Gauss.Sizes.STStep3R: 4 [no certificate]
23:  RBM.Gauss.Sizes.STStep3I: 8 [no certificate]
158: RBM.Gauss.Sizes.STStep3R,

$ git status --short  (after restoring RBM3D.lean)
```
Full `lake build` in the worktree WITHOUT the root import (04:23:12-04:23:26 UTC, before the final docstring edits; output `fullbuild.out`):
```
error: RBM3D.lean:361:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.STStep3II]
```
With `import RBM3D.Induction.Step3` added to `RBM3D.lean` after `import RBM3D.Graph.BAExpandW` (temporary, uncommitted, restored byte for byte; `git status --short` empty above): `lake build` (started 04:27:33 UTC, on the committed content) exit 0, `Build completed successfully (4128 jobs)`.

Narrative (facts from the pasted output and the committed file):
1. Result: the three targets are proved for every `d` in `RBM3D/Induction/Step3.lean` (552 lines; sections end at lines 96, 325, 367, 451, 552, from the `grep -n '^/-! ##'` output); statements equal the check-file texts (the three `example`s elaborate, exit 0); axioms are the three standard ones; no `sorry`/`admit`/`axiom`/`native_decide` (count 0).
2. Target 1: `step3_xB` shows `(1-s) B_s ≤ 2 (1-u) B_u` for `ilambda² ≤ 1-u` (real algebra on `Bctl`), so `(lRB1)` gives `2^{k-1} (W^{-d}B_{u,0})^{k-1}`; the constant is removed by `iterationsA_prec_absorb`. The ticket's `4^{k-1}` is replaced by the sharper `2^{k-1}` (section (a): grid max ratio 1.99999798). `𝔠_d = 1/100` is not used; no `STXiBoot'`, no iteration.
3. Targets 2 and 3 share `step3_assemble` + `step3_skeleton`: the bootstrap `STXiBoot'` from `stOeqQt'_holds` (at `STCaseI`, from `STReg5I` by its first conjunct) resp. `stOeqQtNZ'_holds`; `hIter` from `stIterations'_holds` (at `STRegIterI`, conjunct-wise from `STReg5I`) resp. `stIterationsII'_holds`; the double induction `st_iterate`; `hscale` from `st_hscale_I'`/`st_hscale_II'`; `hBA` from `st_hBA_I`/`st_hBA_II`; scale facts `iterationsA_scale_I`/`iterationsA_scale_II`; `(rela_XILXILK)`, the averaged law and the a priori bound from `iterationsA_rela_of_K`, `iterationsA_avg_of_STAvgU`, `iterationsA_apriori_of_lRB1`.
4. New beyond the probe skeleton: (i) the case `k = 1` (probe: `k ≥ 2`), via `(rela_XILXILK)` at `m = 1` and `B ≤ B A^{3/4} ≤ c` (`A ≥ 1`), not the ticket's `|m| ≤ 1` route (as in section (a)); (ii) `step3_hbase` (finding f1): level `l = 0` from the a priori `Ξ̂^{(𝓛)}` bound, the pair-uniform `𝒦` bound and `(cv A)⁻¹ ≤ B_v` (field `Bctl` of `IterationsAScale`); (iii) `step3_K_pairs` (finding f2): copy of the private `iterationsB_K_pairs`, from `stKbound_timeIcc`; (iv) constants (finding f3): `𝔠_d := min c₁ c₂` (bootstrap pin, iteration pin), `≤ 1/100` since `c₁ ≤ 1/100`; `(con_st_ind)` passed down to `c₁`, `c₂` by `st5_conStInd_mono`; the bounds `1/16`, `1/24`, `1/4` of the scale facts follow from `min ≤ 1/100`.
5. The pins' own `STKbound`, `STKward` hypotheses are handed to the bootstrap pin only; the iteration uses the pair-uniform bound (`step3_K_pairs`), as in `IterationsB.lean`.
6. Imports: two of the six ticket imports (`QtXiRoundLift`, `IterationsB`); the other four are transitive (script output above). No `MainIndRegimes`, no `RBM3D`.
7. Registry: one deletion (`STStep3II`); `STStep3R`, `STStep3I` untouched. See (d1) for the full-build behaviour.
8. Instances: the data of the merged instance files (`sz0`, `z0`; `szB`, `zB`); `STKbound`, `STKward` are discharged by `stKbound_of_flow`, `stKward_of_flow`; what stays a hypothesis is `STLK s`, `(lRB1)`, `STStep2Concl` (other gates' pins).
9. Ports: only from this repository (probe `3c58211` `st_step3_skeleton`, lines 1087-1160; `IterationsB.lean:517`, `:525`); no RBM1D/RBM2D text (count 0 above), so no RBM1D/RBM2D diff-stat applies.
10. Not claimed: `STStep3I` (straddling case (i)), `STStep4R`, the primed assembly (S3-26/T2321).

## (c) Verified Mathlib names used (each `#check`ed in a scratch file, output `names.out`; names verified absent: none needed)
- `abs_of_pos`: `0 < a → |a| = a`
- `div_le_one`: `0 < b → (a / b ≤ 1 ↔ a ≤ b)`
- `le_div_iff₀`: `0 < c → (a ≤ b / c ↔ a * c ≤ b)`
- `div_le_iff₀`: `0 < c → (b / c ≤ a ↔ b ≤ a * c)`
- `div_mul_eq_mul_div`: `a / b * c = a * c / b`
- `mul_pow`: `(a * b) ^ n = a ^ n * b ^ n`
- `pow_le_pow_left₀`: `0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`
- `one_le_pow₀`: `1 ≤ a → 1 ≤ a ^ n`
- `le_mul_of_one_le_left`: `0 ≤ b → 1 ≤ a → b ≤ a * b`
- `Real.rpow_nonneg`: `0 ≤ x → ∀ y, 0 ≤ x ^ y`
- `Real.one_le_rpow`: `1 ≤ x → 0 ≤ z → 1 ≤ x ^ z`
- `inv_anti₀`: `0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`
- `inv_inv`: `a⁻¹⁻¹ = a`
- `norm_sub_le`: `‖a - b‖ ≤ ‖a‖ + ‖b‖`
- `Finset.sup'_le`: `(∀ b ∈ s, f b ≤ a) → s.sup' H f ≤ a`
- `Finset.le_sup'`: `b ∈ s → f b ≤ s.sup' _ f`
- `div_le_div_of_nonneg_right`: `a ≤ b → 0 ≤ c → a / c ≤ b / c`
- `lt_min`: `a < b → a < c → a < min b c`
- `min_le_left`: `min a b ≤ a`
- `half_pos`: `0 < a → 0 < a / 2`
- `pow_succ'`: `a ^ (n + 1) = a * a ^ n`
- `inv_le_of_inv_le₀`: `0 < a → a⁻¹ ≤ b → b⁻¹ ≤ a` (checked, not used)

## (d) Open issues and paper-delta candidates
- (d1) Hub, merge step: `RBM3D.lean` does not import `Step3` on the branch; the full `lake build` then fails the audit with `[RBM.Gauss.Sizes.STStep3II]` (pasted above). With `import RBM3D.Induction.Step3` after the last `import` line it passes (exit 0, 4128 jobs) and the registry pre-check exits 0. Not a defect of the file; the import is the hub's step (CLAUDE.md §3 (A) 4).
- (d2) `STStep3I` stays owed (not a target); `STStep3R` stays owed (generic form).
- (d3) `T2320a` (regime restriction): target 1 covers `ilambda² ≤ 1 - t` only; the paper (`3_5:1384`) splits at `1 - u = ilambda²` and treats `u ∈ [s, 1-ilambda²]` (a straddling `[s,t]` is the middle-time case, DECISIONS §132 (2), §68 (9)); targets 2 and 3 are the regimes `STReg5I`, `STCaseII`, not the paper's full case split.
- (d4) `T2320b` (what `≍` hides): `B_{u,0} ≍ |1-u|⁻¹` (`3_5:1384`) holds with `n`-independent constants only for `1-u ≥ ilambda²`: constant `2` in `step3_xB`; the control run of section (a) (script 1) gives ratio 4545455.05 at `1-u = 1e-7 < ilambda² = 1`.
- (d5) `T2320c` (`k = 1`): the paper states `(rela_XILXILK)` for `n ≥ 2` (`3_5:1387`); the Lean proof uses it at `m = 1` (`iterationsA_rela_of_K` is stated for `1 ≤ m`; its input `(eq:bcal_k)` at `m = 1` is `max|𝒦^{(1)}| ≺ 1`).
