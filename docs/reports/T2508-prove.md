Prover model: claude-sonnet-5-5
## (a) Math preflight — Wed Oct 14 13:55:50 UTC 2026 (row a: targets 1-8)

### (i) Exponent table
Sources: band `Induction/ExpIntEasy`, `ExpIntI`, `ExpWardII`, `Chain/Step34Gen`, `Chain/Step5CasesGen`, `Chain/Step6Gen` (lines as read). Notation `B=Bctl=W^-d(lam²+x)^-1+(Nx)^-1`, `x=1-u`, `N=(WL)^d`, `T=B²((lam²W^d)^(-1/5)+B)`, `A=Aof κm`.
| # | quantity (target) | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | regime-(iii) rates r (T3, `ExpIntEasy:259`) | r=11/5 and r=5/2; coefficient 1/(r-2)=5 and 2 | r>2 (`∫(1-v)^(-(r-1))`, `expIntEasy_integral_rpow` `:48`, `hr: 1<r`); `(1-v)B_v ≤ 2(1-u)B_u` | 11/5-2=1/5, 5/2-2=1/2 |
| 2 | (iii) rate vs target (T3, `ExpIntEasy:104`) | `5(2B)^(11/5)+2(2B)^(5/2) ≤ 64 T`; `B ≤ 2(lam²W^d)^-1` needs lam² ≤ 1-u | `2^(1/5) ≤ 6/5`, `2^(1/2) ≤ 3/2`; partial sums 29·B²G + 12·B²(6G/5+B) = 43.4 B²G+12B³ (`:161-178`) | 64-43.4 on B²G, 64-12 on B³; numerics row 14 |
| 3 | (iv) rate (T3, `ExpIntEasy:185,305`) | `((N(1-v))^-3)`, `∫(1-v)^-2 ≤ (1-u)^-1` gives `(N(1-u))^-3 ≤ B³ ≤ T` | none beyond u<1 (no regime hypothesis) | B³ ≤ T: factor (G+B)/B ≥ 1 |
| 4 | gK vs lam (R1; T6, W-b′) | `0 ≤ gK·lam, gK² ≤ lam², lam² ≤ A gK², 1 ≤ A`, `0<gK≤𝔡^-1` eventually | pattern `step34Gen_ratio_le` (`Step34Gen:704`) | A=1 (band), A=4 (gK=lam/2) both used below |
| 5 | kernel ratio at gK, v ≤ u (T6, W-b′) | `(gK²+1-v)/(gK²+1-u) ≤ 1+A`: `1-v ≤ 1-s ≤ lam² ≤ A gK²`, so `gK²+1-v ≤ (1+A)gK² ≤ (1+A)(gK²+1-u)` | `1-s ≤ lam²` (STReg5I); `gK>0` | 1+A ≤ 2A (A ≥ 1). Merged pattern `ExpIniIGen:762-765` uses ≤ 2A, squared 4A²; band is A=1: ratio ≤ 2 (`ExpIntI:80`), squared ≤ 4 (`:243`) |
| 6 | exponent of ratio (T6) | `(sum_res_2_NAL)`: n_-1 = 1; `(sum_res_2)`: n_ = 2 (`Step34Gen:560,571`) | ratio² ≤ (1+A)² ≤ 4A² | A=4: 25 vs 64 |
| 7 | regime-(i) log integral (T6) | `∫_s^u (1-v)^-1 = log((1-s)/(1-u)) ≤ 2 log L` | `1-s ≤ lam²`, `lam²/L² ≤ 1-u` (STReg5I at `sz.lam`; no gK; `ExpIntI:90`) | equality at the widest window (row 15) |
| 8 | (i) drift integral (T6, `ExpIntI:292`) | `≤ M·3T_u·2 log L`; `B^(11/5)+B^(5/2) ≤ 3T_u` (B_v ≤ B_u), rate needs `lam²/L^d ≤ 1-u` | `L^d ≥ L²` (d ≥ 2) | numerics row 15 |
| 9 | `log L ≺ 1` absorption (T6) | constant 3·2=6: `6 log L ≤ N^τ'` eventually | `N→∞`, `log L ≤ L`, `L^d ≤ N` | n=0, τ'=1/4: 8.32 vs 38.1 |
| 10 | window of the kernel pins (T6) | `STEKWinKgL`: `t ≤ 1-gK²/L²`, `W^-1 ≤ (1-t)/(1-s)` (`Step34Gen:503`) | from `1-t ≥ lam²/L²`, `gK ≤ lam`; `(con_st_ind)` `B_t^(𝔠d) ≤ (1-t)/(1-s) < 1` (`Induction/Defs.lean:168`) with `𝔠d=1/(100d)`, `d𝔠d=1/100<1` (`ExpIniIGen:801-804`) | ρ=(1-t)/(1-s)=0.999 vs B_t^(𝔠d) ≤ 0.9954 (row 11) |
| 11 | Ward constants (T1, T2; `ExpWardII:251,364`) | two-slot constant 3 (1+2, `‖Q g‖ ≤ 2‖g‖`, `ZeroModeCalc:124`); generic `(Im m)^-1 ≤ κm^-1` replaces `2/√(2κ)`; total `3/κm` | `3/κm ≤ N^(τ/2)` eventually, any τ>0 | τ=1 at n=0: 13.42 vs 1448.2; threshold N ≥ (3/κm)^(2/τ) |
| 12 | W-w size level (T1) | `(N η_u)^-1 = ((1-u)N Im m)^-1 ≤ κm^-1 B_u`; `(1-u)^-1 ≤ N B_u` since `N B_u(1-u) = 1+L^d(1-u)/(lam²+1-u) ≥ 1` | `η=(1-u)Im m` (`Step5CasesGen:140`), `κm ≤ Im m` | factor 4.76 at n=0, regime (ii) |
| 13 | W-w identities | slot 0: `Step5CasesGen_WardIdent` (`:187`) integrated, `STExpErrg = ∫L - K` (`Step6Gen:40`), loops integrable by CltRepg (`ExpWardIGen:109`), `K^(1)=m` by FamK1; slot 1: rotation of `TL, TK` (`ZeroModeGen_WardFam` `:226`, first conjunct of `ZeroModeGen_WardCls` `:289`, a field of `B45Gen_Facts`) maps `(σ,a)` to `(σ1σ0, a1a0)`, `σ0≠σ1` preserved | probability law (row 1), `0≤u<1` | exact identities |

### (ii) One concrete nondegenerate instance
Data: `d=3`, size index `n=0` of the merged `sz0` (`Defs/Sizes.lean:260-265`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^-6`), `𝔠=1/6`, `𝔡=1/10`, `κ=ε=1/10`, `κm=√(2κ)/2`, `𝔠d=1/300`, `ρ=0.999`; `1-s` and `1-t=ρ(1-s)` per regime as printed (each has `s<t<1`, `s>0`); (iii) integral checks use the widest window `s=0`, (i) log/drift checks the widest legal window. Hypotheses of the targets: (1) T1/T2 `κm ≤ Im m`, `η=(1-u)Im m`, `3/κm ≤ N^(τ/2)`; (2) T3/T4 `lam² ≤ 1-u` (iii), none (iv); (3) T6/T7 R1 at A=1 and A=4, window, `(con_st_ind)`, `log L`; T8 adds only the pins (hypotheses of the example). Command and output:
```
python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2508/inst.py
n=0: W=32 L=4 lam=0.015625 N=2097152  kappa_m=sqrt(2k)/2=0.2236  c_d=0.00333333333333333333333333333333  d*c_d=0.01
Im m(E) at E=+-(2-kappa): 0.3122 >= kappa_m: True
--- windows: regime, 1-s, 1-t, regime ok, B_t^cd <= (1-t)/(1-s) < 1, 1/W <= (1-t)/(1-s)
i   2.441e-04 2.439e-04 True 0.9909<=0.9990<1:True True
ii  1.526e-05 1.524e-05 True 0.9937<=0.9990<1:True True
iii 5.000e-01 4.995e-01 True 0.9682<=0.9990<1:True True
iv  3.815e-06 3.811e-06 True 0.9954<=0.9990<1:True True
n<=2999: ConStInd (rho=0.999), WO(1/10), Bandwidth(1/6), R1 (gK=lam/2, A=4) all hold: True ; lam_2999=2.14e-23, B_t(i)^cd at n=2999: 0.9146
--- (iii) u=3/4: B_u=1.239e-04 <= 2/(lam^2 W^d)=0.250 ; rates 6.023e-08 <= 64 T_u=6.479e-07  (slack 10.8x)
    int_0^u kernel*drift = 3.246e-09 <= 5(2B_u)^(11/5)+2(2B_u)^(5/2) = 6.023e-08 (slack 18.55x); coefficients 1/(r-2): 5.0 2.0
--- (iv) 1-u=lam^2/L^d: int = 1.953e-03 <= (N(1-u))^-3 = 1.953e-03 <= B_u^3 = 1.527e-02 <= T_u = 5.587e-02
--- (i) A=1 gK=lam/sqrt(A): R1 lam^2<=A gK^2 ok; ratio (gK^2+1-s)/(gK^2+1-u)=1.8824 <= 1+A=2 <= 2A=2; squared 3.543 <= (1+A)^2=4
--- (i) A=4 gK=lam/sqrt(A): R1 lam^2<=A gK^2 ok; ratio (gK^2+1-s)/(gK^2+1-u)=4.0000 <= 1+A=5 <= 2A=8; squared 16.000 <= (1+A)^2=25
    int (1-v)^-1 = 2.77259 <= 2 log L = 2.77259 ; 6 log L=8.318 <= N^(1/4)=38.1
    int (1-v)^-1 (B^(11/5)+B^(5/2)) = 3.295e-02 <= 3 T_u * 2 log L = 1.491e-01 (slack 4.53x)
--- (ii) 1-u=1.526e-05: (1-u)^-1=6.554e+04 <= N B_u=3.123e+05 (N B_u (1-u) = 1+L^d(1-u)/(lam^2+1-u) = 4.76471)
    (N eta)^-1 = 1.001e-01 <= kappa_m^-1 B_u = 6.659e-01 ; 3/kappa_m=13.42 <= N^(tau/2)=1448.2 (tau=1)
--- (ii) 1-u=1.524e-05: (1-u)^-1=6.560e+04 <= N B_u=3.123e+05 (N B_u (1-u) = 1+L^d(1-u)/(lam^2+1-u) = 4.76116)
    (N eta)^-1 = 1.002e-01 <= kappa_m^-1 B_u = 6.661e-01 ; 3/kappa_m=13.42 <= N^(tau/2)=1448.2 (tau=1)
```
External hypotheses (limit computation, TEAM §8 lesson 14): the pins `STEKSumNdecaygL`, `STEKSumRes2NALgL`, `STEKSumRes2gL`, `STExpDuhamelZgL/QgL`, `STExpLKLKHigL`, `STExpDriftDecaygL`, `STExpWardIgL'`, `STExpIniIgL'`, `LWtermEXPG`, `STExpIntIgL'` stay hypotheses of the examples; the deterministic data they read were checked above along n ≤ 2999 (line "n<=2999": `WO(1/10)`, `Bandwidth(1/6)`, R1 with gK=lam/2 and A=4, `(con_st_ind)` at ρ=0.999) and at the limits `lam_n=(2(n+1))^-6 → 0`, `W_n → ∞` (printed `lam_2999=2.14e-23`); `B_t^(𝔠d)` at n=2999 is 0.9146 ≤ 0.999.
Limits of the script: it checks size-level inequalities at one size index and the listed families for n ≤ 2999; it does not check the Lean statements or the BA discharges.

### Verdict per target (row a)
- T1 `expWII_slot0g/slot1g/det_boundg`: PASS (rows 11-13; the generic Ward hypotheses are the family rows `Step5CasesGen_FlowFacts`, FamRep, FamK1, FamWardIdent, `B45Gen_Facts`).
- T2 `STExpWardIIConclgL_of_avgU`, `stExpWardIIgL_of`: PASS (constant `3/κm`, rows 11-12).
- T3 `expIntEasy_kernel_seqg`, `expIntIII/IV_int_unifg`: PASS (rows 1-3; `STEKSumNdecaygL` has no ratio, so no R1 in regimes (iii), (iv)).
- T4 `STExpIntConclgL_of_int`, `STExpIntIII/IVConclgL_of_flow`, `stExpIntIIIgL_of`, `stExpIntIVgL_of`: PASS.
- T5 `STExpIntQConclgL'`, `STExpIntIgL'` (vocabulary, bridges): PASS (no numerical constant).
- T6 `expIntI_kernel_unifg`, `expIntI_concl_of_kernelg`, `expIntI_sameg`: PASS (W-b′ closes at `1+A` from R1 and STReg5I alone, rows 4-10; crossing from `sz.lam` to `gK` is only `gK ≤ lam ≤ √A gK`).
- T7 `st6_caseI_coreg'`, T8 `ST_step6_caseI_of_pinsgL''` and its `_core` corollary: PASS (no new exponent; the two pins are the primed twins; `STExpIntIgL'` is a hypothesis of T8 until row b).
Watch items W-b′ and W-w close within their named texts; no row, layout or binding text changes.
Overall verdict: PASS. 1a-audit needed: no.

## (b) Script output, row a (targets 1-8) — branch `t/T2508` from main 22467000, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2508` — written Wed Oct 14 14:33:56 UTC 2026
```
$ lake build RBM3D.Chain.ExpWardIIGen RBM3D.Chain.ExpIntEasyGen RBM3D.Chain.ExpIntIGen      exit 0   tail: Build completed successfully (3959 jobs).
$ lake build  (whole library, `#assert_rbm_axioms` with the registry edits)                  exit 0   tail: Build completed successfully (4407 jobs).   lines matching "error": 0
  audit line (RBM3D.lean:637): 15353 theorems, 4727 definitions, 0 axioms in `RBM`; premises found by scanning: 131 (borrowed 1, owed 57, structural 53, refuted 6, superseded 14).
$ git diff --numstat 22467000 HEAD            (5 commits on t/T2508, author Jun Yin <321276894+JYin80@users.noreply.github.com>)
435 0 RBM3D/Chain/ExpWardIIGen.lean | 478 0 RBM3D/Chain/ExpIntEasyGen.lean | 835 0 RBM3D/Chain/ExpIntIGen.lean | 3 0 RBM3D.lean | 7 4 RBM3D/Test/Axioms.lean
$ git diff --name-only main...t/T2508 -- RBM3D/Induction RBM3D/Graph RBM3D/BA | wc -l      -> 0      (merged Chain/*: only the three new files)
```
**(1) `wc -l` against the bottom-up figures** (stop 2,450): ExpWardIIGen 435 (420), ExpIntEasyGen 478 (500), ExpIntIGen 835 (825); Σ 1,748 (1,745). `RBM3D.lean` +3, `Test/Axioms.lean` +7 -4.
**(2) imports / importers.** ExpWardIIGen ← Step6KitGen, Induction/ExpWardII, Step5CasesGen, B45Gen, CltGen. ExpIntEasyGen ← Step6KitGen, Induction/ExpIntEasy. ExpIntIGen ← Step6KitGen, Induction/ExpIntI,
ExpIniIGen, ExpWardIGen, ExpIntIIGen, ExpAvgGen. Importers: `RBM3D.lean` only. Closure script: the union closure equals the closure of the planned imports (244 modules incl. the 11 roots; the ticket says 243), `RBM3D.BA.*`: 0, `Chain/Step2Kern`: 0.
**`#print axioms`** of all 28 new public declarations (script `axioms.lean`): every line `[propext, Classical.choice, Quot.sound]`; grep `sorry|admit|native_decide|axiom` over the three files: 0 hits.
**(3) Targets, extracted by script** (`file:line name : conclusion`; hypotheses in the files; the two defs are `Prop`-valued):
```
ExpWardIIGen.lean:132 expWII_slot0g : STExpErrg C μ n u σ a - zeroModeOp d (sz.L n) 0 (fun b => STExpErrg C μ n u σ b) a = ((((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω ∂μ) - C.K n u (fun _ : Fin 1 => …
ExpWardIIGen.lean:175 expWII_slot1g : STExpErrg C μ n u σ a - zeroModeOp d (sz.L n) 1 (fun b => STExpErrg C μ n u σ b) a = ((((∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a 0) ω ∂μ) - C.K n u (fun _ : Fin 1 => …
ExpWardIIGen.lean:195 expWII_det_boundg : ‖STExpErrg C μ n u σ a - zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErrg C μ n u σ b) a‖ ≤ 3 * (M * (((sz.size n : ℕ) : ℝ) * C.eta n u)⁻¹)
ExpWardIIGen.lean:231 STExpWardIIConclgL_of_avgU : STExpWardIIConclgL C μ s t
ExpWardIIGen.lean:288 stExpWardIIgL_of : STExpWardIIgL d law Flow mk T0
ExpIntEasyGen.lean:50 expIntEasy_kernel_seqg : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool, ‖Step2Gen_UN C n σ v (u n) (fun b => STExpDriftg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - v) /…
ExpIntEasyGen.lean:200 expIntIII_int_unifg : PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ) (fun b => STExpDriftg C (law sz) n v p.2.1 b) p.2.2‖) (fun n p…
ExpIntEasyGen.lean:228 expIntIV_int_unifg : PrecL sz (law sz) (U := STIdx2 sz s t) (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), Step2Gen_UN C n p.2.1 v (p.1 : ℝ) (fun b => STExpDriftg C (law sz) n v p.2.1 b) p.2.2‖) (fun n p…
ExpIntEasyGen.lean:260 STExpIntConclgL_of_int : STExpIntConclgL C μ ∅ STSigAll s t
ExpIntEasyGen.lean:291 STExpIntIIIConclgL_of_flow : STExpIntConclgL C (law sz) ∅ STSigAll s t
ExpIntEasyGen.lean:301 STExpIntIVConclgL_of_flow : STExpIntConclgL C (law sz) ∅ STSigAll s t
ExpIntEasyGen.lean:323 stExpIntIIIgL_of : STExpIntIIIgL d law Flow mk T0
ExpIntEasyGen.lean:339 stExpIntIVgL_of : STExpIntIVgL d law Flow mk T0
ExpIntIGen.lean:62 STExpIntQConclgL' : Prop
ExpIntIGen.lean:76 STExpIntIgL' : Prop
ExpIntIGen.lean:89 bandFM_STExpIntQConcl' : STExpIntQConcl' sz E s t ↔ STExpIntQConclgL' (bandFM sz E) (Sizes.seqP sz) s t
ExpIntIGen.lean:98 STExpIntI'_of_gL' : STExpIntI' d
ExpIntIGen.lean:202 expIntI_kernel_unifg : ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) → ‖Step2Gen_UN C n σ v (u : ℝ) (𝒜 n v)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2 * X n v)
ExpIntIGen.lean:300 expIntI_concl_of_kernelg : STExpIntConclgL C μ ∅ P s t
ExpIntIGen.lean:369 expIntI_sameg : STExpIntConclgL C (law sz) ∅ STSigSame s t
ExpIntIGen.lean:473 st6_caseI_coreg' : STStep6ConclgL C μ s t
ExpIntIGen.lean:543 ST_step6_caseI_of_pinsgL'' : STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => STExpAvgUgL (mk sz z) (law sz) s t → STStep6ConclgL (mk sz z) (law sz) s t)
ExpIntIGen.lean:590 ST_step6_caseI_of_pinsgL''_core : STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u) → STStep6ConclgL (mk sz z) (law s…
```
**Statement diff against the `T2508_*` pins (compiled; scratch `<scratchpad>/T2508/audit_T2508a.lean`, uncommitted; exit 0, 0 errors).** It contains the check's Part 2 verbatim and
`Iff.rfl` / term checks: `T2508_ExpIntQConclgL' C μ s t ↔ STExpIntQConclgL' C μ s t`; `T2508_ExpIntIgL' … ↔ STExpIntIgL' …`; `T2508_CaseICoreg' C μ := @st6_caseI_coreg' d sz C μ`;
`T2508_ConsumerOf` from `ST_step6_caseI_of_pinsgL''` and `…_core` (the 12 conjuncts of `T2508_ConsumerPrem` in the order of the hypotheses); `T2508_RowAOf` from `stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of`
(my premises are `hBase.1`, `hBase.2.2.1` of `T2508_FamBase` plus the row premises: fewer than `RowAOf`). The dispatcher's `docs/tickets/checks/T2508-check.lean` compiles on this branch: `lake env lean` exit 0, 0 errors.
**(4) Compiled nonempty instances** (26 `example`s; `d = 3`; band data of each file at `bandFM`; list by `grep -n '^example'`):
```
ExpWardIIGen.lean :366 :379 :393 expWII_slot0g/slot1g/det_boundg (n=0,u=15/16,σ=(+,-),a=(0,0); det_bound with M = η⁻¹+1 discharged by norm_Lloop_le, ‖m‖=1)  :408 STExpWardIIConclgL_of_avgU (hyp: STExpAvgUgL)
                  :417 stExpWardIIgL_of at the band tuple (no hypothesis)  :427 stExpWardII_gen_band at (szB,zB,15/16,31/32) via inst_expWardII
ExpIntEasyGen.lean :390 expIntEasy_kernel_seqg (hyp: the drift bound h) :404 expIntIII_int_unifg (hyp: STExpDriftHiConclgL) :415 expIntIV_int_unifg (hyp: STExpDriftLoConclgL) :426 STExpIntConclgL_of_int (hyp: STExpDuhEqgL, drift)
                  :436 STExpIntIIIConclgL_of_flow :444 STExpIntIVConclgL_of_flow :454 :459 stExpIntIIIgL_of, stExpIntIVgL_of at the band tuple (no hypothesis) :466 :470 band re-derivations via inst_expIntIII/IV
ExpIntIGen.lean   :666 bandFM_STExpIntQConcl' :670 STExpIntI'_of_gL' (hyp: STExpIntIgL') :679 expIntI_kernel_unifg at (szB,zB,7/8,15/16), σ=(+,+), X≡1, family 𝒜_v = 1_{{a=0}} (no hypothesis) :723 expIntI_sameg (hyp: drift bound, drift decay)
                  :736 expIntI_concl_of_kernelg (hyp: kernel bound) :749 st6_caseI_coreg' (hyp: the conclusions of the ingredient pins) :773 ST_step6_caseI_of_pinsgL'' via inst_ing6_I (hyp: LWtermEXPG, STExpIntIgL')
                  :788 ST_step6_caseI_of_pinsgL''_core applied at the data (hyp: LWtermEXPG, STExpIntIgL', the STIngR6gL premises at s) :818 :824 the two band re-derivations via inst_step6I (hyp: LWtermEXP, STExpIntIgL')
```
Discharged in the instances: flow, times, regime, admissibility, probability law, flow facts, `CltRepg`, Ward identity and class, `K^(1)=m`, `(con_st_ind)` (`conStInd_const`, `𝔠d = 1/300`), the kernel pins `stek_sumNdecaygL_band`, `stek_sumRes2NALgL_band`, the band class with R1 at `Aof = 1`,
the Duhamel family (`stExpDuhamelZ_holds`), 16a (`stImproveCoregL_of` at `ExpAvgGen_band_W1fam`), 16b/row 15. Hypotheses that stay: pins of other gates (listed above). The sum-zero branch of `hpin` is not instantiated (row b's `expIntIQ_inig`).
**(5) Family table as used** (T2506b O2, file column updated): 1 `hμ` and 3 `Step5CasesGen_FlowFacts` all three files (BA `baStep5CasesGen_flowFacts`); 4 F7 `Step2EventsGen_Rot3` ExpIntIGen wrapper (`Step2EventsGenTw_baRot3`);
5 `STEKSumNdecaygL` + `hKer` (∃ κm, class at `gK`) ExpIntEasyGen (BA `baEKSumNdecay_holds`); 7, 8 `LWtermEXPG`, `STExpDuhamelZgL/QgL`, `STExpLKLKHigL`, `STExpDriftDecaygL`, `STExpWardIgL'`, `STExpIniIgL'` ExpIntIGen wrapper (hypotheses of the wrapper; BA: V1-BA); 9 `∃ H₀ g' E, CltRepg` ExpWardIIGen (BA `baCltRepg_holds`); 16 `STEKSumRes2NALgL` (+ `STEKSumRes2gL` branch) and R1 ExpIntIGen `expIntI_kernel_unifg`, `expIntI_sameg` (U3-BA (a)); 19 `K^(1)_σ = m_σ` eventual, guarded ExpWardIIGen
`stExpWardIIgL_of`, unguarded `K^(1)_+ = m` ExpIntIGen wrapper (`baKsol_oneLoop`); 19′ `B45Gen_Facts` (field `ZeroModeGen_WardCls`) ExpWardIIGen (`baB45Gen_facts`); 21 average per flow `STExpAvgUgL` ExpWardIIGen (hAvg), ExpIntIGen (hAvgU, `Concl` slot; corollary 16c);
23 `Step5CasesGen_WardIdent` ExpWardIIGen (`baStep5CasesGen_wardIdent`). Not read in row a: 9′, 17 (`IniTermGen_CltFlow`, `STKboundgL`), 22 (`Step5KerGen_ThDecay`).
**(6) UBA-C1 as used.** R1 (`hcmp`) is read only in the private `ExpIntIGen_kernel_seq` (and carried by `expIntI_kernel_unifg`, `expIntI_sameg`): window `step34Gen_winK_of_cmp`, decay class `step34Gen_decayK_of_cmp`, ratio `step34Gen_ratio_le` (`≤ A·2`, constant `4A²`); `STReg5I` at `sz.lam`. ExpIntEasyGen: kernel at `gK` through the pin, no ratio, no R1.
ExpWardIIGen: `Bctl` only. `sz.withLam` occurs only in the private `ExpWardIIGen_integrable_L` (the proof of row 9's text `CltRepg`, as `ExpWardIGen:109`).
**(7) V1L-C1 grep and average inputs** (`STImproveExpAver|st6_expAvgU_of_pin|stImproveExpAver_holds|hAvg :`, script `greps.py`, hits labelled): `STExpWardIIConclgL_of_avgU:238` and the example `:408` (`hAvg : STExpAvgUgL …`: per flow); `ST_step6_caseI_of_pins''_gen_band:625, 634` (re-derivation proof body: 16b + `st6_expAvgU_of_ping`).
No public statement reads `STImproveExpAvergL` or `st6_expAvgU_of_ping`. Average inputs: targets 2, 7, 8 read `STExpAvgUgL (mk sz z) (law sz) s t` on the `Concl` slot (V1-BA via 16c); target 8's corollary reads `STImproveCoregL` + `ExpAvgGen_W1iii` on `[s,t]` (16a/TL1).
**(8) Registry and scan.** Before the registry edit the build fails with: `axiom audit: 2 premise(s) … in none of borrowedProps, owedProps, structuralProps, refutedProps, supersededProps: [RBM.BA.STExpIntIgL', RBM.BA.STExpIntQConclgL']`.
Edits (`git diff 22467000 HEAD -- RBM3D/Test/Axioms.lean`): header of the T2502 block "V1s2'/V1s3'" → "V1s2′ (T2506), V1s3′ (T2508)"; `STExpWardIIgL`, `STExpIntIIIgL`, `STExpIntIVgL` → "generic: `<producer>` (T2508 row a, `Chain/<file>`) under its family rows";
`owedProps` += `STExpIntIgL'` (owner T2508 row b); `structuralProps` += `STExpIntQConclgL'`. After: build exit 0; scan lines `RBM.BA.STExpIntIgL': 5 [no certificate]` (the wrapper, its corollary, `STExpIntI'_of_gL'`, the two re-derivations), `STExpIntIIIgL: 3`, `STExpIntIVgL: 3`.
**(9) Greps (labelled).** Public defs (`grep -nE '^(noncomputable )?(def|abbrev|structure) '`): `STExpIntQConclgL'` (ExpIntIGen:62), `STExpIntIgL'` (:76), nothing else. Name clash (28 new public names against all other `RBM3D/` files): 0 hits except the registry lines I added in `Test/Axioms.lean`.
C1/X1-C1 (T2502 `:73` + `ThetaN d|thetaKer d|seqHflow|STLKM`): hits only in bridges (`bandFM_STExpIntQConcl'`, `STExpIntI'_of_gL'`), re-derivations (`*_gen_band`), private helpers (`ExpWardIIGen_integrable_L|K1_band|L1_band|bandData`, `ExpIntEasyGen_KerF_band`, `ExpIntIGen_avgU_iff`) and examples; 0 in a generic statement.
U5S-C3 `∀ \(sz : Sizes d\)` hits = the family rows of (5) and the tuple binders. UBA `sz.withLam|gK`: rows 5, 16 and targets 3, 4, 6 only (plus the one private `withLam` of (6)). `STGridRepNgL`: 0 hits. No kernel def (U-C4), no `STGridRepNgL`, no `Step5KerGen_ThDecay`/`Step5CasesGen_WardIdent`/`B45Gen_Facts`/`STEK*gL` copy.
**(10) Band files untouched; frozen names unchanged.** The diff touches no file of `RBM3D/Induction`, `Graph`, `BA`, no merged `Chain/*`; `stStep6I_of_LW`, `stExpWardII_holds`, `stExpIntIII_holds`, `stStep6IV_holds`, `QopDecay_*` are unedited. `open private` list (no `private` deleted):
`expWII_zeroModeOp_eq0`, `expWII_zeroModeOp_eq1`, `expWII_zeroModeSet_zero`, `expWII_STKloop_eq1` (ExpWardII); `expIntI_window`, `expIntI_lift`, `expIntI_Bctl_nonneg` (ExpIntI); `ExpIntIIGen_drift_pi`; `Step5CasesGen_prec_mono`; `Step6KitGen_K1_band`, `Step6KitGen_KerFR1_band`.
Ports: pattern copies from merged RBM3D files (`ExpWardIGen`, `Step6KitGen`, `ExpIniIGen`, `ExpIntIIGen`, `ExpIntEasy`/`ExpIntI`/`ExpWardII` band bodies); nothing from `../RBM1D`, `../RBM2D` (no diff-stat).

**Narrative.**
1. All eight targets are proved as pinned; the total of the three new files is 1,748 lines against the bottom-up 1,745 (stop 2,450); no reserve file, no stop rule fired.
2. W-w (ExpWardIIGen): slot 0 is `Step5CasesGen_WardIdent` integrated (loops integrable by `CltRepg`, copy of `ExpWardIGen_integrable_L`; `∫(L-K) = ∫L - K` for the probability law), slot 1 the cyclic rotation field of `ZeroModeGen_WardCls` (`ExpWardIIGen_swap`);
   `(N η_u)⁻¹ ≤ κm⁻¹ B_u` from `η = (1-u) Im m` and `(N(1-u))⁻¹ ≤ B_u` (`ExpWardIIGen_inv_N_le`); constant `3 κm⁻¹` (the band `6/√(2κ)`).
3. W-b′ (ExpIntIGen): the kernel at `gK` closes inside the named text (R1 only at window, decay class, ratio; `STReg5I` at `sz.lam`), constant `4 (Aof κm)²` for both branches (NAL ratio `≤ 2A ≤ 4A²`, sum-zero `(2A)²`); the band is `A = 1`, constant 4.
   `hpin` is one disjunction (`σ₁ = σ₂ ∧ STEKSumRes2NALgL` or sum-zero `∧ STEKSumRes2gL`) so `expIntI_sameg` needs only the NAL pin.
4. The band `STExpIntI'` is obtained from the generic pin only one way (`STExpIntI'_of_gL'`; `STExpDuhEq` is `∀ n`, `STExpDuhEqgL` eventual: D725). Consequence for V1L-C1 (ii): the band `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int` cannot be re-derived from a band `hInt`.
   The two re-derivations `ST_step6_caseI_of_pins''_gen_band`, `ST_step6I_of_LW_Int_gen_band` conclude the band `STStep6I d` from the band ingredient pins (through their bridges) and the generic `STExpIntIgL'`, with the global average recovered (16b `stImproveExpAvergL_of` at the band family texts, `st6_expAvgU_of_ping`), not read.
5. The wrapper `ST_step6_caseI_of_pinsgL''` takes `K^(1)_+ = m` unguarded (the form of `T2508_ConsumerPrem` and of the merged `ST_step6_caseI_of_pinsgL`), not row 19's eventual guarded form used by `stExpWardIIgL_of`.
6. `STExpIntIgL'` and `STExpIntQConclgL'` are registered (owed: T2508 row b; structural); row b removes the owed line when `stExpIntIgL'_of` lands.
7. The instance of `expIntI_kernel_unifg` uses the delta family `𝒜_v = 1_{{a=0}}` (nonzero, decays because it vanishes off `0` and the far-pair premise fails at `a = 0`); the sum-zero branch is first read in row b.

## (c) Verified Mathlib names (all by `#check` after importing `RBM3D.Chain.ExpIntIGen`; script `names.lean`, exit 1 only for the two root-namespace names below)
`MeasureTheory.Measure.nonempty_of_neZero`; `MeasureTheory.integral_div`; `MeasureTheory.integral_const_mul`; `MeasureTheory.integral_finsetSum`; `MeasureTheory.integral_sub`; `MeasureTheory.norm_integral_le_of_norm_le_const`;
`intervalIntegral.norm_integral_le_of_norm_le`; `intervalIntegral.integral_const_mul`; `Complex.abs_im_le_norm`; `Complex.norm_real`; `Complex.norm_natCast`; `pi_norm_le_iff_of_nonneg`; `norm_le_pi_norm`; `Real.one_le_rpow`; `Real.rpow_nonneg`;
`ContinuousOn.intervalIntegrable`; `ContinuousOn.inv₀`; `Filter.eventually_all`; `MeasureTheory.IsProbabilityMeasure.measure_univ`; `Real.rpow_le_rpow`; `inv_anti₀`. Root names (not under `MeasureTheory.`, `#check @MeasureTheory.integral_im` fails): `integral_im`, `integral_ofReal`.
Verified absent / deprecated: `if_neg` is deprecated in this Mathlib (warning; replaced by `simp only [h0, ↓reduceIte]`).

## (d) Open issues and paper-delta candidates
- **T2508a** (finding, Lean-internal consequence of D725): the band `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int` are re-derived with a generic `hInt : STExpIntIgL'` (band `STExpIntI'` is one-way from it); ticket text "re-derived" read accordingly.
- **T2508b** (Lean-internal constants): ExpWardII constant `3 κm⁻¹` (band `6/√(2κ)`); kernel at `gK` constant `4 (Aof κm)²` (band 4); no paper statement changes. Expected D725, D727 only otherwise.
- Open: the sum-zero branch of `expIntI_kernel_unifg` has no instance in row a; `STExpIntIgL'` is a hypothesis of target 8 until row b (`stExpIntIgL'_of`); the second-order cleanup of the header docstrings (long-line warnings before `set_option`, as in the merged `ExpWardIGen`) is left as is.

## Repair (round 1, audit RETURN of T2508-audit.md §6) — Wed Oct 14 14:40:42 UTC 2026
Repairer model: claude-opus-5-5. Scope: Required for resubmission items 1-4 only (instances of targets 4 and 7); no statement, signature, registry or import line changed.
```
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2508 log --oneline -1 ; git diff --stat b6b262b5 HEAD
5d7f96f7 T2508 row a repair: discharge the Duhamel identities in the target 4 and 7 instances
 RBM3D/Chain/ExpIntEasyGen.lean | 28 ++++++++++++++++------------
 RBM3D/Chain/ExpIntIGen.lean    | 12 ++++++------
 2 files changed, 22 insertions(+), 18 deletions(-)
$ lake build RBM3D.Chain.ExpIntEasyGen RBM3D.Chain.ExpIntIGen   (tail)
⚠ [3956/3957] Built RBM3D.Chain.ExpIntEasyGen (5.5s)
⚠ [3957/3957] Built RBM3D.Chain.ExpIntIGen (8.9s)
Build completed successfully (3957 jobs).
$ wc -l RBM3D/Chain/ExpWardIIGen.lean RBM3D/Chain/ExpIntEasyGen.lean RBM3D/Chain/ExpIntIGen.lean
     435 RBM3D/Chain/ExpWardIIGen.lean
     482 RBM3D/Chain/ExpIntEasyGen.lean
     835 RBM3D/Chain/ExpIntIGen.lean
    1752 total                                                   (stop size 2,450)
$ grep -nwE 'sorry|admit|axiom|native_decide' (the two files) | wc -l
0
$ python3 -I <scratch>/T2508/kept.py RBM3D/Chain/ExpIntEasyGen.lean RBM3D/Chain/ExpIntIGen.lean   (hypotheses kept by each example)
ExpIntEasyGen.lean:391 kept: h
ExpIntEasyGen.lean:405 kept: hDr
ExpIntEasyGen.lean:416 kept: hDr
ExpIntEasyGen.lean:427 kept: hDr
ExpIntEasyGen.lean:438 kept: hDr
ExpIntEasyGen.lean:447 kept: hDr
ExpIntEasyGen.lean:458 kept: none
ExpIntEasyGen.lean:463 kept: none
ExpIntEasyGen.lean:470 kept: none
ExpIntEasyGen.lean:474 kept: none
ExpIntIGen.lean:666 kept: h
ExpIntIGen.lean:670 kept: h
ExpIntIGen.lean:679 kept: none
ExpIntIGen.lean:723 kept: hdr hdd
ExpIntIGen.lean:736 kept: hker
ExpIntIGen.lean:749 kept: hlk hegt hdec hAvgU hward hini hint
ExpIntIGen.lean:773 kept: hLW hInt
ExpIntIGen.lean:788 kept: hLW hInt hLK0 hDec0 hExp hS2 hLmax hLKU hS5
ExpIntIGen.lean:818 kept: hLW hInt
ExpIntIGen.lean:824 kept: hLW hInt
```
Updated instance list (target 4: ExpIntEasyGen:427 `STExpIntConclgL_of_int`, :438 `STExpIntIIIConclgL_of_flow`, :447 `STExpIntIVConclgL_of_flow`; target 7: ExpIntIGen:749 `st6_caseI_coreg'`):
`hduh : STExpDuhEqgL` is removed from :427, :438 (passed `st6_duhEq_of_ping (STExpDuhamelZ_to_gL 3 _ (stExpDuhamelZ_holds 3)) _ flow_z0 sz0_hs0 _`) and from :447
(same term with `flow_zG`); `hduh` and `hDuQ` are removed from :749 (passed the `flow_zB` `stExpDuhamelZ_holds` term and `st6_duhEqQ_of_ping (STExpDuhamelQ_to_gL 3 _ (stExpDuhamelQ_holds 3)) _ flow_zB _ _ Cq c ϑ hϑ`).
Docstrings of the four examples and the ExpIntEasyGen §6 header now say the Duhamel identity is discharged. The kept hypotheses above are drift bounds, pin conclusions,
`STExpAvgUgL`, `LWtermEXPG`, `STExpIntIgL'` and `STIngR6gL` premises (unchanged from round 1, judged allowed in the audit §4).
