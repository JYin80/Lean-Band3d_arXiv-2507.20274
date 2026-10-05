Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 03:46:46 UTC 2026

### (i) Exponent table
Notation: `N = sz.size n = (W L)^d`, `Δ = (t−s)/K`, `k = m` the loop length (m ≥ 2), `H = 16N`, `Y = N^{τ_K} = N` (τ_K = 1), `c = 1`.

| # | quantity | value | constraint / source | slack |
|---|---|---|---|---|
| 1 | `H` | `16N` | needs `η_u⁻¹, η_v⁻¹, (1−v)⁻¹ ≤ H/c`; `η_u ≥ N^{-1+ε}/16` (row 10), `1−v ≥ η_v` (row 11); so inverses `≤ 16 N^{1−ε} ≤ 16N` for every ε > 0, N ≥ 1 | factor `N^ε` (ε-independent) |
| 2 | `Z₁` (coeff. of `Δ^{3/2}`) | `16(m+3)⁴·32^{m+4}·N^{m+8}` | `envConst = 16(m+3)⁴N⁴(1+η_v⁻¹)^{m+4}` (Path/OneStep.lean:78), `(1+1/c)H = 32N`; `N⁴(32N)^{m+4}` | exact |
| 3 | `Z₂` (coeff. of `Δ²`) | `(2m⁴+m⁶)16^{4m}N^{4m+7} + 2(m+m2^m)16^{m+2}N^{m+3}` | terms B, C of `gridEnv_stepErr_le` (GridEnvelopeN.lean:268) at `B = Y(H/c)^m = N(16N)^m`: B-term `(2m⁴+m⁶)N³B⁴`, C-term `2(m+m2^m)H²B`; the 𝒰-step bracket `uStepC·M_j ≤ uStepC·2B` equals the C-term; `B-term + 2·C-term ≤ 2 Z₂` | total step: `‖r_j‖ ≤ Z₁Δ^{3/2}+2Z₂Δ²` |
| 4 | `c₂(m)` | `(2m⁴+m⁶)16^{4m}+2(m+m2^m)16^{m+2}`; `Z₂ ≤ c₂ N^{4m+7}` | `N^{m+3} ≤ N^{4m+7}` | m=2: 4.123e11; m=3: 2.508e17 |
| 5 | `C₀` | `m+9` | `‖Rem_k‖ ≤ (Z₁+2Z₂√Δ)√Δ ≤ N^{m+9}√Δ`: need `2Z₂√Δ ≤ 1` and `Z₁+1 ≤ N^{m+9}`; `c₁'N^{m+8}+N^{m+8} ≤ N^{m+9}` iff `N ≥ c₁'+1`, `c₁' = 16(m+3)⁴32^{m+4}` | one power of N; threshold `N₀(m) = c₁'+1`: m=2: 1.0737e13; m=3: 7.1248e14 |
| 6 | `CK₀` | `8m+20` (prover fixes; `8m+16` also closes) | `K ≥ N^{CK₀}`, `KΔ = t−s ≤ 1` ⇒ `Δ ≤ N^{−CK₀}`, `√Δ ≤ N^{−CK₀/2}`; `2Z₂√Δ ≤ 2c₂N^{4m+7−CK₀/2}` ≤ 1 needs `CK₀ > 8m+14` and `N^{CK₀/2−4m−7} ≥ 2c₂` | `CK₀/2−(4m+7) = 3` (at 8m+20): `N ≥ (2c₂)^{1/3}`: m=2: 9378, m=3: 794540; at 8m+16 slack 1: `N ≥ 2c₂` (8.2e11, 5.0e17, i.e. later n) |
| 7 | `ΔH ≤ 1` | `Δ·16N ≤ 16N^{1−CK₀}` | `N^{CK₀−1} ≥ 16`; implied by `N ≥ 16`, `CK₀ ≥ 2` | `CK₀−1 ≥ 35` powers of N |
| 8 | window | `0 ≤ s ≤ u_j < u_{j+1} ≤ t ≤ lemT z < 1` | `lemT_lt_one` (Semicircle.lean:209, Im z > 0 from `N^{−1+ε} ≤ Im z`); `u+Δ<1`, `(1−v)⁻¹` finite; `KΔ = t−s < 1` | `1−lemT ≥ η_{lemT} > 0` |
| 9 | flow bulk | `\|E_n\| ≤ 2−κ` | `lemma28_quant` (:359) / `abs_lemE_le` (:309): `\|lemE z\| ≤ \|Re z\| ≤ 2−κ`; hence `\|E\|<2` for `etaT_le_of_le`, `etaT_pos` | κ > 0 |
| 10 | `η_u` lower | `η_u ≥ η_{lemT} = Im z_{t₀} ≥ Im z/16 ≥ N^{−1+ε}/16`, all `u ≤ lemT` (also u < 0) | `etaT_le_of_le` (CondDom:288), `etaT_eq_zt_im` (GLoop:79), `lemma28_quant` (1/16·Im z ≤ Im z_t), `locDomain` | no loss in ε |
| 11 | `η_u` upper | `η_u = (1−u)Im m ≤ 1−u` | `Im m = √(4−E²)/2 ≤ ‖m‖ = 1` (`norm_mSigma`, Semicircle.lean:87; `mE_im`) | factor `Im m ≤ 1` |
| 12 | 𝒦 envelope | `‖𝒦_w‖ ≤ N^{τ_K}η_v^{−m}`, τ_K = 1, `w ∈ [0,v]`, eventually in n | `stKbound_of_flow` (KLFinal.lean:302; `3 ≤ d`, `0<κ`; `N→∞`, `0<lam≤𝔡⁻¹` from `STFlow`); `exists_norm_Kcal_le_win` (GridDriftN:1098), `gridDriftN_envelope` (GridEnvelopeN:111, τ_K>0, `t n < 1`, `2 ≤ m`) | τ_K free; 1 used |
| 13 | `𝓛` loop | `‖𝓛_u‖ ≤ η_u^{−m}(W^{−d})^{m−1}` | `norm_gloop_le_of_le_abs_im` (Split:757), Hermitian `pathH`; `M_j = η_{u_j}^{−m}(W^{−d})^{m−1}+Y η_t^{−m} ≤ 2B` (`W ≥ 1`) | factor 2 absorbed in row 3 |
| 14 | assembly `CK` | `max(CK_rem, CK_tail(D), CK_wtail(D))` | `N ≥ 1` (`one_le_size`) ⇒ `N^{CK_i} ≤ N^{CK}` (monotone in exponent), so `K ≥ N^{CK}` gives each; all `≥ 0` | CK_rem independent of D |
| 15 | parameter order | `m → C₀=m+9 → (κ,ε,𝔡,𝔠,sz,z,s,t) → CK₀(m) → K → n ≫ 1` | pin's order; `C₀, CK₀` depend on `m` only; no ε, κ, 𝔡, 𝔠 in constants | — |

Pathwise identity (target 2), no hypothesis: `r_j = 𝔼[A_{j+1}|F_j]−A_j−ΔDrift_j`, `Rem_k=Σ_{j<k} r_j`, `Mart_k=Σ_{j<k}(A_{j+1}−𝔼[A_{j+1}|F_j])`; `A_{j+1}−A_j = r_j+ΔDrift_j+(A_{j+1}−𝔼[..])` is algebra, sum over `j<k`. `predIncN = 𝔼[A_{j+1}|F_j] − 𝒰A_j` (GridDuhamelN:284), so `r_j = [predIncN − Δ S_j] + [𝒰A_j − A_j − ΔΘA_j]` with `STgDriftN = ΘA + S` (Step2Defs:784).
Sum: `‖Rem_k‖ ≤ K(Z₁Δ^{3/2}+2Z₂Δ²) = (t−s)(Z₁√Δ+2Z₂Δ) ≤ (Z₁+2Z₂√Δ)√Δ` (t−s<1).

### (ii) Concrete nondegenerate instance
`d = 3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `N=(WL)^3`; Defs/Sizes.lean:260), `z0 = 1/2 + i N^{−4/5}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `s≡0`, `t≡1/16`, `m∈{2,3}`, `K n = ⌈N^{CK₀}⌉+1`, `CK₀ ∈ {8m+16, 8m+20}`. All hypotheses of targets 2–5 are deterministic here except the two owed tails (hypotheses of the assembly instances).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2168/pf3.py` (mpmath, 80 digits); output verbatim:
```
[flow z0: Re z=1/2, Im z=N^-0.8; kappa=eps=1/10; s=0, t=1/16]  n: N | lemT>=1/16 | 1-lemT | |E|<=1.9 | eta_lemT>=N^-0.9/16 | eta_lemT<=1-lemT | 1/16<=lemT
0 2097152 True 9.051e-6 0.5 8.764e-6>=1.278e-7 True True True
1 549755813888 True 4.187e-10 0.5 4.054e-10>=1.697e-12 True True True
2 812479653347328 True 1.219e-12 0.5 1.181e-12>=2.383e-15 True True True
3 144115188075855872 True 1.937e-14 0.5 1.875e-14>=2.254e-17 True True True
4 8000000000000000000 True 7.79e-16 0.5 7.543e-16>=6.069e-19 True True True
[boundary |Re z|=2-kappa=1.9, Im z=N^-0.9]  n: |E| | |E|<=1.9 | lemT<1 | eta_lemT>=Im z/16
0 1.89999999998982 True True True
1 1.9 True True True
2 1.9 True True True
3 1.9 True True True
m=2: c1'=10737418240000  c2=412318171136  threshold N0 for 2*c2*N^(4m+7-CK/2)<=1 at CK=8m+20: N^3>=2c2 i.e. N>=9377.51 ; at CK=8m+16 (slack 1): N>=824636342272
m=3: c1'=712483534798848  c2=250794204305817600  threshold N0 for 2*c2*N^(4m+7-CK/2)<=1 at CK=8m+20: N^3>=2c2 i.e. N>=794540.0 ; at CK=8m+16 (slack 1): N>=501588408611635200
[remainder arithmetic, s=0,t=1/16, K=N^CK+1] m CK n: log10 K(Z1 D^1.5+2Z2 D^2) <= log10 N^(m+9)sqrtD | 2Z2sqrtD<=1 | 16N*D<=1 | N>=c1'+1 | Z1+2Z2sqrtD<=N^(m+9)
2 32 0 -26.7051<=-32.2102 False False True False False
2 32 1 -59.2163<=-59.3029 False True True False False
2 32 2 -78.2342<=-75.1511 True True True True True
2 32 3 -91.7275<=-86.3956 True True True True True
2 32 4 -102.194<=-95.1175 True True True True True
2 36 0 -39.3483<=-44.8535 False True True False False
2 36 1 -82.6966<=-82.7832 False True True False False
2 36 2 -108.054<=-104.971 True True True True True
2 36 3 -126.045<=-120.713 True True True True True
2 36 4 -140.0<=-132.924 True True True True True
3 40 0 -43.8481<=-51.1751 False False True False False
3 40 1 -92.6149<=-94.5234 False False True False False
3 40 2 -121.142<=-119.881 True False True True True
3 40 3 -141.382<=-137.872 True True True True True
3 40 4 -157.081<=-151.827 True True True True True
3 44 0 -56.4913<=-63.8184 False True True False False
3 44 1 -116.095<=-118.004 False True True False False
3 44 2 -150.961<=-149.7 True True True True True
3 44 3 -175.699<=-172.189 True True True True True
3 44 4 -194.887<=-189.633 True True True True True
```
Reading: (1) flow window: lemT ≥ 1/16 and lemT < 1 for n=0..4; |E_n| = 1/2 ≤ 1.9; η_{lemT} ≥ N^{−0.9}/16 and ≤ 1−lemT (boundary t = lemT closes: 1−lemT ≥ η_t > 0). Boundary |Re z| = 2−κ gives |E| ≤ 1.9 (the n=0 value 1.89999999998982 < 1.9). (2) Boundary s = t: Δ = 0, every term Z₁Δ^{3/2}+2Z₂Δ² is 0, Rem ≡ 0 (not a degenerate target: the bound is 0 ≤ 0). (3) From n = 2 the remainder inequality holds for m ∈ {2,3} at both CK₀ (the dispatcher's estimate confirmed for the inequality K(Z₁Δ^{3/2}+2Z₂Δ²) ≤ N^{m+9}√Δ). The proof route's sufficient conditions (2Z₂√Δ ≤ 1, N ≥ c₁'+1) hold from n = 2 for m = 2 (both CK₀) and for m = 3 at CK₀ = 8m+20; at m = 3, CK₀ = 8m+16 = 40, 2Z₂√Δ ≤ 1 first holds at n = 3 (n = 2 gives False). Hence **CK₀ = 8m+20 is recommended**; the instance data are n ≥ 2 (eventual). ΔH ≤ 1 holds for all n ≥ 0 (column 3). N ≥ c₁'+1 first holds at n = 2 (8.1e14 ≥ 7.12e14 for m = 3: tight, slack factor 1.14).
External hypothesis (`STKbound`/`ML:Kbound`): discharged by `stKbound_of_flow` from `STFlow` with `3 ≤ d`; limit computation: `N_n → ∞` (column 2 above: 2.1e6, 5.5e11, 8.1e14, 1.4e17, 8e18, `N_n = (2^7(n+1)^6)^3`, strictly increasing), `lam_n = (2(n+1))^{-6} → 0`, `0 < lam_n ≤ 𝔡⁻¹ = 10` for all n (`lam_0 = 1/64`), `W ≥ N^{1/6}`: `W_0=32`, `N_0^{1/6} = 11.3`; these are the `Admissible` data of `flow_z0` (Induction/Defs.lean:435).

### Verdict
- Target 1 (vocabulary): PASS (definitions only; the statements `GridRepRemNAt`, `GridRepTailNAt`, `GridRepWTailNAt` are the pin's clauses (Step2Defs.lean:817-851) with `Mart`, `Rem` replaced, read there; no exponent to close).
- Target 2 (identity, `difRepMartN_succ_sub`): PASS (pathwise algebra, no hypothesis).
- Target 3 (`difRep_Ugen_step_le`, `difRep_flow_bounds`): PASS (copy of `gdn_Ugen_step_le`; flow bounds from rows 8-11, valid for all `u ≤ lemT`).
- Target 4 (`gridRepRemN_holds`, `C₀ = m+9`): PASS (rows 1-7, 12-14; slack one power of N; CK₀ = 8m+20).
- Target 5 (assembly): PASS (row 14; `0 ≤ m+9`).
Verdict: PASS

## (b) Script output (all from `date -u` and the tool log; scripts in the scratchpad `T2168/`)
```
$ date -u
Mon Oct  5 04:08:45 UTC 2026
$ git log --format="%h %an <%ae> %s" main..t/T2168; git diff --stat main...t/T2168
5b72e15 Jun Yin <321276894+JYin80@users.noreply.github.com> T2168: drop an unused private helper from Path/DifREP1
3d65296 Jun Yin <321276894+JYin80@users.noreply.github.com> T2168: ST2-12 STGridRepN part 1 (Path/DifREP1): split identity, remainder bound C0 = m + 9, assembly
 RBM3D/Path/DifREP1.lean | 1458 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    2 +
 2 files changed, 1460 insertions(+)
$ wc -l RBM3D/Path/DifREP1.lean; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Path/DifREP1.lean; grep -cE "^private (noncomputable )?(def|theorem)" ...
1458 lines
sorry/admit/native_decide/axiom hits: 0
private defs/theorems: 49; public defs/theorems: 25
$ lake env lean RBM3D/Path/DifREP1.lean; echo exit=$?
exit=0
$ lake build RBM3D.Path.DifREP1 2>&1 | tail -3   (cache hit now; the first build after the last edit of the file printed: `✔ [3838/3838] Built RBM3D.Path.DifREP1 (7.3s)`)
Build completed successfully (3838 jobs).
$ lake build 2>&1 | tail -2   (whole library in the worktree, includes #assert_rbm_axioms; root import of the new module is the hub's)
non-vacuity certificates: 0 of 88 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3941 jobs).
$ registry pre-check: printf "import RBM3D
import RBM3D.Path.DifREP1
#assert_rbm_axioms
" > precheck.lean; lake env lean precheck.lean
exit=0
axiom audit: 5069 theorems, 1756 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
37:  RBM.Gauss.Sizes.STGridRepN: 6 [no certificate]
38:  RBM.Ind.GridRepTailNAt: 4 [no certificate]
39:  RBM.Ind.GridRepWTailNAt: 2 [no certificate]
102: RBM.Gauss.Sizes.STGridRepN,
$ definitions (target 1) and theorem types vs docs/tickets/checks/T2168-check.lean: python3 stmtcheck.py
difRepMartN IDENTICAL
difRepRemN IDENTICAL
GridRepRemNAt IDENTICAL
GridRepTailNAt IDENTICAL
GridRepWTailNAt IDENTICAL
difRep_identity == body of DifRepIdentityStmt : IDENTICAL
difRepMartN_succ_sub == body of DifRepMartSuccStmt : IDENTICAL
difRep_Ugen_step_le == body of DifRepUgenStepStmt : IDENTICAL
difRep_flow_bounds == body of DifRepFlowBoundsStmt : IDENTICAL
gridRepRemN_holds == body of GridRepRemNHoldsStmt : IDENTICAL
stGridRepNAt_of_parts == body of StGridRepNAtOfPartsStmt : IDENTICAL
stGridRepN_of_tails == body of StGridRepNOfTailsStmt : IDENTICAL
stGridMartAt_of_parts2 == body of StGridMartAtOfParts2Stmt : IDENTICAL
stGridMart_of_tail == body of StGridMartOfTailStmt : IDENTICAL
ALL OK
$ lake env lean stmt_elab.lean  (section 3 of the check file, `example : XStmt := @thm` for the nine theorems)
exit=0
$ copies: python3 copycheck.py
GridDriftN.lean:73-268: verbatim after renaming (gdn_/gdnTens/gdnGen -> difRep_, gridEnv_ -> difRep_): True
GridDriftN.lean:295-502: verbatim after renaming (gdn_/gdnTens/gdnGen -> difRep_, gridEnv_ -> difRep_): True
GridEnvelopeN.lean:240-362: verbatim after renaming (gdn_/gdnTens/gdnGen -> difRep_, gridEnv_ -> difRep_): True
$ lake env lean axioms.lean   (#print axioms of the 19 public declarations of RBM.Ind: 14 targets/vocabulary, 5 instance theorems)
19 declarations printed, 19 with axioms exactly [propext, Classical.choice, Quot.sound], 0 others
difRepMartN, difRepRemN, GridRepRemNAt, GridRepTailNAt, GridRepWTailNAt, difRep_identity, difRepMartN_succ_sub, difRep_Ugen_step_le, difRep_flow_bounds, gridRepRemN_holds, stGridRepNAt_of_parts, stGridRepN_of_tails, stGridMartAt_of_parts2, stGridMart_of_tail, DifREP1Inst.inst_difRep_identity, DifREP1Inst.inst_difRepMartN_succ_sub, DifREP1Inst.inst_difRep_Ugen_step_le, DifREP1Inst.inst_difRep_flow_bounds, DifREP1Inst.inst_gridRepRemN
$ python3 extract.py   (the nine target theorem types, extracted from the file)
theorem difRep_identity : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz), STgAN sz s t K n (E n) i.1 i.2 k ω = STgAN sz s t K n (E n) i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftN sz s t K n (E n) i.1 i.2 j ω + difRepRemN sz E s t K n i k ω + difRepMartN sz E s t K n i k ω
theorem difRepMartN_succ_sub : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (j : ℕ) (ω : PathΩ sz), difRepMartN sz E s t K n i (j + 1) ω - difRepMartN sz E s t K n i j ω = martIncN sz E s t K n j i.1 ω i.2
theorem difRep_Ugen_step_le : ∀ (d L : ℕ) [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {u Δ : ℝ}, 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x : Fin k → Zd d L, ‖Ugen d L g E σ u (u + Δ) A x - A x - (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤ uStepC k Δ (u + Δ) * M
theorem difRep_flow_bounds : ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) {u : ℝ}, u ≤ lemT (z n) → |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 ≤ etaT (STflowE z n) u ∧ etaT (STflowE z n) u ≤ 1 - u
theorem gridRepRemN_holds : ∀ d : ℕ, 3 ≤ d → ∀ m : ℕ, 2 ≤ m → GridRepRemNAt d m ((m : ℝ) + 9)
theorem stGridRepNAt_of_parts : ∀ (d m : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d m C₀ → GridRepTailNAt d m → GridRepWTailNAt d m → STGridRepNAt d m C₀
theorem stGridRepN_of_tails : ∀ d : ℕ, 3 ≤ d → (∀ m : ℕ, 2 ≤ m → GridRepTailNAt d m) → (∀ m : ℕ, 2 ≤ m → GridRepWTailNAt d m) → STGridRepN d
theorem stGridMartAt_of_parts2 : ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d 2 C₀ → GridRepTailNAt d 2 → STGridMartAt d C₀
theorem stGridMart_of_tail : ∀ d : ℕ, 3 ≤ d → GridRepTailNAt d 2 → STGridMart d
$ grep -nE "^(theorem inst_|theorem gridStep_inst|example)" RBM3D/Path/DifREP1.lean | cut -c1-150
1332:theorem gridStep_inst : gridStep sInst tInst (fun _ => 4) 0 = 1 / 64 := by
1343:theorem inst_difRep_identity (ω : PathΩ sz0) :
1354:theorem inst_difRepMartN_succ_sub (ω : PathΩ sz0) :
1361:example := inst_difRep_identity ω0
1362:example := inst_difRepMartN_succ_sub ω0
1366:theorem inst_difRep_Ugen_step_le (x : Fin 3 → Zd 3 4) :
1375:theorem inst_difRep_flow_bounds :
1385:theorem inst_gridRepRemN (m : ℕ) (hm : 2 ≤ m) :
1409:example := inst_gridRepRemN 2 le_rfl
1410:example := inst_gridRepRemN 3 (by norm_num)
1414:example (hT : GridRepTailNAt 3 3) (hW : GridRepWTailNAt 3 3) :
1420:example (hT : ∀ m : ℕ, 2 ≤ m → GridRepTailNAt 3 m) (hW : ∀ m : ℕ, 2 ≤ m → GridRepWTailNAt 3 m) :
1425:example (hT : GridRepTailNAt 3 2) : STGridMartAt 3 (((2 : ℕ) : ℝ) + 9) :=
1429:example (hT : GridRepTailNAt 3 2) : STGridMart 3 := stGridMart_of_tail 3 (by norm_num) hT
1433:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
1440:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hT : GridRepTailNAt 3 2)
1446:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
$ name-clash grep: grep -rnw <name> RBM3D RBM3D.lean, excluding RBM3D/Path/DifREP1.lean (public names: 14 targets + 7 instance names)
difRepMartN=0 difRepRemN=0 GridRepRemNAt=0 GridRepTailNAt=0 GridRepWTailNAt=0 difRep_identity=0 difRepMartN_succ_sub=0 difRep_Ugen_step_le=0 difRep_flow_bounds=0 gridRepRemN_holds=0 stGridRepNAt_of_parts=0 stGridRepN_of_tails=0 stGridMartAt_of_parts2=0 stGridMart_of_tail=0 DifREP1Inst=0 inst_gridRepRemN=0 inst_difRep_identity=0 inst_difRepMartN_succ_sub=0 inst_difRep_Ugen_step_le=0 inst_difRep_flow_bounds=0 gridStep_inst=0 
(the only other mentions are the two registry lines Test/Axioms.lean:120-121, excluded above)
$ ports: RBM2D read-only, absolute path (the worktree has no ../RBM2D)
RBM2D c9a24cf: c9a24cf  RBM2D HEAD: 9e0f275
 RBM2D/Induction/GridDriftN.lean    | 130 +++++---------------------
 RBM2D/Induction/GridEnvelopeN.lean | 185 ++++---------------------------------
 2 files changed, 41 insertions(+), 274 deletions(-)
RBM3D merge commits of the sources: GridDriftN 14137ce, GridEnvelopeN a438a51 (git log -1 on this branch)
$ RBM2D line numbers at c9a24cf (git show c9a24cf:<file> | grep -n)
189:private theorem gdn_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
408:private theorem gdn_Ugen_step_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} [NeZero k]
161:private theorem GridEnvelopeN_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
187:private theorem GridEnvelopeN_stepErr_le (L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ N H Y c : ℝ)
$ python3 thresh.py   (thresholds the proof of gridRepRemN_holds needs: N >= max(16, c1+1, 2 c2); CK = 8m+20, C0 = m+9; sz0: N_n = (W L)^3)
m=2: CK=36, C0=11, c1+1=10737418240001, 2*c2=824636342272, threshold=10737418240001, first n with N_n>=threshold: n=2, N_2=812479653347328
m=3: CK=44, C0=12, c1+1=712483534798849, 2*c2=501588408611635200, threshold=501588408611635200, first n with N_n>=threshold: n=4, N_4=8000000000000000000
N_n, n=0..5: [2097152, 549755813888, 812479653347328, 144115188075855872, 8000000000000000000, 212986666247081951232]
```

### Narrative (b)
- Delivered: `RBM3D/Path/DifREP1.lean` (new) and two registry lines `RBM3D/Test/Axioms.lean:120-121`, commits 3d65296 and 5b72e15 on `t/T2168` (author and counts above); nothing else is touched.
- Targets 1-5 are in the file; the five definitions and the nine theorem types are text-identical to the check file (`stmtcheck.py`), and `example : XStmt := @thm` elaborates for the nine theorems (`stmt_elab.lean`, exit 0).
- `difRep_identity`: induction on `k` from `STLKM_eq_STLKIM` (`STgAN = AvecN`); one step is `A_{k+1} - A_k = Δ Drift_k + r_k + martIncN_k` by `ring`. No hypothesis; holds pathwise for every `k`.
- `gridRepRemN_holds` (`CK = 8m + 20`, `C₀ = m + 9`): per step `r_j = [predIncN_j - Δ S_j] + [𝒰_{u_j,u_{j+1},σ} A_j - A_j - Δ Θ_{u_j,σ} A_j]`, `S_j` the non-`Θ` part of `STgDriftN` (`KLloopOf = loopOf` is `rfl`; `Θ` of the `STLKIM` function is `Θ` of `AvecN` by `STLKM_eq_STLKIM`).
- First bracket: `gridDriftN_envelope` at `τ_K = 1` with `hKb := stKbound_of_flow`, `|E_n| ≤ 2 - κ` and `t_n < 1` from `difRep_flow_bounds`, for every `σ` at once by `Filter.eventually_all`. Second bracket: `difRep_Ugen_step_le` with `M_j = η_{u_j}^{-m}(W^{-d})^{m-1} + N η_t^{-m}` (`norm_gloop_le_of_le_abs_im`, `exists_norm_Kcal_le_win` at `v = t`).
- `difRep_step_arith` (copy of `gridEnv_stepErr_le` at `c = 1`, `H = 16 N`, `Y = N`, plus the `uStepC` block) gives `‖r_j‖ ≤ Z₁ Δ^{3/2} + 2 Z₂ Δ²`; `difRep_rem_arith` sums over `k ≤ K` with `KΔ = t - s ≤ 1` and `Δ N^{8m+20} ≤ 1` (from `N^{CK} ≤ K`) to `N^{m+9} Δ^{1/2}`.
- The eventual threshold of the proof is `N ≥ max(16, c₁+1, 2 c₂)` with `c₁ = 16 (m+3)^4 32^{m+4}`, `c₂ = (2m⁴+m⁶) 16^{4m} + 2(m + m 2^m) 16^{m+2}`; (a) row 6 tabulates the finer `(2c₂)^{1/3}`. This is a proof choice, not a statement change; no (a′). On `sz0` the first admissible `n` is 2 (`m = 2`) and 4 (`m = 3`) (`thresh.py`).
- Assembly: `CK := max CK_rem (max CK_tail CK_wtail)`; `N ≥ 1` makes `N^{CK_i} ≤ N^{CK}`. `stGridMartAt_of_parts2` takes the loop-length-2 vocabulary by `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`, `STEEM_eq_STeeM`, as `ST_gridMart_of_repN`.
- DECISIONS §36: `(hd : 3 ≤ d)` occurs exactly in `gridRepRemN_holds`, `stGridRepN_of_tails`, `stGridMart_of_tail` (through `stKbound_of_flow`); targets 1-3, `stGridRepNAt_of_parts`, `stGridMartAt_of_parts2` hold for every `d`. `STFlow` gives `N → ∞` and `0 < lam ≤ 𝔡⁻¹`; no `Sizes` field or premise was added.
- Instances (file §6, `d = 3`, `sz0`, `z0`, `flow_z0`, `sInst ≡ 0`, `tInst ≡ 1/16`): `difRep_identity`, `difRepMartN_succ_sub` at `m = 3`, `K ≡ 4` (`Δ = 1/64`, `gridStep_inst`), `n = 0`, `σ = (+,-,+)`, `ω0`; `difRep_Ugen_step_le` at `L = 4`, `g = 1/64`, `E = 1/2`, `u = 0`, `Δ = 1/128`; `difRep_flow_bounds` at `κ = 1/10`, `u = 1/16`; `gridRepRemN_holds` at `m = 2, 3` with `K_n = ⌈N_n^{CK}⌉ + 1`, both clauses; the assembly with `GridRepTailNAt`, `GridRepWTailNAt` as hypotheses (other gate's pins), `STGridRepN 3`, `STGridMart 3`, and `STStep2 3` through `ST_step2_of_pinsN'` and `ST_step2_of_pins'`, and the data-level `STStep2Concl` through `inst_step2`.
- Registry: the two owed lines sit directly after the `STGridRepN` line (not at the end of `owedProps`); the pre-check exits 0 (no unregistered premise); `GridRepRemNAt` is concluded by `gridRepRemN_holds` and has no line; the `STGridRepN` line is untouched.
- Not done here (by the ticket's cut): the two owed tails for every `m ≥ 2` (ST2-13a, ST2-13b); the root import of the new module (the hub's).

## (c) Verified Mathlib names (the environment's module of each name, by `#eval` over `getModuleIdxFor?` in `names.lean`; none was invented, none had to be checked absent)
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`: `Real.rpow_natCast`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `Real.rpow_one`, `Real.rpow_add'`, `Real.sqrt_eq_rpow`, `Real.rpow_pos_of_pos`
- `Mathlib.Analysis.Real.Sqrt`: `Real.mul_self_sqrt`, `Real.sqrt_nonneg`; `Mathlib.Analysis.Complex.Norm`: `Complex.im_le_norm`
- `Mathlib.Order.Filter.Finite`: `Filter.eventually_all`; `Mathlib.Order.Filter.AtTopBot.Tendsto`: `Filter.Tendsto.eventually_ge_atTop`
- `Mathlib.Algebra.Order.GroupWithZero.Basic`: `pow_le_one_iff_of_nonneg`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `inv_anti₀`, `div_le_div_of_nonneg_right`, `le_mul_of_one_le_left`, `one_le_mul_of_one_le_of_one_le`, `pow_le_one₀`, `inv_le_one_of_one_le₀`
- `Mathlib.Algebra.Order.GroupWithZero.Defs`: `le_of_mul_le_mul_right`; `Mathlib.Algebra.Order.Floor.Semiring`: `Nat.le_ceil`; `Mathlib.MeasureTheory.OuterMeasure.AE`: `MeasureTheory.ae_of_all`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: `Finset.sum_range_succ`, `Finset.sum_const`; `Mathlib.Data.Finset.Card`: `Finset.card_range`; `Mathlib.Algebra.Ring.Defs`: `nsmul_eq_mul`
- `Mathlib.Analysis.Normed.Group.Basic`: `norm_sum_le`, `norm_add_le`, `norm_sub_le`; `Init.Data.Nat.Basic`: `Nat.succ_ne_zero`
- Merged RBM3D names used (all public, checked by compile): `STLKM_eq_STLKIM`, `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`, `STEEM_eq_STeeM`, `gridDriftN_envelope`, `exists_norm_Kcal_le_win`, `stKbound_of_flow`, `norm_gloop_le_of_le_abs_im`, `lemma28_quant`, `lemT_lt_one`, `Green.etaT_le_of_le`, `etaT_eq_zt_im`, `etaT_pos`, `zt_im`, `norm_mE`, `pathH_isHermitian`, `inst_step2`.

## (d) Open issues and paper-delta candidates
- Open: `GridRepTailNAt` and `GridRepWTailNAt` for every `m ≥ 2` are the pins owed to ST2-13a/b (registered owed, `Test/Axioms.lean:120-121`); `STGridRepN` and `STGridMart` follow from them by `stGridRepN_of_tails`, `stGridMart_of_tail`. Their truth was not examined here (pinned by the ticket).
- Open (hub): `import RBM3D.Path.DifREP1` after the last import line of `RBM3D.lean` at merge; the full `lake build` above does not contain it (the pre-check does).
- Open (process): the worktree has no `../RBM2D`; RBM2D was read with `git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks`. RBM2D `HEAD` is 9e0f275, not `c9a24cf`; the stat above is `c9a24cf..HEAD` for the two source files (read-only, no RBM2D write).
- T2168a (`Rem`, `Mart` are the Lean device of the grid; paper: the exact SDE `(int_K-L_ST)`, `3_5:136`): `difRepMartN_k = Σ_{j<k}(A_{j+1} - 𝔼[A_{j+1}|F_j])` is the full martingale including its second-order part; `difRepRemN_k = Σ_{j<k}(𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j)`.
- T2168b (constants): `C₀ = m + 9`, `CK = 8m + 20`, both depend on `m` only (the pin's docstring, `Step2Defs.lean:809`, writes `C₀ = C₀(d,m)`; here it is explicit and `d`-free).
- T2168c (strength): the identity `difRep_identity` holds pathwise for every `k` and `ω`, not only a.e. for `k ≤ K`; clause (i) of the pin keeps the a.e. form.
- T2168d (`3 ≤ d` through `STKbound`, D263, DECISIONS §36): on `gridRepRemN_holds`, `stGridRepN_of_tails`, `stGridMart_of_tail`.
- T2168e (conditionality): `STGridRepN` / `STGridMart` are proved only from the owed tails; the remainder part (clauses (i)-(ii)) is unconditional for `3 ≤ d`.
- T2168f (observation, no statement difference): the proof's threshold `N ≥ max(16, c₁+1, 2 c₂)` is coarser than (a) row 6; first admissible `n` on `sz0`: 2 for `m = 2`, 4 for `m = 3`.

