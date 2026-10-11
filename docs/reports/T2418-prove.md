Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 10:31:56 UTC 2026 (`date -u`)

Notation. `B := sz.Bctl n t = W^{-d} B_{t,0}` (`Defs/Sizes.lean:214`), `Ψ = B^{1/2}`, `c_g := lam² + 1`, `η = (1-t) Im m₀` (`etaOf`, `Loop/GLoopFlow.lean:58`),
`X_c := tr(Ǧ E_c) = W^{-d} Σ_{v∈[c]} Ǧ_{vv}`, `ω := Θ_t^{(+,+)} = (1 - t M⁺_B)⁻¹` (`BATheta … true true`, `BA/MFixedPoint.lean:515`; `M⁺_B = M^{(B)}∘M^{(B)}` entrywise), `S = t W^{-d} 1[[α]=[β]]` (`BAlwS`, `Graph/BAExpand.lean:75`),
`(W-1)_{αβ} = W^{-d}(ω-1)_{[α][β]}` (T2398 design §1.3). Scripts: scratchpad `T2418/{inst,budget,limit}.py` (not in the repository). Lean was not run (stage 1a).
S1 in mathematics (charge `σ=-`, `σ=+` is the conjugate), carrier `baFMz`, law `μ = seqP (sz.withLam 0)`, premises `LWAvgLawgL`, `STLocalEntrygL` only (the premises of `BALWCutExpTw` minus the five it does not use, see row 14),
for every `(a,b)`, on `U_n = {lam²/L^d ≤ 1-t}` as in `BALWCutExpTw` (T2398Pins:430-436): `‖𝔼 F_{ab}‖ ≺ (1-t)⁻¹ B^{5/2}` for each of
`F_MM = W^{-2d} Σ_{x∈[a],y∈[b],α} X_{[α]} M_{xα}M_{αy} Ḡ_{xy}`; `F_T1 = … Σ_{α,β} X_{[α]}(W-1)_{αβ} M_{xβ}M_{βy} Ḡ_{xy}`;
`F_T3A^{(k)} = … Σ_{α,w,γ} X_{[α]} W^{(k)}_{αw} M_{wγ} · t X_{[γ]} · G_{γy} Ǧ_{xw} Ḡ_{xy}` (`W^{(0)}=1`, `W^{(1)}=W-1`);
`F_C1 = … Σ_{α,α'} X_{[α]} M_{xα} · t X_{[α']} M_{αα'} G_{α'y} Ḡ_{xy}`, `F_C2 = … Σ_{α,α'} X_{[α]} · t X_{[α']} M_{xα'} G_{α'α} M_{αy} Ḡ_{xy}` (the `Ǧ_{ββ}`-children of `lanlw` for `M_{xα}Ǧ_{αy}`, `Ǧ_{xα}M_{αy}`; `Σ_β S_{α'β}Ǧ_{ββ} = t X_{[α']}`).

### (i) Exponent table
| # | quantity | value / constraint | slack | source |
|---|---|---|---|---|
| 1 | target exponent of `B` | `5/2`; the cut pin has `(1-t)⁻¹`, the ticket `η⁻¹`: `η⁻¹ = ((1-t) Im m₀)⁻¹ ≤ κ⁻¹(1-t)⁻¹` since `Im m₀ ≥ κ` | constant `κ⁻¹` | `BAReal` (`BA/MFixedPoint.lean:432`), `BAflow_real` (`GreenSchur.lean:59`) |
| 2 | `B ≤ 1` and `η ≤ 1` (needed to compare `B^a ≤ B^b`, `η⁻¹ ≥ 1`) | `B ≤ W^{-d}g⁻² + (N(1-t))⁻¹ ≤ W^{-2𝔡} + 2N^{-ε}` (`(eq:WO)`, `1-t ≥ 1-t₀ ≥ Im z/2`, `Im m ≤ 1` from `(self_m)`); no BA analogue of band `st5_Bctl_le_one` found by grep: to be proved in the twin | instance `B = 6.2e-5` | `Defs/Params.lean:36`, `Defs/Sizes.lean:164` (`WO`), `:168` (`Bandwidth`) |
| 3 | pair count `x~y` (same atom, same offset): `W^{-2d}·W^d` | `W^{-d} ≤ c_g B`, `c_g = lam²+1 ≤ 1+𝔡⁻²` (`lam ≤ 𝔡⁻¹`, `(eq:WO)`) | ratio `W^{-d}/(c_g B) = 0.49` at the instance | `STBctl_ge` (`Induction/ScaleFacts.lean:126`); no smallness of `g` |
| 4 | pathwise `|X_c| ≺ B`; `|Ǧ_{xy}| ≺ Ψ`; `|G_{xx}| ≺ 1` | uniform in `c, x, y` | – | `LWAvgLawgL` (`Chain/LWGen.lean:48`); `STLocalEntrygL` (`Chain/Carrier.lean:121`, `STWB ≤ Bctl`); twin of `lwExpTerm4_diag` (`LWExpTerm4:781`) |
| 5 | `M`: `M_{xy} = 1[same offset] M^B_{[x][y]}`, `max|M^B| ≤ 1`, `Σ_b|M^B_{ab}|² = 1`, `Σ_b|M^B_{ab}| ≤ C_M` | `C_M = c⁻¹ expC k c`, `d=k+2`, `(d,Λ,κ)` only; `M^B` symmetric | `C_M = 1.083` (instance), `5.92` (`g=1` row) | `BAMfine_eq` (`BA/GreenSchur.lean:93`), `BAMfine_norm_le_one` (`:105`), `BAMB_row_sq_real` (`BA/Ward.lean:125`), `BAMB_row_l1` (`:139`) |
| 6 | `ω = Θ^{(+,+)}` row and column `ℓ¹` sums `≤ S_ω`, uniform in `t ∈ [0,1)`; `ω-1`: `≤ S_ω+1` | **not** the Neumann bound `(1-t)⁻¹` (non-uniform as `t→t₀→1`, and it would multiply `η⁻¹` in T3A); `S_ω = C_s(1+Λ²expC k c_s)` from `BAProp5s` (`|Θ^{σσ}(0,a)| ≤ C(1_{a=0}+g²e^{-c|a|})`), `g₀ ≤ lam ≤ 𝔡⁻¹ =: Λ`; symmetry `BATheta_isSymm` | instance `0.667 < (1-t)⁻¹ = 2`; `g=1`: `0.993` | `baProp5s_holds` (`BA/Prop5Short.lean:667`, merged); private copies `KStep_theta_l1` (`BA/KStep.lean:350`), `KInduct_theta_l1` (`BA/KInduct.lean:203`): the twin re-proves from `baProp5s_holds`; `BATheta_isSymm` (`BA/KBase.lean:371`) |
| 7 | improved average `𝔼X_c` (`≺ B²` is not needed): required `e ≥ 3/2` since `W^{-d}B^{e} ≤ c_g B^{1+e}`, need `1+e ≥ 5/2` | **derived, not a premise**: `lanlw` with `f=1` at `x=y` (`baLanlw_holds`, `Graph/BAExpand.lean:744`) gives `𝔼 Ǧ_{xx} = t Σ_α M_{xα}𝔼[X_{[α]}G_{αx}]`, so `𝔼X = t M⁺_B 𝔼X + R`, `R_a = tΣ_c … 𝔼[X_c Ǧ_{αx}]`, `|R| ≺ C_M B·Ψ`; `𝔼X = ωR`, `|𝔼X| ≺ S_ω C_M B^{3/2}` | `e = 3/2`: slack 0 (needed) | ticket premise `|𝔼 tr| ≺ B²` = `lem:improve_exp_aver` (`6_Step6_two_loop.tex:12-20`); no BA carrier version exists (grep of `RBM3D/BA`, `RBM3D/Chain`: none; band `STExpAvgAt_of_LWAvgLaw` is `STFlow`-only) |
| 8 | MM, `Ǧ̄_{xy}` part: `W^{-d}·C_M²·|X|·|Ǧ̄_{xy}|`; `M̄_{xy}` part: `W^{-d} C_M²·S_ω C_M B^{3/2}` | exponents `1+1/2+1 = 5/2`; `3/2+1 = 5/2` | 0, 0 | rows 3, 4, 5, 7 |
| 9 | T1 (`(W-1)`): `Σ_{α∈…}X_{[α]}W^{-d}(ω-1)_{[α]c} = Σ_{a₁}X_{a₁}(ω-1)_{a₁c}`, `≤ (S_ω+1)B` | same exponents as MM | 0, 0 | rows 3-7; `lwExpTerm4_kerSum` (`:100`, model-free) not needed |
| 10 | T3A, both `k`: `Σ_{a₁}X_{a₁}ω_{a₁[w]} ≤ S_ωB`, `|tX_{[γ]}| ≤ B`; Schur `Σ_{w,γ}|M_{wγ}|u_wv_γ ≤ C_M‖u‖₂‖v‖₂`; fine Ward `Σ_w|Ǧ_{xw}|² ≤ 2|G_{xx}|η⁻¹ + 2` | `(Ǧ_{γy},Ǧ̄_{xy})`: `B²·η⁻¹·Ψ`: exponent `5/2`. `(Ǧ_{γy}, M̄_{xy})`: `3`; `(M_{γy},Ǧ̄)`: `3`; `(M,M̄)`: `7/2` | 0 / 1/2 / 1/2 / 1 | `lwExpTerm4_ward_row/col` (`:154, 172`, private, model-free, copied); rows 3-6 |
| 11 | `lanlw` children `F_C1`, `F_C2`: `|X||X|`, one `Ǧ` edge, ties `C_M²` | `(Ǧ,Ǧ̄)`: `3`; ties: `7/2`; `(M,M̄)`: `3` | 1/2 minimum | `baLanlw_holds`; `BAMfine_eq` |
| 12 | `lanlw` / `ω` time: `S = tW^{-d}1[[α]=[β]]`, `0 ≤ t < 1`, `t ≤ BAflowT0 = BAt0 z m = Im m/(Im m + Im z) < 1` | `t < 1` | instance `t = 1/2 ≤ t₀ = 0.694` | `BAlwS`; `BAflowT0` (`BA/FlowPins.lean:380`); `BAt0_lt_one` (`BA/MFixedPoint.lean:285`) |
| 13 | flow/size hypotheses at `n=0` of `sz0`: `(eq:WO)`, `W ≥ N^𝔠`, `N^{-1+ε} ≤ Im z ≤ 1`, `lam²/L^d ≤ 1-t`, `κ ≤ Im m(z)` | see (ii) | all True | `Defs/Sizes.lean:260`, `BA/FlowPins.lean:1214` |
| 14 | inputs the twin does **not** use for S1: no `𝒦^{(k)}`, no 2- or 3-loop appears in `F_MM…F_C2` | `STKboundgL`, `STKwardgL`, `STLmaxgL`, `STLKgL`, `STDecaygL` unused by S1 (`baKBoundAt_holds`, `BA/KBound.lean:85`, only for the twisted S2) | – | the band `I₂` route through `lwExpTerm4_L3` (`:488`) and `R23` is a 3-loop `E_a` statement: at BA the tie `M_{wγ}` joins blocks `c₁ ≠ c₂` (`twTie`, T2398Pins) so T3A is a **twisted** loop; the crude bound of row 10 needs no loop |
| 15 | shape consumed by `BALWCutExpTw` (T2398Pins:430-436) | `PrecL sz μ (U := {(σc,σo,ac,ao) // lam²/L^d ≤ 1-t}) ‖∫ LWcutg‖ (1-t)⁻¹ B^{5/2}`, premises `STLocalEntrygL, LWAvgLawgL, STLmaxgL, STLKgL, STDecaygL, BATwistAvgLaw, BATwistLoopLaw` | S1 has the same `U`, `≺`-shape and a subset of the stochastic premises | `BATwistAvgLaw`/`BATwistLoopLaw` are not used by S1 |

### (ii) One concrete nondegenerate instance
`d = 3`, `sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = (WL)³ = 2097152`; `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)` (`flow_sz0`); `z = z_S`, `m = m_S = L^{-3}tr(gΨ^B - 6i/5)⁻¹`, `t₀ = Im m/Im w`, `g₀ = √t₀ g`, `E = (t₀ Re z - (1-t₀)Re m)/√t₀`, `m₀ = m/√t₀` (`GreenSchur.lean:67`), `t ≡ 1/2`. `Ψ^B` = ℓ¹ adjacency of `Z_4³` (degree 6). Row 2 of the output is a second flow datum with `g = 1`, `t = 0.3`, `κ = 1/4`.
```
$ cd SP/T2418 && python3 inst.py        # (header lines and the g=1 block abridged to the checks)
--- g=0.015625: sz0 n=0 (L=4,W=32): THE INSTANCE
  m_S=-0.000000+0.832488j Imz_S=0.367512 t0=0.693740 g0=0.013014 E=0.000000 m0=-0.000000+0.999493j fixed-pt residual=2.2e-16
  Im m0=0.9995 >= kappa=0.5: True; Im m_S=0.8325 >= kappa: True; t=0.5 <= t0: True
  max_a|sum_b|M_ab|^2 - 1|=1.6e-15; max|M_ab|=0.9995; |M-M^T|max=1.2e-17
  C_M=max row l1(M^B)=1.0828; ||~|M^B|~||_2=1.0828 <= C_M: True
  B_t0=Bparam=2.03027; B=Bctl=6.1959e-05; Psi=B^(1/2)=7.8714e-03; B<=1: True
  c_g=lam^2+1=1.000244; W^-d=3.0518e-05 <= c_g*B=6.1974e-05: True; ratio=0.4924
  eta=(1-t)Im m0=0.49975 (<=1: True); eta^-1=2.0010 <= kappa^-1 (1-t)^-1=4.0000: True
  omega: rho(tM^+)=0.5000; max l1 row/col=0.6671; l1 of (omega-1)=0.3333; (1-t)^-1=2.00; omega-1 - tM^+ omega max=2.3e-15
  lam^2/L^d=3.815e-06 <= 1-t=0.5: True
--- g=1.0: same L,W, g=1 (flow z=zS, no smallness of g)
  Im m0=0.6732 >= kappa=0.25: True; Im m_S=0.3777 >= kappa: True; t=0.3 <= t0: True
  C_M=max row l1(M^B)=5.9153; B=Bctl=1.8633e-05; c_g=lam^2+1=2.000000; W^-d=3.0518e-05 <= c_g*B=3.7265e-05: True; ratio=0.8189
  omega: rho(tM^+)=0.3000; max l1 row/col=0.9931; l1 of (omega-1)=0.2308; (1-t)^-1=1.43; lam^2/L^d=1.562e-02 <= 1-t=0.7: True
--- (eq:WO)/(Main_DEL_COND) at n=0: N=2097152; W^(-d/2+dd)=0.00781 <= lam=1/64=0.01562: True; lam<=1/dd=10: True; N^c=11.31 <= W=32: True
    N^(-1+eps)=2.044e-06 <= Im z_S=0.3675 <= 1 (BAdom): True
$ cd SP/T2418 && python3 budget.py      # bookkeeping of the exponents of rows 8-11 (a model of the factor list, not a proof)
required exponent of B (target eta^-1 B^(5/2)): 5/2
MM   Gc_xy part   : X * Gc_xy * count                        exp 5/2  slack 0    B^slack at instance 1.00e+00
MM   Mbar_xy part : EX * count                               exp 5/2  slack 0    B^slack at instance 1.00e+00
T1   Gc_xy part                                              exp 5/2  slack 0    B^slack at instance 1.00e+00
T1   Mbar_xy part : EX * count                               exp 5/2  slack 0    B^slack at instance 1.00e+00
T3A  (Gc_gy, Gc_xy): X*nu*Gc_xy, Ward on Gc_xw,Gc_gy         exp 5/2  slack 0    B^slack at instance 1.00e+00
T3A  (Gc_gy, Mbar_xy): X*nu*count                            exp 3    slack 1/2  B^slack at instance 7.87e-03
T3A  (M_gy, Gc_xy): X*nu*max|Gc_xw|*Gc_xy                    exp 3    slack 1/2  B^slack at instance 7.87e-03
T3A  (M_gy, Mbar_xy): X*nu*max|Gc_xw|*count                  exp 7/2  slack 1    B^slack at instance 6.20e-05
lanlw-child of M Gc (Gc_a'y, Gc_xy): X*nu*Gc*Gc              exp 3    slack 1/2  B^slack at instance 7.87e-03
lanlw-child of M Gc (M_a'y, Mbar_xy): X*nu*count             exp 3    slack 1/2  B^slack at instance 7.87e-03
(three further lanlw rows omitted here: exp 3 or 7/2; min slack over all 13 rows: 0)
```
Every deterministic hypothesis of S1 holds at this datum at once (`3 ≤ d`, `3 ≤ L`, `0 ≤ t ≤ t₀ < 1`, `BAReal` with `κ ≤ Im m₀`, `BAdom`, `(eq:WO)`, `Bandwidth`, `lam²/L^d ≤ 1-t`, `B ≤ 1`, `W^{-d} ≤ c_g B`). The stochastic premises `LWAvgLawgL`, `STLocalEntrygL` are other gates' pins (Step 1/2) and stay hypotheses of the instance.
External hypothesis, limit computation (TEAM §8 lesson 14), `STLocalEntrygL` against the fine Ward identity at the instance (`t = 1/2`): the premise bound summed over `y` must dominate `Σ_y|G_{xy}|² - Σ_y|M_{xy}|² = (1-t)⁻¹ - 1`:
```
$ cd SP/T2418 && python3 limit.py
sum_y [premise bound on |(G-M)_xy|^2] = 54.6410  >=  leading Ward value sum_y|G_xy|^2 - sum_y|M_xy|^2 = 2.000 - 1.0 = 1.000: True
```
`LWAvgLawgL` is stated at the normalization `tr(ǦE_c) = L^{(1)}_c - m` (`M_{vv} = m`, translation invariance of `M^B`; `BAlwGc`), the same as row 7 uses.

### Verdicts
- Target 1 (S1 pinned): **PASS** in mathematics (every row closes, minimum slack 0 as in the paper's `I₂` bound). The Lean `def … : Prop` for S1 is not produced here (this stage writes no Lean); it is the shape of row 15 with the five families above.
- Target 2 (twins of §§2-5, 7, 8 untwisted): **PASS** with three corrections to the ticket's scope, all derived in rows 7, 10, 14: (a) the ticket premise `|𝔼 tr| ≺ B²` is replaced by the derived `|𝔼X_c| ≺ B^{3/2}` (no new premise, `BALWCutExpTw`'s premise list is unchanged); (b) the band route of `I₂` through the 3-loop `lwExpTerm4_L3` and `STLmax` does not transfer (T3A is a twisted loop); the fine-level Ward plus the Schur bound with `ℓ¹` rows of `M^B` replaces it at the same exponent; (c) `STKboundgL`/`STKwardgL` (K12) are not used by S1.
- Target 3 (proof of S1 from target 2): **PASS**. Target 4 (instance): **PASS** (datum above). Target 5 (C1): **PASS**: constants in `(d, κ, 𝔡, Λ = 𝔡⁻¹)`: `c_g ≤ 1 + 𝔡⁻²`, `κ⁻¹`, `C_M`, `S_ω`; no smallness of `g` (row `g = 1`: `c_g = 2`, `C_M = 5.9`). Target 6: no registry entry.
- Paper-delta candidates: `T2418a`: the improved average `𝔼X = O(B²)` of `lem:improve_exp_aver` is not needed at BA for S1; exponent `3/2` suffices and is proved by `lanlw` with `f = 1`.

## (a′) Preflight corrections — Sun Oct 11 11:00:14 UTC 2026
Rule (B) repair of (a) under Amend 1 (`docs/tickets/T2418-amend-1.md`, decisions 1-4; audit `docs/reports/T2418-1a-audit.md` items 2-7). Scratch scripts: `T2418/{lines.py,cites.sh,names.sh}` of the scratchpad (not in the repository).
**Corrections to (a).** (c1) Row 5 cites `BAMB_row_l1` as `BA/Ward.lean:139`; it is `BA/GreenSchur.lean:139` (cites output below). (c2) Row 14 and the Target 2 verdict (b) say T3A "is a twisted loop": by decision 2 T3A stays in S1 by the crude bound of row 10 (fine-level Ward + Schur, no loop is formed), exponent 5/2, slack 0 unchanged. (c3) The Target 2 verdict "twins of §§2-5, 7, 8" is replaced by the map (ii). (c4) `inst.py` needs numpy from the user site: run `python3 inst.py` without `-I`. Rows 1-13, 15 and the instance (ii) of (a) are unchanged.
**Decisions applied.** D1: no premise `|𝔼 tr| ≺ B²`; `|𝔼X_c| ≺ B^{3/2}` is proved in the ticket (row 7; the "row 7" items of `lines.py`); `T2418a`. D2: `T3A` in S1; twins of `lwExpTerm4_L3` (`:488`) and of untwisted §8 (`R23`) dropped. D3: `STKboundgL`/`STKwardgL` unused by S1. D4: S1 covers only the two-weight children `F_C1`, `F_C2`; the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` go to L4b2, the `∂tr` children to S3 (the S1 docstring says so).

### (i) S1 statement
**Not delivered: the Lean `def` and its compile.** This stage's rule forbids any Lean (no `.lean` file, no draft in a file, scratchpad or `/tmp`), so the compile with exit code that the amend asks for was not run. For the dispatcher: the channel for it is a check file `docs/tickets/checks/T2418-s1-check.lean` (CLAUDE.md §1, §4 step 0) compiled by the hub, or the first build of 1b. This is the only item of the repair list not met.
Specification of the def in mathematics (merged identifiers; shape of the consumer, premise lines of `BALWCutExpTw`, `t/T2398:RBM3D/Probe/T2398Pins.lean:436-438`):
```
$ git show t/T2398:RBM3D/Probe/T2398Pins.lean | sed -n '436,438p'
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
```
- Name `BAExp14aS1 d` (`Prop`), integrand `BAExp14aS1Fam`. Binders and range exactly as `BALWCutExpTw`: `3 ≤ d`, `κ ε 𝔡 > 0`, `BAFlow sz κ ε 𝔠 𝔡 z`, `0 ≤ t n ≤ BAflowT0 sz z n`, `μ := seqP (sz.withLam 0)`, carrier `baFMz sz z`.
- Hypotheses: premises (1) `STLocalEntrygL` and (2) `LWAvgLawgL` of the seven of `BALWCutExpTw`; premises (3)-(7) (`STLmaxgL`, `STLKgL`, `STDecaygL`, `BATwistAvgLaw`, `BATwistLoopLaw`) are absent. No premise on `𝔼 tr`.
- Conclusion: `PrecL sz μ` on `U_n = {(k, σ, a, b) : lam²/L^d ≤ 1 - t_n}`, `k ∈ Fin 6` the family tag in the order `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2` (formulas in the header of (a)), `σ` the charge, `(a,b)` the blocks: `‖∫ BAExp14aS1Fam … ∂μ‖ ≺ (1-t_n)⁻¹ (sz.Bctl n (t n))^{5/2}`, the same bound and the same `U` shape as the conclusion of `BALWCutExpTw`. The family sum follows from the tagged bound (six summands).
- Consumer: S1 is an input of the L4a2 assembly of `BALWCutExpTw` (with S2, S3 and the expansion identity), not one of its premises.
- Charge convention: `σ` is the charge of the loop `X` and the tail of `LWcutg` (`Chain/LWGen.lean:39`); `σ = +` is the conjugate (as in (a)).

### (ii) Section map `LWExpTerm4` (file:line) → planned declaration
File A `Graph/BAExp14a.lean`, file B `Graph/BAExp14aB.lean`; planned private names carry the stem `BAExp14a_`.
| band lines | disposition | planned declaration (file) | change |
|---|---|---|---|
| §1 `:54-127` (`kerSum`) | not used | – | ticket header says "reused by import"; ω's `ℓ¹` bound comes from `baProp5s_holds` (row 6), not from `LWExpKer` decay |
| §2 `:129-192` | copy | `BAExp14a_ward_{green_conj,gram,row,col}` (A) | none (model-free in a Hermitian `H`) |
| §3 `:199-228` weights `ρ` | adapt | `BAExp14a_rho*`, `BAExp14a_L1_eq` (A) | `𝓛^{(1)}_a = W^{-d}Σ_{v∈[a]}G_{vv}` of `BALloop` |
| §3 `:230-248` `Gt` Ward | twin | `BAExp14a_Gt_ward_{row,col}` (A) | `Gt` → `BAGt` (`BAGt_eq_green`), `etaT` → `etaOf (BAmF …)`; new Hermitian lemma for `g₀•PsiI + Hflow` |
| §3 `:250-412` `Pm` … `ward2` | **not planned** | – | `𝓛^{(2)}` absent from `F_MM…F_C2`; consumers of `ward2`/`L3` (script below) are §8 `R23`, §9, §10 only |
| §3 `:414-575` … `L3` | **not planned** | – | decision 2 |
| §3 `:576-597` `Gt_entry_le` | twin | `BAExp14a_Gt_entry_le` (A) | `|G_{xx}| ≤ η⁻¹`, `η = (1-t)Im m` |
| §4 `:602-609` `prec_congr` | not copied | – | BA has `PrecL_congr` (`BA/Step1Boot.lean:185`) |
| §4 `:615-624` `Kloop_one` | not planned | – | no `𝒦` in S1 |
| §4 `:626-650` `facts` | twin, new | `baExp14a_Bctl_le_one`, `BAExp14a_facts` (A) | `B ≤ 1`, `η⁻¹ ≤ N²`, `N⁻¹ ≤ B`, `N ≥ 4` from `BAdom`/`BAflow_T0_bounds`; no `𝒦` bound |
| §4 `:651-661, 679-685` `env_X`, `floor3` | twin | `BAExp14a_env_X`, `BAExp14a_floor` (A) | `‖X‖ ≤ 2N`; floor `N^{-K} ≤ B^K` for `K = 5/2` |
| §4 `:662-678, 686-737` `env_L2`, `env_D`, `XD` | not planned | – | `𝓛^{(2)}` / `I₁K` only |
| §5 `:743-777` `kward` | not planned | – | decision 3 (K12 stays with L4b2) |
| §5 `:778-826` `diag` | twin | `baExp14a_diag` (A) | `max|G_{xx}| ≺ 1` from `STLocalEntrygL` at `(x,x)`, `‖M_{xx}‖ ≤ 1` (`BAMfine_norm_le_one`) |
| §6 `:828-939`, §9 `:1394-1721` | **out** | – | L4b2 |
| §7 `:940-1103` `wsum`, `T23_n`, `Ta_n`, `Tb_n` | not copied | – | loop-shaped `W^dΣKS` sums do not occur; the sums are `Σ_a|X_a||K_{ac}| ≤ max|X|·S_K`, `K ∈ {1, ω-1}`, inside the family lemmas |
| §8 `:1106-1166, 1301-1310` helpers | copy | `BAExp14a_{three_mul_rpow_le,rpow52,int_sum3,eta_le_one}`, 6-tag union (A) | `prec_union3` (3 events) → 6 events |
| §8 `:1167-1393` `R23`, `I23` | **dropped** | – | decision 2; `R23_prec` (`:1229-1297`) is the proof model of the family lemmas |
| new, no band source | new | `baExp14a_omega_l1`, `baExp14a_EX_bound`, `baExp14a_W_sub_one_lift`, family lemmas, bridges (A, B) | rows 6, 7, 10, 11 of (a); see (iii) |
| §10 `:1722-1838` | twin | `baExp14a_inst_S1` (B) | one instance at `sz0`, `zSeq`, `flow_sz0` (`BA/LWPinsBA.lean` pattern); `STLocalEntrygL`, `LWAvgLawgL` stay hypotheses |
```
$ grep -n "lwExpTerm4_ward2\|lwExpTerm4_L3" RBM3D/Graph/LWExpTerm4.lean | awk -F: '$1>100{printf "%s ",$1}'
391 488 1198 1212 1457 1525 1541 1583 1797 1808
```
(391, 488: definitions; 1198, 1212: §8 `R23_le`; 1457-1583: §9; 1797, 1808: §10.) Dropping `ward2`'s chain is a consequence of decision 2 and (v), not named in decision 2: flagged for the 1a-audit round 2.

### (iii) Band input → BA source (merged, file:line) or owing row
| band input | BA source / owing row |
|---|---|
| `stKbound_of_flow` (`Loop/KLFinal.lean:302`), `stKward_of_flow` (`:308`) | not used (D3); `baKBoundAt_holds` `BA/KBound.lean:85` stays with L4b2 |
| `st5_Bctl_le_one` (`Induction/Step5Kit.lean:362`, `STFlow`) | **owing** `baExp14a_Bctl_le_one` (row 2): grep finds only `Bctl_le_one_of_conStInd` (`BA/Step1Fam.lean:382`, takes `STConStInd` as a hypothesis: unusable) |
| `expAvg_eta_inv_le` (`ExpAvg.lean:631`), `st5_t_lt_one` (`Step5Kit.lean:192`) | `η⁻¹ ≤ N²`: **owing** inside `BAExp14a_facts` (pattern: private `BASetup_eta_inv_le`, `BA/Step1Setup.lean:674`); `t < 1`: `BAflow_T0_bounds` (`BA/Step1Trivial.lean:47`) |
| `expAvg_Bctl_ge` (`ExpAvg.lean:604`), `STBctl_ge` (`ScaleFacts.lean:126`) | merged, model-free in `sz`; `ba_xy_count` (probe `:184`, not merged) re-proved from `STBctl_ge` |
| `STLocalEntry`, `LWAvgLaw` | `STLocalEntrygL` (`Chain/Carrier.lean:121`), `LWAvgLawgL` (`Chain/LWGen.lean:48`): hypotheses of S1 |
| `STLK`, `STLmax`, `STDecay` | not used by S1 |
| improved average `STExpAvgAt` (`Induction/Step6Pins.lean:177`; `STExpAvgAt_of_LWAvgLaw`, `ExpAvg.lean:799`, `STFlow`) | no BA version; not needed: **derived** `baExp14a_EX_bound` `|𝔼X_c| ≺ B^{3/2}` (row 7; the "row 7" items of `lines.py`) from `baLanlw_holds` (`Graph/BAExpand.lean:744`) at `f = 1`; `T2418a` |
| `ω` `ℓ¹` bound, `t`-uniform | **owing** `baExp14a_omega_l1` from `baProp5s_holds` (`BA/Prop5Short.lean:667`) with `BAflow_real` (`BA/GreenSchur.lean:59`), `BAflow_lam0_window` (`:72`, eventual in `n`), `d = k+2`; private copies `KStep_theta_l1` (`BA/KStep.lean:350`) as pattern; `ω = BATheta … true true`, `BAMss` entry `M_{ba}M_{ab} = (M_{ab})²` by `BAMB_symm` (`BA/Ward.lean:83`), `BATheta_isUnit`/`isSymm` (`BA/KBase.lean:324, 371`) |
| `M` facts | `BAMfine_eq`, `BAMfine_norm_le_one`, `BAMB_row_sq_real`, `BAMB_row_l1` merged (cites); fine-level `ℓ¹`/Schur sums **owing** (row 10, A) |
| `W - 1 = W^{-d}(ω - 1)_{[·][·]}` (D402, design §1.3) | merged `baSp_eq` (`Graph/BASizeClaim.lean:180`, `S W = t·lift ω`), `baW_mul` (`Graph/BAExpandW.lean:268`); exported form **owing**: `baExp14a_W_sub_one_lift` (B) |
| `lanlw` and the law | `baLanlw_holds` over `PF d L W 0`; `seqP_map_slice` (`Gauss/FineModel.lean:184`); `BAGt = BAlwG ∘ slice`, `BAMfine = BAlwM`: **owing** bridge (B) (grep: appears only inside the probe statement `BAGraphPrecJoin`) |
| `≺ → 𝔼` (`lwExpTerm_prec_integral`, `LWExpTerm.lean:143`, law `sz.seqP` only; `first_moment` private) | **owing** `baExp14a_prec_integral` at law `μ` (A); `PrecL_congr` merged |
```
$ bash cites.sh   # first 22 lines: file:line of each merged name cited above (grep -rn on main)
RBM3D/Graph/BAExpand.lean:744:theorem baLanlw_holds (d : ℕ) : BAlanlw d 
RBM3D/BA/Prop5Short.lean:667:theorem baProp5s_holds (d : ℕ) (Λ κ : ℝ) : 
RBM3D/BA/GreenSchur.lean:93:theorem BAMfine_eq {d : ℕ} (sz : Sizes d) (l
RBM3D/BA/GreenSchur.lean:105:theorem BAMfine_norm_le_one {d : ℕ} (sz : S
RBM3D/BA/Ward.lean:125:theorem BAMB_row_sq_real (g E : ℝ) (m : ℂ) (h : B
RBM3D/BA/GreenSchur.lean:139:theorem BAMB_row_l1 (k L : ℕ) [NeZero L] (h
RBM3D/BA/Ward.lean:83:theorem BAMB_symm (g : ℝ) (z m : ℂ) (a b : Zd d L)
RBM3D/Graph/BASizeClaim.lean:180:theorem baSp_eq (d L W : ℕ) [NeZero L] 
RBM3D/Graph/BAExpandW.lean:268:theorem baW_mul (hL : 3 ≤ L) (g0 E t : ℝ)
RBM3D/BA/GreenLDE.lean:46:theorem BAGt_eq_green {d : ℕ} (sz : Sizes d) (
RBM3D/BA/GreenSchur.lean:59:theorem BAflow_real {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (s
RBM3D/BA/GreenSchur.lean:72:theorem BAflow_lam0_window {d : ℕ} (κ ε 𝔠 𝔡 
RBM3D/BA/Step1Trivial.lean:47:theorem BAflow_T0_bounds {sz : Sizes d} {κ
RBM3D/Induction/ScaleFacts.lean:126:theorem STBctl_ge (n : ℕ) {s : ℝ} (h
RBM3D/Induction/ExpAvg.lean:604:theorem expAvg_Bctl_ge {d : ℕ} (sz : Siz
RBM3D/Gauss/FineModel.lean:184:theorem seqP_map_slice (n : ℕ) :
RBM3D/BA/Step1Boot.lean:185:theorem PrecL_congr {sz : Sizes d} {μ : Meas
RBM3D/BA/KBase.lean:324:theorem BATheta_isUnit (g κ E : ℝ) (m : ℂ) (hr :
RBM3D/BA/KBase.lean:371:theorem BATheta_isSymm (g κ E : ℝ) (m : ℂ) (hr :
RBM3D/BA/KBound.lean:85:theorem baKBoundAt_holds (d : ℕ) {Λ κ : ℝ} (hd :
RBM3D/Chain/Carrier.lean:121:def STLocalEntrygL (τ : ℕ → ℝ) : Prop :=
RBM3D/Chain/LWGen.lean:48:def LWAvgLawgL (t : ℕ → ℝ) : Prop :=
```

### (iv) Predicted lines per file (low / central / high) against the stop line 2,000
```
$ python3 -I lines.py   # per-item list in the script: copies by measured band ranges, new lemmas = measured comparable × 1.0/1.3/1.8
BAExp14a.lean    low   744  central   930  high  1245  stop line 2000: high<2000 = True
BAExp14aB.lean   low   865  central  1145  high  1660  stop line 2000: high<2000 = True
both files        low 1609 central 2075 high 2905   (ticket: 1,020 / 1,190 / 2,250)
```
The ticket's 1,020 / 1,190 / 2,250 is replaced by these. The not-planned and dropped rows of (ii) remove 821 band lines (326 + 17 + 52 + 35 + 164 + 227); the items the ticket did not price add: `facts` 80/100/140, ω `ℓ¹` 84/112/156, row 7 (a)-(d) 230/315/470, bridges 95/140/220, four family lemmas 330/420/610. Neither file reaches 2,000 at the high column (A 1,245; B 1,660). Generic glue (`≺ → 𝔼`, helpers) sits in A to keep B below the line; if B passes 1,700 at 1b mid-way, the bridges move to A.

### (v) Scope line
Nothing of §6 (`LWExpTerm4:828-939`, `lwExpI1K_holds`), §9 (`:1394-1721`, `lwExpI41K_holds`) or the twisted `T3B` part of §8 is planned; no `tw*` name, no `BATwistAvgLaw`/`BATwistLoopLaw`, no `∂Ḡ_{xy}` or `∂tr` child (D4).

### Namespace and names
Namespace `RBM.BA` (files in `Graph/`): the consumer `BALWCutExpTw`, the carrier `baFMz`, `FlowFM`, `PrecL`, `LWAvgLawgL`, `LWcutg` and the Step-1/2 chain pins are in `RBM.BA` (`Chain/LWGen.lean:30`, `BA/LWPinsBA.lean`); `RBM.Graph` (`BAlwGc`, `baLanlw_holds`) is opened, as the probe does. The sibling tickets use `RBM.Graph` (T2417, T2419, T2420) and `RBM.BA` (T2421) with other stems. `baS1_holds` is rejected: 38 existing `baS1_*` hits (`BA/Step1.lean`, `Test/Axioms.lean`: Step-1 theorems), so S1 is named `BAExp14aS1`.
```
$ bash names.sh   # planned public names: grep -w on main, in the T2417/T2419/T2420/T2421/T2422 tickets, git grep on their branches
name  main-hits  tickets(T2417,T2419,T2420,T2421,T2422)-hits  branches(t/T2417,19,20,21,22)-hits
BAExp14aS1 0 0 0
BAExp14aS1Fam 0 0 0
baExp14a_S1_holds 0 0 0
baExp14a_omega_l1 0 0 0
baExp14a_Bctl_le_one 0 0 0
baExp14a_EX_bound 0 0 0
baExp14a_W_sub_one_lift 0 0 0
baExp14a_diag 0 0 0
baExp14a_prec_integral 0 0 0
baExp14a_inst_S1 0 0 0
stems baExp14a|BAExp14a|BAS1 on main: 0 hits
rejected name baS1_holds: 38 existing baS1_* hits (files: RBM3D/BA/Step1.lean, RBM3D/Test/Axioms.lean)
```
Verdicts after repair: Target 1 PASS in mathematics, Lean compile of the def NOT delivered (see (i)); Targets 2-5 PASS as scoped by decisions 1-4 and the map (ii); Target 6 no registry entry.
Overall verdict of (a′): **BLOCKED on repair item (i) only** (missing input: authorization to write and compile the S1 `def` in the 1a scratch, which this stage's no-Lean rule forbids); items (ii)-(v) and the namespace/name grep are delivered and every target is PASS in mathematics.

### (a′) probe step: the S1 `def` compiled (Amend 1 repair item (i); CONTROL H219) — Sun Oct 11 13:17:11 UTC 2026
Role `prover-max` (probe step, as T2390 Amend 1 D1); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2418`, branch `t/T2418`, one new file `RBM3D/Probe/T2418Pins.lean` (never merged, no root import). (a) and the text of (a′) above are not edited; item (i) of the repair list ("Not delivered" above) is delivered here; items (ii)-(v) are unchanged.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2418 && lake env lean RBM3D/Probe/T2418Pins.lean     # started at the date -u of the heading
@BAExp14a_F : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (n : ℕ) → ℝ → sz.SeqΩ → Fin 6 → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
@BAExp14aS1Fam : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (n : ℕ) → ℝ → sz.SeqΩ → Fin 6 → Bool → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
BAExp14aS1 : ℕ → Prop
'RBM.BA.BAExp14aS1Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14aS1' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
$ checks (one line)
HEAD=1d302bb merge-base=1d34da3 main=f3a7401 probe-lines=168 modified-or-untracked=0 hits[sorry|admit|native_decide|^axiom ]=0
$ git diff --stat main...t/T2418   # main worktree
 RBM3D/Probe/T2418Pins.lean | 168 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 168 insertions(+)
BAExp14a hits (git grep -n, RBM3D and RBM3D.lean) at main t/T2398 t/T2417 t/T2419 t/T2420 t/T2421 t/T2422 t/T2423 t/T2424: 0 0 0 0 0 0 0 0 0 ; files of other tickets/reports with the new names: 0
```
Consumer shape (`<` = `BALWCutExpTw`; lines 435-436, the binders, the range of `t` and `let μ`, are identical to probe lines 108-109) and a numerical check of the term list:
```
$ diff <(git show t/T2398:RBM3D/Probe/T2398Pins.lean | sed -n '435,440p') <(sed -n '108,112p' RBM3D/Probe/T2418Pins.lean)
3,6c3,5
<       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
<       STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
<       PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
<         (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
---
>       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
>       PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
>         (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
$ python3 s1check.py 20 2>&1 | tee s1check_run.out   # scratch T2418/, finished Sun Oct 11 13:15:08 UTC 2026; then: sed -n '1p;14,17p' s1check_run.out; python3 summ.py
d=1 L=3 W=2 g0=0.8 E=0.3 t=0.3  m=-0.4279+0.5390j Im z_t=0.377; scrambled Sobol 2^20 points, seed 11
x=0 y=2 sigma=-  |LHS_GG|=0.013
   residuals  C1 2.9e-07 (wrong 7.1e-05, |F_C1|=2.2e-03)  C2 7.5e-06 (wrong 3.5e-05, |F_C2|=2.2e-03)  GG 1.3e-05
   GG with the first two sums printed (S+ for W-1): 8.3e-03; with W for W-1 in T1: 1.4e-02  (|T1|=1.9e-03)
   GG with one S1 term wrong: T1 1.3e-05 (|T1|=1.9e-03), T3A0 5.4e-04/5.2e-04 (|T3A0|=1.8e-03), T3A1 1.3e-04/1.2e-04 (|T3A1|=3.6e-04)
cases 6; correct residuals: max over C1, C2, GG = 1.0e-04
variants with residual >= 3x the correct one of the same case: C1 transposed 5/6, C2 transposed 5/6, printed S+ in the first two sums 6/6, W for W-1 in T1 2/2 (cases with T1 != 0), T3A0 orientation 4/6, T3A1 orientation 3/6
$ python3 cutcheck.py   # scratch T2418/: pathwise algebra at one random Hermitian H (L=3, W=2); the two LWcutg claims of the probe docstring (header, lines 91-95)
(1) max |LWcut(true,so,ac,ao) - sum form| over so, ac, ao = 1.2e-16
(2) max |LWcut(false,so,ac,ao) - conj LWcut(true,!so,ao,ac)| = 2.8e-16   (control, blocks not swapped: 6.8e-02)
```
S1 and its integrand by script (`sed -n '40,112p' RBM3D/Probe/T2418Pins.lean | awk '/^\/--/{skip=1} !skip{print} /-\/[[:space:]]*$/{skip=0}' | grep -v '^$' | grep -v '^\(section\|end\|variable\)'`: docstrings dropped; `variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)` is in force for lines 40-96):
```
def BAExp14a_X (c : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v
def BAExp14a_Wk (k : Bool) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  if k then BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) - 1 else 1
def BAExp14a_tail (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)
def BAExp14a_outer (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
    BAExp14a_tail sz z n t ω σ x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * T x y α
def BAExp14a_FMM (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α => (baFMz sz z).M n x α * (baFMz sz z).M n α y
def BAExp14a_FT1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n x β * (baFMz sz z).M n β y
def BAExp14a_FT3A (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ w, ∑ γ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) *
      (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w
def BAExp14a_FC1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n α α' *
      (baFMz sz z).G n t ω α' y
def BAExp14a_FC2 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n x α' * (baFMz sz z).G n t ω α' α *
      (baFMz sz z).M n α y
def BAExp14a_F (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![BAExp14a_FMM sz z n t ω σ a b, BAExp14a_FT1 sz z n t ω σ a b, BAExp14a_FT3A sz z n t ω false σ a b,
    BAExp14a_FT3A sz z n t ω true σ a b, BAExp14a_FC1 sz z n t ω σ a b, BAExp14a_FC2 sz z n t ω σ a b] k
def BAExp14aS1Fam (k : Fin 6) (σc σo : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  if σc then BAExp14a_F sz z n t ω k σo ao ac else star (BAExp14a_F sz z n t ω k (!σo) ac ao)
def BAExp14aS1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
```
Notes (each checkable in the probe file or in the output above).
- Index set: the tags `0..5` of `Fin 6` are `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2` (`rfl` example, line 126); `(σc, σo)` are the first two Bool arguments of `LWcutg`, so `U_n` is `BALWCutExpTw`'s with the tag added. This refines (a′)(i) "σ the charge": the σ of `(eq:ELW_term)` (`B:11-14`) is `σo`, the charge of the closing edge; the paper calls `σ = +` "analogous" (`B:15`), so (a)'s "σ=+ is the conjugate" is not used.
- `σc = false` is defined as `star` of the `σc = true` family at `(!σo, ao ↔ ac)` (lines 91-95): the intended reading of `LWcutg … false …` (cyclic trace, `C.S = 1`), checked pathwise at one random Hermitian datum by `cutcheck.py` above and not proved in Lean; the assembly (L4a2) owes `LWcutg … false σo ac ao = star (LWcutg … true (!σo) ao ac)`. For S1 the red case then follows from the blue case by `‖∫ star f‖ = ‖∫ f‖`.
- `W` is `BAlwW` at the flow data of `baFMz`; the `BAlwM` inside it is the carrier's `M` (`rfl`, line 132). `X_c` is the entry sum of `Ǧ_{vv}`: the 1b bridges it to `𝓛^{(1)} − m` of `LWAvgLawgL` (`M_{vv} = m`) and uses `Σ_δ S_{γδ} Ǧ_{δδ} = t X_{[γ]}` (`BAlwS`, `Graph/BAExpand.lean:75`); both are docstring claims here, not proved.
- Premises: `STLocalEntrygL`, `LWAvgLawgL` only (the first two of `BALWCutExpTw`'s seven, same order); no `𝔼 tr` premise (D1). Not covered (D4): `∂Ḡ_{xy}`, `∂tr`, `T2a`, `T2b`, `T3B`, `T3C`. S1 is a `def`; it is not proved. Apart from `by norm_num` side conditions in the instance example, the only tactic proof in the file is the nonemptiness example of line 149 (Mathlib names in it, compiled: `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `div_le_iff₀`, `mul_le_mul`).
- Instance (line 143): S1 at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2` with `hE`, `hA` as hypotheses (other gates' pins); `U_n` is nonempty for every `n` there (line 149).
- Numerical check above (a sanity check of the term list, not a proof): at one `d = 1`, `L = 3`, `W = 2` datum with complex Hermitian blocks, `F_T1`, `F_T3A^{(0)}`, `F_T3A^{(1)}`, `F_C1`, `F_C2` complete the identities of the merged `BAGGGammaR` (`Graph/BAGGExp.lean:67`) and `BAlanlwR` (`Graph/BAExpand.lean:106`) to QMC noise; the printed `S⁺` coefficient does not (paper delta D402).
- `main` moved on after the branch base (second and third hash above; T2419's `Graph/BAExpandId.lean` is on `main`, absent from this worktree). Paper-delta candidates from this step: none (`T2418a` stands).


## (b) Script output, stage 1b (`prover-hard`, Amend 1; CONTROL H216, H219) — Sun Oct 11 14:41:41 UTC 2026 (`date -u`)
All commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2418`; the output below is verbatim (the scratch scripts `mkb2.sh`, `axioms.lean`, `audit.lean` are in the scratchpad `T2418/`, not in the repository).
```
$ date -u; echo "HEAD=$(git log -1 --format=%h) branch=$(git rev-parse --abbrev-ref HEAD)"; git diff --stat main...t/T2418 | tail -4
Sun Oct 11 14:41:41 UTC 2026
HEAD=3bccf41 branch=t/T2418
 RBM3D/Graph/BAExp14a.lean  | 1307 ++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAExp14aB.lean | 1771 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2418Pins.lean |  168 +++++
 3 files changed, 3246 insertions(+)
$ wc -l RBM3D/Graph/BAExp14a.lean RBM3D/Graph/BAExp14aB.lean | awk '$2 != "total" {print $2, $1, ($1 < 2000 ? "< 2000 (stop line, binding)" : "OVER the stop line")}'
RBM3D/Graph/BAExp14a.lean 1307 < 2000 (stop line, binding)
RBM3D/Graph/BAExp14aB.lean 1771 < 2000 (stop line, binding)
$ lake build RBM3D.Graph.BAExp14a RBM3D.Graph.BAExp14aB 2>&1 | tail -1
Build completed successfully (3981 jobs).
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2418-check.lean > /dev/null 2>&1; echo "check file EXIT=$?"; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BAExp14a.lean RBM3D/Graph/BAExp14aB.lean
check file EXIT=0
RBM3D/Graph/BAExp14a.lean:0
RBM3D/Graph/BAExp14aB.lean:0
$ echo "public decls: $(wc -l < /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2418/pubnames.txt); with exactly [propext, Classical.choice, Quot.sound]: $(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2418/axioms.out)"; grep -E 'S1' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2418/axioms.out
public decls:      157; with exactly [propext, Classical.choice, Quot.sound]: 157
'RBM.BA.BAExp14aS1Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14aS1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExp14a_S1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ diff <(sed -n 35,112p RBM3D/Probe/T2418Pins.lean) <(sed -n 52,129p RBM3D/Graph/BAExp14aB.lean) && echo 'S1 text identical to the probe lines 35-112'
S1 text identical to the probe lines 35-112
$ sed -n '/^def BAExp14aS1 /,/^$/p' RBM3D/Graph/BAExp14aB.lean; grep -n '^theorem baExp14a_S1_holds' RBM3D/Graph/BAExp14aB.lean
def BAExp14aS1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

1692:theorem baExp14a_S1_holds (d : ℕ) : BAExp14aS1 d := by
$ sed -n '/^example (hE : STLocalEntrygL (baFMz sz0 zSeq)/,/hE hA$/p' RBM3D/Graph/BAExp14aB.lean | cut -c1-150
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  baExp14a_S1_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA
$ echo "main: $(git grep -n -e BAExp14a -e baExp14a main -- RBM3D RBM3D.lean | wc -l) hits; $(for b in t/T2417 t/T2419 t/T2420 t/T2421 t/T2422 t/T2423 t/T2424 t/T2425 t/T2426; do git rev-parse -q --verify $b >/dev/null && echo -n "$b:$(git grep -l -e BAExp14a -e baExp14a $b -- RBM3D RBM3D.lean | wc -l) " || echo -n "$b:none "; done)"
main:        0 hits; t/T2417:       0 t/T2419:       0 t/T2420:       0 t/T2421:       0 t/T2422:       0 t/T2423:       0 t/T2424:       0 t/T2425:       0 t/T2426:       0 
$ sed -n 1,2p /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2418/audit.out | cut -c1-130; echo "unregistered-premise lines: $(grep -c unregistered /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2418/audit.out) (scratch: import RBM3D, both modules, #assert_rbm_axioms)"
axiom audit: 11753 theorems, 3580 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
unregistered-premise lines: 0 (scratch: import RBM3D, both modules, #assert_rbm_axioms)
$ for n in BAExp14a_prec_integral BAExp14a_prec_fin BAExp14a_ward_row BAExp14a_green_diag_le BAExp14a_J_T3A_bd BAExp14a_J_C1_le BAExp14a_J_C2_le BAExp14a_T_MM_l1 BAExp14a_frame_le_diag BAExp14a_neumann BAExp14a_kap_l1 BAExp14a_theta_l1 BAExp14a_W_sub_one BAExp14a_Wsub_col BAExp14a_one_sub_t BAExp14a_G_ward BAExp14a_L1_eq BAExp14a_X_eq BAExp14a_Dom_Pg_Pm BAExp14a_Facts BAExp14a_facts_of_flow BAExp14a_lanlw_diag BAExp14a_e_eq BAExp14a_e_bound BAExp14a_Bctl_le_two BAExp14a_env_bd BAExp14a_FG_prec BAExp14a_core baExp14a_S1_holds; do for f in A:RBM3D/Graph/BAExp14a.lean B:RBM3D/Graph/BAExp14aB.lean; do l=$(grep -nE "^(private )?(theorem|def|structure) $n( |$)" ${f#*:} | head -1 | cut -d: -f1); [ -n "$l" ] && echo "${f%%:*}:$l $n"; done; done | tr '\n' ' ' | fold -s -w 118
A:163 BAExp14a_prec_integral A:217 BAExp14a_prec_fin A:341 BAExp14a_ward_row A:379 BAExp14a_green_diag_le A:771 
BAExp14a_J_T3A_bd A:705 BAExp14a_J_C1_le A:737 BAExp14a_J_C2_le A:594 BAExp14a_T_MM_l1 A:547 BAExp14a_frame_le_diag 
A:820 BAExp14a_neumann A:865 BAExp14a_kap_l1 A:988 BAExp14a_theta_l1 A:1116 BAExp14a_W_sub_one A:1142 
BAExp14a_Wsub_col A:1178 BAExp14a_one_sub_t A:1253 BAExp14a_G_ward B:172 BAExp14a_L1_eq B:188 BAExp14a_X_eq B:1189 
BAExp14a_Dom_Pg_Pm B:391 BAExp14a_Facts B:633 BAExp14a_facts_of_flow B:733 BAExp14a_lanlw_diag B:951 BAExp14a_e_eq 
B:978 BAExp14a_e_bound B:1103 BAExp14a_Bctl_le_two B:1018 BAExp14a_env_bd B:1293 BAExp14a_FG_prec B:1668 
BAExp14a_core B:1692 baExp14a_S1_holds 
```
Narrative (line numbers are those of the output above; the exponent counts are read off the lemma statements).
1. S1 is `BAExp14aS1` (B:52-129, byte-identical to the probe lines 35-112: diff above, empty); `baExp14a_S1_holds : ∀ d, BAExp14aS1 d` (B:1692) proves it from `STLocalEntrygL`, `LWAvgLawgL` only. All 157 public declarations of the two files print the three standard axioms; no `sorry`. `import RBM3D` + both modules + `#assert_rbm_axioms` passes with no unregistered premise: the stochastic lemmas that take `LWAvgLawgL` are `private`; the public `Prop`-valued names are `BAExp14aS1` (proved), `BAExp14a_Dom` (concluded by `BAExp14a_Dom.refl/.mul/.add/.of_le/.mono/.const_mul`, A) and `BAExp14a_Facts` (proved pointwise by `BAExp14a_facts_at`, B:589).
2. Route, `F_k = F^Ǧ_k + F^M_k` (`BAExp14a_F_split`, B:366; `G = Ǧ + M`): `a = max_c|X_c| ≺ B` from `LWAvgLawgL` (`X_c = 𝓛^{(1)}_{+,c} - m`, `BAExp14a_X_eq` B:188), `b = max|Ǧ_{xy}| ≺ B^{1/2}` from `STLocalEntrygL` (`STWB ≤ Bctl`); pathwise `J` bounds `BAExp14a_J_T3A_bd` (Ward + Schur, A:771), `_J_C1_le`, `_J_C2_le`, `_T_MM_l1`; frames `BAExp14a_frame_le_full/_diag` (A:532; pair count `W^{-d} ≤ (λ²+1)B`, `BAExp14a_Wd_le` A:1228); `‖F^Ǧ‖ ≤ b·Jm + W^{-d} b a S CM`, `‖F^M‖ ≤ W^{-d} Jm` for T3A, C1, C2; for MM, T1 `F^M = Σ_α X_{[α]} κ_α` (`BAExp14a_kap`) and `‖𝔼F^M‖ ≤ W^{-d} S CM max|𝔼X_c|`; comparison with `(1-t)⁻¹B^{5/2}` in `BAExp14a_cmp` (A:442), assembly `BAExp14a_FG_prec`, `_F_path_prec`, `_F_lin_prec`, `BAExp14a_core` (B:1293-1668), the red charge by `integral_conj` in `baExp14a_S1_holds`.
3. `𝔼X_c`: `baLanlw_holds` with `f = 1`, `y = x`, transported from `PF d L W 0` to `seqP (sz.withLam 0)` (`BAExp14a_int_slice` B:702, `BAExp14a_lanlw_diag` B:733), gives `e = t M⁺ e + R` (`BAExp14a_e_eq` B:951) and `‖e_c‖ ≤ CM ε₂/(1-t)` (`BAExp14a_neumann` A:820, `BAExp14a_e_bound` B:978) with `ε₂ ≺ B^{3/2}` (`BAExp14a_q_prec` B:1377).
4. Differences from (a)/(a′): (i) row 7: the Lean bound on `𝔼X` is the Neumann one (factor `(1-t)⁻¹`, which the pin carries), not `𝔼X = ωR`; the `ℓ¹` bound of `ω = Θ^{(+,+)}` (`BAExp14a_theta_l1` A:988, from `baProp5s_holds`) is used only for the column sums of `W - 1` (`BAExp14a_W_sub_one` A:1116 from `baW_mul`, `baSp_eq`; `BAExp14a_Wsub_col` A:1142); (ii) rows 10-11: T3A, C1, C2 are bounded with `|G| ≤ 1 + b` as a whole, exponent 5/2 (slack 0) in each, not the split of (a); (iii) `B ≤ 2` (`BAExp14a_Bctl_le_two` B:1103), not `B ≤ 1`; (iv) not written: `baExp14a_diag`, the §7 sums (inlined in the `J` lemmas), `lwExpTerm4_kerSum`; the side condition of `U_n` is not used. Constants depend on `(k, 𝔡, κ)` only (`BAExp14a_facts_of_flow`, B:633; `Λ = 𝔡⁻¹`, `c₁ = 𝔡⁻² + 1`, `κ⁻¹`); no smallness of `g`.
5. Section map as written (band → final): §2 `:129-192` → A:341 `ward_row/col`, A:379 `green_diag_le`, A:1253 `G_ward`; §3 `:199-248, 576-597` → B:172 `L1_eq`, B:188 `X_eq`, carrier `G_le`; §4 `:600-740` → A:163 `prec_integral`, A:1178 `one_sub_t`, B:1103 `Bctl_le_two`, B:1138 `eventual_scalars`, B:1018 `env_bd`; §5 `:746-826` → B:391 `BAExp14a_Facts` (no `kward`, no `diag`); §7 `:940-1103` → A:594-865 (`T_MM_l1`, `J_*`, `kap_l1`); §8 untwisted `:1104-1393` → A:217 `prec_fin` (6-tag union), A:442 `cmp`, B:1189 `Dom_Pg_Pm`, B:1293-1668; §10 `:1722-1838` → B:1718 and following (instances). Nothing of §6, §9 or the twisted `T3B` part of §8 is written; no `tw*` name.
6. Ports from `../RBM1D`, `../RBM2D`: none (nothing read from or built in them for this stage). Copies from merged RBM3D files, cited in the docstrings of A and B: `lwExpTerm4_ward_*` (`Graph/LWExpTerm4.lean`), `lwExpTerm_first_moment`/`lwExpTerm_prec_integral` (`Graph/LWExpTerm.lean`), `st6_prec_det_iff` (`Induction/Step6Kit.lean`), `KInduct_theta_l1`/`_theta_shift` (`BA/KInduct.lean`), `B45_STWB_le` (`Induction/B45.lean`), `Gres_blockMat'` (`Main/ZTransfer.lean`)

## (c) Verified Mathlib names (used in the two files; `#check` run in the scratch `names.lean`, `names2.lean`)
`Finset.sup'_le`, `Finset.exists_mem_eq_sup'`, `Finset.le_sup'`, `Finset.sum_ite_mem`, `MeasureTheory.integral_finsetSum`, `integral_mul_const`, `integral_const_mul`, `integral_map`, `integral_conj` (root, `RCLike`), `Integrable.of_bound`, `measure_iUnion_fintype_le`, `Matrix.inv_submatrix_equiv`, `mul_eq_one_comm` (root, `IsDedekindFiniteMonoid`), `Finite.exists_max`, `inv_le_comm₀`, `one_le_inv₀`.
Verified absent (error `unknownIdentifier`): `Matrix.mul_eq_one_comm`, `MeasureTheory.integral_conj`. Deprecated (build warning, replaced): `MeasureTheory.integral_finset_sum` by `integral_finsetSum`; `if_pos`/`if_neg` by `simp only [h, ↓reduceIte]`.

## (d) Open issues and paper-delta candidates
- O1. This report is longer than the 300 lines of CLAUDE.md §6: sections (a) and (a′) already had 296 lines before this stage (`wc -l`), which this stage may not edit; (b)-(d) are as short as the evidence allows. Observation for the auditor, no statement is affected.
- O2. `git diff --stat main...t/T2418` (output above) contains `RBM3D/Probe/T2418Pins.lean` besides the two sole writable files; it is the H219 probe, which stays on the branch and is never merged (the hub's step 2 of rule (A) will see it in the diff). `RBM3D.lean` is not edited here; the hub adds `import RBM3D.Graph.BAExp14a`, `import RBM3D.Graph.BAExp14aB` at merge.
- O3. Registry: none (the scratch audit above has no unregistered premise); the stochastic lemmas are `private`, so downstream L4a2/L4b2 reuse only `baExp14a_S1_holds`, the toolbox/Ward/deterministic lemmas of file A and the public B lemmas.
- O4. Owed by the L4a2 assembly, not by S1 (as in (a′)): `LWcutg … false σo ac ao = star (LWcutg … true (!σo) ao ac)`, the decomposition of the sum behind `LWcutg` into the six families plus the S2/S3 terms (`∂Ḡ_{xy}` children on `MǦ`, `ǦM`, `∂tr` children, `T2a`, `T2b`, `T3B`, `T3C`).
- O5. The facts of `BAExp14a_Facts` hold for `n ≥ n₀(κ, ε, 𝔠, 𝔡, sz, z)` (eventual, as `≺`); `n₀` is not computed.
- Paper-delta candidates: `T2418a` (as (a)): the improved average `O(B²)` of `lem:improve_exp_aver` is not needed at BA for S1; the Lean proof bounds `𝔼X_c` by `CM ε₂/(1-t)` with `ε₂ ≺ B^{3/2}` from `lanlw` with `f = 1`. `T2418b`: the pin carries `(1-t)⁻¹ (W^{-d}B_{t,0})^{5/2}`, the paper `η_t⁻¹ (W^{-d}B_{t,0})^{5/2}`; the Lean proof goes through `η⁻¹ ≤ κ⁻¹(1-t)⁻¹` (`BAExp14a_eta_inv_le`, `Im m₀ ≥ κ`), a constant `κ⁻¹` (as row 1 of (a)).
