Prover model: claude-sonnet-5-5
## (a) Math preflight — 2026-10-14 02:51:13 UTC (row a1 only: targets 1, 3, 4, 5, 6, 7 of `docs/tickets/T2501.md`; `Step5KerBA`)

### (i) Exponent table (merged sources at `t/T2501` = `main` 84915e5f; every `∃` constant depends on `(d, κ, 𝔡)` only and is chosen before `(sz, ε, 𝔠, z)`)
| # | quantity | value | constraint | slack / source |
|---|---|---|---|---|
| 1 | `A` (T1) | `(κ+1)/κ` = 3 at κ = 1/2 | `1 ≤ A`; `lam² ≤ A g₀²` | `g₀² = t₀ lam²`, `t₀ ≥ κ/(κ+1)` (`TwistStep2_T0_ge`, `TwistStep2:731`): needs `1/t₀ ≤ A`; instance `1/t₀` = 1.440 vs 3 (x2.08); limit 36/25 |
| 2 | R1 conjunct, every `n` | `0 ≤ g₀·lam`, `g₀² ≤ lam²`, `lam² ≤ A g₀²` | no window, no `0 < g₀` | `g₀·lam = √t₀ lam² ≥ 0`; `g₀² = t₀ lam²`, `t₀ < 1` (`EMn2BA_T0_lt_one`), `TwistStep2_lam0_sq` (`:740`) is `∀ n`; `g₀² = lam²` only if `lam n = 0` |
| 3 | window `Λ = 𝔡⁻¹` | `10` at 𝔡 = 1/10 | eventually `0 < g₀ ≤ 𝔡⁻¹` (`BAflow_lam0_window`, `GreenSchur:72`) | instance `g₀ ≤ 1.3e-2` (x770); guard of `ThDecay`, `KerFacts` last conjunct, `A9` (`∀ᶠ n`) |
| 4 | `C₆` (T1, `ThDecay`) | `Q₀(d, 𝔡⁻¹, κ)` of `NewKLKBA_tail` (`NewKLKBA:269`, `open private`) | row sum `C₆/(1-t) ≥ Σ_b|ΘM|`; `baComp_row_le` (`EMn2BA:386`) gives exactly `(1-t)⁻¹`, so `C₆ ≥ 1` | `Q₀ = max(2(C₅e^{1/(4c₅)} + Λ²+1), …) ≥ 2(Λ²+1) > 2` (`NewKLKBA:281`): x2; observed `Σ_b|ΘM|(1-t)` = 1.000000 (equality, so rows need `C₆ ≥ 1`); `∃ C₆` after `κ` (T2498 Amend 1: `Q₀` depends on `κ`); entry: `‖ΘM‖ ≤ Q₀ 𝒯_t(|a-b|∞)`, `zdistInf (a-b) = zdistInf (b-a)` (1b lemma) |
| 5 | `C₈`; `Cs, c₀` (T1) | `baProp8_holds d 𝔡⁻¹ κ`; `baProp5s_holds d 𝔡⁻¹ κ` (`Prop6Path:1009`, `Prop5Short:667`) | stated at `(0, a)`; move to `(a,b)` by `BAMB_shift` (`Ward:53`); mixed `Θ^{-+}` by `BATheta_swap` (`KBase:350`); column sum by `BATheta_isSymm` (`:371`) + `BATheta_row_sum_pm` (`:381`) | `BATheta0 = Θ - L^{-2d} ΣΣ Θ`, `ΣΣ = L^d/(1-t)` so offset `(L^d (1-t))⁻¹` as in `KerFacts`; observed `C₈ ≥ 0.985, 0.998`, `Cs ≥ 1.000` (`c₀ = 1/2`) at n = 0, 1 |
| 6 | semigroup, swap (T1), every `n` | `Step2Kern_uKer_BA` (`Step2Kern:112`) + `BAuKerSemigroup_holds` (`TwistGrid:199`); `BATheta_swap` | `BAReal` (`BAflow_real`) at every `n`, any sign of `g₀`; `hIm ≠ 0` from `Im m ≥ κ > 0` | no `0 < g₀` anywhere; observed residuals 1e-14 / 1e-16 (`uKer(v,w)uKer(u,v) = uKer(u,w)`; `Θ^{+-} = Θ^{-+}`) |
| 7 | A9 constants (T3) | `C_K = 1`, `C_s = 2^{d-2}e` (=2e=5.4366 at d=3), `C_T = ekPropTInf_holds d` (`PropTInf:534`, `d` only), `Ck = 2(4+C_K)+C_s C_T = 10 + 5.4366 C_T`, `δ₀ = κ/2 = 1/4` | `κ ≤ Im m` at every `n` (`EMn2BA_mF_data`, `EMn2BA:125`) | `δ₀`: `Im m₀ ≥ 0.9995` vs `κ = 0.5` (x2); `K_c = Q₀C_T + C_s` of `baNewKLKGenHyp` is not read (F7 unused): **R1 does not enter**; `(TTT2)` at `g = sz.lam n`, `u = t`: side condition `le_total`, `0 < sz.lam n` from `(eq:WO)` (instance `W^{-1.4} = (2(n+1))^{-7} ≤ lam = (2(n+1))^{-6}`, x2(n+1)) |
| 8 | A9 index fields (T3) | F5, F8, F9 of `baNewKLKGenHyp` (`NewKLKBA:446`) at `sz.withLam g₀`, index `n`, `E = BAflowEs sz z n` | `0 < g₀ n ≤ 𝔡⁻¹` (window, row 3) | fields agree at index `n` (`baStep2_newKLK` pattern, `Step2IterBA:706-731`); F8 `C_K = 1`: observed `colsum|ΘM|(1-u)` = 1.000000 (equality); F9 `M_xx = m` residual 6.7e-16 |
| 9 | D2 `c` (T4) | `c = 1`, `G = contGood (sz.withLam 0)`, `Hm = sz.seqHflowBA g₀` | `‖H_u - H_{u'}‖_entry ≤ 2N^c √|u-u'|`, `g₀Ψ` cancels | `lemDecCalELipG_seqHflow_entry_sub` (`LemDecCalELip:337`) is exactly `2 N^1 √|u-u'|`; `HighProbAt` needs only `size → ∞` (`Admissible`, `cont_highProbAt_good`); no slack in `c`, none needed |
| 10 | D3 exponent (T5) | `2k+2 = 6` at `k = 2` (`NQEndFlowGen:209`) | `(Θ_u - Θ_{u'})M = (u-u')(Θ_uM)(Θ_{u'}M)`, entry `≤ \|u-u'\|(1-u)⁻¹(1-u')⁻¹`, `W^{-d} ≤ 1`; `1-t ≥ 1-T₀ ≥ Im z/2 ≥ N^{-1+ε}/2` (`EMn2BA_one_sub_T0`) gives `(1-t)⁻² ≤ 4N^{2-2ε}` | need `4N^{2-2ε} ≤ N^6` iff `N^{4+2ε} ≥ 4`: any `N ≥ 2` (eventual); exponent slack 4+2ε = 4.2; source `baKsol_two` (`KInduct:88`), `t n ≤ T₀ < 1` |
| 11 | inline `hmn`, `hSr` (T6) | `‖m‖ ≤ 1` (`BAm_norm_le_one`, `Ward:136`, every `n`), `Σ_b‖S‖ = 1` (`S = 1`) | `≤ 1` | no slack: `‖m₀‖ → 1` as `n → ∞` (`m₀ → i`), `0.9995` at n = 0; non-strict, so fine |
| 12 | T7 | `stNewKLKLgL'_of d (fun sz E => baStep2Fam sz E)` with `baNewKLKGenHyp` | premise shape `3 ≤ d → ∀ κ 𝔡, 0<κ → 0<𝔡 → NewKLKGenHyp …` | ≤ 5 lines, no new constant |
| 13 | `∀ n` at `g₀ n ≤ 0` (fill-in vi) | semigroup row 6, swap row 6, R1 row 2, `hmn`/`hSr` row 11 | all sources need `BAReal` or nothing | none needs `0 < g₀`: no stop; `ThDecay`, `A9`, `D3` are guarded or eventual |
| 14 | registry, imports, size (fill-in viii, ix, x) | row a1: no `owedProps` line; `RBM3D.lean`: add `import RBM3D.BA.Step5KerBA` after `import RBM3D.BA.Step5IIITargets` (line 604); bottom-up ≈ 740 lines | stop lines 1150 (row), 2000 (file) | name-clash grep of the 6 target names and `Step5KerBA` over `RBM3D/` and `RBM3D.lean`: 0 hits; `RBM3D/BA/Step5KerBA.lean` absent; the 13 imports of the ticket exist and their import closure (371 modules) contains `Step2Kern`, `EMn2BA`, `Ward`, `KKernel`, `GreenSchur`, `EKPins`, `Step2BA`, `FlowPins`, `ContinuityNet`, `LemDecCalELip`, `EtermsMid2`, `PropTInf`, `Step5KerGen`, `NewKLKGen`, `GridDuhamelGen`, `BlockAnderson`, `KSolve` (`SEforLnBA` is not needed by row a1); `Test/Axioms.lean` has no `T2501` or `Step5KerBA` text |

### (ii) Concrete nondegenerate instance
`d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`, `Defs/Sizes.lean:260`), `z_n = zS(L_n, lam_n)` with `w = 6i/5` (`FlowPins:1181`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`: `BAFlow sz0 … zSeq` is the merged `flow_sz0` (`FlowPins:1214`). Not degenerate: `N_0 = 2097152`, `L_0 = 4` (64 sites), `W_0 = 32`, window `0 < g₀ ≤ 1.3e-2 ≤ 10`, `t ≤ t₀ ≈ 0.694 < 1`. The dense checks at `n = 0, 1` build `M = (g₀Ψ - (E+m₀))⁻¹` and `Θ_t^{(σσ')}`; external hypotheses: none for row a1 (all inputs merged), the limit computation of the flow data is the `limit` line. Observed constants are lower bounds at these points; the Lean constants are the merged ones (rows 4, 5, 7).
Command: `python3 -u /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2501/inst2.py`
```
n  L  W  lam  N | Im m  Im z  t0  E  g0 | g0>0,<=1/D | g^2/g0^2<=A=3 | N^-1+eps<=Im z<=1 | Im m>=kappa | 1-t0>=Im z/2 | |m0|<=1 | N^eps>=2
0 4 32 1.56e-02 2.10e+06 | 0.8325 0.3675 0.6937 3e-18 1.301e-02 | True 1.441 True True True True 4
1 8 1024 2.44e-04 5.50e+11 | 0.8333 0.3667 0.6944 2e-20 2.035e-04 | True 1.440 True True True True 15
2 12 7776 2.14e-05 8.12e+14 | 0.8333 0.3667 0.6944 7e-21 1.786e-05 | True 1.440 True True True True 31
5 24 248832 3.35e-07 2.13e+20 | 0.8333 0.3667 0.6944 1e-22 2.791e-07 | True 1.440 True True True True 108
10 44 5153632 8.82e-09 1.17e+25 | 0.8333 0.3667 0.6944 2e-24 7.350e-09 | True 1.440 True True True True 321
20 84 130691232 1.82e-10 1.32e+30 | 0.8333 0.3667 0.6944 8e-27 1.518e-10 | True 1.440 True True True True 1028
limit n->inf (g->0): Im m_S -> 1/1.2=0.8333, Im z_S -> 1.2-5/6=0.3667, t0 -> 25/36=0.6944, E -> 0, Im m0 -> sqrt(1.2*5/6)=1.0000, g^2/g0^2=1/t0 -> 1.440 <= A=3.0

n=0 (dense 64x64, W^d=32768): self_m residual 1.1e-16, max|M_xx-m0| 6.7e-16, |M^T-M| 1.0e-17, max|sum_b|M_ab|^2-1| 1.1e-15
 t in [0.0, 0.3, 0.694, 0.9, 0.99, 0.999] observed: C6>=0.984  rowsum*(1-t)<=1.000000  colsum(|ThM|)*(1-t)<=1.000000 (C_K=1)  C8>=0.985  Cs>=1.000 (c0=1/2)
 scaled by (1-t): |Th^{+-}-Th^{-+}| 2.8e-16, |Th^T-Th| 1.4e-16, |colsum Th^{+-}-1/(1-t)| 7.4e-13
 semigroup (u,v,w)=(.1,.5,.8): err 1.3e-14; uKer(v,v)-1: 2.1e-15
 (TTT2) observed C_T>=15.07 ; D3 on [0,t0=0.6937]: max|Th_uM-Th_u'M|/|u-u'|=7.695 <= (1-t0)^-2=10.662 ; W^-d*that=2.3e-04 <= N^6=8.5e+37 (exponent 2k+2=6, needed 2)

n=1 (dense 512x512, W^d=1073741824): self_m residual 3.3e-16, max|M_xx-m0| 6.7e-16, |M^T-M| 1.4e-19, max|sum_b|M_ab|^2-1| 1.3e-15
 t in [0.0, 0.3, 0.694, 0.9, 0.99, 0.999] observed: C6>=0.998  rowsum*(1-t)<=1.000000  colsum(|ThM|)*(1-t)<=1.000000 (C_K=1)  C8>=0.998  Cs>=1.000 (c0=1/2)
 scaled by (1-t): |Th^{+-}-Th^{-+}| 5.6e-20, |Th^T-Th| 6.9e-20, |colsum Th^{+-}-1/(1-t)| 1.1e-12
 semigroup (u,v,w)=(.1,.5,.8): err 1.8e-15; uKer(v,v)-1: 2.2e-16
 (TTT2) observed C_T>=54.96 ; D3 on [0,t0=0.6944]: max|Th_uM-Th_u'M|/|u-u'|=7.768 <= (1-t0)^-2=10.711 ; W^-d*that=7.2e-09 <= N^6=2.8e+70 (exponent 2k+2=6, needed 2)

A9: C_K=1, C_s=2^(d-2)e=5.4366, delta0=kappa/2=0.25, Ck=2(4+C_K)+C_s*C_T=10+5.4366*C_T (C_T merged, d only); K_c=Q0*C_T+C_s unused (F7 not read)
D2: c=1, |dH entry|<=2*N*sqrt|u-u'| on {all coords |x|<=N}; N_0=2097152, exp(-N_0^2/2)=exp(-2.20e+12) (coordinate variance<=1); N_n>=n so size->inf holds
```
Observations from the output: `Im z ≥ N^{-1+ε}` and `1-t₀ ≥ Im z/2` hold at every listed `n`; `|E_n| ≤ 3e-18` (bipartite torus, `Re m_S = 0`), so the real energy is 0; the observed `(TTT2)` constant grows from 15 (L = 4) to 55 (L = 8) and is only a lower bound for the merged `d`-only constant.

### Verdicts (row a1)
- Target 1 `baIniTermGen_kerFacts` (`T2501_KerFactsBA`) and `baStep5KerGen_thDecay` (`T2501_ThDecayBA`, `∃ C₆` after `κ`): PASS (rows 1-6, 13).
- Target 3 `baEtermsMid_newKLKL` (A9, copy of `stNewKLKLAtgL'_of`, no R1): PASS (rows 7, 8).
- Target 4 `baLemDecCalELipG_flowMod` (D2, `c = 1`): PASS (row 9).
- Target 5 `baKLip_two` (D3, `N^6` vs needed `4N^{2-2ε}`): PASS (row 10).
- Target 6 inline `hmn`, `hSr`: PASS (row 11). Target 7 `baNewKLKLgL'`: PASS (row 12).
- No stop rule is triggered: no `∀ n` clause needs `0 < g₀`; A9 does not read F7; no merged file changes (the only `private` read, `NewKLKBA_tail`, `NewKLKBA:269`, is taken by `open private`).

## (b) Script output (stage 1b, row a1; commits b2899ab2, 0d98bc2b on t/T2501; written 2026-10-14 03:18:08 UTC)
Scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2501/evidence.sh`, `evidence.py`, `routes.py` (scratchpad); output pasted verbatim.
```
$ lake build RBM3D.BA.Step5KerBA 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.setOption false`
Build completed successfully (4112 jobs).
lines of that build output that mention Step5KerBA.lean: 0
$ lake build (full, tail; registry line from #assert_rbm_axioms)
6760:registry: 2 borrowed + 119 owed + 123 structural + 7 refuted + 18 superseded; 146 registered premise(s) c
Build completed successfully (4378 jobs).
$ lake env lean pins_a1.lean  (scratch, uncommitted: pins T2501_* copied from the check; `example : T2501_X := <name>` for the six a1 pins; then #print axioms)
'RBM.BA.baIniTermGen_kerFacts' axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5KerGen_thDecay' axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEtermsMid_newKLKL' axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLemDecCalELipG_flowMod' axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKLip_two' axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baNewKLKLgL'' axioms: [propext, Classical.choice, Quot.sound]
exit code: 0
$ wc -l RBM3D/BA/Step5KerBA.lean
     708 RBM3D/BA/Step5KerBA.lean
$ git diff main...t/T2501 --stat
 RBM3D.lean               |   1 +
 RBM3D/BA/Step5KerBA.lean | 708 +++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 709 insertions(+)
diff-stat lines under RBM3D/Chain Induction Evolution Graph Test:        0
files changed under RBM3D/BA (merged BA files untouched iff only the new file):
RBM3D/BA/Step5KerBA.lean
$ grep (hypothesis rules) on the new file
C1 hits: 0
X1-C4 ^(noncomputable )?(def|abbrev|structure) : 0
local copies of the pinned classes (def|theorem): 0
T24*_ text: 0
sorry|admit|axiom|native_decide: 0
withLam line numbers (lines >= 50, excluding docstring line 358):
374 375 376 377 378 387 392 395 396 402 403 647 667 669 670 672 674 675 679 681 684 686 690 692 695 697 
$ name-clash grep (hits outside the new file, new public names and the stem)
baStep5KerGen_thDecay:        0
baIniTermGen_kerFacts:        0
baEtermsMid_newKLKL:        0
baLemDecCalELipG_flowMod:        0
baKLip_two:        0
baNewKLKLgL':        0
Step5KerBA_:        0
RBM3D.lean import line: 605:import RBM3D.BA.Step5KerBA
```
Target statements (`evidence.py targets`; `file:line` prefixes are lines of `RBM3D/BA/Step5KerBA.lean`):
```
132: theorem baStep5KerGen_thDecay : ∀ d : ℕ, 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ : ℝ, 0 < C₆ ∧
133:     ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
134:       Step5KerGen_ThDecay (baFMz sz z) (BAflowLam0 sz z) 𝔡⁻¹ C₆ := by
161: theorem baIniTermGen_kerFacts : ∀ d : ℕ,
162:     IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowLam0 := by
361: theorem baEtermsMid_newKLKL : ∀ d : ℕ, EtermsMid_NewKLKL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
362:     (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) := by
390: theorem baLemDecCalELipG_flowMod : ∀ d : ℕ, ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
391:     ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
392:       LemDecCalELipG_FlowMod (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) c := by
476: theorem baKLip_two : ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
477:     ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → NQEndFlowGen_KLip (baFMz sz z) t 2 := by
550: theorem baNewKLKLgL' : ∀ d : ℕ, STNewKLKLgL' d (fun sz E => baStep2Fam sz E) :=
```
Compiled nonempty instances (`evidence.py instances`: the `example` statements of section 6; proofs in the file):
```
585: example : ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧
586:     Step2Gen_USemigroup (baFMz sz0 zSeq) 0 ∧
587:     (0 ≤ BAflowLam0 sz0 zSeq 0 * sz0.lam 0 ∧ BAflowLam0 sz0 zSeq 0 ^ 2 ≤ sz0.lam 0 ^ 2 ∧
588:       sz0.lam 0 ^ 2 ≤ A * BAflowLam0 sz0 zSeq 0 ^ 2) ∧
589:     (∀ σ : Bool, STThg (baFMz sz0 zSeq) 0 σ (!σ) (1 / 2) = STThg (baFMz sz0 zSeq) 0 (!σ) σ (1 / 2)) ∧
590:     ∀ σ : Bool,
591:       (∀ b : Zd 3 (sz0.L 0), ∑ a : Zd 3 (sz0.L 0), STThg (baFMz sz0 zSeq) 0 σ (!σ) (1 / 2) a b = (((1 - 1 / 2 : ℝ) : ℂ))⁻¹) ∧
592:       (∀ a b : Zd 3 (sz0.L 0), ‖STThg (baFMz sz0 zSeq) 0 σ (!σ) (1 / 2) a b - (((sz0.L 0 : ℕ) : ℂ) ^ 3)⁻¹ * (((1 - 1 / 2 : ℝ) : ℂ))⁻¹‖ ≤
593:           C₈ * (BAflowLam0 sz0 zSeq 0 ^ 2 + |1 - 1 / 2|)⁻¹ * ((((zdistD 3 (sz0.L 0) (b - a) : ℕ) : ℝ) + 1) ^ (3 - 2))⁻¹) ∧
594:       (∀ a b : Zd 3 (sz0.L 0), ‖STThg (baFMz sz0 zSeq) 0 σ σ (1 / 2) a b‖ ≤
595:           Cs * ((if a = b then (1 : ℝ) else 0) +
596:             BAflowLam0 sz0 zSeq 0 ^ 2 * Real.exp (-(c₀ * ((zdistD 3 (sz0.L 0) (b - a) : ℕ) : ℝ))))) := by
605: example : ∃ C₆ : ℝ, 0 < C₆ ∧ Step5KerGen_ThDecay (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) ((1 / 10 : ℝ)⁻¹) C₆ ∧
606:     ∀ (σ σ' : Bool) (a b : Zd 3 (sz0.L 0)),
607:       ‖Step2Gen_thetaKer (baFMz sz0 zSeq) 0 σ σ' (1 / 2) a b‖ ≤
608:         C₆ * tailT 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (1 / 2) ((zdistInf 3 (sz0.L 0) (b - a) : ℕ) : ℝ) := by
616: example : ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧
617:     (∀ᶠ n in atTop, EtermsMid_NewKLKLAtN (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n Ck δ₀) ∧
618:     ∃ n : ℕ, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
619:       ‖STELKLKMg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n 0
620:           (((BAflowLam0 sz0 zSeq n : ℝ) : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)) σ a‖ ≤
621:         Ck / (1 - 0) * (STJhatMg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n 1 ((sz0.L n : ℕ) : ℝ) 0
622:               (((BAflowLam0 sz0 zSeq n : ℝ) : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)) ^ 2 * STprof sz0 n 0 1 ((sz0.L n : ℕ) : ℝ) (a 0) (a 1) +
623:           STJhatMg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n 1 ((sz0.L n : ℕ) : ℝ) 0
624:               (((BAflowLam0 sz0 zSeq n : ℝ) : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)) * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ *
625:             ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
646: example : ∃ c : ℝ, 0 ≤ c ∧
647:     LemDecCalELipG_FlowMod (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (Sizes.seqP (sz0.withLam 0)) c := by
653: example : NQEndFlowGen_KLip (baFMz sz0 zSeq) (fun _ => (1 / 2 : ℝ)) 2 ∧
654:     ∃ n : ℕ, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
655:       ‖(baFMz sz0 zSeq).K n 0 σ a - (baFMz sz0 zSeq).K n (1 / 2) σ a‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |(0 : ℝ) - 1 / 2| := by
662: example : (∀ n : ℕ, ‖(baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).m n‖ ≤ 1) ∧
663:     ∀ (n : ℕ) (a : Zd 3 (sz0.L n)), ∑ b, ‖(baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).S n a b‖ ≤ 1 :=
668: example : ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧
669:     ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 ((sz0.withLam (BAflowLam0 sz0 zSeq)).L 0)),
670:       ‖STELKLKMg (baStep2Fam (sz0.withLam (BAflowLam0 sz0 zSeq)) (fun _ => BAflowEs sz0 zSeq 0)) 0 0
671:           (((BAflowLam0 sz0 zSeq 0 : ℝ) : ℂ) • PsiI 3 (sz0.L 0) (sz0.W 0)) σ a‖ ≤
672:         Ck / (1 - 0) * (STJhatMg (baStep2Fam (sz0.withLam (BAflowLam0 sz0 zSeq)) (fun _ => BAflowEs sz0 zSeq 0)) 0 1
673:               (((sz0.L 0 : ℕ) : ℝ)) 0 (((BAflowLam0 sz0 zSeq 0 : ℝ) : ℂ) • PsiI 3 (sz0.L 0) (sz0.W 0)) ^ 2 *
674:             STprof (sz0.withLam (BAflowLam0 sz0 zSeq)) 0 0 1 (((sz0.L 0 : ℕ) : ℝ)) (a 0) (a 1) +
675:           STJhatMg (baStep2Fam (sz0.withLam (BAflowLam0 sz0 zSeq)) (fun _ => BAflowEs sz0 zSeq 0)) 0 1
676:               (((sz0.L 0 : ℕ) : ℝ)) 0 (((BAflowLam0 sz0 zSeq 0 : ℝ) : ℂ) • PsiI 3 (sz0.L 0) (sz0.W 0)) *
677:             (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
```
Merged sources used (`routes.py`, `name file:line` under `RBM3D/`):
```
Step2Kern_uKer_BA Chain/Step2Kern.lean:112; BAuKerSemigroup_holds BA/TwistGrid.lean:199
Step2Kern_thetaKer_BA Chain/Step2Kern.lean:90; Step2Kern_Mss_BA Chain/Step2Kern.lean:73
NewKLKBA_tail BA/NewKLKBA.lean:269; baComp_row_le BA/EMn2BA.lean:386
TwistStep2_lam0_sq BA/TwistStep2.lean:740; BATheta_swap BA/KBase.lean:350
BATheta_isSymm BA/KBase.lean:371; BATheta_row_sum_pm BA/KBase.lean:381
BATheta_resolvent BA/KBase.lean:330; baProp8_holds BA/Prop6Path.lean:1009
baProp5s_holds BA/Prop5Short.lean:667; baP8_BATheta_shift BA/Prop6Path.lean:497
BAflow_real BA/GreenSchur.lean:59; BAflow_lam0_window BA/GreenSchur.lean:72
baNewKLKGenHyp BA/NewKLKBA.lean:446; ekPropTInf_holds Evolution/PropTInf.lean:534
stNewKLKLAtgL'_of Chain/NewKLKLGen.lean:190; stNewKLKLgL'_of Chain/NewKLKLGen.lean:301
NewKLKLGen_bound2 Chain/NewKLKLGen.lean:57; NewKLKGen_ward_LKM Chain/NewKLKGen.lean:296
lemDecCalELipG_seqHflow_entry_sub Induction/LemDecCalELip.lean:337; cont_highProbAt_good Induction/ContinuityNet.lean:369
baKsol_two BA/KInduct.lean:88; EMn2BA_one_sub_T0 BA/EMn2BA.lean:111
EMn2BA_T0_lt_one BA/EMn2BA.lean:106; BAm_norm_le_one BA/Ward.lean:136
baStep2Fam_lam_pos_le BA/Step2BA.lean:170
```

Narrative (row a1; facts from the output above and from `RBM3D/BA/Step5KerBA.lean`):
- Delivered: new `RBM3D/BA/Step5KerBA.lean` (708 lines; stop line 1,150, bottom-up 740) and `RBM3D.lean:605`; nothing else changed (the diff above). Commits b2899ab2 (2026-10-13T20:10:04-07:00) and 0d98bc2b (20:13:17-07:00, docstring only). Full `lake build` after the last commit: completed, 0 `error` lines.
- Lines by section (`grep -n '^section\|^end '`): header 1-76; KerFacts + ThDecay 77-229 (153; ticket 300); A9 230-381 (152; 180); D2 382-408 (27; 30); D3 409-527 (119; 130); inline facts + target 7 528-554 (27; 25); instances 555-705 (151; the ticket's 80 is for header and instances).
- Target 1. `baStep5KerGen_thDecay`: `Step2Kern_thetaKer_BA` turns `thetaKer` into `Θ M^{(σσ')}`, `NewKLKBA_tail` (opened private) gives `Q₀ 𝒯_{g₀}`, `baComp_row_le` gives `(1-t)⁻¹`; `C₆ = max Q₀ 1`, chosen after `κ`. `baIniTermGen_kerFacts` takes `C₆` from it, `C₈` from `baProp8_holds`, `(Cs, c₀)` from `baProp5s_holds`, `A = (κ+1)/κ`; semigroup `BAuKerSemigroup_holds` through `Step2Kern_uKer_BA`; R1 `TwistStep2_lam0_sq` with `g₀·lam = √t₀·lam²`; swap `BATheta_swap`; column sum `BATheta_isSymm` and `BATheta_row_sum_pm`; the zero mode and short range are moved from `(0, b-a)` to `(a, b)` by the public lemma `baP8_BATheta_shift` (`Prop6Path:497`; section (a) names `BAMB_shift`, which is not needed); the double sum is `L^d (1-t)⁻¹` from the row sums and `BAcard_Zd`.
- Target 3 (A9). Route: private per-carrier copy `Step5KerBA_newKLKLAtN_of` of the body of `stNewKLKLAtgL'_of` (`NewKLKLGen:190-299`, this repository; no RBM1D/RBM2D text); `Ck = 2(4+C_K) + C_s C_T`, `δ₀ = κ/2` before the sizes; F5, F8, F9 from `baNewKLKGenHyp` at `sz.withLam g₀` (lines 374-378), `(TTT2)` at `g = sz.lam n`, `κ ≤ Im m` from `EMn2BA_mF_data`. R1 did not enter: `TwistStep2_lam0_sq` occurs once in the file, line 180 (KerFacts); F7 is not read.
- Targets 4, 5. D2: `Hm = sz.seqHflowBA g₀`, `G = contGood (sz.withLam 0)`, `c = 1`; the clauses `LM`, `GMM` are `rfl`. D3: `baKsol_two` at the window; `(Θ_u - Θ_{u'})M = (u-u')(Θ_uM)(Θ_{u'}M)` from `BATheta_resolvent` (private `Step5KerBA_Theta_sub`); entries bounded by two row sums; `(1-u)⁻¹ ≤ 2N` from `EMn2BA_one_sub_T0` and `N^{-1+ε} ≤ Im z`; `W^{-d} ≤ 1`; `4N² ≤ N⁶` for `N ≥ 2` (eventually, `Sizes.tendsto_size`).
- Statement diff: the six targets equal their `T2501_*` pins (scratch `example : T2501_X := name` compiles, exit 0). Family table (U5S-C3) rows used: 2 (target 1), 7 (target 3), 8 (targets 4, 5), 9 (target 6); no premise beyond the table, no new public `def` (X1-C4 count 0).
- UBA-C1 as used: the only crossing is R1's conjunct (line 180). Targets 3-5 read `STprof`, `STJhatMg`, `(TTT2)` at `sz.lam n` and the kernel at `g₀` through F5/F8/F9 with no comparison. Constants depend on `(d, κ, 𝔡)` only (`A = (κ+1)/κ`, `c = 1`, `δ₀ = κ/2`). `withLam` in code: 374-378 (target 3), 392-403 (target 4: `seqP (sz.withLam 0)`, `contGood (sz.withLam 0)`, `seqHflow` of `sz.withLam 0`), 647 (D2 instance) and 669-697 (target-7 instance at `sz0.withLam g₀`); 358, 387, 667 are docstrings.
- `∀ n` sources at `g₀ n ≤ 0`: semigroup `BAflow_real` + `BAuKerSemigroup_holds` (`BAReal` only; `Step5KerBA_hIm` uses `0 < κ`, `κ ≤ Im m`); R1 `TwistStep2_lam0_sq`, `√t₀ ≥ 0`; swap `BATheta_swap` (no hypothesis); D2 clauses (no window). ThDecay, the three entrywise facts, A9 and D3 are guarded by `0 < g₀ ≤ 𝔡⁻¹` or `∀ᶠ n` (`BAflow_lam0_window`). No stop rule triggered.
- Registry: row a1 has no `Test/Axioms.lean` edit (`git diff ... -- RBM3D/Test` is 0 lines); the registry line on this branch reads `119 owed` and `RBM3D/Test` is identical to `main`'s, so this row changes nothing there (the ticket's 119 → 114 → 109 starts with rows a2 and b).
- Instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`): `Step5KerBA_inst_window` proves `0 < g₀_n ≤ 10` for every `n`; `sz0_values` (`Defs/Sizes:267`): `L_0 = 4`, `W_0 = 32`, `N_0 = 2097152`, `lam_0 = 1/64`; `g₀_0 ≈ 1.3·10⁻²` is from section (a)'s script. The A9 and target-7 instances use `H = g₀Ψ` at `u = 0`, where `G_0 - M = 0` (so the premise `‖GMM‖ ≤ δ₀` is met, not vacuous); the D3 instance uses `t ≡ 1/2 ≤ t₀` (`half_lt_t0`), `u = 0`, `u' = 1/2`. No hypothesis is left open.
- Imports: the ticket's 13 with `Induction/EtermsMid` replaced by `Induction/EtermsMid2` (it defines `EtermsMid_NewKLKL`; `EtermsMid` imports it). Opened private names: `NewKLKBA_tail`, `Step2IterBA_lam_window`, `nkl_zdistInf_sub_comm`, `newKLKL_Cs_ge_one`, `newKLKL_tailT_le_tailW`, `NewKLKGen_ward_LKM`, `NewKLKLGen_bound2`; no merged file changed. No port from RBM1D or RBM2D (no file there was read), so the RBM1D/RBM2D diff-stat does not apply.

## (c) Verified Mathlib names used (the build above compiles every one; none was invented)
- `Finset.single_le_sum`, `Finset.sum_mul`, `Finset.sum_ite_eq`, `Finset.card_univ`, `Finset.le_sup'`, `nsmul_eq_mul`
- `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `inv_anti₀`, `inv_div`, `div_eq_mul_inv`, `div_le_iff₀`, `le_div_iff₀`, `div_le_div_of_nonneg_right`
- `Real.rpow_neg`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.sqrt_nonneg`
- `Matrix.conjTranspose_smul`, `Matrix.mul_apply`, `Matrix.sub_mul`, `Matrix.one_apply`, `Matrix.mul_assoc`
- `Complex.conj_ofReal`, `Complex.norm_real`, `Complex.norm_natCast`, `Nat.one_le_cast`, `Nat.cast_pos`, `norm_sum_le`
- `sub_eq_iff_eq_add`, `mul_self_nonneg`, `Filter.Eventually.exists` (used as `h.exists`), `Filter.Tendsto.eventually_ge_atTop`
- Names verified absent: none were searched.

## (d) Open issues and paper-delta candidates
- No Lean/paper statement difference arises in this file (A9 reads `(i2kk2zgg)` only; R1 enters only through the KerFacts conjunct). Candidate `T2501a` (numbering for the dispatcher, shape only): the BA kernel-decay constant `C₆` depends on `κ` (`NewKLKBA_tail`, `NewKLKBA:269`: `Q₀` in `(d, Λ, κ)`), so `baStep5KerGen_thDecay` publishes `∃ C₆` after `κ`, as T2498 Amend 1 requires.
- Doc finding (not a statement difference): the docstring of `EMn2BA_mF_data` (`EMn2BA:124`) says `‖m_F‖ ≤ 1` but its second conjunct is `Im m_F ≤ 1` (the compiler rejected it as `hmn`); `hmn` uses `BAm_norm_le_one` (`Ward:136`).
- Merge note for the hub: the ticket lists `RBM3D.lean` import lines for rows a1 and a2, so the two rows each add one import line at the same place (after `import RBM3D.BA.Step5IIITargets`); the merge is a union of lines. Row b (`Step5CasesBA`) starts after a1 and a2 are audited and merged; it reads targets 1, 3, 4, 5 (and 6 only as inline facts).
- Not done here (not row a1): target 2 (row a2), targets 9-12 (row b), the registry deletions (rows a2 and b).
