Prover model: claude-sonnet-5-5
## (a) Math preflight — 2026-10-14 09:26:59 UTC (row a only: targets 1-5)

Mathematics fixed for row a. Source lines: band `Induction/QtNonzeroBoot` (`stBoot_rounds` :136, `qtBoot_contraction` :246, `qtBoot_crude` :337, `stXiBoot'_of_round` :522, `stXiBootR_of_round` :581), `Induction/QtXiRoundLift` (`qtLift_arith` :439, `qtLift_lift` :640), merged `Chain/NQGood1Gen:618` (`STXiLKMg_crudeNg`), `LemDecCalELip:434` (`Lloop_subg`), `:1111` (`envg`), `Chain/NQEndFlowGen:215` (`KLipFam`), `Chain/Step2EventsGen:68` (`_Flow`). Notation: `N = sz.size n`, `B_u = sz.Bctl n u`, `cH` = the `∃ c ≥ 0` of `T2505_FlowModFam` (Hölder `2 N^cH √|u-u'|`), `τT` = the `∃ τ > 0` of `hT0` (`RangeCond τT (T0 sz z)`), `κm` = the `∃ κm` of `DecayGen_Spec` (`κm ≤ Im m`, `η_u = (1-u) Im m`).

### (i) Exponent table

| # | quantity | value (instance: `d=3, κ=ε=𝔡=1/10, 𝔠=1/6, n_=2, cH=1, τT=1/2`) | constraint | slack |
|---|---|---|---|---|
| 1 | contraction level `c₁ = min(2𝔡𝔠, τT)` (band: `min(2𝔡𝔠, ε/2)`, `QtNonzeroBoot:229`) | `1/30` (`2𝔡𝔠 = 1/30` binds; `τT = 1/2`; band `ε/2 = 1/20`) | `c₁ > 0`; `B_u ≤ 2N^{-c₁}` from `W ≥ N^𝔠`, `λ ≥ W^{-d/2+𝔡}` (`lam_sq_mul_pow_ge`) and `1-u ≥ N^{-1+τT}` | `τT / (2𝔡𝔠) = 15`; the generic `c₁` has no `ε`: `τT` comes from `hT0`, the band's `ε/2` is one admissible `τT` (finding, not a statement change) |
| 2 | contraction `c = c₁/12`, `B_u^{1/6} ≤ N^{-c}` | `1/360` | `B_u ≤ 2N^{-c₁} ≤ N^{-c₁/2} ≤ 1`, needs `N^{c₁/2} ≥ 2` i.e. `N ≥ 2^{2/c₁} = 2^{60}` | proof threshold (sufficient, not a hypothesis): first instance index `n=4`, `N = 8.0e18 = 2^{62.8}`, slack `2^{2.8}`; the inequality itself already holds at `n = 0` (`0.179 ≤ 0.960`) |
| 3 | crude exponent `C₀ = 2n_+1` (`STXiLK ≤ N^{2n_+1}`) | `5` | `1 + (η^{-n_} + N)/B^{n_} ≤ (2+μ^{n_}) N^{2n_} ≤ N^{2n_+1}`, `μ = κm⁻¹`, `η⁻¹ ≤ μ N B ≤ μ N` (`expWII_inv_Neta_le` twin from `η=(1-u)Im m`, `B ≥ (N(1-u))⁻¹`), `B⁻¹ ≤ N` | `N ≥ 2+μ^{n_}`: with `κm = √(κ/2)/2 = 0.1118`, `μ² = 80`, threshold `82`, `N_0 = 2.1e6` (factor `2.6e4`) |
| 4 | rounds `r = ⌈C₀/c⌉ + 1` | `1801` | finite, depends on `(C₀, c)` only, not on `n` (`stBoot_rounds`); `r+1` absorbed by `const_mul_right` | no `n`-dependence; `r` grows linearly in `1/c` (`1/c = 360`) |
| 5 | window `(1-t)⁻¹ ≤ N` and `η_t⁻¹ ≤ N²` (`LemDecCalELip_envg`) | `(1-t)⁻¹ = 16/15`, `N^{1-τT} = 1448` at `n=0`; `η_t⁻¹ = (1-t)⁻¹/Im m = 1.10 ≤ N²` | `t ≤ T0`, `RangeCond τT`: `(1-t)⁻¹ ≤ N^{1-τT} ≤ N`; `N ≥ κm⁻¹` | `N^{τT}` (`1448` at `n=0`); `N/μ = 2.3e5` |
| 6 | Hölder exponent `cH` of `T2505_FlowModFam` (band `c = 1`, `lemDecCalELipG_seqHflow_entry_sub`) | `1` | `cH ≥ 0` (`Lloop_subg` `hc`); pinned `∃ c` after `(κ, ε, 𝔡)`, before `(sz, z, n_)` | `cH` enters only the mesh exponent (row 7) |
| 7 | net mesh `δ ≤ N^{-m}`, `m = 6n_ + 18 + 2cH` (band `6n_+20` at `cH = 1`, `qtLift_arith :439`) | `32` (`n_=2`) | `‖Δ𝓛‖ ≤ 3n_ N^{2n_+6+cH}√δ` (`Lloop_subg`), `‖Δ𝒦‖ ≤ N^{2n_+2}δ` (`KLip`, `k=n_`), `B⁻¹ ≤ N`: `N^{n_}(3n_N^{2n_+6+cH}√δ + N^{2n_+2}δ) = 3n_N^{-3} + N^{-(3n_+16+2cH)} ≤ (3n_+1)N^{-3} ≤ 1` | needs `N ≥ 3n_+1 = 7`; value `0.0175` at `N = 7` (`n_=2`), `6.5e-19` at `N_0` (script below); net size `N^m` is absorbed by the arbitrary `D` of `≺` |
| 8 | `KLip` exponent `2k+2` at `k = n_ ≥ 2` | `6` | merged text `NQEndFlowGen_KLip`, no `∃`; unit `|u-u'|`, `u,u' ≤ t ≤ T0` | none needed (explicit) |
| 9 | `ζ♯` halving `N^{τ/2} ≥ 1+√2` (`qtLift_core_below` :359-400) | any `τ > 0` of `≺` | `N^τ - 2N^{τ/2} - 1 ≥ 0`, eventually in `n` | eventually only; `τ`-dependent threshold is not a hypothesis |
| 10 | `𝔠_d` (pinned `∃`, before `(𝔠, sz, z)`) | inherited from `stOeqQtRoundPTgL''_of`: `min(.., 1/(2d)) ≤ 1/6`, `≤ 1/100` by `STIngRgL` | the lift (3) and bootstrap (2) keep the pin's `𝔠_d` (as `stXiBootR_of_round` :581) | no new constraint; `d 𝔠_d ≤ 1/2` is T2498's |
| 11 | `∃`-order | `C5` (D1) n/a row a; `cH`: after `(κ, ε, 𝔡)`; `τT`, `κm`: per `(sz, z)` inside the proof, never pinned | no `∃` after `(sz, z)` is introduced by row a | `c`, `r`, `m` are built inside the proof from `(cH, τT, κm, n_)` |

Hypothesis bundle fixed for `T2505_XiBootROfRound` (the check's `Hyp d law Flow mkM T0`, "fixed at row a's 1a"; shape of `IterationsGen2_Fam`, `Chain/IterationsGen2:373`): (H1) `Step2EventsGen_Flow d Flow T0` (admissible, `T0 < 1`); (H2) `∀ sz, IsProbabilityMeasure (law sz)`; guarded by `0 < κ` and `Flow sz κ ε 𝔠 𝔡 z`: (H3) `∃ E, StepDecompGen_LoopForm (mkM sz z) E` and `∀ n, ‖(mkM sz z).m n‖ ≤ 1`, (H4) `∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm`, (H5) `∃ τ > 0, RangeCond τ (T0 sz z)` (also `0 < ε`); (H6) `T2505_FlowModFam d law Flow mkM`, read only for its first, third and fourth conjuncts (`lemDecCalELipG_flowMod_base`): a model matrix `Hm` with `LM n u (Hm n u ω) = L n u ω` that is Hermitian on a high-probability event, which is what `STXiLKMg_crudeNg` needs (no other Hermitian source in the check's `Hyp`, which has no `Hf`). Hence ticket table row 16 (`hFM`) is read by targets 2 and 4 as well as 3, 12. `STKboundgL` is the pin's own premise (`stKbound_timeIccgL`, `KDecayGen:92`). All guarded, no pinned `∃` after `(sz, z)`.

### (ii) One concrete nondegenerate instance

Band data of `QtXiRoundLiftInst` (`Induction/QtXiRoundLift:748`) and `SizesInst` (`Defs/Sizes:257`): `d=3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3` (`n=0`: `L=4, W=32, lam=1/64, N=2^21`), `z_n = 1/2 + i N_n^{-4/5}`, `s ≡ 0`, `t ≡ 1/16`, `T0 ≡ lemT z_n`, regime `STCaseI`, `n_=2, p=1`, `XL ≡ XLK ≡ 1`, `cH = 1`, `τT = 1/2`, `κm = √(κ/2)/2`. Hypotheses checked by the script: `Admissible` (`Bandwidth`, `WO`), `locDomain`, `t ≤ lemT z_n`, `STCaseI`, `RangeCond τT`, `κm ≤ Im m_E`, `η_t⁻¹ ≤ N²`, contraction `B^{1/6} ≤ N^{-c}`, `B ≤ 1`. The mesh arithmetic is evaluated at the smallest admissible `N = 3n_+1`.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505/inst2.py` (script in the scratchpad, 20 lines; exact expressions: `c1=min(2dd*cc,tau)`, `c=c1/12`, `B=max_{u in {0,t}} W^-d((lam^2+1-u)^-1+(L^d(1-u))^-1)`, `lemE = -2 Re m/|m|`, `m_sc` = root of `m²+zm+1=0` with `Im m>0`).

```
c1=0.03333 c=0.002778 rounds=1801  mesh m=6n_+18+2cH=32  thr(N)=max(2^60,7,82.0)
n= 0 N=2.097e+06 log2N= 21.0 E=0.5000 lemT=0.999991 B^(1/6)=0.179 N^-c=0.960 all=True thr_ok=False
n= 1 N=5.498e+11 log2N= 39.0 E=0.5000 lemT=1.000000 B^(1/6)=0.032 N^-c=0.928 all=True thr_ok=False
n= 3 N=1.441e+17 log2N= 57.0 E=0.5000 lemT=1.000000 B^(1/6)=0.006 N^-c=0.896 all=True thr_ok=False
n= 4 N=8.000e+18 log2N= 62.8 E=0.5000 lemT=1.000000 B^(1/6)=0.003 N^-c=0.886 all=True thr_ok=True
n= 5 N=2.130e+20 log2N= 67.5 E=0.5000 lemT=1.000000 B^(1/6)=0.002 N^-c=0.878 all=True thr_ok=True
n=50 N=1.143e+37 log2N=123.1 E=0.5000 lemT=1.000000 B^(1/6)=0.000 N^-c=0.789 all=True thr_ok=True
mesh n_=2 cH=0 m=30: value at N=3n_+1: 0.0175 (=3n_N^-3+N^-(3n_+16+2cH)=0.0175) <=1
mesh n_=2 cH=1 m=32: value at N=3n_+1: 0.0175 (=3n_N^-3+N^-(3n_+16+2cH)=0.0175) <=1
mesh n_=2 cH=3.5 m=37: value at N=3n_+1: 0.0175 (=3n_N^-3+N^-(3n_+16+2cH)=0.0175) <=1
mesh n_=6 cH=1 m=56: value at N=3n_+1: 0.0026 (=3n_N^-3+N^-(3n_+16+2cH)=0.0026) <=1
```

Reading: `all=True` is every deterministic hypothesis above at `n_=2`, `d=3`, nonempty index sets (`N_0 = 2^21`, `L=4`, `W=32`, `[s,t] = [0, 1/16]`, `|Fin 2 → Bool|·L^{2d}` loops), including `n = 0`. `thr_ok` is only the sufficient proof threshold of row 2 (`N ≥ 2^60`), which no hypothesis of any target uses; it is first met at `n = 4` (`N = 8.0e18`), the "eventually" of every pin. The band's `cH = 1` (`2 N √|u-u'|`, `lemDecCalELipG_seqHflow_entry_sub`) gives `m = 32 = 6n_+20` (the band's `N^{-32}`, `QtXiRoundLift:827`). External hypotheses: none in row a (`KLipFam`, `FlowModFam`, `stOeqQtRoundPTgL''_of`'s premises are merged texts with band discharges; the stochastic premises `STLK`, `STStep2Concl`, the pair controls stay example hypotheses per CLAUDE.md §4 step 2); so no limit computation is owed.

Per target (mathematics): 1 `STXiRoundgL'` is a text (the merged `STXiRoundPTgL''` with `PrecL` for `PrecPTL`); 2 closes by rows 1-5 and the bundle; 3 closes by rows 5-9 (the lift reads (H3)-(H6) and `NQEndFlowGen_KLipFam`); 4 = 2 ∘ 3 ∘ `stOeqQtRoundPTgL''_of` (same `𝔠_d`, row 10); 5 instances at `d = 3` as above. No hypothesis set is empty, no exponent fails to close, no statement is false.

Verdict: target 1 PASS; target 2 PASS; target 3 PASS; target 4 PASS; target 5 PASS. Overall PASS. The pinned `T2505_*` texts and the stop rules do not move (`Hyp` is the text the check leaves to this 1a; the generic contraction uses `τT` from `hT0` in place of the band's `ε/2`, inside the proof only). No 1a-audit needed.

### (a′) Preflight corrections — 2026-10-14 10:03:38 UTC
One change to (a); no verdict changes (the exponent table (i) and the instance (ii) stand; the mesh is `6n_+18+2c` and the contraction level `min(2𝔡𝔠, τT)/12`, as in (a)).
- (H2) is guarded in the 1b form: `∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → IsProbabilityMeasure (law sz)`, weaker than the unguarded text of (a).  Target 4 derives it from the premises `hW` (`.2.1`,
  `isProbabilityMeasure_pathP`) and `hLaw` (`NQEndFlowGen_isProb`) at a flow, so no premise beyond the ticket's table rows is added.  `QtBootGen_Hyp` (`QtBootGen.lean:91`) is the bundle.
- Not in (a): `Chain/Step6KitGen` is imported for `st6_prec_det_iffg`; no `BA/*` or `Chain/Step2Kern` import.

## (b) Script output — 2026-10-14 10:03:38 UTC
### Build
$ lake build RBM3D.Chain.QtBootGen RBM3D.Chain.QtXiRoundLiftGen   (worktree ../RBM3D-wt/T2505, branch t/T2505, HEAD 2a7ddae2)
Build completed successfully (3949 jobs).
$ lake build   (whole library, runs #assert_rbm_axioms)
info: RBM3D.lean:622:0: axiom audit: 15231 theorems, 4702 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STXiRoundgL': 7 [no certificate]
Build completed successfully (4392 jobs).
$ lake env lean docs/tickets/checks/T2505-check.lean   -> exit 0, 712 output lines, 0 lines containing "error"
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^ *axiom ' <the two files>   -> no output
### `#print axioms` of every target and new public declaration (scratch file outside the repo, verbatim)
'RBM.BA.STXiRoundgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STXiRound'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stBoot_roundsg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stXiBootgL'_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stXiBootRgL'_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.qtBootGen_flowModFam_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.qtBootGen_hyp_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stXiRoundgL'_of_PTfam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stXiRoundQtgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQtgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtXiRoundLiftGenCheck.stXiRoundQtgL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQt'_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtXiRoundLiftGenCheck.stXiRoundQt_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
### Target statements extracted by script (full text for 1 and the family theorem of 2; digests for the long ones: the text is at the cited line)
--- QtBootGen.lean:55  STXiRoundgL'
def STXiRoundgL' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
--- QtBootGen.lean:114  stBoot_roundsg
theorem stBoot_roundsg (sz : Sizes d) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto) {U : ℕ → Type} (π : ∀ n, U n → ℝ)
   premises (5): hsz hc hR h0 hround
   conclusion: PrecL sz μ (U := U) ξ (fun n q _ => R n (π n q)) := by
--- QtBootGen.lean:346  stXiBootgL'_of_round
theorem stXiBootgL'_of_round {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
   premises (11): hL hm hspec hA hFM hK hs hst ht1 hrange hround
   conclusion: STXiBootgL' Cm.toFlowFM μ s t := by
--- QtBootGen.lean:409  stXiBootRgL'_of_round
theorem stXiBootRgL'_of_round (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hH : QtBootGen_Hyp d law Flow mkM T0)
    (h : STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t)) :
    STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) := by
--- QtXiRoundLiftGen.lean:364  stXiRoundgL'_of_PTfam
theorem stXiRoundgL'_of_PTfam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
   premises (8): hFlow hSpec hL hm hT0 hKLip hFM hPT
   conclusion: STIngRgL d STCaseI law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t) := by
--- QtXiRoundLiftGen.lean:397  stXiRoundQtgL_of
theorem stXiRoundQtgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
   premises (27): hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hKerFam hR1 hT0 hEK4 hTh hB45 hKLip hFM
   conclusion: STIngRgL d STCaseI law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t) := by
--- QtXiRoundLiftGen.lean:466  stOeqQtgL'_of
theorem stOeqQtgL'_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
   premises (27): hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hKerFam hR1 hT0 hEK4 hTh hB45 hKLip hFM
   conclusion: STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
--- QtXiRoundLiftGen.lean:649  stOeqQt'_holds_of_gen
theorem stOeqQt'_holds_of_gen (d : ℕ) : STOeqQt' d := by
### Statement diff against the pinned `T2505_*` (scratch file = the check's Part 2 plus these examples; compiles, no error)
textual after renaming: `T2505_XiRoundgL'` vs `STXiRoundgL'`: 0 differing lines; `T2505_FlowModFam` vs `QtBootGen_FlowModFam`: 4 differing lines, all line breaks of the binder list
compiled: `T2505_XiRoundgL' Cf μ s t = STXiRoundgL' Cf μ s t := rfl`;  `T2505_FlowModFam d law Flow mkM = QtBootGen_FlowModFam d law Flow mkM := rfl`
compiled: `example : T2505_XiBootROfRound QtBootGen_Hyp := fun d R law Flow mkM T0 hH h => stXiBootRgL'_of_round d R law Flow mkM T0 hH h`   (target 2)
compiled: `STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 = STIngRgL d STCaseI … (fun sz z s t => STXiBootgL' …) := rfl`   (target 4 concludes the merged `STOeqQtgL'`)
### Compiled nonempty instances (`d = 3`, band data `sz0, z0, sInst ≡ 0, tInst ≡ 1/16`, `C_d = 1`; `example` lines by script with the docstring head)
QtBootGen:478 **Target 2, the abstract bootstrap `stBoot_roundsg` at the data**: `d = 3`, 
QtBootGen:496 **Target 2, `stXiBootgL'_of_round` at the data** (one carrier `bandStep2Mat 
QtBootGen:509 **Target 2, `stXiBootRgL'_of_round` at the band family** (`d = 3`, `R = STCa
QtBootGen:519 **Target 2, the family theorem at the data, conclusion applied**: from the r
QtBootGen:540 **Target 1, the text at the band** (`bandFM_STIngR`): the band round pin is 
QtXiRoundLiftGen:678 **Target 4 at the data, the case-(i) round**: `stXiRoundQtgL_band3` evaluate
QtXiRoundLiftGen:698 **Target 4 at the data, `stOeqQtgL'_of`** (`stOeqQtgL'_band3`, i.e. `stOeqQt
QtXiRoundLiftGen:716 **Target 2 at the band family, round pin discharged**: `stXiBootRgL'_of_roun
QtXiRoundLiftGen:723 **Target 2 at the data, `stXiBootgL'_of_round` with the round discharged**: 
QtXiRoundLiftGen:742 **Target 5, the band corollary at the data**: the band pin `STOeqQt' 3` (`st
QtXiRoundLiftGen:746 (band corollary, `inst_ing`)
QtXiRoundLiftGen:752 **Target 3, `stXiRoundgL'_of_PTfam` at the band family** (`d = 3`): the per-
QtXiRoundLiftGen:766 **Target 3 at the data**: the lift `QtLiftGen_lift` applied at the carrier `
QtXiRoundLiftGen:778 **Target 3 at numbers, the mesh arithmetic** (`QtLiftGen_arith` at `N = 7 =
kept as hypotheses of the examples: the stochastic pins `STLKgL s`, `STStep2ConclgL` (premises of `STIngRgL`), the pair controls `Ξ̂ ≺ 1`; the round pin in the `QtBootGen` examples (it is proved in the second file:
discharged at `QtXiRoundLiftGen:716, 723`); the per-time pin in the carrier-level lift example (`QtXiRoundLiftGen:766`; the family-level instance of target 3 has it discharged).  Every deterministic hypothesis is discharged.
### Name clash, hypothesis rules, layering, diff-stat
git grep -F <name> in RBM3D, docs/tickets (this branch, other files) and on main (089052ca): 20 patterns checked, nonzero: none
X1-C4 `(def|abbrev|structure) <pinned names>` in the two files: 0.  TN-C4 `STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds`: 0.  `^import RBM3D.(BA|Chain.Step2Kern)`: 0.  New `def`s (U-C4): `STXiRoundgL'`, `QtBootGen_FlowModFam`, `QtBootGen_Hyp`.
imports: QtBootGen ← QtNonzeroBoot, LemDecCalELip, NQEndFlowGen, NQGood1Gen, KDecayGen, Step6KitGen;  QtXiRoundLiftGen ← QtBootGen, QEndB1Gen, QtXiRoundLift;  importers: each other and `RBM3D.lean` (2 lines after `QEndB1Gen`).
U5S-C3 `grep -cE "∀ \(sz : Sizes d\)"`: 9 (QtBootGen) + 56 (QtXiRoundLiftGen) hits, all in the premise lists of `QtBootGen_FlowModFam`, `QtBootGen_Hyp`, `stXiBootRgL'_of_round`, `stXiRoundgL'_of_PTfam`, `stXiRoundQtgL_of`, `stOeqQtgL'_of` (rows in (v)); no `∀ n` drift or hierarchy premise; the pinned `∃ c` (row 16) is after `(κ, ε, 𝔡)`.
C1 / X1-C1 regex (ticket list) over the declaration statements (`stmts.py`; private lemmas and examples skipped; the `Lloop` hits are `KLloopOf` in `hKK`, copied from `stOeqQtRoundPTgL''_of`, excepted; the `seqP` hit of `bandFM_STXiRound'` is the band bridge):
== QtBootGen.lean
  55 def       STXiRoundgL'                       [generic] hits=0
  73 theorem   bandFM_STXiRound'                  [generic] hits=['seqP']
  83 def       QtBootGen_FlowModFam               [generic] hits=0
  91 def       QtBootGen_Hyp                      [generic] hits=0
 114 theorem   stBoot_roundsg                     [generic] hits=0
 346 theorem   stXiBootgL'_of_round               [generic] hits=0
 409 theorem   stXiBootRgL'_of_round              [generic] hits=0
     band/inst declarations: 2, hits ['STFlow', 'STflowE', 'lemT', 'seqP']
== QtXiRoundLiftGen.lean
 364 theorem   stXiRoundgL'_of_PTfam              [generic] hits=0
 397 theorem   stXiRoundQtgL_of                   [generic] hits=['Lloop']
 466 theorem   stOeqQtgL'_of                      [generic] hits=['Lloop']
     band/inst declarations: 6, hits ['STFlow', 'STflowE', 'lemT', 'seqP']
$ git diff main...t/T2505 --stat   (main = 089052ca, merge-base d3104f3b):  RBM3D.lean | 2 +;  RBM3D/Chain/QtBootGen.lean | 551 +;  RBM3D/Chain/QtXiRoundLiftGen.lean | 788 +;  RBM3D/Test/Axioms.lean | 1 +
$ git diff main...t/T2505 --stat -- RBM3D/Induction RBM3D/BA RBM3D/Graph | wc -l   -> 0;  no merged `RBM3D/Chain` file is touched (name-status: M RBM3D.lean, A the two Chain files, M Test/Axioms.lean)
RBM1D/RBM2D diff-stat: n/a, no port from RBM1D/RBM2D (every copy is from an RBM3D band file at d3104f3b, listed in (ix))
### `wc -l` per file against the census (`count.py`: wc = lines; decl = non-blank non-comment lines; band rows = the same script on the band source ranges)
band QtNonzeroBoot §1-§4 (1-590) wc=590 nonblank=547 decl(no comments)=441
band QtXiRoundLift non-instance (1-737) wc=737 nonblank=685 decl(no comments)=577
QtBootGen §1-§4 (1-429) wc=429 nonblank=392 decl(no comments)=332
QtBootGen all wc=551 nonblank=494 decl(no comments)=413
QtXiRoundLiftGen §1-§4 (1-536) wc=536 nonblank=500 decl(no comments)=436
QtXiRoundLiftGen §1-§5 (1-653) wc=653 nonblank=605 decl(no comments)=528
QtXiRoundLiftGen all wc=788 nonblank=721 decl(no comments)=620
ticket census (non-instance declaration lines, `new files ×1.24; ×1.06`): QtBootGen 348; 369, QtXiRoundLiftGen 292; 309, row ≈ 640 / 680 (hi 1,160).  `wc -l`: QtBootGen 551, QtXiRoundLiftGen 788, row 1,339 (both `< 2,000`).
measured/band (same script): QtBootGen §1-§4 332/441 = 0.75 (decl), 429/590 = 0.73 (wc); QtXiRoundLiftGen §1-§4 436/577 = 0.76, 536/737 = 0.73; with the band re-derivation §5: 528/577 = 0.92, 653/737 = 0.89.
### Narrative
Scope: row a only (targets 1-5): two new files, two import lines in `RBM3D.lean`, one registry line in `Test/Axioms.lean`; the six band files, `Step3`, `Step4` are untouched (G1: the `Induction/BA/Graph` diff above is empty).
(iii) hypothesis table (band fact → field → band discharge → BA source), new premises only:
 - row 16 `hFM` = `QtBootGen_FlowModFam`: band `seqHflow` Hermitian with entrywise Hölder-1/2 modulus `2N√|u-u'|` on `contGood` → `LemDecCalELipG_FlowMod` (`LM`, `HighProbAt`, Hermitian + modulus) → `qtBootGen_flowModFam_band` (`c = 1`) → BA `baLemDecCalELipG_flowMod` (`Step5KerBA:390`, T2501, merged; not imported here).
 - row 15 `hKLip` = `NQEndFlowGen_KLipFam` (merged): band `stKloop_lip` → `nqEndFlowGen_kLip_band` → BA: U3-BA (`BAKsol_isKLoopS`, `baKbound_holds`).
 - bundle `QtBootGen_Hyp` (flow facts, guarded law, loop form + `‖m‖ ≤ 1` + `DecayGen_Spec`, `∃ τ` range, row 16) → `qtBootGen_hyp_band` (`Step2EventsGen_bandFlow`, instance `isProbabilityMeasure_seqP`, `stepDecompGen_loopForm_band`, `norm_mE`, `DecayGen_bandSpec`, `v3_premises_of_stFlow` at `ε/2`).
(v) family-premise table as used: `stXiBootRgL'_of_round`: `hH` (= bundle) + the round pin `h`;  `stXiRoundgL'_of_PTfam`: `hFlow hSpec hL hm hT0` + `hKLip` + `hFM` + `hPT : STOeqQtRoundPTgL''`;  `stXiRoundQtgL_of`, `stOeqQtgL'_of`: the 25 premises of
   `stOeqQtRoundPTgL''_of` (rows 1-13, texts unchanged, read under the merged names) + `hKLip` + `hFM`.  All guarded by `0 < κ`, `Flow`; `∃ c` after `(κ, ε, 𝔡)`; no `∀ n` premise; D1 (`C5`) and the probe belong to row b, not here.
(vi) scope table, public band names: converted: `STXiRound'` → `STXiRoundgL'`; `stBoot_rounds` → `stBoot_roundsg`; `stXiBoot'_of_round` → `stXiBootgL'_of_round`; `stXiBootR_of_round` → `stXiBootRgL'_of_round`; `stXiRoundQt_holds` → `stXiRoundQtgL_of`;
   `stOeqQt'_holds` → `stOeqQtgL'_of`; private conversions: `qtBoot_crude` → `QtBootGen_crude(_det)`, `qtLift_lift` → `QtLiftGen_lift` (public at family level: `stXiRoundgL'_of_PTfam`), `qtLift_{sharp_prec,diag_PT,diag_to_pair,arith,xi_close,xiLK_close}` → `QtLiftGen_*`;
   band only: `qtBoot_flowLam`, `qtBoot_prec_sup/of_add_le/sum`, `qtBoot_sharp_*`, `QtNonzeroBoot` §5-§7 (rows b, c); instances: §6 of each file.
(ix) `open private` (model-free band helpers, no copy): `qtBoot_Y qtBoot_c qtBoot_c_pos qtBoot_contraction qtBoot_bootRHS_update qtBoot_bootRHS_one_le` (`QtNonzeroBoot`); `qtLift_sharp_one_le qtLift_sharp_le qtLift_sharp_mono qtLift_zeta_mono qtLift_zeta_le qtLift_zeta_one_le qtLift_core_below`
   (`QtXiRoundLift`); `NQEndFlowGen_prec_of_le_right NQEndFlowGen_isProb` (`NQEndFlowGen`); `nqEnd_rangeCond_mono` (`NQEndLin`); `QtBootGen_flow_abs_le` (`QtBootGen`).  Copies (from RBM3D, at d3104f3b): `stBoot_roundsg` ← `QtNonzeroBoot:136-217`; `QtBootGen_crude_det` ← `:337-444`;
   `stXiBootgL'_of_round` ← `:522-574`; `stXiBootRgL'_of_round` ← `:581-589`; `QtLiftGen_sharp_prec` ← `QtXiRoundLift:94-116`; `_diag_PT`, `_diag_to_pair` ← `:611-633`; `QtLiftGen_arith` ← `:439-485` (`6n_+20`, `N^{2n_+7}` → `6n_+18+2c`, `N^{2n_+6} N^c`);
   `_xi_close`, `_xiLK_close` ← `:491-561`, `:582-606` (the `𝓛` and `𝒦` moduli are premises, no `contGood`); `QtLiftGen_lift` ← `:640-701` (event `G`, `lemDecCalELipG_loops`, `hKLip`).
New in the generic proofs: the crude start `Ξ̂ ≤ N^{2n_+1}` holds on the high-probability Hermitian event `G` of `LemDecCalELipG_FlowMod` (the band matrix is Hermitian everywhere), the failure set lies in `(G n)ᶜ` (`QtBootGen_crude`); the contraction
uses the range exponent `τ` of `hT0` in place of `ε/2` (`qtBoot_contraction` at `ε := 2τ`, level `c = min(2𝔡𝔠, τ)/12`).  UBA-C1 as used: R1 (`lam² ≤ Aof κ gK²`) never enters row a's own proofs; `hR1`, `Aof`, `gK` are passed to `stOeqQtRoundPTgL''_of` only.
Registry (7): `Test/Axioms.lean:217` adds `RBM.BA.STXiRoundgL'` to `owedProps` (the scan line above: `7 [no certificate]`); the lines `:121`, `:214` are row c's.  No other premise is flagged by the final scan.

## (c) Verified Mathlib names used (each `#check`ed at Mathlib v4.34.0 in a scratch file importing `RBM3D.Chain.QtBootGen`; none absent)
`Real.one_le_rpow`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `inv_anti₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`,
`pow_le_one₀`, `le_self_pow₀`, `div_le_iff₀`, `div_le_one`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`, `Finset.sup'_le`, `Finset.le_sup'`, `exists_lt_of_csInf_lt`, `one_le_mul_of_one_le_of_one_le`, `mul_inv_cancel_left₀`, `Nat.le_ceil`.

## (d) Open issues and paper-delta candidates
- Layering of target 3 (design choice for the dispatcher): the carrier-level lift is private (`QtLiftGen_lift`) and target 3 is public at the family level (`stXiRoundgL'_of_PTfam`, premise `STOeqQtRoundPTgL''`).  With a public carrier-level lift
  (premise `STXiRoundPTgL''`) the first full build failed with the unregistered premises `[RBM.BA.QtBootGen_FlowModFam, RBM.BA.STXiRoundPTgL'']`; the final shape (plus `qtBootGen_flowModFam_band`) fails only on `[RBM.BA.STXiRoundgL']`, the line the ticket expects, now registered.
- Row c (`t/T2505c`) edits `Test/Axioms.lean:121, 214`; this row's line is `:217`; with T2502 row c and T2506 row b the file is a union of lines at merge, `RBM3D.lean` a union of import lines (after the last `import`).
- Calibration for 0843 (2): row sum `wc -l` 1,339 against the ticket's hi 1,160 (non-instance decl lines 332 + 436 = 768 against 640 / 680; the second file contains two 27-premise statements, the family-level lift, two band calls and the instances).  No stop rule fired (files 551, 788 `< 2,000`).
- Paper-delta candidates: `T2505a` the generic bootstrap's crude start holds on the high-probability Hermitian event `G` (band: every sample) and its contraction level is `min(2𝔡𝔠, τ)` with `τ` the range exponent of `T0` (band `ε/2`); it reads `STKboundgL` (`stKbound_timeIccgL`).
  `T2505b` the net mesh is `N^{-(6n_+18+2c)}` with the pinned Hölder exponent `c` of `𝓛` (`∃ c` after `(κ, ε, 𝔡)`, band `c = 1`, `6n_+20`); `T2505c` the guarded probability premise of the bundle (a′); `T2505d` the carrier-level lift of `QtXiRoundLift` is private in both, public here only at the family level.
