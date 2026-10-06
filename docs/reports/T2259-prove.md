Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 05:59:54 UTC 2026

(Worktree `t/T2259` is at `7672749`; the files the ticket cites are unchanged there: `git log -1 --format=%h -- RBM3D/Induction/IterationsA.lean` = `6583ca2`, `.../NQEndFlow.lean` = `0f60da2`. Only `Test/Axioms.lean` lines moved: `STIterations`/`STIterationsII` superseded lines are `:406-407` (ticket: `:403-404`); owed lines `:121 :125 :128 :129 :130` are as in the ticket.)

### (i) Exponent table (no new inequality; every row is closed by a merged lemma)

| Quantity | Value | Constraint (source) | Slack |
|---|---|---|---|
| `d` | `3 ≤ d` (pin) | `iterationsA_scale_I` needs `2 ≤ d`; `stKbound_timeIcc` needs `3 ≤ d` | `0` (for `stKbound_timeIcc`), `1` (scale_I) |
| `𝔠d` | `1/100` | `0 < 𝔠d`; `≤ 1/100` (pin `STIterR′`); `≤ 1/16` (`iterationsA_scale_I` `hc`); `≤ 1/24` (`iterationsA_scale_II` `hc`) | `0`; `21/400`; `19/600` |
| `κ′` for `stKbound_timeIcc` | `κ/2` | `0 < κ′`; `\|E n\| ≤ 2 − κ′`, from `v3_premises_of_stFlow` `\|E n\| < 2 − κ/2` | strict, `κ/2 > 0` |
| `gmax` | `𝔡⁻¹` | `0 < gmax`; `lam n ≤ gmax` from `WO 𝔡` (`hA.2.2.2.2`) | strict |
| `\|E n\| < 2` (`hE`) | from `< 2 − κ/2` | `iterationsA_scale_I/II`, `iterationsA_apriori_of_lRB1` | `κ/2` |
| `t n < 1` | from `t ≤ lemT z`, `lemT_lt_one` (via `v3_premises_of_stFlow`) | all plumbing lemmas | strict |
| `N, k, p` | `2 ≤ N`, `1 ≤ k`, `p = N+4` | `STXiBoot′ n_ p`: `2 ≤ n_`, `1 ≤ p`; `iterationsA_boot_bound` `2 ≤ p` | `p − 2 ≥ N+2 ≥ 4` |
| `Bu` (changed slot) | `sz.Bctl n (s n)` | only hypothesis on `Bu`: `(cv·A n)⁻¹ ≤ Bu` (`hlow`); conclusion `STbootRHS 1 XL XLK Bu N p ≤ C·STPsi` | `hlow` at `w = s ∈ TimeIcc s t n`: case (i) `0.5/W³ ≤ 1.0139/W³` (factor 2.03); case (ii) equality `(1·A)⁻¹ = Bctl(s)`, slack `0` |
| `ρ² ≤ K A^{1/8}`, `T ρ² A^{7/8} ≤ cB K`, `T A^{3/4} ≤ cB`, `(cvA)⁻¹ ≤ Bctl ≤ T` | taken from `IterationsAScale` (merged `scale_I/II`) | unchanged from `iterationsA_step` | see (ii) table of thresholds |

Conclusion of (i): `𝔠d := 1/100` satisfies all four bounds; the pin's own `STKbound` hypothesis is not needed (the uniform `𝒦` bound is rebuilt from `stKbound_timeIcc`), allowed since a hypothesis may stay unused.

**Preflight check (i), privacy closure** (command: `python3 closure2.py` over `IterationsA.lean:876-1046, 1072-1276, 1283-1340`; it tokenises the three ranges, resolves every `iterationsA_*`, `IterationsAScale`, `st_*`, `ST*`, `etaT`, `Bparam`, `Sizes.*`, `StochDomAt.*` token to a declaration line in `RBM3D/**`; verbatim summary):
```
StochDomAt.* tokens: ['StochDomAt.mul', 'StochDomAt.trans']
   StochDomAt.mul RBM3D/Defs/StochDomAt.lean:439 public
   StochDomAt.trans RBM3D/Defs/StochDomAt.lean:411 public
public: IterationsAScale :1058; iterationsA_STPsi_anti_k :510, _STPsi_nonneg :494, _one_le_STPsi :497, _boot_bound :630,
  _prec_absorb :834, _prec_mono_left :826, _prec_mono_right :818, _prec_one_add_mul :865, _prec_rpow :850, _xiL_odd_le :740,
  st_one_le_XiL :151, st_one_le_XiLK :160 (all IterationsA.lean); STIterHyp :469, STPair :48, STPsi :76, STXiBoot :414,
  STXiL :63, STXiLK :68, STlenL :391, st_Bctl_pos :680 (Step34Pins.lean); Bparam Params.lean:36; etaT GLoop.lean:75; Sizes.Bctl Sizes.lean:214
private, all declared INSIDE the copied ranges: iterationsA_Bctl_nonneg :881, _XL :1077, _XLK :1081, _XLKv :903, _XLKv_ge_one :1001,
  _XLKv_le :1006, _XLv :895, _XLv_four_p :996, _XLv_ge_one :906, _XLv_le :947, _XLv_le_Z :1014, _XLv_le_chain :962, _XLv_le_pred :928,
  _obl_K :1256, _obl_chain :1180, _obl_four_p :1241, _obl_short :1092, _one_le_ratio :876, _prec_XL_of :1029,
  _prec_chain_abs :1143, _rho :1073, _rho_eq :1087, _rho_ge_one :1084, _sqrt_prod_le :1168
private identifiers declared outside the copied blocks: 0
```
Line count `sed -n '876,1046p;1072,1276p' IterationsA.lean | wc -l` = `376`. No `set_option`/`maxHeartbeats` in the ranges; no `RBM.Ind.*` token in them (the `RBM.Ind` privates `iterationsA_sum_*`, `_STn12_bounds'`, `_rho_le_sq` are used only by `iterationsA_boot_bound`, which is public). The copy needs the header of `IterationsA` (`noncomputable section`, `open MeasureTheory ProbabilityTheory Filter Matrix`, `open RBM RBM.Loop RBM.Path RBM.Gauss`, `variable {d : ℕ} (sz : Sizes d)`, `set_option linter.style.longLine false`). Verdict (i): **PASS**.

**Preflight check (ii), the changed slot.** `sed -n 630,643p IterationsA.lean | grep -n Bu` (verbatim):
```
3:    ∃ C : ℝ, 0 < C ∧ ∀ (A ρ T Bu : ℝ) (p : ℕ) (XL XLK : ℕ → ℝ), 2 ≤ p → 1 ≤ A → 1 ≤ ρ →
5:      T * ρ ^ 2 * A ^ (7 / 8 : ℝ) ≤ cB * K → (cv * A)⁻¹ ≤ Bu →
12:      STbootRHS 1 XL XLK Bu N p ≤ C * STPsi A ρ N k := by
```
So `Bu` occurs in the binder, in `hBu`, and in the conclusion only. In `iterationsA_step` (`:1316-1336`) `hlow := (hBn ⟨q.1.2, q.2.1.trans q.2.2.1, q.2.2.2⟩).1` and `hb := hC … (sz.Bctl n q.1.2) …`. New: `hlow := (hBn ⟨s n, le_rfl, q.2.1.trans (q.2.2.1.trans q.2.2.2)⟩).1`, type `(cv * A n)⁻¹ ≤ sz.Bctl n ((⟨s n,_⟩ : TimeIcc s t n) : ℝ)`, defeq to `… (s n)`; `STPair` fields: `q.2.1 : s n ≤ q.1.1`, `q.2.2.1 : q.1.1 ≤ q.1.2`, `q.2.2.2 : q.1.2 ≤ t n`. `hBn : ∀ w : TimeIcc s t n, (cv * A n)⁻¹ ≤ sz.Bctl n w ∧ …` (`IterationsAScale.Bctl`, `:1070`). The conclusion of `hbootN` under `STXiBoot′` is `STbootRHS 1 … (sz.Bctl n (s n)) n_ p`, matching `hb` at `Bu = sz.Bctl n (s n)`. Verdict (ii): **PASS** (hypothesis `hlow` only changes; the upper bound `Bctl ≤ T` is not used by `hC`).

**Preflight check (iii), binder fit.** `diff <(sed -n 414,422p Step34Pins.lean | sed "s/STXiBoot /STXiBoot' /") <(sed -n 95,104p NQEndFlow.lean)`:
```
9c9,10
<       (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)
---
>       (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
```
(the second `10` is a trailing blank line of my range): one hunk, exactly `Bctl n q.1.2 ↦ Bctl n (s n)`. Token diff of `T2259_iterationsB_step` (check file `:127`) against `IterationsA.lean:1283-1294` (python `difflib`, binder names and `(…)`↔`→` stripped) printed only the binder-to-arrow punctuation opcodes and the single content change `['STXiBoot'] -> ["STXiBoot'"]`. Verdict (iii): **PASS**.

**Preflight check (iv), setting fit** (read in the worktree):
- `Admissible 𝔠 𝔡 := 0 < 𝔠 ∧ 0 < 𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡` (`Sizes.lean:177`): `hA.2.2.1 : SizeTendsto`, `hA.2.2.2.2 : WO 𝔡`, `hA.2.1 : 0 < 𝔡`. `STFlow … := Admissible ∧ ∀ n, locDomain …` (`Defs.lean:286`).
- `RBM.Green.v3_premises_of_stFlow` (`Green/Pins.lean:1049`, namespace `RBM.Green`, `sz` explicit via `variable (sz)` at `:717`): `Admissible ∧ (∀ n, |STflowE z n| < 2 − κ/2) ∧ (∀ n, t n < 1) ∧ RangeCond`; destructuring `⟨hA, hE', ht1, -⟩` fits. `tendsto_size sz : SizeTendsto → Tendsto sz.size atTop atTop` (`StochDomAt.lean:735`).
- `STStep2Concl := STLocalEntryU ∧ STAvgU ∧ STGdecayW` (`Step34Pins.lean:221`): `hStep2.2.1 : STAvgU` is the argument of `iterationsA_avg_of_STAvgU`. `iterationsA_apriori_of_lRB1` takes `STStep1Loop`, `hE : ∀ n, |E n| < 2`.
- `stKbound_timeIcc (hd : 3 ≤ d) (hκ) (hg) (hN : SizeTendsto) (hE : ∀ᶠ n, |E n| ≤ 2 − κ) (hlam : ∀ᶠ n, 0 < lam n ∧ lam n ≤ gmax) (hs0) (hst) (ht1) : ∀ k, 1 ≤ k → sz.Prec (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (‖STKloop … (p.1 : ℝ) p.2.1 p.2.2‖) (Bctl n (p.1:ℝ) ^ (k−1))` (`KDecay.lean:1062`). `×` is right-associative, so `TimeIcc × (A × B)`, the shape of `precomp_param` with `φ n (q, p) = (⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩, p)` (`StochDomAt.lean:335`), landing on `iterationsA_rela_of_K`'s `STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))` with `p.1.1.1 = q.1.1` by `Subtype.val`/`mk` defeq. `hlam` is `KLFinal_flowLam` (`KLFinal.lean:294-298`, private, 4 lines) with `gmax = 𝔡⁻¹`, rebuilt from `hA.2.2.2.2` and `sz.W_pos`.
- Regime hypotheses: case (i) `STIterations′` has `R = STRegIterI`, matching `hreg : STRegIterI sz s t` of `iterationsA_scale_I` (`:1631`); `Aof sz s = fun n => STAI sz n` and `T = 2·(STAI)⁻¹`, `cB = cv = K = 2`. Case (ii) `A = STAII s`, `T = A^{−1+𝔠d}`, `1 1 1` (`:1704`); `STCaseII` is not consumed, as merged.
Verdict (iv): **PASS**.

**Preflight (v), consumer fit (note only).** `STIngR` (`Step34Pins.lean:445`) and `STIterR′` (`NQEndFlow.lean:134`) have the same prefix `3 ≤ d → ∀ κ ε 𝔡, … ∀ Cd, ∃ 𝔠d ∈ (0, 1/100], ∀ 𝔠 sz z, …`; `STStep3R` (`:250`) has it too. S3-25 must therefore take `𝔠d ≤ min` of its sources' `𝔠d`; `stIterations′_holds` supplies `𝔠d = 1/100` (the maximum the pin allows), so it imposes no restriction. No action in T2259.

**Preflight (vi), registry plan.** Owed lines to delete: `STIterations'` `:129`, `STIterationsII'` `:130`; comments to change: `STIterR'` `:128`, `STXiBoot'` `:125`. `grep` on the worktree for the new names `iterationsB`, `IterationsB`, `stIterations'_holds`, `stIterationsII'_holds`, `IterationsBInst`, `inst_iterations'`, `inst_iterationsII'` in `RBM3D/` and `RBM3D.lean`: 0 hits each. `git diff --name-only main...HEAD | wc -l` = 0.

### (ii) One concrete nondegenerate instance

Data (as the merged `inst_iterations`, `Step34Pins.lean:1025`): `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `szB` (`L = 4`, `W_n = n+4`, `lam = 1`, `N_n = (4(n+4))³`), `z_n = 1/2 + i/64`, `Cd` any `> 0`, `𝔠d = 1/100`. Case (i) `(s,t) = (7/8, 15/16)`, case (ii) `(15/16, 31/32)`. Step data: `(N,k) = (3,2)` (see note). Command: `python3 inst.py` (floats; `msc` = root of `m² + z m + 1 = 0` with `Im > 0`, `lemE = −2 Re m/|m|`, `lemT = |m|²`, `Bctl = W⁻³ Bparam(3, 4, 1, w, 0)`, `Bparam = (g²+|1−t|)⁻¹ + (L^d|1−t|)⁻¹` at `K = 0`); output verbatim:
```
zB= (0.5+0.015625j)  lemE=0.499984 lemT=0.983992
|E|<2-kappa/2=1.95: True   31/32=0.968750<=lemT: True
3<=d: True ; 2<=d: True
cd=1/100 vs pin 1/100, scale_I 1/16, scale_II 1/24: True True True
Admissible(1/6,1/10)+locDomain at n=0,10,10**6: (True, True, True) (True, True, True) (True, True, True)
case i
  n=0 {'rho>=1,rho^2<=K A^(1/8)': False, 'T rho^2 A^(7/8)<=cB K': False}
  n=10 all scale facts hold
  n=1000 all scale facts hold
  n=10000 all scale facts hold
  last failing n (scale facts, scan n<2e4): 2
  con_st_ind (c_d=1/100) first holds at W ~ 1.147e+10 (n ~ 1.147e+10)
case ii
  n=0 {'rho>=1,rho^2<=K A^(1/8)': False, 'T rho^2 A^(7/8)<=cB K': False, '(cv A)^-1<=Bctl(w)<=T, w in [s,t]': False}
  n=10 {'rho>=1,rho^2<=K A^(1/8)': False, 'T rho^2 A^(7/8)<=cB K': False, '(cv A)^-1<=Bctl(w)<=T, w in [s,t]': False}
  n=1000 {'(cv A)^-1<=Bctl(w)<=T, w in [s,t]': False}
  n=10000 all scale facts hold
  last failing n (scale facts, scan n<2e4): 1162
  con_st_ind (c_d=1/100) first holds at W ~ 1.230e+10 (n ~ 1.230e+10)
step: N=3>=2, k=2>=1, p=N+4=7>=2; IH1 range r in [2,N-1]=[2]; IH2 r in [2,N+2]=[2, 3, 4, 5] (k-1=1)
ticket (N,k)=(2,1): IH1 range r in [2,N-1]= []  (empty)
```
Hypotheses checked: `s < t ≤ lemT z_n < 1` (`15/16 ≤ 31/32 ≤ lemT = 0.98399`), `|lemE| = 0.49998 < 1.95`, regimes (`STRegIterI`: `1−s = 1/8 ≤ lam² = 1`, `lam²/L² = 1/16 ≤ 1−t = 1/16`; `STCaseII`: `1−s = 1/16 ≤ 1/16`), all scale facts of `IterationsAScale` incl. `hlow` at `w = s` (rows `(cvA)⁻¹ ≤ Bctl(w) ≤ T` over a 21-point grid of `[s,t]`, and `hlow`), and `STConStInd 𝔠d`. Scale facts hold for every scanned `n ≥ 3` (case (i)) resp. `n ≥ 1163` (case (ii)), `n < 2·10⁴`.

Notes (non-blocking):
1. **Size of the `STConStInd (1/100)` threshold.** At the instance data `(Bctl n t)^{1/100} ≤ (1−t)/(1−s) = 1/2` holds first at `W ≈ 1.2·10¹⁰`. This is the eventual-in-`n` hypothesis of the pin itself (`𝔠d ≤ 1/100` is forced by the pin; a larger `𝔠d` only helps, so `1/100` is the best choice), discharged in Lean for every `𝔠d > 0` by the merged `conStInd_const` (`Step34Pins.lean:825`, `Bctl_tendsto_const`) with no explicit `n`, exactly as in merged `inst_iterations`/`inst_iterationsII` (`:1025-1038`). Every Lean hypothesis is a sequence-level `∀ᶠ`, so no witness `n₀` enters any compiled statement; the instance is not vacuous (the scale facts above hold already for `n ≥ 3` resp. `n ≥ 1163`).
2. **Ticket instance (3), `(N,k) = (2,1)`:** `IH1` quantifies `r` with `2 ≤ r ∧ r+1 ≤ N`, empty at `N = 2`. The step is true there, but the hypothesis is vacuous. Recommend `(N,k) = (3,2)` for example (3) (`IH1` at `r = 2`, level `k = 2`; `IH2` at `r = 2..5`, level `1`); the stochastic `STIterHyp` premises stay hypotheses of the example in either case. No change to any pin.
3. **External hypothesis, limit computation (TEAM §8 lesson 14).** The only external-type input is `STXiBoot′` (hypothesis of the pins, discharged by S3-18b/S3-22, not here). Its deterministic content at the instance is `hlow` at `w = s`: `(cv A)⁻¹·W³ = 0.5` (case i), `1.1912` (case ii) against `Bctl(s)·W³ = 1.0139`, `1.1912`, computed by the script `python3 -` printing `i W^3*Bctl(s)=1.0139 W^3*Bctl(t)=1.1912 ; (cvA)^-1*W^3=0.5000 ; T*W^3=2.0000` and `ii W^3*Bctl(s)=1.1912 W^3*Bctl(t)=1.4697 ; (cvA)^-1*W^3=1.1912 ; T*W^3=1.5675` (at `W = 10⁴`); `W³·Bctl(w) = 1/(2−w) + 1/(64(1−w))` exactly (`K = 0`, `d = 3`, `lam = 1`, `L = 4`), which lies in `[1/2, 1.1912]` on `[s,t]`, so `T` and `(cv A)⁻¹` bracket it for large `W` in case (i) and `hlow` is equality in case (ii).

### Verdicts

- Target 1 (copied private block, 376 lines): **PASS** (privacy closure closed, 0 private names outside the blocks).
- Target 2 (`iterationsB_step`): **PASS** (one changed hypothesis type, one changed slot).
- Target 3 (setting facts `iterationsB_flowLam`, `iterationsB_K_pairs`, `iterationsB_setting`): **PASS** (all inputs merged; types fit as in (iv)).
- Target 4 (`stIterations'_holds`, `stIterationsII'_holds`): **PASS** with `𝔠d := 1/100`.
- Target 5 (instances (1)-(5)): **PASS**, with Note 2 (use `(N,k) = (3,2)` in example (3)).

### (b) Script output (written Tue Oct  6 06:13:16 UTC 2026)

**Build** (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2259`, branch `t/T2259`, commit `04e4465 Jun Yin <321276894+JYin80@users.noreply.github.com>`; the output below is Lake's replay of the cached module build, as the module had been built before; the last lines are the `#print axioms` of the five public declarations):
```
$ lake build RBM3D.Induction.IterationsB   # Tue Oct  6 06:11:28 UTC 2026 .. Tue Oct  6 06:11:30 UTC 2026
ℹ [3847/3847] Replayed RBM3D.Induction.IterationsB
info: RBM3D/Induction/IterationsB.lean:755:0: 'RBM.Gauss.Sizes.iterationsB_step' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:756:0: 'RBM.Gauss.Sizes.stIterations'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:757:0: 'RBM.Gauss.Sizes.stIterationsII'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:758:0: 'RBM.Gauss.IterationsBInst.inst_iterations'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:759:0: 'RBM.Gauss.IterationsBInst.inst_iterationsII'' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3847 jobs).
exit 0
$ lake env lean RBM3D/Induction/IterationsB.lean   # real elaboration, no warning, no error
lake env lean RBM3D/Induction/IterationsB.lean  7.62s user 2.71s system 156% cpu 6.588 total
exit 0
```
Full library in the worktree after the registry edit (root `RBM3D.lean` unchanged, so without `import RBM3D.Induction.IterationsB`): `lake build RBM3D` -> `Build completed successfully (4062 jobs).` (three runs: with the final registry, with the baseline registry for the 'before' count below, and again with the final registry). `maxHeartbeats`/`sorry`/`admit`/`native_decide`/`axiom` lines in `RBM3D/Induction/IterationsB.lean`:        0 (default heartbeats everywhere).

**Target statements, extracted from `RBM3D/Induction/IterationsB.lean` by script** (`awk` from the declaration to its first `:= by`; `file-line: text`):
```
454: theorem iterationsB_step (hsize : Tendsto sz.size atTop atTop)
455:     {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K)
456:     (hboot : STXiBoot' sz E s t)
457:     (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
458:       (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
459:     (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
460:     (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
461:       (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)))
462:     {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
463:     (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
464:     (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1)) :
465:     STIterHyp sz E s t A N k := by
570: theorem stIterations'_holds : ∀ d : ℕ, STIterations' d := by
581: theorem stIterationsII'_holds : ∀ d : ℕ, STIterationsII' d := by
606: theorem inst_iterations' (Cd : ℝ) (hCd : 0 < Cd) :
607:     ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
627: theorem inst_iterationsII' (Cd : ℝ) (hCd : 0 < Cd) :
628:     ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
```
(the two instance statements are shown by their first two lines; they are compared with the pinned statements below.)

**Pinned statements against the proved declarations** (statement script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2259/stmt.lean` = `docs/tickets/checks/T2259-check.lean` with `import RBM3D.Induction.IterationsB` and these five lines before `end RBM.Gauss.Sizes.T2259Check`; `lake env lean`, exit 0, no error):
```
example : T2259_iterationsB_step := @RBM.Gauss.Sizes.iterationsB_step
example : T2259_stIterations'_holds := @RBM.Gauss.Sizes.stIterations'_holds
example : T2259_stIterationsII'_holds := @RBM.Gauss.Sizes.stIterationsII'_holds
example : T2259_inst_iterations' := @RBM.Gauss.IterationsBInst.inst_iterations'
example : T2259_inst_iterationsII' := @RBM.Gauss.IterationsBInst.inst_iterationsII'
exit 0
```

**The compiled nonempty instances** (namespace `RBM.Gauss.IterationsBInst`; `grep -n` of their declarations in `RBM3D/Induction/IterationsB.lean`):
```
606:theorem inst_iterations' (Cd : ℝ) (hCd : 0 < Cd) :
627:theorem inst_iterationsII' (Cd : ℝ) (hCd : 0 < Cd) :
648:example (Cd : ℝ) (hCd : 0 < Cd) :
664:private theorem iterationsB_zB_abs_E (n : ℕ) : |STflowE zB n| < 2 := abs_lemE_lt_two (by simp [zB])
667:private theorem iterationsB_szB_scaleII : IterationsAScale szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 
674:private theorem iterationsB_szB_scaleI : IterationsAScale szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 1
684:example (hboot : STXiBoot' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32))
702:example (hboot : STXiBoot' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32))
720:example (hboot : STXiBoot' szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
739:example {d : ℕ} (sz : Sizes d) (hsize : Tendsto sz.size atTop atTop)
```
(1) `inst_iterations'` and (2) `inst_iterationsII'` apply `stIterations'_holds 3` / `stIterationsII'_holds 3` at `szB, zB`, `kappa = eps = d = 1/10`, `c = 1/6`, `(7/8, 15/16)` resp. `(15/16, 31/32)`; discharged: `flow_zB`, `0 <= s < t <= lemT z` (`szB_flow_ht`), the regime (`szB_regIterI`, `szB_caseII`), `(con_st_ind)` (`conStInd_const`); open: the stochastic premises. (5) `:648` discharges `STKbound` of (1) by `stKbound_of_flow`. (3) `:684` case (ii), `(N,k) = (3,2)` (`IH1` at `r = 2`, `IH2` at `r = 2..5`, nonempty: preflight Note 2); `:702` case (ii), ticket data `(N,k) = (2,1)` (`IH1` empty); `:720` case (i), `(3,2)`; `hS` from the public `iterationsA_scale_I/II` at `szB` with `(con_st_ind)` from `conStInd_const`, `|E| < 2` from `abs_lemE_lt_two`. (4) `:739` generic `sz`: `iterationsB_step` with `stXiBoot'_of_stXiBoot` gives the conclusion of `iterationsA_step` under `STXiBoot`.

**The copied block** (`IterationsA.lean in the worktree == 6583ca2`):
```
$ diff <(sed -n '876,1046p;1072,1276p' IterationsA.lean | sed 's/iterationsA_/iterationsB_/g') <(sed -n '67,237p;240,444p' IterationsB.lean) | grep -c '^[0-9]'
22   (hunks; every one is a call of a PUBLIC name, which a blanket rename would break: iterationsA_one_le_STPsi iterationsA_prec_mono_left iterationsA_prec_mono_right iterationsA_prec_one_add_mul iterationsA_prec_rpow iterationsA_STPsi_anti_k iterationsA_STPsi_nonneg iterationsA_xiL_odd_le )
$ same diff with `perl rename.pl` in place of the `sed` (the 24 private names only; list below)
selective-rename diff: IDENTICAL (0 hunks)
```
`rename.pl` renames `iterationsA_<n>` to `iterationsB_<n>` (not followed by `[\w']`) for `<n>` in: Bctl_nonneg, XL, XLK, XLKv, XLKv_ge_one, XLKv_le, XLv, XLv_four_p, XLv_ge_one, XLv_le, XLv_le_Z, XLv_le_chain, XLv_le_pred, obl_K, obl_chain, obl_four_p, obl_short, one_le_ratio, prec_XL_of, prec_chain_abs, rho, rho_eq, rho_ge_one, sqrt_prod_le. Block A = `RBM3D/Induction/IterationsB.lean:67-237` (171 lines), block B = `:240-444` (205 lines), total 376 = the preflight count. No `private` had to be added: every declaration of both blocks is already `private` in the source.

**The step against the merged step** (`diff <(sed -n 1283,1340p IterationsA.lean | perl rename.pl) <(sed -n 454,512p IterationsB.lean)`):
```
1c1
< theorem iterationsA_step (hsize : Tendsto sz.size atTop atTop)
---
> theorem iterationsB_step (hsize : Tendsto sz.size atTop atTop)
3c3
<     (hboot : STXiBoot sz E s t)
---
>     (hboot : STXiBoot' sz E s t)
42,43c42,44
<     have hlow := (hBn ⟨q.1.2, q.2.1.trans q.2.2.1, q.2.2.2⟩).1
<     have hb := hC (A n) (iterationsB_rho E s n q.1.2) (T n) (sz.Bctl n q.1.2) (N + 4)
---
>     -- R2*: the lower bound of `IterationsAScale.Bctl` at `w = s ∈ [s,t]` (`s ≤ v ≤ u ≤ t` on a pair)
>     have hlow := (hBn ⟨s n, le_rfl, q.2.1.trans (q.2.2.1.trans q.2.2.2)⟩).1
>     have hb := hC (A n) (iterationsB_rho E s n q.1.2) (T n) (sz.Bctl n (s n)) (N + 4)
```

**Name-clash grep** (`grep -rn -F -e <name> RBM3D RBM3D.lean`, hits outside `RBM3D/Induction/IterationsB.lean`; the non-zero hits are the two registry comment lines I wrote in `Test/Axioms.lean`, listed last):
```
iterationsB_: 1 hit(s) outside the new file
iterationsB_step: 1 hit(s) outside the new file
stIterations'_holds: 1 hit(s) outside the new file
stIterationsII'_holds: 1 hit(s) outside the new file
IterationsBInst: 0 hit(s) outside the new file
inst_iterations': 0 hit(s) outside the new file
inst_iterationsII': 0 hit(s) outside the new file
RBM3D/Test/Axioms.lean:125:   `RBM.Gauss
RBM3D/Test/Axioms.lean:128:   `RBM.Gauss
```

**Registry** (edit `Test/Axioms.lean`; `git diff HEAD~1 HEAD`, changed lines only):
```
-   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hypothesis of `STIterR'`
+   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hypothesis of `STIterR'`; h
-   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot'` (DECISIONS §80): S3-24b
-   `RBM.Gauss.Sizes.STIterations', -- `lem:iterations`, case (i), R2* (DECISIONS §80): S3-24b
-   `RBM.Gauss.Sizes.STIterationsII', -- `lem:iterations`, case (ii), R2* (DECISIONS §80): S3-24b
+   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot'` (DECISIONS §80); proved at both
```
Pre-check: `import RBM3D` (+ `import RBM3D.Induction.IterationsB` after) then `#assert_rbm_axioms`, `lake env lean`; before = the registry and library of `7672749` without `IterationsB`:
```
BEFORE (registry_before.lean):
axiom audit: 7615 theorems, 2557 definitions, 0 axioms in `RBM` (compiler-generated declarations exc
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 160 owed + 98 structural + 7 refuted + 12 superseded; 126 registered premise(s) carry nothing yet
  RBM.Gauss.Sizes.STIterR': 0 [no certificate]
  RBM.Gauss.Sizes.STIterations': 0 [no certificate]
  RBM.Gauss.Sizes.STIterationsII': 0 [no certificate]
exit 0
AFTER (registry.lean = import RBM3D + import RBM3D.Induction.IterationsB):
axiom audit: 7620 theorems, 2557 definitions, 0 axioms in `RBM` (compiler-generated declarations exc
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet
  RBM.Gauss.Sizes.STIterR': 0 [no certificate]
exit 0
```
Owed 160 -> 158 (`STIterations'`, `STIterationsII'` removed), premises found by scanning 153 -> 153 (not larger), no unregistered premise, theorems 7615 -> 7620 (the five public declarations), exit 0 both times. `STIterR'` stays owed (0 theorems rest on it, as in the ticket).

**Scope** (`git diff --name-only main...t/T2259`): `RBM3D/Induction/IterationsB.lean RBM3D/Test/Axioms.lean `
```
 RBM3D/Induction/IterationsB.lean | 759 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean           |   6 +-
 2 files changed, 761 insertions(+), 4 deletions(-)
```
`git merge-tree --write-tree main t/T2259` (main has moved on, T2258 removed the registry line `:124`, adjacent to my hunk):
```
Auto-merging RBM3D/Test/Axioms.lean
CONFLICT (content): Merge conflict in RBM3D/Test/Axioms.lean
```
**Ports:** none from RBM1D/RBM2D (not read, not touched); the only copy is of RBM3D `IterationsA.lean` at `6583ca2` (unchanged in the worktree), so no RBM1D/RBM2D diff-stat.

**Narrative.**
- New file `RBM3D/Induction/IterationsB.lean` (759 lines): §1 the 376-line private block under the `iterationsB_` prefix; §2 `iterationsB_step`; §3 the private `iterationsB_flowLam`, `iterationsB_K_pairs`, `iterationsB_setting`; §4 `stIterations'_holds`, `stIterationsII'_holds`; §5 the instances.
- The step differs from `iterationsA_step` in exactly the two slots of the ticket (diff above): `hboot : STXiBoot'`, and `hlow` at `w = s` with `Bu := sz.Bctl n (s n)` in `hC`.
- The ticket's literal rename command (`s/iterationsA_/iterationsB_/g` on all names) is not the right comparison: the copied text calls public `iterationsA_*` lemmas, which must keep their names. Only the 24 private names are renamed; with that rename the copy is identical to the source (0 hunks).
- `iterationsB_setting` takes `hS` as a function of `(t < 1, |E| < 2, WO d)`, so that the two pins share the plumbing; `hK` (uniform `K` bound on pairs) is `stKbound_timeIcc` reindexed along `(q,p) -> (<q.1.1, ..>, p)` by `StochDomAt.precomp_param` (the fallback through `perTime_timeIcc_of_forall_seq` was not needed).
- Both pins use `𝔠d = 1/100` (preflight (i): `<= 1/16` and `<= 1/24` for the scale facts); `STXiBoot'` remains the pins' own hypothesis; the pins' hypotheses `STKbound` and `STLK` are not used (a hypothesis may stay unused), `STCaseII` is not consumed in case (ii), as in the merged `iterationsA_scale_II`.
- The stochastic premises (`STXiBoot'`, `hrela`, `havg`, `hapri`, induction hypotheses, `STStep1Loop`, `STStep2Concl`, `STLK`) stay hypotheses of the instances; every deterministic hypothesis is discharged.
- Not done by me: the root import in `RBM3D.lean` (hub, at merge), no edit of any other file.

### (c) Verified Mathlib names used (new text only; the copied block uses the same names as `IterationsA.lean`)
- `Real.rpow_pos_of_pos` `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:117`
- `half_pos` `Mathlib/Algebra/Order/Field/Basic.lean:112`
- `inv_pos` `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:837`
- `Filter.Eventually.of_forall` `Mathlib/Order/Filter/Basic.lean:663`
- `lt_of_lt_of_le` `Mathlib/Order/Defs/PartialOrder.lean:91`
- Names verified absent: none checked.

### (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (`T2259a...` empty). The R2* slot (`B_s` for `B_u`) is `T2246a`; case (ii) of `lem:iterations` ("we omit the details", `3_5:1594`) is D173 (merged `iterationsA_scale_II`).
- Registry: my hunk touches `:125-:130`; main's `:124` removal (T2258) makes a plain three-way merge of `Test/Axioms.lean` conflict (`merge-tree` above); the hub resolves by the union rule (CONTROL H23 b): keep main's removal of `STOeqNQ''`, and my two removals and two comment changes.
- Example (3) at `(N,k) = (3,2)` is added to the ticket's `(2,1)` because `IH1` is empty at `N = 2` (preflight Note 2); no pin changed.
- Preflight Note 1 stands: `STConStInd (1/100)` at the instance data first holds at `W ~ 1.2e10`; it is the pin's own eventual-in-`n` hypothesis, discharged for every `𝔠d > 0` by `conStInd_const` with no explicit `n`.
- Consumer note (S3-25): `𝔠d = 1/100` is the maximum the pins allow, so the pins impose no restriction on the `𝔠d` of the other pins.
- No (a′): no mistake found in section (a).
