Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 20:01 UTC 2026

Source: `git show 0362cbc:RBM3D/Probe/T2039Pins.lean` lines 819–2127 (probe §3–§8); merged `Induction/Step2Defs.lean`, `ScaleFacts.lean`. Paper: `3_5:493–577`.

### (i) Exponent table (and the declaration list the ticket asks for)

| quantity | value / statement | constraint | slack |
|---|---|---|---|
| closure exponents of `ST_alpha'_le`, `ST_closure_arith` | `b^{1/2}`, `b^{1/4}`, `b^{1/5}`, `b^{1/6}`, `b^{1/30}`; `1/5 = 1/6 + 1/30` | `0<b≤1`; `1/2,1/4 ≥ 1/5` so `b^{1/2},b^{1/4} ≤ b^{1/5}` | exact identity; constant `(3+3/mI)Λ²(1+q+L)` covers `2q+ΛL/mI+Λ+Λ²L/mI+Λq` (from `√(2x)≤1+x`; `3Λ²-Λ-2≥0`) |
| `hsmall` of `ST_good_engine` (`hclose` of `ST_engine`) | `(3+3/mI)Λ²(1+q+log r_k) r_k^{3C} b_k^{1/30} < 1`, `r_k=(1-s)/(1-u_k)`, `b_k=Bctl n u_k` | `mI=Im mE E ≤ 1`, so `3+3/mI ≥ 6`; `Λ≥1`; `b_k ≈ W^{-3}` (d=3) | at `n=100`, `q=1/10`, `Λ=1`, `C=1`, `s=0`, `t=1/16`: max_k LHS = 0.5979 (slack 0.40); floor: needs `b < 6^{-30}`, i.e. `W^3 ≳ 2.2e23` |
| size at which `hsmall` first holds (`sz0`, E=0, K=16, `C=1`,`Λ=1`) | least `n = 30` (q=0), `n = 36` (q=1/10) | forced by the exponent `1/30`, not by the witness choice; `ST_good_engine` is per-`n`, no `∀ᶠ` inside | `n=100`: slack 0.40 |
| downstream `Λ = N^ε` (not in this ticket) | `Λ² b^{1/30} ≲ N^{2ε} 2^{1/30} W^{-d/30}`, `N ≤ W^{1/𝔠}` | `ε < 𝔠 d/60` (d=3: `ε < 𝔠/20`; `sz0`, `𝔠=1/6`: `ε<1/120`) | informational for ST2-03/04 |
| `hb1 : Bctl n (t n) ≤ 1` | `b_t = 2.804e-35` at n=100 | `≤ 1` | huge |
| `ha, hr, hρ` | `a₀=r₀=q b_s^{1/5}=1.213e-8`, `ρ₁=(q b_s^{1/5})²` | `≤ q b_s^{1/5}`, `≤ (q b_s^{1/5})²` | equality (allowed) |
| `hbelow` of the sample | `Jh = a₀ = 1.213e-8` vs `min_k b_k^{1/6} = 1.724e-6` | `Jh_j < b_j^{1/6}` | factor 142 |
| `hclose` of `ST_engine` (the α-sums) | `max_k α_k r_k^{3C}/b_k^{1/6} = 0.0254` | `< 1` | 0.97 |
| time window of `ST_good_engine` | `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`; uses `1-u>0` only; no `ilambda²≤L²(1-t)`, no `L^d ≤ W^K` (DECISIONS §29 items 2, 3) | `s=0,t=1/16` | `1-t = 15/16` |
| quantifiers (§29 item 4) | `ST_good_engine`, all §3, §4, §6, §7 lemmas are per-`n`/per-sample; `ST_whp_grid`, `ST_model_of_whp_grid` carry `∀ n, 0≤s n, s n≤t n, K n≠0` for the chosen sequences (as the probe) | satisfied by `sInst, tInst, K≡16` | not a pin: no new `∀ n` imposed on a size condition |
| `Kf` in `ST_good_engine` | `Kf ≡ 1` (instance) | `0 ≤ Kf ≤ L`; `u ↦ tailT_u(Kf)` nondecreasing on grid | `tailT_{u_0}(1)=0.1839 ≤ … ≤ tailT_{u_K}(1)=0.1962` at n=100 (script line `hTmono`) |
| tail lemmas (`ST_tailW_final`) | `tailT_0(L)=4.606e-12`, `W^{-1/2}=1.724e-06` (n=100, D=1/2) | `tailT(K) ≤ W^{-D}` | factor 3.7e5 |

Declarations moved (probe line; role). Role "skel" = used in `ST_step2_of_pins` (probe §12, 4531–4726) directly; "→§k" = used first in probe section k and reaches the skeleton through §11 `ST_iterate`/`ST_decay_pt`/`ST_selfImprove` (script `roles.py`, direct-reference counts by section).

| § | declarations | role |
|---|---|---|
| 3 (826–1043) | `ST_one_le_prod`, `ST_gronwall`, `ST_bootstrap`, `ST_logstep`, `ST_logsum`, `ST_prod_le_rpow`, `ST_pathwise_ineq`, `ST_alpha_mono` | discrete Grönwall and stopped bootstrap (`3_5:493`, `533`, `568`); used in §6 `ST_engine` |
| 4 (1051–1153) | `ST_tailT_mono_time`, `ST_tailW_mono_time`, `ST_tailW_scale_step`, `ST_tailW_L_le`, `ST_tailW_final` | `(eq:monotone_Ku)`, `(eq:def_ell1)` (`3_5:520–577`); →§8, §10; `ST_tailW_L_le` is skel |
| 5 (1162–1309) | `ST_gridTime_mem`, `ST_pathP_eq_seqP`, `ST_whp_grid`, `ST_model_of_whp_grid`, `ST_PT_of_sections`, `ST_sections_of_PT` | transfer model ↔ grid walk via merged `transferLaw` (proved, `Path/Walk.lean:637`); →§9, §11; `ST_PT_of_sections`, `ST_sections_of_PT` skel |
| 6 (1319–1721) | `ST_rpow_half_mono`, `ST_rpow_half_add_le`, `ST_cube_le`, `ST_engine`, `ST_alpha_bound`, `ST_alpha'_le`, `ST_closure_arith` | Grönwall closure of `3_5:556–568` at a fixed sample; →§8 |
| 7 (1729–1765) | `ST2_Bctl_pos`, `ST2_Bctl_mono` | **replaced** by merged `STBctl_pos`, `STBctl_mono` (`ScaleFacts.lean:64,74`): signatures identical (checked below); copies dropped; used in §8, §11, skel |
| 8 (1773–2125) | `STLab`, `STGoodAt` (structure Prop), `ST_firstHit_hit`, `ST_good_engine` | good event of one self-improving step; →§11 `ST_selfImprove_section` |

Probe names replaced by merged ones: `ST2_Bctl_pos → STBctl_pos`, `ST2_Bctl_mono → STBctl_mono` (8 lines in §3–§8 mention `ST2_Bctl`); `STNewKLKAt, STGMM, STEEM, STEGtM, STprof, STJhatM, STgA, STgDrift, STthetaOp, STELKLKM, STLKM, STstopIdx` are already in `Step2Defs.lean` (probe lines 277–753 → merged; imported, not copied); `tailT, tailW, tailW_pos, ellT, Bctl, gridTime, pathH, firstHit, transferLaw, HighProbAt, Prec, PrecPT` are merged (Defs/Tail, Params, Sizes, Path/Walk, Path/Stop, Defs/StochDomAt). `st_Bctl_ge`/`STBctl_ge` are not used by §3–§8 (not needed). Name-clash grep of all 31 new names against `RBM3D/` (outside the probe): 0 hits each. Namespace: probe §3–§7 sit in `RBM.Probe.T2039`, only §8 in `RBM.Gauss.Sizes` (`open RBM.Probe.T2039`); the ticket pins `RBM.Gauss.Sizes` for all, so the 5 `namespace RBM.Probe.T2039` brackets and the `open` of line 1775 are changed (listed for the prover's change list).

**Registry (CLAUDE.md §5.5, DECISIONS §20) differs from the ticket's "no new hypothesis Prop expected".** `scanPremises` (`Test/Axioms.lean`) fails the build on a `Prop` def/structure that some theorem takes as a hypothesis and no theorem proves. `ST_good_engine` takes `hNew : STNewKLKAt …` and `hg : STGoodAt …`; neither name is in `Test/Axioms.lean` (grep: only `STNewKLK` l.131 and `STContractPt` l.132 occur) and no theorem concludes them. Both need a registry line in the writable `Test/Axioms.lean`: `STNewKLKAt` owed (the pointwise form of the registered pin `STNewKLK`, ST2-07); `STGoodAt` structural or owed (the pathwise event (E1)–(E5) of probe §11, which holds w.h.p. by `ST_good_prob`; its conclusion head is `HighProbAt`, so the scan never sees it proved). Classification is the dispatcher's.

### (ii) One concrete nondegenerate instance (`d=3`, `sz0`, `n=100`)

Data: `L=404`, `W=202^5=336323216032`, `lam=202^{-6}`, `E=0` (`mE 0 = I`, `Im=1`), `κ=𝔡=1/10`, `s≡0`, `t≡1/16`, `K≡16` (`Δ=1/256`), `Λ=1`, `C=1`, `q=1/10`, `D=1/2` (tail rows) / any `D≥0`, `Kf≡1`. Sample (`ι` a one-point label set): `P≡1`, `x_k≡a₀`, `dr=mart=remk=ee≡0`, `Jh≡a₀`, `τ=K` (all inequality hypotheses of `ST_engine` hold). Transfer lemmas: `F≡0`, `Z≡1`, `τ=0`, `V n = Fin 1`, `J n = range 17` (`hcard`: 17 ≤ N^1); measurable constants; `S={H | ‖H 0 0‖ ≤ 1}`, `k=7`. Stochastic premises that stay hypotheses of the example (allowed by CLAUDE.md §4 step 2): `hNew` (pin `STNewKLK` not proved) and `hg : STGoodAt` (a high-probability event; its satisfiability at this `n` is the paper's `ST_good_prob`, probe §11, outside this ticket; not discharged here). Every other hypothesis of `ST_good_engine` is deterministic and checked below. External-hypothesis limit computation (TEAM §8 lesson 14): the constants of `hNew` enter only through `C` in `hsmall`; for every fixed `C ≥ 0`, `Λ`, `q`, `mI`, LHS `≤ c·W^{-1/10}·2^{1/30} → 0` as `W→∞` (`b ≤ 2W^{-3}`, `b^{1/30} ≤ 2^{1/30}/√202 = 0.0720` at this `n`), so `hsmall` holds eventually for any `C` the pin supplies; the `δ₀` of the pin does not enter `hsmall`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2071/inst2.py` (Python, floats; numerical check of the hypotheses, no Lean). Output, verbatim:
```
n=100 L=404 W=336323216032 lam=1.472e-14  b_s=2.629e-35 b_t=2.804e-35
OK  hsmall: max_k LHS = 0.5979 (<1);  hb1: OK 
OK  b_u<=2W^-3; (2W^-3)^(1/30)=2^(1/30)/sqrt(202)=0.0720
OK  hbelow: Jh=a0=1.213e-08 < min_k b_k^(1/6)=1.724e-06
OK  hclose: max_k alpha_k r_k^{3C}/b_k^{1/6} = 0.0254
OK  alpha_bound/alpha'_le chain: 3.643e-08 <= 3.643e-08 <= 8.587e-07
OK  ST_cube_le: J=1/2,b=9/10: J<b^(1/6), J^3<=b^(1/2)
OK  ST_gronwall: J_k<=alpha_k prod: J= [1.0, 1.225, 1.4781, 1.7629, 2.0833] bounds [1.0, 1.2375, 1.5188, 1.851, 2.2425]
OK  ST_bootstrap: hclose with theta=10, tau=K=4 (hhit vacuous)
OK  ST_logsum: 0.27752<=0.28768 ; ST_prod_le_rpow(c=1): 1.30769<=1.33333
OK  ST_logstep x=1,Delta=1/16
OK  ST_tailT_mono_time: 4.423030e-02<=4.717899e-02
OK  ST_tailW_mono_time (K=1 both, hK holds by tailT mono)
OK  ST_tailW_scale_step: e=0.0271
OK  ST_tailW_L_le (l=1, rho<=L)
OK  ST_tailW_final: tailT_0(L)=4.606e-12 <= W^-1/2=1.724e-06
OK  ST_gridTime_mem: k<=K=16, hK: K!=0
least n (sz0) with hsmall, q=0.0: 30
least n (sz0) with hsmall, q=0.1: 36
scalar floor: (3+3/mI)>=6 so b^(1/30)<1/6 => b<6^-30=4.52e-24 => W^3>~2.21e+23
OK  hTmono (Kf=1): tailT_{u_0}(1)=0.1839 <= ... <= tailT_{u_K}(1)=0.1962; 0<=Kf<=L
```
Signature check (probe lines 1738, 1748–1749 vs `RBM3D/Induction/ScaleFacts.lean` lines 64, 74, printed by `sed -n`): probe `ST2_Bctl_pos (n : ℕ) {u : ℝ} (hu : u < 1) : 0 < sz.Bctl n u`, merged `STBctl_pos (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < sz.Bctl n t`; probe `ST2_Bctl_mono (n) {s u} (hsu : s ≤ u) (hu : u < 1) : sz.Bctl n s ≤ sz.Bctl n u`, merged `STBctl_mono` identical; both have explicit `sz`. `Bctl` in the script: `Bparam 3 L g u 0 = (g²+|1-u|)⁻¹·1 + (L³|1-u|)⁻¹` (the `K=0` factor `((0+1)^{d-2})⁻¹ = 1`), as coded in `inst2.py`.

### Verdicts
- §3 (`ST_one_le_prod … ST_alpha_mono`): PASS (hypotheses jointly satisfiable, rows 1, Grönwall/bootstrap/log lines above).
- §4 (`ST_tailT_mono_time … ST_tailW_final`): PASS.
- §5 (`ST_gridTime_mem … ST_sections_of_PT`): PASS (instance trivial `F≡0, Z≡1`; `transferLaw` is a proved theorem, not a pin).
- §6 (`ST_rpow_half_* … ST_closure_arith`, `ST_engine`): PASS.
- §7 (`STBctl_*` reuse): PASS (copies dropped).
- §8 (`STLab`, `STGoodAt`, `ST_firstHit_hit`, `ST_good_engine`): PASS, with two flags for the prover: (1) the nonempty instance needs `n ≥ 36` (`sz0`, `q=1/10`), so use `n=100` not `n=0`; `hNew`, `hg` stay example hypotheses; (2) registry lines for `STNewKLKAt`, `STGoodAt` are required (see above), contrary to the ticket text; also namespace change of §3–§7 from `RBM.Probe.T2039` to `RBM.Gauss.Sizes`. Later tickets that cite `ST2_Bctl_pos/mono` (probe §11, §12) must use `STBctl_pos/mono`.

### (a′) Preflight corrections — Sat Oct  3 20:18:50 UTC 2026
Section (a) says "31 new names"; script count of new public names is 30 (28 theorems, `abbrev STLab`, `structure STGoodAt`; table below). No verdict changes; (a) is otherwise confirmed: before the two registry lines were added, the pre-check printed (tool log) `error: axiom audit: 2 premise(s) that no theorem of this development proves are in none of borrowedProps, owedProps, structuralProps: [RBM.Gauss.Sizes.STGoodAt, RBM.Gauss.Sizes.STNewKLKAt]`.

## (b) Script output (stage 1b, Sat Oct  3 20:18:50 UTC 2026)

Branch `t/T2071`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2071`.
```
$ git log -1 --format='%h %an' ; git diff --stat HEAD~1 HEAD
167e4f0 Jun Yin
 RBM3D/Induction/Step2Core.lean | 1771 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    2 +
 2 files changed, 1773 insertions(+)
$ git diff --name-only main...t/T2071
RBM3D/Induction/Step2Core.lean
RBM3D/Test/Axioms.lean
```
```
$ lake build RBM3D.Induction.Step2Core 2>&1 | grep -E "Built|Build completed|error|Step2Core.lean" | grep -v "line exceeds"
Build completed successfully (3719 jobs).
exit: 0
$ lake build   # whole library in the worktree (new module is not yet in RBM3D.lean)
Build completed successfully (3789 jobs).
exit: 0
$ cat precheck.lean; lake env lean precheck.lean | grep -E "error|non-vacuity|axiom audit"
import RBM3D
import RBM3D.Induction.Step2Core
#assert_rbm_axioms
axiom audit: 2475 theorems, 1048 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 2, owed 67, structural 13).
non-vacuity certificates: 4 of 91 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
exit: 0
```

`#print axioms`, script `axcopy2.lean` (the file with each `example` renamed `inst_N`, then `#print axioms` of all 30 new declarations and 28 instances); std3 = [propext, Classical.choice, Quot.sound]:
```
ST_one_le_prod (Step2Core.lean:46) : std3
ST_gronwall (Step2Core.lean:56) : std3
ST_bootstrap (Step2Core.lean:98) : std3
ST_logstep (Step2Core.lean:117) : std3
ST_logsum (Step2Core.lean:127) : std3
ST_prod_le_rpow (Step2Core.lean:160) : std3
ST_pathwise_ineq (Step2Core.lean:201) : std3
ST_alpha_mono (Step2Core.lean:245) : std3
ST_tailT_mono_time (Step2Core.lean:276) : std3
ST_tailW_mono_time (Step2Core.lean:302) : std3
ST_tailW_scale_step (Step2Core.lean:326) : std3
ST_tailW_L_le (Step2Core.lean:347) : std3
ST_tailW_final (Step2Core.lean:356) : std3
ST_gridTime_mem (Step2Core.lean:387) : std3
ST_pathP_eq_seqP (Step2Core.lean:400) : std3
ST_whp_grid (Step2Core.lean:422) : std3
ST_model_of_whp_grid (Step2Core.lean:464) : std3
ST_PT_of_sections (Step2Core.lean:500) : std3
ST_sections_of_PT (Step2Core.lean:515) : std3
ST_rpow_half_mono (Step2Core.lean:540) : std3
ST_rpow_half_add_le (Step2Core.lean:544) : std3
ST_cube_le (Step2Core.lean:551) : std3
ST_engine (Step2Core.lean:571) : std3
ST_alpha_bound (Step2Core.lean:782) : std3
ST_alpha'_le (Step2Core.lean:844) : std3
ST_closure_arith (Step2Core.lean:917) : std3
STLab (Step2Core.lean:955) : none
STGoodAt (Step2Core.lean:963) : std3
ST_firstHit_hit (Step2Core.lean:987) : std3
ST_good_engine (Step2Core.lean:997) : std3
instances (28 `example`s): {'[propext, Classical.choice, Quot.sound]': 28}
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Step2Core.lean
0
```

Registry lines (`git diff HEAD~1 HEAD -- RBM3D/Test/Axioms.lean`, `+` lines, cut to 150 chars):
```
+   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the form `ST_good_engine` takes: ST2-07 (+ST2-06b)
+   `RBM.Gauss.Sizes.STGoodAt, -- the pathwise good event (E1)-(E5) of one self-improving step of Step 2 (`3_5:537-577`), hypothesis of `ST_good_engin
```

Moved block vs probe (`git show 0362cbc:RBM3D/Probe/T2039Pins.lean | sed -n 819,2127p` against Step2Core.lean lines 35-1301, `diff`): 107 diff lines; the new-side changed lines, counted (`sort | uniq -c`), and the deleted probe lines: 58 (the probe section 7 block, `ST2_Bctl_pos`/`ST2_Bctl_mono`, and its brackets):
```
  4 > namespace RBM.Gauss.Sizes
  4 > end RBM.Gauss.Sizes
  1 > open RBM RBM.Loop RBM.Path
  1 >     STBctl_pos sz n (hu_lt j hj)
  1 >     exact STBctl_mono sz n (hu_mono j k hjk) (hu_lt k hk)
  1 >     (STBctl_mono sz n (hu_le j hj) ht1).trans hb1
  1 >     STBctl_mono sz n (hu_ge k hk) (hu_lt k hk)
  1 >     mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (STBctl_pos sz n hs1).le (hbs k hk)
  1 >     refine hρ.trans (pow_le_pow_left₀ (mul_nonneg hq0 (Real.rpow_nonneg (STBctl_pos sz n hs1).le _))
```

Target statements extracted by script (`STGoodAt`, `ST_good_engine`; the other 28 declarations are verbatim from the probe by the diff above, line numbers in the axiom table):
```
-- Step2Core.lean:963
structure STGoodAt (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E D : ℝ) (ℓk : ℕ → ℝ) (Λ δ₀ a₀ r₀ ρ₁ : ℝ)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ)
    (ω : PathΩ sz) : Prop where
-- Step2Core.lean:997
theorem ST_good_engine (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (Efun : ℕ → ℝ) (D : ℝ)
    (Kf : ℕ → ℝ → ℝ) {Λ δ₀ C a₀ r₀ ρ₁ q κ 𝔡 : ℝ}
    (hK : K n ≠ 0) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hD : 0 ≤ D)
    (hmI : 0 < (mE (Efun n)).im) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀)
    (hρ₁ : 0 ≤ ρ₁) (hlam : 0 < sz.lam n) (hlam' : sz.lam n ≤ 𝔡⁻¹) (hE : |Efun n| ≤ 2 - κ)
    (hNew : STNewKLKAt d κ 𝔡 C δ₀)
    (hKf0 : ∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s t K n j))
    (hKfL : ∀ j, j ≤ K n → Kf n (gridTime s t K n j) ≤ ((sz.L n : ℕ) : ℝ))
    (hTmono : ∀ j k, j ≤ k → k ≤ K n →
      tailT d (sz.L n) (sz.lam n) (gridTime s t K n j) (Kf n (gridTime s t K n j)) ≤
        tailT d (sz.L n) (sz.lam n) (gridTime s t K n k) (Kf n (gridTime s t K n k)))
    (hb1 : sz.Bctl n (t n) ≤ 1) (hq0 : 0 ≤ q)
    (ha : a₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) (hr : r₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ))
    (hρ : ρ₁ ≤ (q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2)
    (hsmall : ∀ k, k ≤ K n →
      (3 + 3 * ((mE (Efun n)).im)⁻¹) * Λ ^ 2 *
          (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) *
          (sz.Bctl n (gridTime s t K n k)) ^ (1 / 30 : ℝ) < 1)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (hg : STGoodAt sz s t K n (Efun n) D (fun j => Kf n (gridTime s t K n j)) Λ δ₀ a₀ r₀ ρ₁
      Mart Rem ω) :
    STstopIdx sz s t K Efun D Kf n ω = K n ∧ ∀ k, k ≤ K n →
      STJhatM sz n (Efun n) D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
          (pathH sz s t K n k ω) ≤
        ((3 + 3 * ((mE (Efun n)).im)⁻¹) * Λ ^ 2 *
            (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
            (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) := by
```

Compiled nonempty instances: 28 `example`s, one per theorem (`example@line -> theorem`, found by script; `ST_alpha_bound`, `ST_alpha'_le`, `ST_closure_arith`, `ST_engine` at the data `s=0, Δ=1/256, K=16, b≡10^{-30}, a₀=r₀=q b^{1/5}`, `q=1/10`, `Λ=C=mI=1`; the transfer lemmas at `sz0`, `s≡0, t≡1/16, K≡16`, `F≡0, Z≡1`, `V=Fin 1`):
```
ST_one_le_prod@1336; ST_gronwall@1340; ST_bootstrap@1348; ST_logstep@1362; ST_logsum@1365; ST_prod_le_rpow@1369;
ST_pathwise_ineq@1374; ST_alpha_mono@1386; ST_tailT_mono_time@1395; ST_tailW_mono_time@1398; ST_tailW_scale_step@1404;
ST_tailW_L_le@1412; ST_tailW_final@1439; ST_gridTime_mem@1446; ST_pathP_eq_seqP@1452; ST_whp_grid@1477; ST_model_of_whp_grid@1486;
ST_PT_of_sections@1503; ST_sections_of_PT@1510; ST_engine@1585; ST_rpow_half_mono@1638; ST_rpow_half_add_le@1641; ST_cube_le@1644;
ST_alpha_bound@1648; ST_alpha'_le@1666; ST_closure_arith@1680; ST_good_engine@1726; ST_firstHit_hit@1764; 
-- the endpoint instance, Step2Core.lean:1726-1767 (`hNew`, `hg` stay hypotheses; everything else is discharged):
/-- `ST_good_engine` at `d = 3`, `sz0`, `n = 100` (`L = 404`, `W = 202^5`, `lam = 202^{-6}`),
`E = 0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`, `D = 1/2`, `Kf ≡ 1`, `Λ = C = 1`, `q = 1/10`; the pin `hNew`
and the good event `hg` stay hypotheses. -/
example (δ₀ : ℝ) (ω : PathΩ sz0) (hNew : STNewKLKAt 3 (1 / 10) (1 / 10) 1 δ₀)
    (hg : STGoodAt sz0 sI tI KI 100 0 (1 / 2) (fun _ => 1) 1 δ₀ a0 a0 (a0 ^ 2)
      (fun _ _ _ => 0) (fun _ _ _ => 0) ω) :=
  ST_good_engine sz0 sI tI KI 100 (fun _ => 0) (1 / 2) (fun _ _ => 1) (Λ := 1) (δ₀ := δ₀) (C := 1)
    (a₀ := a0) (r₀ := a0) (ρ₁ := a0 ^ 2) (q := 1 / 10) (κ := 1 / 10) (𝔡 := 1 / 10)
    (by norm_num [KI]) (by norm_num [sI]) (by norm_num [sI, tI]) (by norm_num [tI]) (by norm_num)
    (by rw [mE_zero_im]; norm_num) le_rfl (by norm_num) a0_nonneg a0_nonneg (sq_nonneg _)
    (lam_pos 100) (by
      have : sz0.lam 100 ≤ 1 := by
        change ((2 * (((100 : ℕ) : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith) (by norm_num) hNew
    (fun _ _ => by norm_num) (fun _ _ => one_le_L100)
    (fun j k hjk hk => by
      refine ST_tailT_mono_time one_le_L100 (lam_pos 100).le ?_ ?_ (by norm_num)
      · rw [gt_eq, gt_eq]
        have : (j : ℝ) ≤ k := by exact_mod_cast hjk
        linarith
      · have := gt_le hk; linarith)
    (by
      have := Bctl_small (c := tI 100) (by norm_num [tI])
      refine this.trans ?_
      norm_num)
    (by norm_num) le_rfl le_rfl le_rfl
    (fun k hk => by
      have hrb := r_bounds hk
      have hb := Bctl_small (c := gridTime sI tI KI 100 k) (gt_le hk)
      have hb0 : 0 < sz0.Bctl 100 (gridTime sI tI KI 100 k) :=
        Sizes.STBctl_pos sz0 100 (by have := gt_le hk; linarith)
      rw [gt_eq] at hb hb0
      have h := core_small hb0 hb hrb.1 hrb.2
      rw [mE_zero_im]
      simp only [sI]
      rw [gt_eq]
      simpa using h)
    (fun _ _ _ => 0) (fun _ _ _ => 0) ω hg

/-- `ST_firstHit_hit` at `J_k = k`, `θ = 2`, `K = 5`: the first hit is `2 < 5`. -/
example : (2 : ℝ) ≤ (fun (k : ℕ) (_ : Unit) => (k : ℝ)) (firstHit (fun (k : ℕ) (_ : Unit) => (k : ℝ)) 2 5 ()) () :=
  ST_firstHit_hit (fun (k : ℕ) (_ : Unit) => (k : ℝ)) 2 5 (ω := ())
    (lt_of_le_of_lt (MeasureTheory.hittingBtwn_le_of_mem (n := 0) (i := 2) (by norm_num)
      (by norm_num) (by simp)) (by norm_num))
```

Name-clash grep (`grep -rn --include=*.lean -E "(theorem|def|abbrev|structure|lemma) <name>( |$)" RBM3D`, excluding Step2Core.lean and Probe/): 30 new public names, 0 hits. The 27 private helpers: 1 same short name (`lam_pos`) in `RBM.Gauss.LWPsiInst` (`Graph/LWPsi.lean:542`), another namespace; `lake build` passes.

Narrative (facts from the files and the tool log above):
- Moved: probe lines 819-1723 (sections 3-6) and 1768-2127 (section 8) into `RBM3D/Induction/Step2Core.lean`, namespace `RBM.Gauss.Sizes`; changes are exactly the diff above (namespace brackets, one `open`, six lines renamed `ST2_Bctl_*` -> `STBctl_*`). No proof was edited.
- Probe section 7 (`ST2_Bctl_pos`, `ST2_Bctl_mono`) is dropped; merged `STBctl_pos`, `STBctl_mono` (`Induction/ScaleFacts.lean:64,74`) are used. `STBctl_ge`/`st_Bctl_ge` are not used by sections 3-8.
- `STGMM, STEEM, STJhatM, STgA, STgDrift, STthetaOp, STELKLKM, STstopIdx, STNewKLKAt` are `def`s of `Step2Defs.lean` (grep, each count 1), imported, not copied.
- New: section `Instances` (lines 1302-1771, 28 `example`s + 27 `private` helpers). No hypothesis was added to any theorem.
- Data of the instances: `sz0` at `n = 100` (`L = 404`, `W = 202^5`, `lam = 202^{-6}`), `E = 0` (`(mE 0).im = 1`, proved), `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`, `D = 1/2`, `Kf ≡ 1`, `Λ = C = 1`, `q = 1/10`, `κ = 𝔡 = 1/10`.
- `hsmall` of `ST_good_engine` is discharged for all `k ≤ 16` by the private `core_small`: `b ≤ (1/10)^30` gives `b^{1/30} ≤ 1/10`, `1 ≤ r ≤ 16/15`, so the left side is `≤ 6(1+1/10+1/15)(16/15)^3/10 = 0.8495 < 1`; `Bctl_small` gives `Bctl 100 c ≤ (1/10)^30` for `c ≤ 1/16` (`norm_num` on `2 (15/16)^{-1} (202^15)^{-1}`). This is cruder than the preflight's 0.5979 (a float of the exact value); (a) is not changed.
- `hTmono` is `ST_tailT_mono_time` at `Kf ≡ 1`; `hb1`, `hlam'`, `hE`, `hKf*`, `ha`, `hr`, `hρ` (equality `a₀ = q Bctl(0)^{1/5}`) are discharged; `Mart = Rem ≡ 0` are arguments.
- Differences from the data of (a)(ii): `ST_tailW_final` at `D = 0` (`W^{-D} = 1`, from `tailT_0(404) ≤ 1`, proved) not `D = 1/2`; `ST_tailW_scale_step` at `K = K' = 1`, `e = 1/2`; the `ST_engine` instance has `b ≡ 10^{-30}` (abstract `b`), one label, `a₀ = r₀ = q b^{1/5}`.
- `STGoodAt` is a structure `Prop` with the seven fields `weak, init, lw, mg, mart, rem, ident` (Step2Core.lean:966-984, verbatim from the probe); they are hidden hypotheses of `ST_good_engine` through `hg`.
- Left as example hypotheses (CLAUDE.md §4 step 2): `hNew : STNewKLKAt 3 (1/10) (1/10) 1 δ₀` and `hg : STGoodAt ...`. `STGoodAt` has no instance here (its satisfiability is the paper's `ST_good_prob`, probe section 11, outside this ticket).
- Registry: contrary to the ticket text, two lines were needed (`STNewKLKAt`, `STGoodAt`), added to `owedProps` as proposed; the class is the dispatcher's to confirm.
- Not done: the root import (hub, at merge); a Lean check of the preflight's `n >= 36` floor (the instance uses `n = 100` only).

## (c) Verified Mathlib names (the module compiles with each)
`Real.pow_rpow_inv_natCast`, `Real.log_le_sub_one_of_pos`, `Real.log_nonneg`, `Real.sqrt_sq`, `Real.exp_le_one_iff`, `Real.rpow_le_rpow`, `MeasureTheory.hittingBtwn_le_of_mem`, `measurableSet_le`, `measurable_pi_apply`, `inv_le_one_of_one_le₀`, `inv_anti₀`, `pow_le_one₀`, `one_le_pow₀`, `pow_le_pow_right₀`, `Nat.cast_le`. Merged: `highProbAt_univ`, `Sizes.prec_of_le`, `Sizes.precPT_of_le`, `InductionDefsInst.W_ge_32`, `InductionDefsInst.Bctl_const_le_gen`, `Sizes.STBctl_pos`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- Registry classification (dispatcher): `STNewKLKAt` (pointwise form of the registered pin `STNewKLK`, ST2-07) and `STGoodAt` (pathwise event of one step, w.h.p. by `ST_good_prob`) were put in `owedProps`; `STGoodAt` could instead be `structuralProps`.
- T2071a: probe sections 3-7 were in `RBM.Probe.T2039` (section 8 in `RBM.Gauss.Sizes`); here all are in `RBM.Gauss.Sizes`. Probe sections 9-12 are in `RBM.Probe.T2039` with `open RBM.Gauss.Sizes` (probe line 2137): later tickets moving them find these names in `RBM.Gauss.Sizes`.
- T2071b: probe `ST2_Bctl_pos`/`ST2_Bctl_mono` (defined at probe lines 1738, 1748) are the merged `STBctl_pos`/`STBctl_mono`; probe lines 2723, 3013, 3091, 3821, 3905, 4696, 4697, 4704, 4706 use them, so later tickets copying sections 9-12 must rename.
- T2071c: per (a) the exponent `1/30` in `hsmall` needs `b < 6^{-30}`, i.e. `W^3` about `2.2e23` (float script of (a)); the instance therefore uses `n = 100`, not small `n`. `ST_good_engine` is per-`n` (no `∀ᶠ`).
- Observation: `ST_PT_of_sections` raises the `unusedFintypeInType` linter warning (probe text, unchanged).
