Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:10:10 UTC 2026

Notation: `a_u := sz.Bctl n u = W^{-d}B_{u,0} = (W^d(g²+x_u))⁻¹ + (N x_u)⁻¹` (`g = sz.lam n`, `x_u = 1-u`, `N = (WL)^d`), the d ≥ 3 role of RBM2D's `M_u⁻¹` (merged `ScaleFacts.lean:12-34`).
Cut (RBM2D `Induction/Step1.lean` at `c9a24cf`): S1-35 = `:1–965` (`end Bridge` at `:965`; 60 declarations, `Step1TargetV3` … `s1_wl_det`); S1-36 = `:967–1515` (31 declarations, `WeakLawSeq` `s1x`, `s1_card_block*` (`:983-1000`), `Net`, `Bootstrap`, `step1` `:1378`, `Checks`). Needed by S1-36 and so public with their `s1_` names: `Step1TargetV3`, `S1Std`, `s1_std_of_*`, `s1_bulk`, `s1_inv_rpow`, `s1_one_le_L`, `s1_one_le_size`, `s1_hsize`, `s1_Ms_pos`/`s1_Mu_pos` (now `a_s>0`), `s1_ratio_ev`, `s1_F3`–`s1_F8`, `s1_highProb_of_pt`, `s1_pt_of_highProb`, `s1_stochDom_unit`, `S1H55`, `s1_h55`, `s1_LI`, `s1xM`, `s1xM_ge/_le/_le_add`, `s1_gMax_le`, `s1_wl_det`; the rest is `private`.

### (i) Exponent table

| # | Quantity | Value / form at d ≥ 3 (RBM2D value) | Constraint | Slack (instance: d=3, 𝔠=1/6, 𝔡=ε=κ=1/10, 𝔠_d=1/100) |
|---|---|---|---|---|
| 1 | `N` | `(WL)^d` (`(WL)²`); `W^d ≤ N` (`W² ≤ N`) | `L ≥ 1` | none needed (`s1_size_eq`, `s1_W_sq_le_size`) |
| 2 | `τ_R`, `c₀` | `τ_R = ε/2`, `c₀ = min(2𝔠𝔡, τ_R)` (`min(2c,τ)`) | `c₀>0`; `1-t ≥ 1-lemT z ≥ Im z/16 ≥ N^{-1+ε}/16 ≥ N^{-1+ε/2}` for `N^{ε/2} ≥ 16` (`lemma28_quant`), eventually only | `c₀ = 1/30`; `τ_R=1/20` |
| 3 | R1 | `a_u ≤ 2N^{-c₀}`, `u ≤ t`, eventually (`M_u ≥ Im m N^{c₀}`); needs `sz.WO 𝔡` (merged `scaleFacts_R1`) | `Bandwidth 𝔠`, `WO 𝔡`, `τ_R` | `a_0(n=0)=3.1e-5` vs `2N^{-c₀}=1.2` |
| 4 | `Im m` bound | `c₁ = √(2κ)/2`, `Im m(E) ≥ c₁` for `|E| ≤ 2-κ` (unchanged, `s1_bulk`) | `κ>0` | `c₁=0.2236` |
| 5 | `M_u ≤ W²` (`s1_scaleM_le_W2`) | no d ≥ 3 reading; replaced by the lower bounds `a_s ≥ W^{-d}(g²+1)⁻¹` (`STBctl_ge`, `0 ≤ s`) and `a_s ≥ N⁻¹` | `0 ≤ s < 1`, `g² ≤ 𝔡⁻²` (WO) | `W^{-d} ≤ 2(g²+1)a_s(1-s)/(1-u)` checked below |
| 6 | `s1_ratio_pt` | `a_s(1-s)/(1-u) ≤ a_s^{1-𝔠_d}` (merged `closure_scale`; from `a_t^{𝔠_d} ≤ (1-t)/(1-s)`, `s ≤ u ≤ t < 1`); `(ℓ_u/ℓ_s)²M_u⁻¹ ≤ M_s^{-14/15}` has no `ℓ` in the merged pin `STStep1Loop` | need `1-𝔠_d ≥ 14/15`, i.e. `𝔠_d ≤ 1/15` | pin `𝔠_d ≤ 1/100`: `0.99-14/15 = 17/300` |
| 7 | F3 `τ₀` | `N^{τ₀}a_s^{1/2} < a_s^{1/4}`, `τ₀ = c₀/8` | `N^{τ₀}<a_s^{-1/4} ≥ (N^{c₀}/2)^{1/4}` | exponent `c₀/4-c₀/8 = 1/240` |
| 8 | F4 `ε` | `C_d a_s^{7/15} ≤ N^{-ε}a_s^{1/4}/2`, `ε = c₀/8`, `C_d = 2·3^d` (`6`) | `(7/15-1/4)=13/60 > ε/c₀` | `(13/60-1/8)c₀ = 11/3600` |
| 9 | F5 `c'` | `2a_s^{1/4} ≤ W^{-c'}`, `c' = c₀/4`; uses `W ≤ N^{1/d}` (`W ≤ N^{1/2}`) | `(c₀/4)(1-1/d)>0` | `c₀/6 = 1/180` |
| 10 | F6, F7 | `2N⁻¹ ≤ a_s^{1/4}` (from `a_s ≥ N⁻¹`: `N^{3/4}≥2`); `a_s^{1/4} ≤ 1` (R1) | eventually | `3/4` |
| 11 | F8 | `W^{-d} ≤ a_s^{14/15}` (`W^{-2} ≤ M^{-14/15}`): `W^{-d} ≤ (g²+1)a_s`, need `(g²+1)a_s^{1/15} ≤ 1` | needs `g ≤ 𝔡⁻¹` (WO), `a_s→0` | crude threshold `N ≳ (101·2^{1/15})^{450}` (eventual); at `sz0` `g≈0`, holds from `n=0` |
| 12 | weak-law constant | `s1_wl_det`: `‖G-M‖_ij² ≤ (2·9^d+1)N^{2τ}g` (`26`) | `STgexRHS` sums 2 σ and `|a'-a|_∞ ≤ 1` | `2·9^d+1 = 1459`; `√ ≤ 2·3^d = 54` |
| 13 | `s1_near_card` | `#{a' : zdistInf(a'-a) ≤ 1} = 3^d` for `L ≥ 3` (`5`); the ticket's `2d+1` is the `zdistD` ball, not the `zdistInf` ball of `STgexRHS` | `L ≥ 3` | script: 27 (not 7) |
| 14 | `s1_gexRHS_le` | `STgexRHS ≤ 2·9^d B + (W^d)⁻¹` (`25B+W⁻²`) | each `‖Lloop σ (a',b')‖ ≤ B` | tight (equality) in script |
| 15 | `s1_loop_det` (`u<1/2`) | `norm_gloop_le_sharp`: `‖𝓛‖ ≤ (2/c₁)^k (W^{-d})^{k-1}` `≤ (2/c₁)^k (2(𝔡⁻²+1))^{k-1}(a_s(1-s)/(1-u))^{k-1}` | `0 ≤ s ≤ u < 1/2`, `g ≤ 𝔡⁻¹` | const `κ,𝔡,k` only |
| 16 | `s1_LI` (`u ≥ 1/2`) | merged `RBM.Ind.conArg` at `(t₁, v)`, `t₁=max(s,1/2)`, `v=max(u,t₁)=u`: `(a_{t₁}(1-t₁)/(1-u))^{k-1} ≤ (a_s(1-s)/(1-u))^{k-1}` by `STBctl_xmono`; `k=1` included in `conArg` | `1/2 ≤ t₁ ≤ v < 1` | exact, no loss; ratio `ℓ_u/ℓ_s` not used |
| 17 | `s1_h55` | `s ≥ 1/2`: `a_s^k + a_s^{k-1} ≤ 2a_s^{k-1}` (`a_s ≤ 1`, eventually); `s<1/2`: row 15 at `t₁=1/2` | `STKbound` at `τ=s` | — |

**Map `S1Std`/`MainIndHyp` → merged** (`STStep1`, `STFlow sz κ ε 𝔠 𝔡 z`, `E = STflowE z = lemE ∘ z`): `hκ,hc` ← pin args, `Admissible.1`; `hE` ← `lemma28_quant` (`|lemE z_n| ≤ 2-κ`); `hN` ← `Admissible.2.2.1`; `hB` ← `.2.2.2.1`; **new field `hWO`** ← `Admissible.2.2.2.2` (rows 3, 11, 15 need it); `hτ,hR` ← row 2 (`τ=ε/2`, eventual); `hs0` ← pin; `hst` ← `s<t`; `ht1` ← `t ≤ lemT z < 1` (`lemT_lt_one`); `hCond` ← `STConStInd 𝔠_d s t` (exponent `30` → `𝔠_d`, `M_s⁻¹` → `a_t`); `InitLK` ← `STLK s`; `InitLocal` ← `STLocalMax s`; `KboundConcl κ` ← `STKbound`; `InitDecay` unused; `GbEXPHypV3 d (κ/2) c τ` ← `STGbEXPii d`, `STGbEXPij d` (the pins quantify over all `κ ε 𝔡 ε₀`; `STGbEXPav` unused).
**`Step1TargetV3` d-form:** `STGbEXPii d → STGbEXPij d → STStep1 d`, concluding both conjuncts `STStep1Loop ∧ STStep1Weak` of `STStep1` (hypotheses `STKbound, STLK s, STLocalMax s, STConStInd` are `STStep1`'s own; the GbEXP pins are the only addition, as RBM2D's `GbEXPHypV3`); S1-36 proves it. Weak conclusion `a_s^{1/4} ≤ a_u^{1/4}` by `STBctl_mono`.
**§26 lemmas:** `StochDomAt.of_subset_whp`, `of_subset_compl` are absent from `RBM3D/Defs/StochDomAt.lean` (grep: no match; `of_subset`, `of_subset_union` only); the probe proofs use `P(bad) ≤ 2N^{-(D+1)} ≤ N^{-D}` (`eventually_two_mul_rpow_le`, exists), `N ≥ 2` from `hsize`: true as stated, to be ported.
**§29 checks** (statements with a time window): (1) `0 ≤ s` is needed in rows 5, 11, 15 (`a_s·W^d = 1.0e-6` at `s=-10^6`: bound false without it); `t<1`, `t ≤ lemT z` from `lemT_lt_one`; rows 6, 16 need only `s ≤ u ≤ t < 1`. (2) no statement of the cut contains `ℓ` (the `ilambda>L` regime is irrelevant; `scaleFacts_ellT_ratio` is not used). (3) no `L^d ≤ W^K` is used (R1 uses `W ≥ N^𝔠`; `a_s⁻¹ ≤ N` uses `Bparam ≥ L^{-d}`). (4) pin hypotheses are `∀ n`; every derived fact (rows 2, 3, 7–11, 17, `STConStInd`, `Admissible`) is `∀ᶠ n`; positivity `a_u > 0` uses `∀ n`, `t_n<1`. Constants: `c₁, C_d=2·3^d, (2/c₁)^k, 2(𝔡⁻²+1)` depend on `κ, d, 𝔡, k` only.

### (ii) Concrete instance (`sz0`, d=3; `z_n = 1/2 + iN_n^{-4/5}`, `flow_z0`, `sz0_admissible`)
Hypotheses of all targets: `STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (merged, `Induction/Defs.lean:435`), `s ≡ 0 < t ≡ 1/16 ≤ lemT z_n`, `STConStInd 1/100 s t`; `STKbound`, `STLK s`, `STLocalMax s`, `STGbEXPii/ij` stay hypotheses (other gates' pins). Limit computations for the external-type hypotheses: rows 3, 7–11 at `s=0`, all `n < 80`.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2079/pre2.py` (mpmath, 80 digits). Output, verbatim:
```
c0=min(2*c*d,eps/2)= 0.03333333333333333 ; c1=sqrt(2k)/2= 0.22360679774997896 ; Cd=2*3^d= 54
n<60: Admissible(1/6,1/10)+locDomain(1/10,1/10): True ; lemT>=1/16=t, 1-lemT>=Imz/16, N^(-1+eps/2)<=1-lemT: True
STConStInd(cd=1/100) at s=0,t=1/16, n<60: True ; n=0: a_t^c=0.9020 <= 0.9375
failing n in 0..79: R1: none; F3: none; F4: [0, 1]; F5: none; F6: none; F7: none; F8: none; A>=W^-d/(lam^2+1): none
n=0 L=4 W=32 lam=1.562e-02 N=2097152 A_0=3.0987e-05  F4 lhs=4.249e-01 rhs=3.511e-02
n=2 L=12 W=7776 lam=2.143e-05 N=812479653347328 A_0=2.1281e-12  F4 lhs=1.930e-04 rhs=5.234e-04
n=0 (s,u,t)=(0.0000,0.0312,0.0625) hyp:True | 3.199e-05 <= a_s^(1-c)=3.438e-05 <= a_s^(14/15)=6.191e-05: True | a_u<=a_s^(1-c):True | (l_u/l_s)^2<=(1-s)/(1-t):True
n=0 (s,u,t)=(0.0625,0.0938,0.1250) hyp:True | 3.419e-05 <= a_s^(1-c)=3.664e-05 <= a_s^(14/15)=6.575e-05: True | a_u<=a_s^(1-c):True | (l_u/l_s)^2<=(1-s)/(1-t):True
n=3 (s,u,t)=(0.0000,0.0312,0.0625) hyp:True | 2.935e-14 <= a_s^(1-c)=3.883e-14 <= a_s^(14/15)=2.274e-13: True | a_u<=a_s^(1-c):True | (l_u/l_s)^2<=(1-s)/(1-t):True
n=3 (s,u,t)=(0.0625,0.0938,0.1250) hyp:True | 3.137e-14 <= a_s^(1-c)=4.140e-14 <= a_s^(14/15)=2.415e-13: True | a_u<=a_s^(1-c):True | (l_u/l_s)^2<=(1-s)/(1-t):True
d=3, L=3,4,8: #{zdistInf<=1} = [27, 27, 27] (3^d=27); #{zdistD<=1} = [7, 7, 7] (2d+1=7)
u=0.0312, loops=B=3.199e-05: gexRHS=4.666690e-02 (#pairs=729) <= 2*9^d*B+W^-d=4.666690e-02: True; 25B+W^-d=8.302e-04 < gexRHS
u=0.0938, loops=B=3.419e-05: gexRHS=4.988241e-02 (#pairs=729) <= 2*9^d*B+W^-d=4.988241e-02: True; 25B+W^-d=8.853e-04 < gexRHS
W^-d<=2(lam^2+1)a_s(1-s)/(1-u), 0<=s<=u<1/2, n<50: True
s=-10^6 (0<=s dropped): a_s*W^d=1.016e-06 -> W^-d<=C*a_s fails
```
Reading: the window `[0,1/16]` has positive length; `n=0` (`L=4,W=32,N=2097152`) satisfies every hypothesis; F4 holds from `n=2` (`N≈8·10^14`), all other `∀ᶠ` facts from `n=0` (no astronomical witness; `g=lam→0` at `sz0`, the crude `𝔡`-threshold of row 11 is not needed). The ported constants `25`, `5` are false for the merged `STgexRHS` at `d=3` (last two gexRHS lines: `25B+W^{-d}` is below the actual value).

### Verdicts
- `Step1TargetV3` (d-form), rows 1–17, `s1_ratio_pt`, `s1_ratio_ev`, F3–F8, `s1_loop_det`, `s1_h55`, `s1_LI`, `s1_gexRHS_le`, `s1_near_card`, `s1_wl_det`, §26 lemmas `StochDomAt.of_subset_whp`, `of_subset_compl`: **PASS** (all exponents close; every change above is forced by the merged vocabulary: `Bctl` for `scaleM⁻¹`, `zdistInf`, two σ in `STgexRHS`).
- Ticket corrections for stage 1b: (1) `s1_near_card` is `3^d`, not `2d+1`; (2) constants `25 → 2·9^d`, `26 → 2·9^d+1`, `6 → 2·3^d`; (3) `s1_scaleM_le_W2` is deleted (no d ≥ 3 form), `S1Std` gets `hWO`; (4) `s1_card_block*` lie after the cut (S1-36).
- Overall: **PASS**.

## (a′) Preflight corrections — Sat Oct  3 22:48:23 UTC 2026
Clarifications of (a); none changes a verdict.
1. Rows 5, 15 give `W^{-d} ≤ 2(g²+1) a_s (1-s)/(1-u)`; Lean proves `W^{-d} ≤ (g²+1) a_u` (`s1_Wd_le_Bctl`, `0 ≤ u < 1`) and uses `(1-s)/(1-u) ≥ 1`: no factor 2.
2. Row 9 takes `c' = c₀/4`, which needs `d ≥ 2`; Lean takes `c' = c₀/8` (any `d ≥ 1`; `d ≥ 1` is `s1_d_pos`, from `N → ∞`).
3. Rows 12, 14: `s1_wl_det`, `s1_gexRHS_le` are stated at a sample `ω` in the merged ST vocabulary (`STGM`, `STgexRHS`, `STindMax`, `STomegaC`), not at a matrix.

## (b) Script output — report assembled Sat Oct  3 22:48:23 UTC 2026
Branch `t/T2079`, HEAD `be32ccb` (working tree clean: `git status --short` empty); every output below is for this HEAD.  Sole files: `RBM3D/Induction/Step1Setup.lean` (new, 1554 lines), `RBM3D/Test/Axioms.lean` (one registry line).

```
$ lake build RBM3D.Induction.Step1Setup 2>&1 | tail -2        # in /Users/junyin/Lean_proof/RBM3D-wt/T2079
Build completed successfully (3330 jobs).
$ lake build 2>&1 | tail -1     # whole library, root `#assert_rbm_axioms` included (the root does not import the new module; the hub adds it at merge)
Build completed successfully (3819 jobs).
$ lake env lean axioms_check.lean   # one `#print axioms` per public new name (67: 60 in sections 0-6, 7 helpers in section 7)
65 of 67 depend on exactly [propext, Classical.choice, Quot.sound]; the others:
'RBM.Ind.s1_one_le_L' depends on axioms: [propext, Quot.sound]
'RBM.Ind.s1_one_le_W' does not depend on any axioms
selected targets:
'RBM.StochDomAt.of_subset_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.StochDomAt.of_subset_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.Step1TargetV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_ratio_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_F4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_loop_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_h55' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_LI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_near_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_gexRHS_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_wl_det' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Registry (ST1-COMMON item 8): `Step1TargetV3` is a `Prop` that `stStep1_of_target` takes as hypothesis and no theorem here proves: owed (S1-36).  Pre-check:
```
$ git diff main...t/T2079 -- RBM3D/Test/Axioms.lean | grep "^+ " | cut -c1-175
+   `RBM.Ind.Step1TargetV3, -- Step 1 of `lem:main_ind` (`1_2:1317-1328`) under `STGbEXPii`, `STGbEXPij`, RBM2D `Step1TargetV3` (`Induction/Step1.lean:84`): proved by S1-36 (T
$ lake env lean registry_check.lean 2>&1 | (head -3; tail -1 | cut -c1-150)   # import RBM3D; import RBM3D.Induction.Step1Setup; #assert_rbm_axioms
axiom audit: 2618 theorems, 1080 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 4 of 93 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what ea
exit code: 0  (of `lake env lean registry_check.lean`)
```

Target statements, extracted from the file by script (`extract.py`; docstrings and proofs removed):
```
-- Step1TargetV3 (Step1Setup.lean:149)
def Step1TargetV3 (d : ℕ) : Prop := STGbEXPii d → STGbEXPij d → STStep1 d
-- of_subset_whp (Step1Setup.lean:105)
theorem of_subset_whp (hsize : Tendsto size atTop atTop) {U₁ : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {f g : ∀ l, U₁ l → Ω → ℝ} {Ξ :
    ℕ → Set Ω} (h : StochDomAt P size f g) (hΞ : HighProbAt P size Ξ) (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
    badSetAt size ξ ζ τ l ⊆ badSetAt size f g τ' l ∪ (Ξ l)ᶜ) : StochDomAt P size ξ ζ
-- of_subset_compl (Step1Setup.lean:125)
theorem of_subset_compl {ξ ζ : ∀ l, U l → Ω → ℝ} {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ) (hsub : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in
    atTop, badSetAt size ξ ζ τ l ⊆ (Ξ l)ᶜ) : StochDomAt P size ξ ζ
-- s1_ratio_pt (Step1Setup.lean:215)
theorem s1_ratio_pt (n : ℕ) {c s u t : ℝ} (hc : 0 < c) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1) (hstep : (sz.Bctl n t) ^ c ≤ (1 -
    t) / (1 - s)) : sz.Bctl n s * ((1 - s) / (1 - u)) ≤ (sz.Bctl n s) ^ (1 - c)
-- s1_ratio_ev (Step1Setup.lean:340)
theorem s1_ratio_ev (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n → sz.Bctl n (s n) * ((1 - s n)
    / (1 - u)) ≤ sz.Bctl n (s n) ^ ((14 : ℝ) / 15)
-- s1_F3 (Step1Setup.lean:356)
theorem s1_F3 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∃ τ₀ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ τ₀ * (s1B sz s n) ^ ((1
    : ℝ) / 2) < (s1B sz s n) ^ ((1 : ℝ) / 4)
-- s1_F4 (Step1Setup.lean:389)
theorem s1_F4 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 * (3 : ℝ) ^ d) * (s1B sz s n) ^ ((7 : ℝ) /
    15) ≤ ((sz.size n : ℕ) : ℝ) ^ (-ε) * ((s1B sz s n) ^ ((1 : ℝ) / 4) / 2)
-- s1_F5 (Step1Setup.lean:438)
theorem s1_F5 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∃ c' > (0 : ℝ), ∀ᶠ n : ℕ in atTop, 2 * (s1B sz s n) ^ ((1 : ℝ) / 4) ≤ ((sz.W n :
    ℕ) : ℝ) ^ (-c')
-- s1_F6 (Step1Setup.lean:477)
theorem s1_F6 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (s1B sz s n) ^ ((1 : ℝ) / 4) / 2
-- s1_F7 (Step1Setup.lean:496)
theorem s1_F7 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∀ᶠ n : ℕ in atTop, (s1B sz s n) ^ ((1 : ℝ) / 4) ≤ 1
-- s1_F8 (Step1Setup.lean:504)
theorem s1_F8 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (s1B sz s n) ^ ((14 : ℝ) / 15)
-- s1_loop_det (Step1Setup.lean:653)
theorem s1_loop_det {L W : ℕ} [NeZero L] [NeZero W] {E u c₁ : ℝ} (hc₁ : 0 < c₁) (hm : c₁ ≤ (mE E).im) (hu : u ≤ 1 / 2) (M : Matrix
    (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) : ‖loopFine d L W
    M (zt E u) σ a‖ ≤ (2 / c₁) ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1)
-- S1H55 (Step1Setup.lean:681)
def S1H55 (sz : Sizes d) (E s : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L
    n))) (fun n p ω => ‖Sizes.Lloop sz n (E n) (s1T1 s n) p.1 p.2 ω‖) (fun n _ _ => (sz.Bctl n (s1T1 s n)) ^ (k - 1))
-- s1_h55 (Step1Setup.lean:693)
theorem s1_h55 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (hIK : STLK sz E s) (hK : STKbound sz E) : S1H55 sz E s
-- s1_LI (Step1Setup.lean:774)
theorem s1_LI (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s) (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) {k : ℕ} (hk :
    1 ≤ k) : sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => sz.STomegaC n (E n) (u n) 2 ω *
    ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
-- s1_near_card (Step1Setup.lean:882)
theorem s1_near_card {L : ℕ} [NeZero L] (a : Zd d L) : ((Finset.univ.filter (fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1)).card :
    ℝ) ≤ 3 ^ d
-- s1_gexRHS_le (Step1Setup.lean:1015)
theorem s1_gexRHS_le (n : ℕ) (E u B : ℝ) (ω : sz.SeqΩ) (hL : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), ‖Sizes.Lloop sz n E
    u σ b ω‖ ≤ B) (a b : Zd d (sz.L n)) : sz.STgexRHS n E u ω a b ≤ 2 * 9 ^ d * B + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
-- s1_wl_det (Step1Setup.lean:1064)
theorem s1_wl_det (n : ℕ) (ω : sz.SeqΩ) {E u a c' g Nτ : ℝ} (hE : |E| ≤ 2) (hc' : 0 < c') (hx : s1xM d (sz.L n) (sz.W n) E u
    (sz.seqHflow n u ω) ≤ 2 * a) (hΩ : 2 * a ≤ ((sz.W n : ℕ) : ℝ) ^ (-c')) (hNτ : 1 ≤ Nτ) (hg : 0 ≤ g) (hWg : (((sz.W n : ℕ) : ℝ)
    ^ d)⁻¹ ≤ g) (hLoop : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), sz.STomegaC n E u 2 ω * ‖Sizes.Lloop sz n E u σ b ω‖ ≤
    Nτ * g) (hii : ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), sz.STindMax n E u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω *
    ‖sz.STGM n E u ω p.1 p.2‖ ^ 2 ≤ Nτ * sz.STmaxLoop2 n E u ω) (hij : ∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W
    n) // p.1 ≠ p.2}, sz.STindMax n E u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖Sizes.Gt sz n E u true ω p.1.1 p.1.2‖ ^ 2 ≤ Nτ *
    sz.STgexRHS n E u ω (sz.STblk n p.1.1) (sz.STblk n p.1.2)) : ∀ i j, ‖sz.STGM n E u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g
```

Statement diff against RBM2D (ST1-COMMON item 6), by script on the numeric literals of each statement (the `d`-dependent content); every residual difference is listed in the narrative:
```
numeric literals of the statements: only in RBM2D (c9a24cf:line) | only in Step1Setup (line)
s1_ratio_pt       159 | 14 15 2 2 30   -> s1_ratio_pt       215 | 1
s1_ratio_ev       273 | 2              -> s1_ratio_ev       340 | 1 1
s1_F3             300 | -              -> s1_F3             356 | -
s1_F4             329 | 6              -> s1_F4             389 | 2 3
s1_F5             382 | -              -> s1_F5             438 | -
s1_F6             418 | -              -> s1_F6             477 | -
s1_F7             439 | -              -> s1_F7             496 | -
s1_F8             445 | 2              -> s1_F8             504 | -
s1_loop_det       525 | 1 2            -> s1_loop_det       653 | -
s1_h55            581 | -              -> s1_h55            693 | -
s1_LI             641 | 0 2            -> s1_LI             774 | 1
s1_near_card      810 | 5              -> s1_near_card      882 | -
s1_gexRHS_le      823 | 0 25 3         -> s1_gexRHS_le     1015 | 2 2 9
s1_wl_det         918 | 0 1 26 3       -> s1_wl_det        1064 | 2 2 9
s1_size_eq        122 | 2              -> s1_size_eq        180 | -
s1_W_sq_le_size   135 | 2              -> s1_W_pow_le_size  193 | -
```

Compiled nonempty instances (section 7, lines 1135-1554, `d = 3`, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠_d = 1/100`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`).  `S1Std` is discharged completely (`s1Std_sz0`; windows `[0,1/16]`, `[1/16,3/4]`, `[1/2,3/4]`).  Script: target -> instance line(s); every public declaration is applied in section 7:
```
69 instance blocks; applied public declarations: 60 of 60
s1_std_of_stFlow:1142 s1_c0_pos:1150 s1_s_lt_one:1151 s1_B_pos:1152 s1_Bu_pos:1153 s1_c1_pos:1154 s1_size_eq:1157
  s1_one_le_L:1159 s1_one_le_W:1160,1405,1441 s1_one_le_size:1161 s1_W_pow_le_size:1162 s1_hsize:1163 s1_d_pos:1164
  s1_inv_rpow:1165 s1_bulk:1166,1267 s1_apow_le:1169 s1_a_le:1181 s1_B_tendsto:1184 s1_B_ev_pow:1185 s1_B_le_one:1187
  s1_N_pow_ev:1188 s1_lam_sq_le:1190 s1_Wd_le_Bctl:1192 s1_ratio_pt:1197 s1_ratio_ev:1203 s1_F3:1208 s1_F4:1211 s1_F5:1214
  s1_F6:1216 s1_F7:1218 s1_F8:1219 s1_loop_det:1267 s1T1:1278 s1_Kbound_seq:1283 s1_h55:1291,1293,1299,1310,1320
  s1_LI:1299,1310,1320 s1_near_card:1333 s1xM:1346,1352,1355,1362,1366,1441 s1xM_le:1346 s1xM_ge:1352 s1xM_nonneg:1355
  s1_llErrMat_eq:1357 s1_gMax_le:1362 s1xM_le_add:1366 s1_STGM_norm:1370,1405 s1_omegaC_eq_one:1376,1405,1441
  s1_indMax_eq_one:1378 s1_gexRHS_le:1383 s1_wl_det:1405,1441 s1_stochDom_unit:1474 s1_highProb_of_pt:1483,1490
  s1_pt_of_highProb:1490 of_subset_whp:1500 of_subset_compl:1509 s1_omegaC_le_one:1521 Step1TargetV3:1543 stStep1_of_target:1543
```
The pin instance, verbatim (`STKbound`, `STLK`, `STLocalMax`, `STGbEXPii`, `STGbEXPij`, `Step1TargetV3` itself are hypotheses: other gates / S1-36; `STConStInd`, `STFlow`, the times are discharged):
```
example (h : Step1TargetV3 3) (hii : STGbEXPii 3) (hij : STGbEXPij 3)
    (hK : STKbound sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  stStep1_of_target h hii hij (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 100) (by norm_num) le_rfl (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    zero_le_lemT (fun n => by simp only [sInst, tInst]; norm_num) sixteenth_le_lemT hK hLK hLoc
    (conStInd_inst (by norm_num))
```
`s1_wl_det` has an instance at `u = 0` with no premise left (matrix `0`, `G_0 = m I`; line 1405) and at `u = 1/16`, where the event premise `‖G_u - m‖_max ≤ 2a` and the pins `STGiiGEX`, `STGijGEX` at `ω` stay hypotheses (line 1441).  DECISIONS §29 (1): `0 ≤ u` cannot be dropped from `s1_Wd_le_Bctl` (compiled counterexample at `u = -10^6`, line 1527).

Name clash (CLAUDE.md §5.2): every public new name searched as a word in `main:RBM3D/`:
```
$ git -C /Users/junyin/Lean_proof/RBM3D grep -n -w -F -e <name> main -- RBM3D   # for each name of pub_names.txt
public new names: 67
names with a word match in main:RBM3D/*.lean: 0
$ grep -n -E "sorry|admit|native_decide|^axiom" RBM3D/Induction/Step1Setup.lean; echo "grep exit $?"; grep -n -w "decide" RBM3D/Induction/Step1Setup.lean
grep exit 1
1337:  decide
```

Ports (RBM2D `c9a24cf`, `RBM2D/Induction/Step1.lean:1-965`; RBM1D is not read, its citations (`Hierarchy/Step1.lean`, commit `86573b9`) are copied from the RBM2D docstrings):
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks rev-parse --short c9a24cf
c9a24cf
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Step1.lean
 RBM2D/Induction/Step1.lean | 259 ++++++++++-----------------------------------
 1 file changed, 56 insertions(+), 203 deletions(-)
$ git diff --stat main...t/T2079
 RBM3D/Induction/Step1Setup.lean | 1554 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    1 +
 2 files changed, 1555 insertions(+)
```

Which of the 60 RBM2D declarations S1-36 needs (script: names of `Step1:1-965` occurring in `Step1:967-1515`); each has a public counterpart here (`s1_Ms_pos`, `s1_Mu_pos`, `s1Ms`, `s1_std_of_mainIndHyp` are `s1_B_pos`, `s1_Bu_pos`, `s1B`, `s1_std_of_stFlow`):
```
RBM2D declarations of Step1:1-965: 60; used by Step1:967-1515 (S1-36): 30
Step1TargetV3 s1_bulk s1_inv_rpow s1_one_le_L s1_one_le_size s1_hsize S1Std s1_std_of_mainIndHyp s1_Ms_pos s1_Mu_pos s1_ratio_ev
s1Ms s1_F3 s1_F4 s1_F5 s1_F6 s1_F7 s1_F8 s1_highProb_of_pt s1_pt_of_highProb s1_stochDom_unit S1H55 s1_h55 s1_LI s1xM s1xM_ge
s1xM_le s1_gMax_le s1xM_le_add s1_wl_det
```

`d = 2` tokens of the cut (ST1-COMMON item 2; portmap P.7 row 86 classes W2, L2, N2, inv2, d=2, Z2/zdist2, scal; the class `1/5` does not occur):
```
RBM2D Step1.lean:1-965, token counts per declaration (regex; classes of portmap P.7 row 86):
s1_size_eq{L2:1,N2:2} s1_one_le_size{N2:2} s1_W_sq_le_size{W2:1,L2:1,N2:1} s1_scaleM_le_W2{W2:9,L2:3,N2:3,scal:3}
  s1_ratio_pt{L2:4,scal:23,ex30:15} s1_Ms_ge{N2:1,scal:1} s1_Ms_tendsto{N2:2,scal:1} s1_Ms_pos{scal:2} s1_Mu_pos{scal:2}
  s1_Ms_ev_pow{scal:1} s1_one_le_Ms{scal:1} s1_ratio_ev{scal:4} s1Ms{scal:1} s1_F3{N2:3} s1_F4{N2:4} s1_F5{W2:1,N2:2}
  s1_F6{N2:6,scal:1} s1_F7{inv2:1} s1_F8{W2:3,inv2:2,scal:1} s1_ellT_nonneg{inv2:1,d=2:1,scal:2} s1_loop_det{inv2:1,Z2:1,scal:5}
  s1_Kbound_seq{N2:2,Z2:1,scal:1} S1H55{Z2:1,scal:1} s1_h55{Z2:3,scal:9} s1_LI{Z2:3,scal:40} s1_norm_loopPM{Z2:2}
  s1_mem_sbSupport{Z2:1,zd2:2} s1_near_card{inv2:1,Z2:3,zd2:2} s1_gexRHS_le{W2:3,inv2:3,Z2:13,zd2:15}
  s1_wl_det{W2:1,inv2:1,Z2:2}
TOTAL: W2=18 L2=9 N2=28 inv2=10 d=2=1 Z2=30 zd2=19 scal=99 ex30=15
Step1Setup.lean, code outside comments, same regexes: W2=0 L2=0 d=2=0 Z2=0 zd2=0 scal=0 ex30=0 (N2/inv2 left are d-generic `sz.size n`, real `(𝔡⁻¹)^2`)
```
Disposition: `W²`, `(WL)²`, `W⁻²` -> `W^d`, `(WL)^d = sz.size n`, `(W^d)⁻¹`; `Z2 L` -> `Zd d L`; `zdist2` -> `zdistInf d L`; `scaleM` -> `sz.Bctl n u` (`a_u = W^{-d}B_{u,0}`); `ellT`, `sbSupport`, `s1_scaleM_le_W2`, `s1_ellT_nonneg` have no `d ≥ 3` use and are dropped; `spectralM`, `spectralZ` -> `mE`, `zt`; the exponent `30` -> `𝔠_d`.

### Narrative
* **Cut.** S1-35 = `Step1:1-965` (60 declarations, `end Bridge` at `:965`); S1-36 = `:967-1515` (`WeakLawSeq` incl. `s1_card_block*` `:983-1000`, `Net`, `Bootstrap`, `step1` `:1378`, `Checks`).  Both declaration lists and the fate of every RBM2D declaration: module docstring `Step1Setup.lean:29-62`.
* **Public / private.** Public (S1-36 needs 30 of the RBM2D declarations, list above): `Step1TargetV3`, `S1Std`, `s1_std_of_stFlow`, `s1_bulk`, `s1_inv_rpow`, `s1_one_le_L/W/size`, `s1_hsize`, `s1_ratio_pt/_ev`, `s1_B_*`, `s1B`, `s1_F3`-`s1_F8`, `s1_highProb_of_pt`, `s1_pt_of_highProb`, `s1_stochDom_unit`, `S1H55`, `s1_h55`, `s1_LI`, `s1xM*`, `s1_gMax_le`, `s1_wl_det`, and the rest of `pub_names.txt`.  Private: `s1_mul_rpow_le`, `s1_pt_of_le`, `s1_blockMat_herm`, `s1_zdist_le_one`, `s1_pt_of_ev_or` (new), two helpers of section 7.
* **`Step1TargetV3`** `:= STGbEXPii d → STGbEXPij d → STStep1 d`: both conjuncts `STStep1Loop`, `STStep1Weak` of `STStep1` (whose own hypotheses `STKbound`, `STLK s`, `STLocalMax s`, `STConStInd` replace `KboundConcl`, `InitLK`, `InitLocal`, `CondStInd`); the two GbEXP parts are the only addition, as RBM2D's `GbEXPHypV3`.  S1-36 proves it.  Map `S1Std`/`MainIndHyp` -> `STFlow`: `Step1Setup.lean:72-80`; `S1Std` has the new fields `hWO` (`(eq:WO)`, needed by `scaleFacts_R1`), `h𝔠d`, `h𝔠d'`.
* **Scales.** `M_s⁻¹` is `a_s = sz.Bctl n s`.  `s1_a_le` is `scaleFacts_R1`; `s1_ratio_pt` is `closure_scale` (`a_s(1-s)/(1-u) ≤ a_s^{1-𝔠_d}`, no `0 ≤ s`); `s1_ratio_ev` needs `𝔠_d ≤ 1/15` (pin: `1/100`).  F3-F8 keep the exponents `1/2, 1/4`, `7/15`, `1/4`, `14/15`; `τ₀ = ε = c₀/8`, `c' = c₀/8`; `C_d = 2·3^d` (`(2·3^d)² = 4·9^d ≥ 2·9^d+1`) replaces `6`.
* **`d`-dimensional exponents asked by the ticket.** `s1_size_eq`: `N = (WL)^d`; `s1_W_sq_le_size` -> `W^d ≤ N`; `s1_scaleM_le_W2` deleted (replaced by `STBctl_ge`, `cont_inv_size_le_Bctl`); `s1_near_card`: the `zdistInf` ball has `3^d` blocks (`decide`: `27` at `d = 3`, `L = 4`, lines 1336-1337; the ticket's `2d+1 = 7` is the `zdistD` ball, (a) script line 49); `s1_card_block*` lie after the cut (S1-36).
* **Residual differences from RBM2D** (forced by the merged vocabulary): `S1H55`, `s1_h55`, `s1_LI` are `PrecPT` over `(σ,a)` without `Unit ×` and use `STomegaC` for `1(‖G‖_max ≤ 2)` (merged `ConArgPin` shape); `s1_h55` takes `STLK`, `STKbound` (`Prec`, read per time by `perTimeOfStochDomAt`); `s1_loop_det` keeps `W^{-d}`, and `s1_Wd_le_Bctl`, `s1_lam_sq_le` give `W^{-d} ≤ (𝔡⁻²+1)a_s` eventually (`(eq:WO)`), so the `u < 1/2` branches use the eventual case split `s1_pt_of_ev_or`; constants `2·9^d`, `2·9^d+1` and the sample-level form of `s1_gexRHS_le`, `s1_wl_det`.
* **DECISIONS §29** (docstring `Step1Setup.lean:81-87`): (1) `0 ≤ s` is used in `s1_Wd_le_Bctl`, `s1_F6`, `s1_F8`, the `u < 1/2` branches (counterexample compiled above); `s1_ratio_pt` and the `u ≥ 1/2` branch use `s ≤ u ≤ t < 1` only; (2) no `ℓ` occurs; (3) no `L^d ≤ W^K`; (4) the `S1Std` fields are `∀ n` as in `STStep1`, every derived fact is `∀ᶠ n`; constants depend on `κ, 𝔡, d, k` only.
* **Reuse (not copied):** `conArg`, `scaleFacts_R1`, `scaleFacts_etaT_div_etaT`, `STBctl_pos/_mono/_xmono/_ge`, `closure_scale`, `cont_bulk`, `cont_inv_size_le_Bctl`, `Green.llErrMat`, `Green.v3_premises_of_stFlow`, `norm_loopM_le_sharp`, `PerTimeCalc.PerTime.*`, `perTimeOfStochDomAt`, `stochDomAt_of_perTimeDomAt`.  DECISIONS §26: `of_subset_whp`, `of_subset_compl` are not in `Defs/StochDomAt.lean` (`of_subset`, `of_subset_union` only); ported with the probe proofs (`752e027:RBM3D/Probe/T2015Pins.lean:907,926`), same names, namespace `RBM.StochDomAt`.

## (c) Verified Mathlib names (used and compiled)
`Real.rpow_le_rpow`, `Real.rpow_neg`, `Real.inv_rpow`, `Real.rpow_add`, `Real.rpow_mul`, `Real.mul_rpow`, `Real.rpow_le_one`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.one_le_rpow`, `Real.zero_rpow`, `Real.rpow_neg_one`, `Real.sqrt_pos`,
`tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_iff`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `tendsto_inv_atTop_zero`, `tendsto_pow_atTop`, `gt_mem_nhds`, `Filter.Tendsto.eventually_ge_atTop`, `Finset.prod_le_pow_card`, `Finset.card_le_three`, `Finset.card_le_two`,
`Fintype.mem_piFinset`, `Fintype.card_piFinset`, `Finset.sup'_le`, `Finset.le_sup'`, `Finset.sup_le_iff`, `Finset.card_image_le`, `Finset.card_le_card`, `div_le_div_of_nonneg_right`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `mul_le_of_le_one_left`,
`Matrix.nonsing_inv_eq_ringInverse`, `Matrix.IsHermitian.submatrix`, `norm_le_norm_sub_add`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `Nat.cast_sub`, `inv_anti₀`, `one_le_div`, `le_div_iff₀`.
Not usable as written: `Finset.prod_le_prod fun _ _ => Nat.zero_le _` followed by a second argument (compiler: "Function expected"; `Finset.prod_le_pow_card` used); `if_pos`, `if_true` (deprecated; `simp [h]`, `ite_true` used).

## (d) Open issues and paper-delta candidates
* **T2079a** (`Step1TargetV3`): the d-form is `STGbEXPii d → STGbEXPij d → STStep1 d`; RBM2D's `GbEXPHypV3 d (κ/2) c τ` is per size sequence and `c, τ`, the pins quantify over every `κ ε 𝔡 ε₀`; `STGbEXPav` unused.
* **T2079b** (constants): `s1_near_card` `≤ 3^d` (`zdistInf` ball; ticket `2d+1`); `s1_gexRHS_le` `2·9^d B + W^{-d}` (RBM2D `25 B + W⁻²`); `s1_wl_det` `(2·9^d+1) N^{2τ} g` (RBM2D `26`); `C_d = 2·3^d` (RBM2D `6`).
* **T2079c** (`S1Std`): new fields `hWO` (cf. T2045a), `h𝔠d`, `h𝔠d'`; RBM2D's exponent `30` of `CondStInd` is the parameter `𝔠_d` of `STConStInd`; `s1_ratio_ev` needs `𝔠_d ≤ 1/15` (pin `1/100`).
* **T2079d** (regime `u < 1/2`): `‖𝓛‖ ≤ (2/c₁)^k (W^{-d})^{k-1} ≤ C a_s^{k-1}`, `C = (2/c₁)^k (𝔡⁻²+1)^{k-1}`, needs `0 ≤ s` and `ilambda ≤ 𝔡⁻¹` (eventually); RBM2D `M_u ≤ W²` has no analogue.
* **T2079e** (`F5`): `c' = c₀/8` (RBM2D `c₀/4` with `W² ≤ N`), valid for every `d ≥ 1`.
* Open for S1-36: apply `s1_wl_det` on the events given by `Prec.whp` of `STGiiGEX`, `STGijGEX` (same shape as `hii`, `hij`) and `s1_highProb_of_pt` of `s1_LI` at `k = 2`; `s1_card_block*`, `s1_card_loops`, `Net`, `Bootstrap`, `step1` are S1-36.  The root import `import RBM3D.Induction.Step1Setup` is added by the hub at merge.
* RBM2D at `HEAD` (`9e0f275`) has a shorter `Step1.lean` (1368 lines, diff-stat above); the port is from `c9a24cf` as the ticket says.

