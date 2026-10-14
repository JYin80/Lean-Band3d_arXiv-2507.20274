Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 04:25:45 UTC 2026

Targets (mathematics only): D1 the family step `BAMainIndFamTL` (hypotheses at `s` for every `z' ∈ Fam(s)`, conclusions at `t` for every `z' ∈ Fam(t)`) and the wrapper `S1 → Fam`; D2 the family Step-1 call (`baStep1_holds'`, K2); D3 members are flows after a finite modification at `(κ', ε')`; D4 the V price. File:line below are in `/Users/junyin/Lean_proof/RBM3D-wt/T2503/RBM3D/` (HEAD 6b359e50).

### (i) Exponent table

| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `d` | 3 | `3 ≤ d` (pins); `2 ≤ d` for `baStep1_holds'` (`BA/Step1Prime.lean:892`) | 0 / 1 |
| 2 | `𝔠d` (family step: `∃` before `𝔠, sz, z`) | `1/100` | `0 < 𝔠d ≤ 1/100`; `BAStep1` is `∀ 𝔠d ∈ (0,1/100]` (`BA/Step1Fam.lean:361`), so any value of the wrapper's S1 is accepted by the Step-1 call | 0 (upper end) |
| 3 | `(κ, ε, 𝔡, 𝔠)` | `(1/4, 1/10, 1/10, 1/6)` | `BAFlow sz κ ε 𝔠 𝔡 z` = `Admissible ∧ ∀ n, BAdom` (`BA/FlowPins.lean:389`); `BAdom`: `κ ≤ Im m`, `N^{-1+ε} ≤ Im z ≤ 1` (`BA/MFixedPoint.lean:435`). Along `sz0`: `Im m ≥ 4/5`, `11/30 ≤ Im z ≤ 7/10`, `N^{-9/10} ≤ 1/4` (`FlowPins.lean:1168, 1197, 1205, 1214`; flow at `κ = 1/2`, `BAdom` monotone in `κ`) | `Im m`: 0.55; `Im z` vs `N^{-0.9}`: `11/30 - 1/4 = 0.1167` (actual `N_0^{-0.9} = 2.04e-6`) |
| 4 | `κ' = c_κ(κ) κ`, `c_κ(κ) = √min(κ/(κ+1), 1/2)` (`Step1Fam.lean:488, 624-626`) | `c_κ(1/4) = 0.44721`, `κ' = 0.11180` | `0 < κ' ≤ κ` (`BAFlowMember`, `BA/Step1Boot.lean:133`) | `κ - κ' = 0.1382` |
| 5 | `ε' = ε/2` (same proof) | `1/20` | `0 < ε' ≤ ε` | `ε - ε' = 1/20` |
| 6 | tail threshold `n₀` of the modification: `N_n^{-ε/2} < c_κ κ` for `n ≥ n₀` (`Step1Fam.lean:631-635`) | `n₀ = 5` (`N_5 = 2.13e20`, `N_5^{-1/20} = 0.0963 < 0.1118`) | a threshold in `n`, not a witness size; `sz0`: `N_n = 2^21 (n+1)^18` | `0.1118 - 0.0963 = 0.0155` |
| 7 | `c₁` | `1/3` | `0 < c₁ ≤ 1/2`; `BAWinBulk sz z c₁ κ` (`BA/CouplingWindow.lean:799`) | `1/2 - 1/3 = 1/6` |
| 8 | window bulk | `Im m(E, g') ≥ 3/5` on `[√(1-c₁) g₀, g₀]` (`sz0_win`, `Step1Fam.lean:769`, stated at `1/2`, `sz0_win_third` `:802`) | `κ ≤ Im m(E,g')` at `κ = 1/4` | `3/5 - 1/4 = 0.35` |
| 9 | window loss budget (`Step1Fam.lean:790-800`): `3/5 + 6 (3/640)/(3/5)^4` | `0.81701` | `≤ 41/50 = 0.82` (needs `1 - √(1-c₁) = 0.1835 ≤ ρ = 1/5 ≤ 3/10`) | `0.0030` (in `ρ`: `0.1` to `3/10`) |
| 10 | `T0_n = BAflowT0 sz0 zSeq n` | `17/25 ≤ T0_n ≤ 25/36` (`Step1Fam.lean:748, 753`) | `0 < T0 < 1` (`BAflow_T0_bounds`, `BA/Step1Trivial.lean:47`); `s < t ≤ T0` | `t = 1/2`: `0.18`; `s < t`: `0.4` |
| 11 | `1 - c₁` against `T0` | `2/3 ≤ 17/25` | cone `Fam(u) = {z': Es equal, min(T0, max(u, 1-c₁)) ≤ T0' ≤ T0}` (`Step1Trivial.lean:42`) has a non-main member only if `1-c₁ < T0` | `17/25 - 2/3 = 1/75 = 0.0133` (cone width at `s=1/10` and at `t=1/2`) |
| 12 | D3 (d), class `t_n = 0`: `Fam(0) = Fam(T0/2)` | `T0/2 ≤ 25/72 = 0.347` | `max(T0/2, 1-c₁) = 1-c₁`, i.e. `T0/2 < 1/2 ≤ 1-c₁` for every `c₁ ≤ 1/2`, `T0 < 1` (`BAFamZ_mono_max`, `Step1Fam.lean:172`) | `1 - c₁ - T0/2 = 0.319` here; `> 0` always |
| 13 | `(s, t)` | `(1/10, 1/2)` (also `(1/10, 17/25)`, narrow cone `[17/25, T0]`) | `0 ≤ s < t ≤ T0`; `STConStInd 𝔠d s t` (`Induction/Defs.lean:168`): `Bctl^{𝔠d} ≤ (1-t)/(1-s) < 1` eventually | ratio `5/9 < 1` (slack `4/9`); `16/45` for `17/25` |
| 14 | `STConStInd` threshold (`Bctl ≤ 2 (1-t)^{-1} W^{-3}`, `Induction/Defs.lean:472`, `s1Setup_conStInd_const` `Step1Setup.lean:1226`) | first `n` with `(4 W_n^{-3})^{1/100} ≤ 5/9`: `n = 27` (`W = 550731776`); for `t = 17/25`: `n = 557` | eventual in `n` | limit: `Bctl → 0`, `W_n → ∞` |
| 15 | regimes at `sz0`, `1 - t_n ≥ 1 - T0_n ≥ 11/36` vs `lam_n² ≤ 1/4096` | (iii) `STReg5III` holds (`lam² ≤ 1-t`), hence `STCaseI`, `STAny` | (i), (ii), (iv) need `1-s ≤ lam² ≤ 1/4096`, i.e. `s ≥ 0.99976 > T0` | (i), (ii), (iv) are vacuous at `sz0` (see verdict note) |
| 16 | tail passage (D4 (b)): `BAWinBulk_of_dom_holds` (`CouplingWindow.lean:836`) window at `κ/2` for `0 < lam ≤ Λ` | `κ = 1/2 → 1/4`, `Λ = 1/64` (instance `Step1Fam.lean:975-977`) | `Λ ≤ 𝔡⁻¹ = 10` | `10 - 1/64` |
| 17 | V forecast (D4, Q1 of supervisor 0342) | `≈ 12` (`11-14`) | first-line flag iff `≥ 15` | `3` rows to 15 from 12; `1` from 14 |

Quantifier closure checks (all from the files):
- Wrapper `S1 → Fam`: `κ', ε'` are fixed by `(κ, ε, 𝔡)` before `𝔠, sz, z` (`BAFlowMember`, `Step1Boot.lean:133-141`), so the wrapper's `𝔠d := 𝔠d_S1(κ', ε', 𝔡)` is a function of `(κ, ε, 𝔡)`, as the family step requires; `R sz s t` does not read `z`, so it passes to the modified flow `z''`.
- D2 (b): the six family conjuncts are `LK ∧ Decay ∧ DecayStrong ∧ LocalMax ∧ Exp2 ∧ TL2`; `BAStep1`'s premise is `Kbound ∧ LK(s) ∧ LocalMax(s)` = K2 plus conjuncts 1 and 4 (`.1`, `.2.2.2.1`). `T2503_FamStep1Call` reproduces `BAStep1`'s binder order (`Step1Fam:361-378`).
- K2: `Fam(s) ⊆ Fam(0)` needs only `0 ≤ s` (`BAFamZ_mono`, `Step1Boot.lean:173`); `baKbound_holds` (`KBound.lean:245`) is `∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow → STKboundgL`, so it applies at `(κ', ε')`; transfer by `STKboundgL_congr` (`Step1Fam.lean:247`) over `FlowFM.EvEq` (`baFMz_eqAt`, `:273`).
- TL2 congruence: `twL2'` reads `C.G n` and `twK` reads `C.M n` (`BA/TwistPins.lean:70, 76`); `FlowFM.EqAt` has fields `L K G M S eta m` (`Step1Fam.lean:187-197`), and `BATwistLoopLaw` is a `PrecL` over a type depending only on `sz.L n`, so `PrecL_congr` (`Step1Boot.lean:185`) applies.
- D3 base: `STBaseG` (`Induction/MainIndBase.lean:58`) and `baTwistLoopBase_holds` (`BA/TwistChain.lean:110`) are `∀ κ ε 𝔡 𝔠 > 0`-uniform over `BAFlow`, so they hold at `(κ', ε')` for `z''`; `STG0M` is the local hypothesis uniform over `BAFlow`. All base facts are at time `0`, tail-local through `EvEq`.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), `zSeq`, `(κ, ε, 𝔡, 𝔠) = (1/4, 1/10, 1/10, 1/6)`, `c₁ = 1/3`, `𝔠d = 1/100`, `s ≡ 1/10 < t ≡ 1/2 ≤ T0_n`, `R = STReg5III` (regime (iii)); the family premise at `s` for members of `Fam(s)` stays a local hypothesis (other gates' stochastic pins `STLKgL`, `STLocalMaxgL`, ...). Every deterministic hypothesis is discharged by rows 1-14: `BAFlow` at `κ = 1/4` (weakening of `flow_sz0`), `0 < lam_n`, `BAWinBulk sz0 zSeq (1/3) (1/4)` (from `sz0_win_third` at `1/2`), `s_n ≥ 0`, `s_n ≤ T0_n`, `s_n < t_n`, `t_n ≤ T0_n` (`half_lt_t0`, `FlowPins.lean:1254`), `R`, `STConStInd`. Family nondegenerate: `Fam(1/10) = Fam(1/2) = {z': Es equal, 2/3 ≤ T0' ≤ T0}`, width `≥ 1/75`; main flow and the `BAzSrc` member (`inst_BAFamZ_closed`) are inside.

Command and output (exact `Fraction` arithmetic for `sz0`, floats for the limits; script `.../scratchpad/T2503/inst.py`):

```
$ python3 -I inst.py
d=3>=3: True ; N_0=2^21: True ; lam_0=1/64: True
0<kappa'<=... flow kappa=1/4 <= Im m_S>=4/5: True slack 0.55
N^(-1+eps) at n=0: 2.0442456484533175e-06  <= 1/4 <= 11/30<=Im z<=7/10<=1: True
c1 in (0,1/2]: True slack 1/6
window rho: 1-sqrt(1-c1)= 0.18350341907227397  <= rho=1/5 <= 3/10
window budget 3/5+6*(3/640)/(3/5)^4 = 0.8170138888888889 <= 41/50: True slack 0.0029861111111111113
1-c1=2/3 <= T0lo=17/25: True slack 0.013333333333333334 ; t<=T0lo slack 0.18 ; s<t slack 0.4
Fam(s)=Fam(t)=[2/3,T0_n] since max(s,1-c1)=max(t,1-c1)=2/3: True
D3(d): T0/2 <= 25/72 = 0.3472222222222222  < 1-c1 ; slack 0.3194444444444444
t2=17/25<=T0lo; Fam(t2)=[17/25,T0_n]; 1-c1<t2: True
c_kappa(1/4)= 0.4472135954999579 kappa'= 0.11180339887498948 (<=1/4, slack 0.13819660112501053 ) eps'= 0.05
n0 (first n with N^(-eps/2)<c_k*kappa): 5 N_n0=2.130e+20 ; N^(-1/20)= 0.09629026439698388
(s,t)=(1/10,1/2): (1-t)/(1-s)=5/9<1; first n with (2/(1-t)W^-3)^(1/100)<=ratio: n=27, W=550731776
(s,t)=(1/10,17/25): (1-t)/(1-s)=16/45<1; first n with (2/(1-t)W^-3)^(1/100)<=ratio: n=557, W=1731095283096576
1-t=1/2 >= lam_0^2= 0.000244140625 (Reg5III, STCaseI hold); (i)(ii)(iv) need s>= 0.999755859375  > T0hi= 0.6944444444444444 : True
max_n 1-T0_n >=  0.3055555555555556  > lam_0^2 so 1-t_n>lam_n^2 for every admissible t_n<=T0_n
tail passage: kappa=1/2 -> window bulk kappa/2=1/4; Lambda=1/64 <= 1/dd= 10.0
```

External hypothesis `STConStInd 𝔠d s t` (an eventual statement), concrete limit: `Bctl(n, 1/2) ≤ 2 (1-1/2)^{-1} W_n^{-3} = 4 W_n^{-3} → 0` since `W_n = (2(n+1))^5 → ∞`; hence `Bctl^{1/100} → 0 < 5/9`, and the inequality holds from `n = 27` (`W_27 = 550731776`; `(4 W^{-3})^{1/100}` first at most `5/9` there, per the script). No hypothesis relies on an astronomically large `N`: the modification threshold is `n₀ = 5`.

### Verdict

- D1 (family step; wrapper `S1 → Fam`): PASS. Hypothesis set is satisfiable (rows 1-14), quantifier order closes (`κ', ε'` before `𝔠, sz, z`; `𝔠d` depends on `(κ, ε, 𝔡)` only).
- D2 (K2, family Step-1 call, wrapper): PASS. The six-conjunct premise contains the three `BAStep1` needs; `baKbound_holds` is uniform over `BAFlow` at `(κ', ε')`; `baStep1_holds'` needs `2 ≤ d`, given `3 ≤ d`.
- D3 (members): PASS with the stated reading: a member is a `BAFlow` only at `(κ', ε') = (c_κ κ, ε/2)` after a modification below `n₀ = 5` here (not at `(κ, ε)`); horizon `t ≤ T0'` at every `n` is `BAFamZ_horizon`; base facts are uniform over `BAFlow`, so they apply at `(κ', ε')`. Class `t_n = 0`: `Fam(0) = Fam(T0/2)` by row 12 (so no mixing at the main flow is needed).
- D4 (price): PASS (no mathematical obstruction; the table needs no new exponent). Forecast row 17 unchanged by the mathematics above.
- Note for the probe/1b (not a FAIL): at `sz0` with constant `(s, t)` only regime (iii) is non-vacuous (row 15); regimes (i), (ii), (iv) cannot be exhibited at `sz0` because `1 - T0_n ≥ 11/36 > lam_n²`. The nonempty instances of D2/D3 therefore use `R = STReg5III` (or `STAny`); the wrapper is generic in `R`, so this does not affect the statements.

Overall verdict: PASS.

## (a′) Preflight corrections — Wed Oct 14 05:15:09 UTC 2026
- (a), verdict D3, class `t_n = 0`: "`Fam(0) = Fam(T0/2)` by row 12 (so no mixing at the main flow is needed)". Row 12 is right (`Fam(0) = Fam(T0/2)`); the parenthesis is wrong. On the class the chain ends at `t'_n = T0_n/2`, while `BAMLOutTL` is stated at `t_n = 0` there, so the base at the zero sequence must still be mixed with the chain at `t'` at the main flow (`TwistChain_*_mix`, by `open private`; compiled: probe `T2503_baChainFamTL`, `RBM3D/Probe/T2503Pins.lean:235-261`, last `exact`). `Fam(0) = Fam(T0/2)` is true and unused. No verdict changes (D3 PASS).
- The instance data of rows 3, 7, 8, 10 and 13 are those of the compiled examples (flow at `κ = 1/4`, `c₁ = 1/3`, window `sz0_win_third` weakened to `1/4`, `T0 ≥ 17/25`, `(s, t) = (1/10, 1/2)` with `STConStInd` by `s1Setup_conStInd_const`); no other correction.

## (b) Script output (report-only design ticket: the deliverable is `docs/reports/T2503-design.md` plus the probe `RBM3D/Probe/T2503Pins.lean`)
Branch `t/T2503` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2503`), `git log --oneline main..t/T2503`:
```
93bd54cd T2503: probe comment (c₁ of BAWinBulk_of_dom_holds)
194da6f1 T2503: design report wording (carrier objects, V2a role)
f5ab5a3c T2503: design report, diff stat and T2205 line spans
ca5cb169 T2503: design report (V2a design gate; V-C1 steps 1-4)
9c304204 T2503: comment-only edits (BAMainIndTL/BAChainTL off the route; LC-1 stale owner comments)
6a7a3c64 T2503: probe, instance at the c₁ of BAWinBulk_of_dom_holds
ccb5b566 T2503: probe (family step pins, K2, family Step-1 call, wrapper, members, tail passage, family chain, d = 3 instances)
```
Build, forbidden words, axioms of every target theorem (`zsh probe_check.sh`, scratchpad `T2503/`; the same output is in the design report, section 0):
```
$ zsh probe_check.sh
lines:           391
lake env lean RBM3D/Probe/T2503Pins.lean: exit=0, output lines=       0
lake build RBM3D.Probe.T2503Pins: exit=0, last line: Build completed successfully (4230 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs: 18, theorems: 15, examples: 16
T2503_tl2Congr [propext, Classical.choice, Quot.sound]
T2503_k2Member [propext, Classical.choice, Quot.sound]
T2503_famStep1Call [propext, Classical.choice, Quot.sound]
T2503_memberFlow [propext, Classical.choice, Quot.sound]
T2503_famOfS1 [propext, Classical.choice, Quot.sound]
T2503_memberBase [propext, Classical.choice, Quot.sound]
T2503_tailPassage [propext, Classical.choice, Quot.sound]
T2503_precL_shift [propext, Classical.choice, Quot.sound]
T2503_conclShift [propext, Classical.choice, Quot.sound]
T2503_baChainFamTL [propext, Classical.choice, Quot.sound]
```
Target statements, first lines extracted from the probe by script (the pins are the check's Part 2 text, equal by `Iff.rfl`, design report section 0 and D1):
```
:95  theorem T2503_tl2Congr : T2503_TL2Congr
:103  theorem T2503_k2Member (d : ℕ) : T2503_K2Member d
:110  theorem T2503_famStep1Call (d : ℕ) : T2503_FamStep1Call d
:115  theorem T2503_memberFlow (d : ℕ) : T2503_MemberFlow d
:124  theorem T2503_famOfS1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2503_FamOfS1 d R
:142  theorem T2503_memberBase (d : ℕ) (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
:155  theorem T2503_tailPassage (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
:177  theorem T2503_conclShift {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (n₀ : ℕ) :
:235  theorem T2503_baChainFamTL (d : ℕ) : T2503_BAChainFamTL d
```
One compiled nonempty instance in full (the Step-1 pair at the non-main member `BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(1/2)`, `d = 3`, `(κ, ε, 𝔠, 𝔡) = (1/4, 1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2`; the family premise `hfam` stays a hypothesis); the others are probe :310-391 (list in the design report, D2):
```
-- D2 (b): the Step-1 pair at the non-main member of `Fam(1/2)`; the family premise (six per member of `Fam(1/10)`) is the one hypothesis
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → T2503_Six (baFMz sz0 z') μ0 (fun _ => 1 / 10)) :
    STStep1LoopgL (baFMz sz0 T2503_m) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) ∧ STStep1WeakgL (baFMz sz0 T2503_m) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  T2503_famStep1Call 3 le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq T2503_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) T2503_win (fun _ => 1 / 10) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 17 / 25).trans (t0_sz0_ge n)) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hfam (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) (by norm_num))
    T2503_m (T2503_mem _ (by norm_num))
```
Name clash: `grep -rn 'T2503\|BAMainIndFamTL\|BAMainIndS1TL\|BAChainFamTL\|BATwistLoopLaw_congr' RBM3D/ | grep -v Probe/T2503Pins.lean` finds only `RBM3D/BA/TwistPins.lean:168, :184` (the two doc comments edited under answer (4)); no declaration; `git grep T2503_` over `t/T2[45]*`: only `t/T2503`.
Ports: none from `../RBM1D` or `../RBM2D`. Copied texts: the four `T2503v1_*` defs from `docs/tickets/checks/T2502-check.lean:182-213` (commit 6b359e50), equal after the prefix map (design report section 0); the binder order follows `t/T2205:RBM3D/Probe/T2205Pins.lean:1715` (commit 96e4087c), read with `git show` only.
Narrative:
- The probe states the check's nine pins and proves from merged names: the TL2 congruence, K2, the family Step-1 call, the member flow, the wrapper `S1 → Fam` (16 lines), the per-member base, the tail passage with the shift transport, and the whole family twin of `baChainTL_holds` (`T2503_baChainFamTL`, 110 lines with its helpers). Every target has a `d = 3` example; other gates' pins are hypotheses.
- Verdict and all tables are in `docs/reports/T2503-design.md` (179 lines, first line = the four-part verdict). No stop rule fired: the family Step-1 call and the per-member base typecheck at exact type, no merged statement changed, V forecast 12 (11-14).
- Comment-only edits (answer (4)): `BA/TwistPins.lean:168, 184`, `BA/LWPinsBA.lean:20, 44, 46, 48`, `BA/Step2CloseBA.lean:201`, `Graph/BAGGExp.lean:78`; a script shows every changed line inside a comment; the full `lake build` (4382 jobs, 95 modules rebuilt, no certificate module) passes.

## (c) Verified Mathlib names used (resolved by `#check` in the worktree, scratchpad `T2503/names.lean`)
- `Filter.eventually_atTop` (`∀ᶠ x in atTop, p x ↔ ∃ a, ∀ b ≥ a, p b`)
- `Filter.tendsto_add_atTop_nat` (`Tendsto (fun a => a + k) atTop atTop`)
- `Real.rpow_pos_of_pos`
- `half_le_self`, `half_pos`
- `exists_nat_ge`
- `div_le_iff₀`
- `Nat.pos_of_ne_zero`
- `tendsto_natCast_atTop_iff`
- `StrictMono.injective`
- `lt_of_le_of_ne`
- `Filter.Eventually.mono`
- Names verified absent: none searched in Mathlib. In the repository a grep of `BA/` and `Graph/` for `∃ z … BAdom`, `BAdom_exists`, `flow_exists`, `BAFlow_exists` finds nothing (design report D4 (b)).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. D536 (family form, the finite modification `(κ', ε')`) and D538 (`∀ n, 0 < sz.lam n`, tail, window at `κ/2`) cover every Lean/paper difference of this gate (`docs/paper-deltas.md:1495, 1497`).
- LC-1 extension for the dispatcher: `BA/LWPinsBA.lean:50, 52` (`BASTLWB`, `BASTLWT`: "owed: T1-BA / T7-BA, through L5") are stale like the four edited lines; outside this ticket's writable lines.
- `T2503v1_` copies: re-check against T2502's merged `Chain/Step6Gen` at its merge (design report, re-check bullet).
- V1-BA's `BAStep6R` shape is proposed in the probe (`T2503_Step6BA`, :288-294: T2502's `Step6RgL` at the BA tuple with TL1 and TL2 at every `u ∈ [s,t]` on the `Concl` slot); the decision is V1-BA's ticket's.
- Regimes (i), (ii), (iv) are empty at `sz0` for constant `(s, t)` ((a) row 15): V2a's 1b instances for them need private data or hypothesised intervals (T2501 Amend 1 precedent).
- Preflight correction: (a′) above.
