Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 16:59:25 UTC 2026

Targets (mathematics only): T1 = `STNetLift2gL d` at law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0` (pin: `Chain/Step2Gen:602`);
T2 = `t_n < 1 ∧ RangeCond (ε/2) t` from `BAFlow`, `t ≤ BAflowT0` (`t/T2452:RBM3D/Probe/T2452Pins.lean:177-195`). Route: `cont_core` (`ContinuityNet:142`) with good event
`contGood (sz.withLam 0)` and `cont_highProbAt_good`, as `baNetLift` (`Step1Setup:877`); `N = sz.size n = (WL)^d`, `Δ = |u-u'|`, `Q = η_t⁻¹`, `δ_G = Q²(Xb+1)√Δ`.

### (i) Exponent table (source / band counterpart in the last column)

| item | value | constraint | slack | source (band twin) |
|---|---|---|---|---|
| T2 `t_n<1` | `t_n ≤ T₀_n < 1` | `T₀<1` every n | strict, no smallness | `EMn2BA_T0_lt_one` (`EMn2BA:106`) |
| T2 range | τ = ε/2 | `N^{-1+ε/2} ≤ 1-t_n`; `1-T₀ ≥ Im z/2 ≥ N^{-1+ε}/2` and `N^{ε/2} ≥ 2` eventually | factor `N^{ε/2}/2` | `EMn2BA_one_sub_T0` (`:111`), `eventually_le_rpow`; band twin `v3_premises_of_stFlow` (`Green/Pins:1049`) |
| window | `(1-t_n)⁻¹ ≤ N` | from RangeCond: `(1-t)⁻¹ ≤ N^{1-ε/2} ≤ N`; so `(1-u)⁻¹ ≤ N` for `u ≤ t` | `N^{ε/2}` | `nl2_evR` (`NetLift2:567`), reused |
| bulk data | `κ ≤ Im m_F`, `‖m_F‖ ≤ 1`, `1/κ ≤ N` | `η_t⁻¹ = ((1-t) Im m_F)⁻¹ ≤ N²` | `N/κ` vs `N²` | `EMn2BA_mF_data` (`:125`), `BAm_norm_le_one`, `BASetup_eta_inv_le` (`Step1Setup:674`); band `c₁`, `mE` not used |
| `G` modulus | `δ_G ≤ 3N⁶ N^{-A/2}` on `‖X‖ ≤ 2N²` (contGood) | `Δ ≤ N^{-A}`, `Δ ≤ 1`, `‖z_u-z_u'‖ ≤ Δ` | per family below | `BASetup_entry_diff` (`:299`), `BASetup_zdiff`, `BASetup_eta_le`; alt. `baGopbound` (`:346`, `C=6 ⇒ C'=22`, entries only) not used |
| entries of `G`, `M` | `‖G_{u,xy}‖ ≤ η_t⁻¹ ≤ N²`; `M = G_0` (`BASetup_GM_zero`, `:1030`) so `‖M_xy‖ ≤ 1/κ ≤ N` | `‖GM_{u'}‖ ≤ N²+N ≤ 2N²` | factor 2 | band `nl2_entry_le` bound `N²+1` |
| **L** `V=Idx×Idx` | `#V=N²`, `Cv=2`, `A=40`, `ε_n=N⁻¹` | `15N⁹N^{-A/2} ≤ N⁻¹` (`2‖b‖+δ ≤ 5N²`); `N·N^{-A} ≤ 1/10` | `N¹⁰/15`; `1/10` vs `N^{-39}` | `nl2_loc_close` (`NetLift2:339`) via `nl2_eventual` (`:541`) |
| L floor | `ε_n=N⁻¹ ≤ STWB_{u,K}`, every K | `0≤u<1` | none needed | `nl2_STWB_low` (`:249`) |
| L ratio | `STWB_{u'} ≤ (1+x)STWB_u`, `x=N·N^{-A}≤1/10` | `1+x ≤ 2` | `11/10` vs `2` | `nl2_STWB_ratio` (`:217`) |
| **A** `V=Zd` | `#V=L^d ≤ N`, `Cv=1`, `A=40`, `ε_n=N⁻¹` | loop `k=1`: `N·Q·δ_G ≤ 3N⁹N^{-A/2} ≤ N⁻¹`; `m=BAmF` indep. of `u` | `N¹⁰/3` | `nl2_avg_close` (`:439`); `BASetup_LP_close` (`Step1Setup:712`) |
| A floor / ratio | `N⁻¹ ≤ Bctl_u`; `Bctl_{u'} ≤ (1+x)Bctl_u` | `1+x ≤ 2` | `11/10` vs `2` | `cont_inv_size_le_Bctl` (`ContinuityNet:701`), `cont_Bctl_ratio` (`:725`) |
| **D** `V={±}²×Zd²` | `#V=4L^{2d} ≤ 4N² ≤ N³` (N ≥ 4), `Cv=3`, `A=4D+40`, `ε_n=N^{-D}` | `6N^{11-A/2}+N^{2-A} ≤ N^{-D}`; exponents `-2D-9`, `-4D-38` | `N^{D+9}/7` | `nl_close` (`NetLift1:533`), `step2NetLift` (`:706`) |
| D loop mod. | `‖L²_u-L²_u'‖ ≤ card(Vtx)·(2·Q²·δ_G) = N·2N⁴·3N⁶N^{-A/2} = 6N^{11-A/2}` | `k=2`, `card Vtx = N` | as above | **norm of difference needed**: `BASetup_loopAbs_diff` (`:519`) bounds `|‖L‖-‖L'‖|` only; band twin `nl_loop_sub` (`:159`) is `\|E\|<2` |
| D `𝒦` mod. (new) | `‖𝒦²_u-𝒦²_u'‖ ≤ Δ(1-u)⁻¹(1-u')⁻¹ ≤ N^{2-A}`, all `σ∈{±}²` incl. same charge | `u,u' ∈ [0,T₀]`, `(1-u)⁻¹ ≤ N`; eventually `0<g₀` | `N^{-A}·9` vs `N^{2-A}` (inst. below) | `baKsol_two` (`KInduct:88`): `𝒦=(W^d)⁻¹(Θ_u Q)(a₀,a₁)`, `Q=BAMss`; `BAKBase_sub` (`KBase:216`); `EKPins_norm_Theta_le`/`_Q_le` (`:161`/`:151`, any σ); `BAflow_lam0_window` (`GreenSchur:72`), `BAflow_real` (`:59`); band `nl_K_diff` (`:281`) |
| D control ratio | `(\|Cd\|+2)x+δ ≤ 1/2`, `x=N^{1-A}`, `δ=√(zd·g·(1-t)⁻¹√Δ)`, `g = sz.lam n ≤ 𝔡⁻¹` | `c=(1+x)^{\|Cd\|}(1+x)^{1/5}(1+x)e^δ ≤ 2` | `(\|Cd\|+2)N^{-4D-39} ≤ 1/4`, `δ ≤ 1/4` | `nl_zeta_ratio` (`:484`), `nl_c_le` (`:459`), `nl_exp_ell` (`:363`), `nl_STWB_ratio` (`:391`), `nl_rpow_ratio` (`:434`) |
| `WO` | `sz.lam n ≤ 𝔡⁻¹`, `0 ≤ sz.lam n`, eventually | `BAFlow.1.2.2.2.2 = WO`; control uses `sz.lam`, never `g₀` | `lam_n ≤ 10` | `BAflow_lam0_window` proof (`GreenSchur:72-85`) |
| floor D | `N^{-D} ≤ W^{-D}` | `W ≤ N`, needs `d ≥ 1` (from `N→∞`) | factor `(N/W)^D` | `nl_one_le_d` (`NetLift1:679`) |

Hypotheses beyond `BAFlow`, `0≤s≤t≤BAflowT0`: none (no `3 ≤ d`, no spectral/`mE`, no smallness of `g`; `0<g₀` only eventually, from `BAflow_lam0_window`).

### (ii) One nondegenerate instance and its check

Data: `d=3`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `sz0` (`Defs/Sizes:260`: `L=4(n+1)`, `W=(2(n+1))⁵`, `lam=(2(n+1))⁻⁶`), `zSeq` with `flow_sz0` (`FlowPins:1214`), `s≡1/2`, `t≡2/3 ≤ T₀` (`t0_sz0`: `2/3 ≤ T₀_n`),
`Im m_F ≥ 1/2` (`inst_im_m_ge`, `Step1Setup:1100`), `C_d=5`, `D∈{1,5}`. The three per-time statements stay hypotheses of the example (stochastic inputs inside the pin); no other external hypothesis.
Limit input: `N_n=(W_nL_n)³ → ∞` (`sz0_tendsto`; values below), `d ≥ 1`. Thresholds are exact-integer/log checks of the table rows; the last lines give the least `N` at which each gap holds (so `N_0=2097152` is far above, not a large-witness artifact), and a random test of the `𝒦` Lipschitz bound.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2461/inst.py`
```
(1-t)^-1 = 3  eta^-1 <= 6  1/kappa = 2
n=0: L=4 W=32 N=(WL)^3=2097152 (~1e6.3) lam=1.562e-02 lam<=1/dd:True
   WO: W^(-3/2+1/10)=(2(n+1))^-7 = 0.0078125  <= lam = 0.015625
   RangeCond(eps/2): log10 N^{-1+eps/2} = -6.01  <= log10(1/3) = -0.477
   (L) A=40: N*N^-A=1e-246.5 <=1/10; 15N^9N^-20=1e-68.4 <= N^-1=1e-6.3; slack N^10/15=1e62.0; #V=N^2
   (A) A=40: 3N^9N^-20=1e-69.1 <= N^-1; Bctl ratio x=N*N^-A=1e-246.5<=1/10; #V=L^d=64<=N
   (D) D=1 A=44: (|Cd|+2)N^(1-A)=1e-271.0<=1/4; 10N^(2-A/2)=1e-125.4<=1/16; 6N^(11-A/2)+N^(2-A)=1e-68.8 <= N^-D=1e-6.3; K-Lip=1e-277.2<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
   (D) D=5 A=60: (|Cd|+2)N^(1-A)=1e-372.1<=1/4; 10N^(2-A/2)=1e-176.0<=1/16; 6N^(11-A/2)+N^(2-A)=1e-119.3 <= N^-D=1e-31.6; K-Lip=1e-378.3<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
n=8: L=36 W=1889568 N=(WL)^3=314771264602372300603392 (~1e23.5) lam=2.940e-08 lam<=1/dd:True
   WO: W^(-3/2+1/10)=(2(n+1))^-7 = 1.6333996728810076e-09  <= lam = 2.9401194111858137e-08
   RangeCond(eps/2): log10 N^{-1+eps/2} = -22.32  <= log10(1/3) = -0.477
   (L) A=40: N*N^-A=1e-916.4 <=1/10; 15N^9N^-20=1e-257.3 <= N^-1=1e-23.5; slack N^10/15=1e233.8; #V=N^2
   (A) A=40: 3N^9N^-20=1e-258.0 <= N^-1; Bctl ratio x=N*N^-A=1e-916.4<=1/10; #V=L^d=46656<=N
   (D) D=1 A=44: (|Cd|+2)N^(1-A)=1e-1009.6<=1/4; 10N^(2-A/2)=1e-469.0<=1/16; 6N^(11-A/2)+N^(2-A)=1e-257.7 <= N^-D=1e-23.5; K-Lip=1e-1033.0<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
   (D) D=5 A=60: (|Cd|+2)N^(1-A)=1e-1385.5<=1/4; 10N^(2-A/2)=1e-656.9<=1/16; 6N^(11-A/2)+N^(2-A)=1e-445.7 <= N^-D=1e-117.5; K-Lip=1e-1408.9<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
n=20: L=84 W=130691232 N=(WL)^3=1323052915536356766729237430272 (~1e30.1) lam=1.822e-10 lam<=1/dd:True
   WO: W^(-3/2+1/10)=(2(n+1))^-7 = 4.33765460284498e-12  <= lam = 1.8218149331948917e-10
   RangeCond(eps/2): log10 N^{-1+eps/2} = -28.62  <= log10(1/3) = -0.477
   (L) A=40: N*N^-A=1e-1174.7 <=1/10; 15N^9N^-20=1e-330.2 <= N^-1=1e-30.1; slack N^10/15=1e300.0; #V=N^2
   (A) A=40: 3N^9N^-20=1e-330.9 <= N^-1; Bctl ratio x=N*N^-A=1e-1174.7<=1/10; #V=L^d=592704<=N
   (D) D=1 A=44: (|Cd|+2)N^(1-A)=1e-1294.4<=1/4; 10N^(2-A/2)=1e-601.4<=1/16; 6N^(11-A/2)+N^(2-A)=1e-330.6 <= N^-D=1e-30.1; K-Lip=1e-1324.4<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
   (D) D=5 A=60: (|Cd|+2)N^(1-A)=1e-1776.3<=1/4; 10N^(2-A/2)=1e-842.4<=1/16; 6N^(11-A/2)+N^(2-A)=1e-571.5 <= N^-D=1e-150.6; K-Lip=1e-1806.3<=N^(2-A); floor N^-D<=W^-D ok; #V=4L^6<=N^3
min N, (L) g3 at A=40 (15N^9N^-20<=N^-1): 2
min N, (D) D=1 A=44 g3 (6N^11 N^-22 + N^2 N^-44 <= N^-1): 2
min N, (D) D=1 gdelta (10 N^-20 <= 1/16): 2
N_0 = 2097152 (n=0, all constraints already hold)
K-modulus random test (2000 trials, |Q_ab|=stochastic, arbitrary phases): max lhs/rhs = 0.7456 (<=1 required)
```

### Verdicts

- Stop rules (ticket): no spectral or `3 ≤ d` premise, no smallness of `g`, no `0<g₀` for every `n` is needed for T1; the `𝒦²` modulus holds for same-charge pairs (`‖Q‖≤1` for every `σ`, random test max ratio 0.7456 ≤ 1); every control ratio uses `sz.lam` with `WO`, not `g₀`; no merged file or `private` edit is needed (`open private`).
- Finding for 1b (not a stop rule): families A and D need `‖L_u-L_u'‖` (norm of the difference); merged BA `BASetup_loopAbs_diff` gives only `|‖L‖-‖L'‖|`, so 1b writes a private twin under the stem `NetLiftBA_` (copy of `BASetup_loopAbs_diff` without its last `abs_norm_sub_norm_le`, using `open private` of `BASetup_word_diff`, `BASetup_loopFine_eq`).
- Not in this section (stage-1a rules): size estimate, reserve-file decision, importer scan, name checks.

**T1 `baNetLift2_holds`: PASS. T2 `baFlow_premises`: PASS.**

### (a′) Preflight corrections
None: no row of (a) needed a correction.

## (b) Script output — Mon Oct 12 17:19:17 UTC 2026

Size against the stop line (`wc -l`, run at each of the three section commits: 413, 798, 838 lines):
```
$ wc -l RBM3D/BA/NetLiftBA.lean            -> 838      (stop line 2,000 per file; U-D central 900; landed/central = 0.93)
$ git log --oneline main..t/T2461           -> d36677f, b8170b2, fe10791 (only RBM3D/BA/NetLiftBA.lean, 838 insertions)
one file; the reserve file NetLiftBA2 is not used; RBM3D.lean is not touched on the branch (precedent T2451; the hub adds the import)
```
Build, axioms, hygiene:
```
$ lake build RBM3D.BA.NetLiftBA 2>&1 | grep -E "NetLiftBA|Build completed"
Build completed successfully (4062 jobs).
$ (temporary root import line, removed again; git status clean) lake build 2>&1 | tail
info: RBM3D.lean:521:0: axiom audit: 13373 theorems, 4251 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4289 jobs).
$ grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/BA/NetLiftBA.lean   -> 0
$ lake env lean ax.lean     (import RBM3D.BA.NetLiftBA; #print axioms of both public declarations)
'RBM.BA.baNetLift2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFlow_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Statement diff against the check file (script `stmt.py`: the text after `(d : ℕ) :` of each theorem against the body of `T2461_*`, whitespace-normalised):
```
$ python3 -I stmt.py
== baNetLift2_holds vs T2461_NetLift2BA      IDENTICAL
lean : STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
== baFlow_premises vs T2461_BAFlowPremises   IDENTICAL
lean : ∀ (κ ε 𝔠 𝔡 : ℝ), 0 < κ → 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t
$ lake env lean docs/tickets/checks/T2461-check.lean ; echo $?                       -> 0
$ (check file + `example : ∀ d : ℕ, T2461_NetLift2BA d := baNetLift2_holds` + `example : ∀ d : ℕ, T2461_BAFlowPremises d := baFlow_premises`) lake env lean chk.lean ; echo $?   -> 0
```
Target 2 is stated in the check-file form (`d` and the data explicit); the probe `T2452_ba_premises` has the same body with the data as implicit binders.

Compiled nonempty instances (file lines 802-836, namespace `RBM.BA.NetLiftBAInst`; `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t0_sz0`; the three per-time statements stay hypotheses of the example, every deterministic premise is discharged):
```
example (Cd : ℝ)
    (hL : STStep2LocalPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3))
    (hA : STStep2AvgPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3))
    (hD : STStep2DecayPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 1 / 2) (fun _ => 2 / 3)) :
    STStep2LocalgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) ∧
      STStep2AvggL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) ∧
      STStep2DecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 1 / 2) (fun _ => 2 / 3) :=
  baNetLift2_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun n => t0_sz0 n) Cd hL hA hD
```
Instance (b), `s ≡ 0`, `t ≡ 1/2` via `half_lt_t0`, is at file lines 819-830. Target 2 at the same data (lines 831-834):
```
example : (∀ n : ℕ, (fun _ : ℕ => (2 / 3 : ℝ)) n < 1) ∧ sz0.RangeCond ((1 / 10) / 2) (fun _ => 2 / 3) :=
  baFlow_premises 3 (1 / 2) (1 / 10) (1 / 6) (1 / 10) (by norm_num) (by norm_num) sz0 zSeq flow_sz0
    (fun _ => 2 / 3) (fun n => t0_sz0 n)
```
Name-clash grep (`git grep -n -E "baNetLift2_holds|baFlow_premises|NetLiftBA" <ref> -- RBM3D`, outside the new file): 0 hits on main, t/T2450, t/T2454, t/T2455, t/T2456, t/T2457, t/T2460.
Importer scan (`grep -rn NetLiftBA RBM3D RBM3D.lean | grep -v "^RBM3D/BA/NetLiftBA.lean" | wc -l`): 0.
Diff scan: `git diff main...t/T2461 -- RBM3D/Path RBM3D/Chain RBM3D/Induction RBM3D/BA/FlowPins.lean RBM3D/BA/TwistLoop.lean RBM3D/BA/Step1Setup.lean RBM3D/BA/KBase.lean | wc -l` -> 0; `-- RBM3D/Test/Axioms.lean RBM3D.lean` -> 0 lines.
Ports: none from RBM1D/RBM2D (no diff-stat needed). Copies from RBM3D, under the stem `NetLiftBA_`: `NetLiftBA_loop_sub` = `BASetup_loopAbs_diff` (`Step1Setup:519`) without its last step; `NetLiftBA_ctrl_ratio` = second half of `nl_close` (`NetLift1:533`); the lifts follow `step2LocalNetLift` (`NetLift2:586`), `step2AvgNetLift` (`:627`), `step2NetLift` (`NetLift1:706`), `baNetLift` (`Step1Setup:877`).

Moduli table (1a (iii)); all three use `cont_core` with `contGood (sz.withLam 0)`, `A` = mesh exponent, `Cv` = card exponent:
| family (V, A, Cv, ε_n) | ξ modulus (this file) | ζ ratio ≤ 2 | floor ε ≤ ζ | band counterpart |
|---|---|---|---|---|
| L (`Idx²`, 40, 2, `N⁻¹`) | `‖G_u-G_u'‖ ≤ 3N⁶N^(-A/2)` (`G_diff`:211), `‖GM‖ ≤ 2N²` via `M = G_0` (`G_le`:193) → squares (`loc_close`:293) | `nl2_STWB_ratio` | `nl2_STWB_low` | `nl2_loc_close` NetLift2:339 |
| A (`Zd`, 40, 1, `N⁻¹`) | loop `k=1`: `N·N²·3N⁶N^(-A/2) ≤ N⁻¹` (`L_diff`:246, `avg_close`:366), `m = BAmF` indep. of `u` | `cont_Bctl_ratio` | `cont_inv_size_le_Bctl` | `nl2_avg_close` NetLift2:439 |
| D (`{±}²×Zd²`, `4D+40`, 3, `N^(-D)`) | loop `k=2`: `6N^(11-A/2)`; **new** `‖K²_u-K²_u'‖ ≤ |u-u'|(1-u)⁻¹(1-u')⁻¹ ≤ N^(2-A)`, every `σ` (`K_diff`:96); `decay_close`:490 | `nl_zeta_ratio` + `nl_c_le`, `nl_exp_ell`, `nl_STWB_ratio`, `nl_R_le` (`ctrl_ratio`:407), `sz.lam ≤ 𝔡⁻¹` from `WO` | `N^(-D) ≤ W^(-D)` (`nl_one_le_d`) | `nl_close` NetLift1:533 |
Privates by `open private` (file:line): Step1Setup `BASetup_herm`:239 `_entry_diff`:299 `_H_sub`:314 `_zdiff`:325 `_eta_le`:336 `_word_diff`:469 `_loopFine_eq`:508 `_eta_inv_le`:674 `_X_norm`:698 `_GM_zero`:1030 `_norm_BAmF_le_one`:1048; KBase `BAKBase_sub`:216; TwistKer2 `TwistKer2_norm_winv`:705; NetLift2 `nl2_STWB_nonneg`:196 `_ratio`:217 `_low`:249 `nl2_eventual`:541 `nl2_evR`:567; NetLift1 `nl_exp_ell`:363 `_STWB_ratio`:391 `_R_le`:420 `_c_le`:459 `_zeta_ratio`:484 `_one_le_d`:679. No private is deleted or edited.
Good event: `contGood (sz.withLam 0)` with `cont_highProbAt_good` (as `baNetLift`); `baGopbound` is not used (it bounds entries of `G` only; the loops need the operator-norm modulus).

C1 / spectral grep (`grep -c -F <token> RBM3D/BA/NetLiftBA.lean`): `|E`, `2 - κ`, `mE`, `zt`, `etaT`, `lemT`, `lemE`, `STFlow`, `STflowE`, `v3_premises_of_stFlow`, `bandFM`, `nl_loop_sub`, `nl_eta_inv_le`, `nl_K_diff`, `nl_close`, `nl2_loop_sub`, `nl2_eta_inv_le`, `nl2_entry_`, `nl2_loc_close`, `nl2_avg_close`, `3 ≤ d` -> 0 each. `sz.lam` occurs only in the controls (`STWB`, `ellT`, `Bctl` via `sz`) and in `0 ≤ sz.lam n ≤ 𝔡⁻¹` from `WO`; `g₀` (`BAflowLam0`) occurs only in the hypothesis `0 < g₀` (for `baKsol_two`), in the matrix `Q` of the `𝒦` modulus and as the flow parameter of the carrier.

Narrative:
- Route BA-direct as the ticket fixes it; no stop rule fired: no spectral or dimension premise, no smallness of `g`, `0 < g₀` only eventually (`BAflow_lam0_window`), the `𝒦^{(2)}` modulus holds for every charge pair, no merged file or `private` is edited.
- The one finding of (a) is realised: families A, D need `‖L_u - L_u'‖` (norm of the difference), so `NetLiftBA_loop_sub` is a copy of `BASetup_loopAbs_diff` without `abs_norm_sub_norm_le`.
- The local family uses `‖(G_u'-M)_xy‖ ≤ 2N²` (`M = G_0`, `BASetup_GM_zero`) in place of the band `N²+1`; the factor in `g3` stays `15`.
- `BAflow_lam0_window` is used inside the decay family only (for `baKsol_two`); the other two families need no `g₀`.
- Target 1 holds for every `d`, `κ`, `ε`, `𝔡`, `𝔠`, `s`, `t`, `C_d` of the pin; the stochastic content stays in the three per-time hypotheses (inputs of T1-BA, produced inside the iteration).
- Proposed closing line for T (dispatcher note (7)), true after the merge: "P2 merged with compiled nonempty `d = 3` instances; `STNetLift2gL` proved at `baFMz`". The T1-BA pin REQ cites `baNetLift2_holds` and `baFlow_premises`.

## (c) Verified Mathlib names (each occurs in the compiled file)
`Finset.single_le_sum`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `le_self_pow₀`, `Real.rpow_le_rpow_of_nonpos`, `Real.sqrt_le_iff`, `smul_mul_assoc`, `Matrix.sub_apply`, `Matrix.trace_sub`, `tendsto_natCast_atTop_iff`, `Filter.Tendsto.eventually_ge_atTop`, `Real.rpow_two`, `Fintype.card_bool`. Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
1. Hub step: add `import RBM3D.BA.NetLiftBA` after the last import of `RBM3D.lean` (the full `lake build` above ran with that line, then it was removed from the worktree).
2. Paper-delta candidate `T2461a` (informational): the BA text (`7_8:1993-1994`) has no net lift; the Lean `STNetLift2gL` at BA is proved by the standard net argument of `1_2:1400` with one new routine BA modulus, the time Lipschitz bound of `𝒦^{(2)}` (resolvent identity of `Θ`). No statement of the paper is changed.
3. The three per-time statements are hypotheses of the examples (no producer of `STStep2DecayPTgL` is merged); the per-family lifts are private for that reason (premise scan, ticket "Registry: none").
4. `Test/Axioms.lean` and `RBM3D.lean` are unchanged on the branch.
