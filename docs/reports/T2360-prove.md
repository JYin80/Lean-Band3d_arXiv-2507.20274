Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 03:08:04 UTC 2026

Target: the stage-K design (T2360): pin `STKboundgL (baFMz sz z)` (`RBM3D/BA/FlowPins.lean:424`, `:550`): for all `τ n ∈ [0,1)`, `k ≥ 1`: `max_{σ,a} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}`, with `B` = `Bctl` (`Defs/Sizes.lean:214`) `= W^{-d}·Bparam d L (sz.lam n) τ 0` and `Bparam = (g²+|1-t|)⁻¹((K+1)^{d-2})⁻¹ + (L^d|1-t|)⁻¹` (`Defs/Params.lean:36`). Paper: `ML:Kbound` (`1_2:1054-1061`), `B_{t,K}` (`eq_B_param`, `1_2:1108`), proof `A:672-806`. Carrier data (`FlowPins.lean:537-550`): `g₀ = √t₀ g`, `E = BAflowE`, `m₀ = m(E,g₀)`, `t₀ = Im m/(Im m + Im z)` (`MFixedPoint.lean:279`).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | exponent of `W^{-d}B_{τ,0}` | `k-1`, `k ≥ 1` (`k=1`: exponent 0, bound `1`) | BA initial datum at length 1 is `(W^d)^{-0}M_{aa}(σ)` (`BAMLoop`, `FlowPins.lean:274`; that `K^{(1)}` equals it is the `k=1` tree equation, to be checked in the K1 table); `|M_{aa}| ≤ ‖M‖ = 1/Im(E+m₀) = 1/Im m₀ ≤ 1/κ` (real `E`, `BAReal`); paper `A:673`: `K^{(1)} = O(1)` | inst. A: `max|M_aa| = 0.9995 ≤ 1/Im m₀ = 1.0005 ≤ 1/κ = 2` |
| 2 | exponent `d-2` in `B_{t,K}` | `d-2 = 1` at `d = 3`; the `K = 0` value is `(0+1)^{d-2} = 1` | `d ≥ 3` (`A:661`: "additional modifications to handle d ≥ 3"); `Θ` pointwise `≲ B_{t,0}` (`eq:pointwise_Theta`) | none lost at `K=0` |
| 3 | lower bound `B_{t,0} ≥ (1+g²)⁻¹` for `t ∈ [0,1)` | `(g²+|1-t|)⁻¹ ≥ (g²+1)⁻¹` | needed so pure-loop bound `C_n W^{-d(n-1)}e^{-c|a|}` (`lem_pureloop`, `A:643-654`, `res_pureKes`) is `≲ (W^{-d}B_{τ,0})^{n-1}`; `g ≤ 𝔡⁻¹ = 10` (`WO`) so `B ≥ 1/101` | inst.: `B ≥ 0.99976` (g = 1/64) |
| 4 | `B` at coupling `g` (pin, `sz.lam`) vs at `g₀` (carrier `Θ`, `Bparam … P.g0` in `FlowPins.lean` `inst_BAProp5`) | `B_{g}≤B_{g₀}≤B_{g}/t₀`, because `g₀²+|1-t| = t₀g²+|1-t| ≥ t₀(g²+|1-t|)`, second term of `B` identical | `t₀ ≥ κ/(κ+1)`: `t₀` increases in `Im m ≥ κ`, decreases in `Im z ≤ 1` (`BAdom`, `MFixedPoint.lean:435`); so per factor constant `≤ (κ+1)/κ`, i.e. `((κ+1)/κ)^{k-1}` absorbed in the constant of `≺` for fixed `k` | `κ=1/2`: `t₀ ≥ 1/3`, ratio `≤ 3`; inst.: ratio `1.0001`, `t₀ = 0.694` |
| 5 | `t` range of `Θ_t^{(σ₁σ₂)} = (1 - tM^{(σ₁σ₂)})⁻¹` (`BATheta`, `PropThetaQ = Ring.inverse(1 - tQ)`, `Propagator/Pins.lean:214`) | real `t ∈ [0,1)`; the loop equation is on `Set.Ico 0 1` (`BAKsol`, `FlowPins.lean:281`) | `M^{(+,-)}_{ab} = |M_{ba}|²` has row sums `1` (Ward at real `E`, `BAward_avg` (averaged), `MFixedPoint.lean:389`: `(Im m + 0)·avg Σ|M|²=Im m`; row-wise is the pin `BAWard`, `MFixedPoint.lean:558`) so `ρ(M^{(+,-)}) ≤ 1`, `1-tM` invertible for `t<1`; `M = (g₀Ψ - E - m₀)⁻¹` is complex symmetric (`Ψ` real symmetric), so `|M^{(+,+)}_{ab}| = |M_{ab}|² = M^{(+,-)}_{ab}` and `ρ(M^{(+,+)}) ≤ ρ(M^{(+,-)}) ≤ 1` | inst.: `cond(1-tM) ≤ 3.3` at `t = 0.999` |
| 6 | data of every `Θ`/`M` in the K-loop | `(g₀, κ, E, m₀)` with `BAReal` = `BASelf d L g₀ E m₀ ∧ κ ≤ Im m₀` (`MFixedPoint.lean:432`), independent of `t` | `BAdom_real` (`MFixedPoint.lean:479`) derives `BAReal` from `BAdom` (`κ ≤ Im m(z,g)`, `0 < Im z`, `BASelf` from `baMExists_holds`) for every `n`; `BAFlow` (`FlowPins.lean:546`) gives `BAdom` for every `n` | `κ = 1/2`: `Im m₀ ≥ Im m ≥ 1/2` (`√t₀ ≤ 1`); inst.: `Im m₀ = 0.9995 / 0.8676` |
| 7 | horizon of the flow | BA: `t₀ = BAflowT0` (`FlowPins.lean:537`), NOT `lemT(z) = ‖msc z‖²` (`Defs/Semicircle.lean:193`, band only; the ticket's "t ≤ lemT(z)" is the band horizon) | `STKboundgL` quantifies all `τ ∈ [0,1)`, so no horizon enters; the data of row 6 do not depend on `t` | `t₀ ≥ 2/3` along `sz0` (`t0_sz0`, `FlowPins.lean:1379`); `t₀ ≤ 25/36` (`t0_sz0_le`, `Step1Fam.lean:753`) |
| 8 | smallness `W^{-d}B_{τ,0} ≤ W^{-2𝔡} + (N|1-τ|)⁻¹` | uses `lam_sq_mul_pow_ge` (`Sizes.lean:193`: `g²W^d ≥ W^{2𝔡}` from `WO`), `N = (WL)^d ≥ W^d L^d` | `𝔡 = 1/10` ⇒ `W^{-1/5}`; at flow points `1-τ ≥ 1-t₀ = Im z/(Im m+Im z) ≥ N^{-1+ε}/(Im m+1)` (`Im z ∈ [N^{-1+ε},1]`), so `(N(1-τ))⁻¹ ≤ (Im m+1)N^{-ε}` | inst.: `3.1e-4 ≤ 0.5` (`n=0`; loose since `W^{-1/5} = 0.5`) |
| 9 | `Admissible 𝔠 𝔡` (`Sizes.lean:177`): `W ≥ N^𝔠`; `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` | `𝔠 = 1/6`, `𝔡 = 1/10` | `sz0` (`Sizes.lean:260`): `W_n=(2(n+1))^5`, `L_n=4(n+1)`, `g_n=(2(n+1))^{-6}` (`sz0_admissible`, `Sizes.lean:331`) | `n=0`: `32 ≥ 11.31`; `0.0078 ≤ 0.0156 ≤ 10` |
| 10 | `BAdom` constants `κ, ε` | `κ = 1/2`, `ε = 1/10` (`flow_sz0`, `FlowPins.lean:1366`) | `κ ≤ Im m(z,g)`, `N^{-1+ε} ≤ Im z ≤ 1` | `n=0`: `Im m = 0.832`, `N^{-0.9} = 2.0e-6 ≤ Im z = 0.3675 ≤ 1` |
| 11 | sum-zero `Σ^{(∅)}` (`A:731`): `O(\|1-t\|)` and `O(g²+\|1-t\|)` | `(1-t)·Σ_b\|Θ^{(+,-)}_{ab}\| ≲ 1` (`THETAinftinf`, `1_2:1141`; here the row sum is exactly `(1-t)⁻¹`, stochastic `M^{(+,-)}`), and `(g²+\|1-t\|)⁻¹ ≲ B_{t,0}` (`A:760-775`) | each reduces `B^{n-2}` count: `B·B^{n-2} = B^{n-1}` | inst.: row sum `Θ^{(+,-)} = 1/(1-t)` to 4 decimals at `t=0.5, 0.999` |

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`, `N = (WL)³ = 2097152`, `g = 1/64`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `k ∈ {1,…,4}`, `τ ∈ {0.5, 0.9}`, `t` up to `0.999`. Instance A: `z = z_S` (`zSeq 0`, `MFixedPoint.lean:868`, `w = 1.2i`, `Im z = 0.3675`); instance B: `z = 1 + 0.2i` (`E ≠ 0`). `Ψ^{(B)}` = adjacency of `Z_4³` with `zdistD(x-y) = 1` (`Defs/Lattice.lean:108`); `m` solves `(self_m)` by damped iteration, `M = (g₀Ψ - E - m₀)⁻¹`; `M^{(+,-)}_{ab} = |M_{ba}|²`, `M^{(+,+)}_{ab} = M_{ba}M_{ab}`. Mirrors `flow_sz0` (`FlowPins.lean:1366`), which is compiled with `BAFlow` for all `n`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2360/inst3.py`
```
Admissible(c=1/6,dd=1/10): W>=N^c: 32 >= 11.314 True ; WO: W^(-d/2+dd)= 0.007812500000000002 <=g= 0.015625 <=1/dd= 10.0 True
[A: z=zS] z=0.3675i Im m=0.832488 t0=0.693740 E=0.000000 g0=0.013014 Im m0=0.999493 selfres(z)=0.0e+00 selfres(E,g0)=2.2e-16
   BAdom: kappa=0.5<=Im m:True; N^(-1+eps)=2.044e-06<=Im z<=1:True; t0>=kappa/(1+kappa)=0.3333:True
   BAReal(g0,kappa,E,m0): self_m at real E holds, Im m0=0.999493>=kappa:True; Ward max|rowsum(|M^T|^2)-1|=1e-15; rho(M^(+,+))=1.000000; max|M_aa|=0.9995<=1/Im m0=1.0005
   t=0.500: cond(1-tM^(+-))=1.0e+00 cond(1-tM^(++))=1.0e+00; rowsum Theta^(+-)=2.0000 vs 1/(1-t)=2.0000; Theta^(+-)_00=1.9980 <= B_(t,0)=2.0303
   t=0.999: cond(1-tM^(+-))=3.0e+00 cond(1-tM^(++))=1.0e+00; rowsum Theta^(+-)=1000.0000 vs 1/(1-t)=1000.0000; Theta^(+-)_00=520.4109 <= B_(t,0)=819.3927
   tau=0.5: B_g=2.03027 B_g0=2.03057 B_g<=B_g0<=B_g/t0:True; W^-d B_g=6.196e-05<=W^-2dd+(N(1-tau))^-1=5.000e-01:True; B_g>=1/(1+g^2):True
   tau=0.9: B_g=10.13190 B_g0=10.13934 B_g<=B_g0<=B_g/t0:True; W^-d B_g=3.092e-04<=W^-2dd+(N(1-tau))^-1=5.000e-01:True; B_g>=1/(1+g^2):True
   k=1..4 targets (W^-d B_(0.5,0))^(k-1): ['1.000e+00', '6.196e-05', '3.839e-09', '2.379e-13']
[B: z=1+0.2i] z=(1+0.2j) Im m=0.773358 t0=0.794526 E=0.993291 g0=0.013928 Im m0=0.867614 selfres(z)=5.6e-17 selfres(E,g0)=5.6e-17
   BAdom: kappa=0.5<=Im m:True; N^(-1+eps)=2.044e-06<=Im z<=1:True; t0>=kappa/(1+kappa)=0.3333:True
   BAReal(g0,kappa,E,m0): self_m at real E holds, Im m0=0.867614>=kappa:True; Ward max|rowsum(|M^T|^2)-1|=2e-15; rho(M^(+,+))=0.999427; max|M_aa|=0.9994<=1/Im m0=1.1526
   t=0.500: cond(1-tM^(+-))=1.0e+00 cond(1-tM^(++))=1.0e+00; rowsum Theta^(+-)=2.0000 vs 1/(1-t)=2.0000; Theta^(+-)_00=1.9977 <= B_(t,0)=2.0303
   t=0.999: cond(1-tM^(+-))=3.3e+00 cond(1-tM^(++))=1.0e+00; rowsum Theta^(+-)=1000.0000 vs 1/(1-t)=1000.0000; Theta^(+-)_00=488.4254 <= B_(t,0)=819.3927
   tau=0.5: B_g=2.03027 B_g0=2.03047 B_g<=B_g0<=B_g/t0:True; W^-d B_g=6.196e-05<=W^-2dd+(N(1-tau))^-1=5.000e-01:True; B_g>=1/(1+g^2):True
   tau=0.9: B_g=10.13190 B_g0=10.13689 B_g<=B_g0<=B_g/t0:True; W^-d B_g=3.092e-04<=W^-2dd+(N(1-tau))^-1=5.000e-01:True; B_g>=1/(1+g^2):True
   k=1..4 targets (W^-d B_(0.5,0))^(k-1): ['1.000e+00', '6.196e-05', '3.839e-09', '2.379e-13']
```

External-input limit check (TEAM §8 l.14). The BA inputs not merged for stage K (tree representation `A:584-598`, sum-zero `A:728-734`, row-wise Ward `BAWard`) enter the probe as hypotheses; their data `(m₀, M, t₀)` along `sz0` converge (command `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2360/inst.py | grep -E "^sz0|^  (t0|Im_m0|ward_rowsum_dev|self_res_real) =|Admissible"`, `n = 0, 1, 2`, `L = 4, 8, 12`; output verbatim, 2-space indent stripped):
```
sz0, n = 0
t0 = 0.6937399277285086
Im_m0 = 0.9994926192469118
self_res_real = 2.220446049250313e-16
ward_rowsum_dev = 1.3322676295501878e-15
Admissible: W>=N^c: 32 >= 11.31370849898476 True | WO: W^(-d/2+dd)= 0.007812500000000002 <= g= 0.015625 <= 10.0 True
sz0, n = 1
t0 = 0.6944442719774082
Im_m0 = 0.9999998758237262
self_res_real = 3.3306690738754696e-16
ward_rowsum_dev = 1.2212453270876722e-15
Admissible: W>=N^c: 1024 >= 90.50966799187806 True | WO: W^(-d/2+dd)= 6.103515625000004e-05 <= g= 0.000244140625 <= 10.0 True
sz0, n = 2
t0 = 0.6944444431151807
Im_m0 = 0.9999999990429299
self_res_real = 2.220446049250313e-16
ward_rowsum_dev = 4.440892098500626e-16
Admissible: W>=N^c: 7776 >= 305.47012947258844 True | WO: W^(-d/2+dd)= 3.5722450845907664e-06 <= g= 2.143347050754458e-05 <= 10.0 True
```
(limit `t₀ → 25/36 = 0.69444`, `Im m₀ → 1`, `g → 0`, `W^{-d}B_{τ,0} → 0` for fixed `τ`; the `≺` statements are asymptotic, so a finite `n` instance checks the hypotheses of the data, not the conclusion.)

### Verdicts
* K2 / pin `STKboundgL (baFMz sz z)`: **PASS** at the mathematical level. Every `Θ_BA` value of the K-loop bounds is at real `t ∈ [0,1)` with data `(g₀, κ, E, m₀)` satisfying `BAReal` for every `n` (rows 5-6); `BAReal` comes from `BAFlow` via `BAdom_real`, independent of `t`. No complex-`t` use is needed in the paper argument (`A:672-806` uses `Θ_t`, `tS^{(B)}Θ_t`, `t ∈ [0,1)`, `A:673`). Two points for the design, neither a gap: (a) the pin states `B` at `sz.lam = g`, the carrier `Θ` decays at `g₀`: constant `≤ ((κ+1)/κ)^{k-1}` (row 4), absorbed in `≺`, to be stated in the report; (b) the BA horizon is `BAflowT0`, not `lemT` (row 7).
* K1, K3, K4-K6 (file classification, paper status of `tree-representation_BA`, pure loops, sum-zero, `lem_WI_K`, row table): no hypothesis set or exponent obstructs; nothing here is BLOCKED. Observation from the paper text: `tree-representation_BA` is `[Lemma 4.16 of RBSO1D]` (`A:592`) and `lem_WI_K` is cited (`1_2:1043-1046`, "Lemma 3.17 of [RBSO1D]"), so for K3 the stage-1b design must either show class (g) or name the gap (TEAM §3); this preflight makes no claim about it.
* Overall: **PASS**.

## (a′) Preflight corrections — Fri Oct  9 20:01:27 UTC 2026
Section (a) is not edited; its verdicts stay PASS. Two statements are corrected or qualified by the stage-1b findings (`docs/reports/T2360-design.md`):
1. Row 1: `K^{(1)}` is `PropSpin m` by the third clause of `IsKLoopS` (`Loop/KLTree.lean:833`), not by `BAMLoop` (the datum for length ≥ 2); `‖PropSpin m σ‖ ≤ 1` is `BAm_norm_le_one` (`BA/Ward.lean:136`); the case `n = 1` of the target is proved (`BAKBoundAt_one`, probe 318).
2. Verdict K2 "PASS at the mathematical level" is for the paper's `𝒦`. The merged carrier uses `BAMLoop` (`BA/FlowPins.lean:274`), whose pairing of charges and labels differs from `(eq:KMloop)` (`1_2:1003`) for `n ≥ 3` with mixed charges (design F1, B8); row K00 repairs it before any proof of the pin. The exponent table and the instance of (a) involve no loop with mixed charges at `n ≥ 3` and are unchanged.

### (b) Script output — assembled Fri Oct  9 20:01:27 UTC 2026 (scratchpad subdirectory `S = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2360`; scripts `*.py`, `*.sh`, `*.lean` there, not in the repository; each block is the verbatim output of the command shown or named)
**B1 build and acceptance** (probe on branch `t/T2360`; the reports are in the main worktree as for T2348 and T2356, so the branch diff lists the probe)
```
Fri Oct  9 19:48:46 UTC 2026
$ lake env lean RBM3D/Probe/T2360Pins.lean; echo "exit=$?"; wc -l RBM3D/Probe/T2360Pins.lean
exit=0
     396 RBM3D/Probe/T2360Pins.lean
$ touch RBM3D/Probe/T2360Pins.lean; lake build RBM3D.Probe.T2360Pins 2>&1 | grep -E "T2360Pins|error"; lake build RBM3D.Probe.T2360Pins 2>&1 | tail -1
Build completed successfully (3764 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2360Pins.lean
0
$ git log -1 --format=%h; git status --short | wc -l; git diff --stat main...t/T2360
6a3b821
       0
 RBM3D/Probe/T2360Pins.lean | 396 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 396 insertions(+)
```
**B2 axioms** (`lake env lean S/ax.lean`: `#print axioms` of the 16 theorems of the probe, grouped by the printed axiom set)
```
16 declarations: [propext, Classical.choice, Quot.sound]
  precL_of_loss bparam_comp t0_ge BAKbound_of_uniform BAMLoop_witness kernelFacts_one kernelFacts_SB isKLoop_unique_of_UniqS baK_unique_of_UniqS KLindStepAt_iff BAKsol_isKLoopS BAKBoundAt_one inst_BAKbound Prec_of_loss KLsumZeroAt_iff BATheta_swap
```
**B3 statements** (`S/extract.py`: `lines: text`, definitions in full, theorems up to `:=`)
```
38-44: def BAKBoundAt (d n : ℕ) (Λ κ : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L), ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖ ≤ C * (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 1)
49-52: def BAKbound (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
110-160: theorem BAKbound_of_uniform (d : ℕ) (U : ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt d n Λ κ) : BAKbound d
180-197: theorem BAMLoop_witness : BAMLoop 1 3 1 witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ = 14 ∧ BAMLoop' 1 3 1 witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ = 15
232-237: def UniqS : Prop := ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ), (∀ a b, ‖S a b‖ ≤ 1) → ∀ {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M T K → IsKLoopS d L W S m M T K' → ∀ {T₀ R : ℝ}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R → (∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) → ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I
261-268: def IndStepAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (Bp : ι → ℝ) (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool) (r : Fin n), σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d (L i), ∑ b : Zd d (L i), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = b), Sig i σ δ * ∏ j ∈ Finset.univ.erase r, TH i (σ j) (σ (j + 1)) (a j) (δ j)‖ ≤ C * (L i : ℝ) ^ τ * (Bp i) ^ (n - 2)
281-290: def BAKsolve (d : ℕ) : Prop := ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m) (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧ ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L), K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂
306-314: def BAKward (d : ℕ) : Prop := ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 → ∑ x : Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: μ ++ [!s], a ++ [x]⟩ = (2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * m.im : ℝ) : ℂ))⁻¹ * (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨true :: μ, a⟩ - BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨false :: μ, a⟩)
318-335: theorem BAKBoundAt_one (d : ℕ) (Λ κ : ℝ) : BAKBoundAt d 1 Λ κ
343-347: theorem inst_BAKbound (U : ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt 3 n Λ κ) : STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0))
362-370: def BATreeRep (d : ℕ) (Γ : ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ → Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ) : Prop := ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L), BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, Γ L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a
374-378: def SumZeroAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ) (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (x : Zd d (L i)), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ 0 = x), Sig i (KLsigAlt n) δ‖ ≤ C * (1 - t i) ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ 0 = x), ‖Sig i (KLsigAlt n) δ‖ ≤ C * (g i ^ 2 + (1 - t i))
```
**B4 the compiled nonempty instance** (`sed -n 343,347p` of the probe; the witness `BAMLoop_witness` is in B3)
```
$ sed -n 343,347p RBM3D/Probe/T2360Pins.lean
theorem inst_BAKbound
    (U : ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt 3 n Λ κ) :
    STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) :=
  BAKbound_of_uniform 3 U le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0
```
`inst_BAKbound` is `BAKbound_of_uniform` at `d = 3`, `sz0`, `zSeq`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, with `BAFlow` from `flow_sz0` (`FlowPins.lean:1366`); the one open hypothesis `U` is the stage-K uniform bound (rows K00-K12). `BAKBoundAt_one` (probe 318) has no hypothesis. Names: 59 `#check @NAME` (58 used by the probe, `IsKLoop_iff_IsKLoopS` cited in the design) gave 0 errors (`lake env lean S/chk_names.lean`, exit 0, 0 lines with `error`).
**B5 name clash and ports** (`bash S/b5.sh`, the `T2360` grep omitted)
```
$ NAMES=$(grep -oE "^(theorem|def|structure) +[^ (:{\[]+" RBM3D/Probe/T2360Pins.lean | awk '{print $NF}'); echo $NAMES | wc -w
      27
$ for n in $NAMES; do grep -rnE "^\s*(private |noncomputable |protected )*(theorem|lemma|def|abbrev|structure|inductive|instance) +([A-Za-z0-9_.]*\.)?$n( |$|\(|:)" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe/T2360Pins.lean"; done | wc -l
       0
$ grep -c "RBM1D\|RBM2D" RBM3D/Probe/T2360Pins.lean
0
names: BAKBoundAt BAKbound precL_of_loss bparam_comp t0_ge BAKbound_of_uniform BAMLoop' witM BAMLoop_witness KernelFacts kernelFacts_one kernelFacts_SB UniqS isKLoop_unique_of_UniqS baK_unique_of_UniqS IndStepAbs KLindStepAt_iff BAKsolve BAKsol_isKLoopS BAKward BAKBoundAt_one inst_BAKbound Prec_of_loss BATreeRep SumZeroAbs KLsumZeroAt_iff BATheta_swap
```
No port from RBM1D/RBM2D (the probe names neither, last command above); the one adaptation is of the private RBM3D lemma `KLFinal_prec_of_loss` (`Loop/KLFinal.lean:212`), generalised to any law as `precL_of_loss` (probe 58).
**B6 K1 evidence** (`python3 S/k1rows.py table`; the segments of `k1rows.py segments` are in design §1; `S/consumers.py` on 20 names, paths shortened by `sed`; the greps; counts are `wc -l`, the class of each segment is a reading of the file, not compiled)
```
file           lines   H+I     R     G     T     X | band-token lines / code lines (non-H/I)  star-tree-object lines  kProd
KBound           154    53    73    28     0     0 |    1 /   69 =  1%      0   0
TreeRep          188    47   141     0     0     0 |    4 /   90 =  4%      0   0
KLTree           976   159   408    83   326     0 |   96 /  581 = 16%     30   0
KLTreeDeriv     1153   163     0     0   990     0 |  132 /  862 = 15%     26   0
TreeThree        471    40     0     0   431     0 |  121 /  366 = 33%      0   0
TreeFour         252    30     0     0     0   222 |   50 /  165 = 30%      0   0
PureLoop         290    46     0     0   244     0 |    9 /  199 =  4%      0   0
KLMolecule      1029   195     0     0   834     0 |   47 /  695 =  6%     25   0
KLSumZero       1080   295    88     0   697     0 |   61 /  646 =  9%     19   0
KLSumZeroWard   1265   154   174     0   937     0 |   75 /  938 =  7%      4   0
KLSumAll         842   164   146     0   532     0 |   62 /  597 = 10%      0   0
KLWard          1224   126   132   966     0     0 |  130 /  943 = 13%      0   0
KLWardIneq      1083   205     0     0   878     0 |  169 /  768 = 22%     31   0
KLUnique         766   217    93   456     0     0 |   37 /  464 =  7%      0   0
KLCut           1648   381   829     0   438     0 |    0 / 1075 =  0%     28   0
KLFinal          541   209    52   149   131     0 |   22 /  250 =  8%      0   0
KLInduct        1394   278    22   258   836     0 |  234 /  970 = 24%     61   0
KLIndStepA      1474   266   255   686   267     0 |  180 / 1024 = 17%     32   0
KLIndStepB       947   138   197   612     0     0 |   97 /  709 = 13%     28   0
TOTAL          16777  3166  2610  3238  7541   222 | 1527 / 11411 = 13%    284   0

outside the 19: Unique      374 lines: H+I 53, R 59, G 197, T 65
outside the 19: Primitive   159 lines: H+I 38, R 0, G 0, T 121
isKLoop_unique  [defined in Unique]  used in: KLUnique(1)
KLretire_twoLoopBounded  [defined in Unique]  used in: KLUnique(4), KLWard(1), TreeThree(1)
kTwoFormula_of_isKLoop  [defined in Unique]  used in: KLUnique(1), TreeThree(1)
pureLoop_two_of_isKLoop  [defined in Unique]  used in: KLUnique(1)
KLK_unique  [defined in KLUnique]  used in: KLWard(1)
KLK_rotate  [defined in KLUnique]  used in: Gr/LWExpTerm(1), Gr/LWExpTerm4(1), I/ExpWardII(1), I/NewPQ(1), I/SEforLn1(1), I/SEforLn2(1), I/WardII(1), KLSumAll(1), KLWard(1)
KLK_translate  [defined in KLUnique]  used in: KLSumAll(1)
KLK_ward  [defined in KLWard]  used in: I/B45(1), I/NewPQ(1), I/QLevelsA(1), KLSumAll(1)
KLWard_flip  [defined in KLWard]  used in: 
KLindStep_nonAlt  [defined in KLIndStepA]  used in: KLIndStepB(1)
KLindStep_alt  [defined in KLIndStepB]  used in: 
KLindStepAt_holds  [defined in KLIndStepB]  used in: 
KLindStepPin_holds  [defined in KLIndStepB]  used in: KLInduct(2), KLWardIneq(2)
KLInduct_BoundAt_of_Kpi  [defined in KLInduct]  used in: 
KLboundPin_holds  [defined in KLInduct]  used in: KLFinal(1)
KLKpiBoundPin_holds  [defined in KLInduct]  used in: 
stKbound_holds  [defined in KLFinal]  used in: I/KDecay(1), I/NQEndLin(2), I/QDriftA(2), I/QDriftB(1), I/QEndA(3), I/QEndGrid(3), I/QtNonzeroEnd(2)
stKward_holds  [defined in KLFinal]  used in: I/KDecay(1)
KLbound_holds  [defined in KLFinal]  used in: I/NQEndFlowLift(1)
KLK_isKLoop  [defined in KLTreeDeriv]  used in: I/AzumaProxyN(1), I/GridDriftN(1), I/HierAlgebra(1), I/NQEndFlowLift(1), KLUnique(3), KLWard(2)
$ grep -rn "BAMLoop" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe" | cut -c1-120
RBM3D/BA/FlowPins.lean:274:def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
RBM3D/BA/FlowPins.lean:283:    (∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLo
RBM3D/BA/FlowPins.lean:286:      (BAMLoop d L W M) (Set.Ico (0 : ℝ) 1) K then h.choose else fun _ _ => 0
$ grep -rn "baFM" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe" | wc -l; (same) | cut -d: -f1 | sort -u | wc -l; grep -rln "baFM" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe" | xargs grep -l "BAMLoop" | wc -l
     302
      10
       1
$ grep -rn "kProd" RBM3D/Loop/{KBound,KLInduct,KLIndStepA,KLIndStepB,KLTree,KLTreeDeriv,TreeRep,TreeThree,TreeFour,PureLoop,KLMolecule,KLSumZero,KLSumZeroWard,KLSumAll,KLWard,KLWardIneq,KLUnique,KLCut,KLFinal}.lean | wc -l
       0
$ grep -n "sbKernel" RBM3D/Loop/{KBound,KLInduct,KLIndStepA,KLIndStepB,KLTree,KLTreeDeriv,TreeRep,TreeThree,TreeFour,PureLoop,KLMolecule,KLSumZero,KLSumZeroWard,KLSumAll,KLWard,KLWardIneq,KLUnique,KLCut,KLFinal}.lean | cut -c1-90
RBM3D/Loop/KLWard.lean:998:  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]
```
**B7 row table** (`python3 S/k1rows.py rows`; ratios by `wc -l` of the merged files; `g` from `T2326-pilot.md` §0 (0.148, 0.241, 0.303), twin ratios 0.73 and 0.85 from `T2325-portmap.md:23`; TW = 0.73/0.85/1.11, CT = 0.85/1.20/2.10, `g` = 0.15/0.24/0.30)
```
measured BA / band line ratios of the merged stage-P twins (wc -l):
  BA/Prop5                        1479 /  1399 = 1.06
  BA/PropUnit                     1119 /  1008 = 1.11
  BA/Prop5Short                    814 /   506 = 1.61
  BA/Prop6Path                    1178 /   560 = 2.10
  BA/KHeat+KHeatTail+KHeatDiff    3963 /  2152 = 1.84

row   kind    lo central    hi  deps              role         basis
K00   b      503     579   744  -                 prover-hard  634 (Propagator Basic+Deriv+Props4) x TW + 40
K01   g      323     452   571  K00               prover-hard  653 G x g + 5 wrappers x 15 + BA instances 150/220/300
K02   g      425     612   770  K01               prover-hard  966 G x g + 2 wrappers x 15 + BA instance 250/350/450
K03   t      550     624   785  K01               prover-hard  617 T x TW + 100
K04   b      500     700  1000  K00               prover-max   assumed 500/700/1000 (no band base: the cactus is new; band star API KLTree 1-5: 458 lines)
K05a  t      660     932  1630  K03,K04           prover-max   1553 T x CT / 2
K05b  t      660     932  1630  K05a              prover-max   1553 T x CT / 2
K06   t      482     680  1191  K05b              prover-hard  567 T x CT
K07   t      718    1014  1774  K06               prover-hard  845 T x CT
K08a  t      978    1380  2415  K02,K07           prover-max   2300 T x CT / 2
K08b  t      978    1380  2415  K08a              prover-max   2300 T x CT / 2
K09a  g      355     472   549  -                 prover-hard  1298 G x g + 4 wrappers x 15 + BA 100
K09b  g      234     357   472  K09a,K08b         prover-hard  258 G x g + 3 wrappers x 15 + BA 150/250/350
K10   t      771    1063  1816  K05b,K06          prover-hard  836 T x CT + 60
K11   t      746    1054  1844  K02,K10           prover-hard  878 T x CT
K12   b      350     500   700  K09b,K10,K11,K08b prover-hard  assumed 350/500/700 (band assembly KBound+KLTree+KLFinal G/T: 391 lines)
sum         9233   12731 20306   rows = 16;  (t)-rows only: 6543 / 9059 / 15500;  per-stage flag 1.5 x 16 = 24
```
**B8 numerics** (`S/{conv,kode,kn2,mgraph,conv2,ward,molecule,molecule2}.py`, `kode.py | head -1`; ODE `treeEqRhsS` with `S = I`, `W = 1`, RK4; `Z_q`, `d = 1`; BA data from `(self_m)`)
```
trace    (0.03484137640376931-0.00042930929096613585j)
paper    (0.03484137640376931-0.00042930929096613585j)
BAMLoop  (-0.013202634097564003+0.03224587212438645j)
2 max |trace-paper| so far 5.551115123125783e-17 | #(sigma,a) with |trace-BAMLoop|>1e-9: 0 max diff 5.551115123125783e-17
3 max |trace-paper| so far 5.551115123125783e-17 | #(sigma,a) with |trace-BAMLoop|>1e-9: 108 max diff 0.07700689971230097
4 max |trace-paper| so far 5.551115123125783e-17 | #(sigma,a) with |trace-BAMLoop|>1e-9: 876 max diff 0.07700689971230097
m = (0.03664599576077138+0.6998656616013607j)  |m| = 0.7008244240136103  Ward row sum |M_ab|^2: 1.0000000000000002  ward M-M* vs 2i Im m M M*: 2.482534153247273e-16
(Kn2sol) BA: max |K^(2)_ODE - Theta^(s1 s2) M^(s1 s2)| = 4.1e-12  (q=5 g=0.8 E=0.3 t=0.6; W=1)
TSP sizes {3: 1, 4: 3, 5: 11, 6: 45, 7: 197}
q=5 g=0.8 E=0.3 t=0.5: {3: '#trees=1 max|tree-ODE|=9.84e-13 max|K|=6.42e-01', 4: '#trees=3 max|tree-ODE|=1.48e-11 max|K|=7.60e-01', 5: '#trees=11 max|tree-ODE|=2.75e-11 max|K|=7.34e-01'}
q=4 g=0.6 E=-0.4 t=0.7: {3: '#trees=1 max|tree-ODE|=1.32e-10 max|K|=1.83e+00', 4: '#trees=3 max|tree-ODE|=3.36e-09 max|K|=3.81e+00', 5: '#trees=11 max|tree-ODE|=1.07e-08 max|K|=5.96e+00'}
q=3 g=1.1 E=0.0 t=0.6: {3: '#trees=1 max|tree-ODE|=2.94e-11 max|K|=1.45e+00', 4: '#trees=3 max|tree-ODE|=7.23e-10 max|K|=2.98e+00', 5: '#trees=11 max|tree-ODE|=2.52e-09 max|K|=5.07e+00', 6: '#trees=45 max|tree-ODE|=1.98e-08 max|K|=1.12e+01'}
paper n=3: max|K_ODE - tree(sigma)|=1.21e-11   vs tree(rot sigma by +1)=3.71e-01  by -1=3.71e-01   max|K|=1.30e+00
paper n=4: max|K_ODE - tree(sigma)|=2.91e-10   vs tree(rot sigma by +1)=5.26e-01  by -1=5.26e-01   max|K|=2.16e+00
lean  n=3: max|K_ODE - tree(sigma)|=3.18e-01   vs tree(rot sigma by +1)=1.74e-01  by -1=3.82e-01   max|K|=1.24e+00
lean  n=4: max|K_ODE - tree(sigma)|=6.21e-01   vs tree(rot sigma by +1)=4.46e-01  by -1=4.46e-01   max|K|=2.19e+00
paper q=5 g=0.8 E=0.3 t=0.5: {2: 'max|WI defect|=3.0e-12 (max|rhs|=2.00e+00)', 3: 'max|WI defect|=2.8e-12 (max|rhs|=1.64e+00)', 4: 'max|WI defect|=5.3e-11 (max|rhs|=1.83e+00)'}
paper q=4 g=0.6 E=-0.4 t=0.7: {2: 'max|WI defect|=1.6e-10 (max|rhs|=3.33e+00)', 3: 'max|WI defect|=3.4e-10 (max|rhs|=4.03e+00)', 4: 'max|WI defect|=9.7e-09 (max|rhs|=7.79e+00)'}
lean q=5 g=0.8 E=0.3 t=0.5: {2: 'max|WI defect|=3.0e-12 (max|rhs|=2.00e+00)', 3: 'max|WI defect|=6.7e-01 (max|rhs|=1.64e+00)', 4: 'max|WI defect|=5.5e-01 (max|rhs|=1.71e+00)'}
lean q=4 g=0.6 E=-0.4 t=0.7: {2: 'max|WI defect|=1.6e-10 (max|rhs|=3.33e+00)', 3: 'max|WI defect|=1.2e+00 (max|rhs|=4.03e+00)', 4: 'max|WI defect|=1.9e+00 (max|rhs|=7.24e+00)'}
n=4, sigma_alt, q=5, g=0.8, E=0.3, eta0 = Im m = 0.6999
  t=0.9      signed slice sum (x=0..): [0.10616659+0.j 0.10616659+0.j 0.10616659+0.j]   |sum|/(1-t) = 1.0617   abs slice sum = 2.4473
  t=0.999    signed slice sum (x=0..): [0.00102119-0.j 0.00102119-0.j 0.00102119+0.j]   |sum|/(1-t) = 1.0212   abs slice sum = 2.3601
  t=0.99999  signed slice sum (x=0..): [1.021e-05+0.j 1.021e-05-0.j 1.021e-05-0.j]   |sum|/(1-t) = 1.0208   abs slice sum = 2.3592
  t=1.0      signed slice sum (x=0..): [-0.+0.j -0.+0.j  0.-0.j]   |sum|/(1-t) = nan   abs slice sum = 2.3592
n=6, q=3, g=1.1, E=0.0
   t=0.999: signed slice sum[x=0] = -3.927e-03-2.359e-16j   /(1-t) = 3.9274
   t=1.0: signed slice sum[x=0] = 1.277e-15-1.249e-16j   /(1-t) = nan
n=4, q=4, g=0.5, E=0.2
   t=0.999: signed slice sum[x=0] = 7.171e-04-1.605e-17j   /(1-t) = 0.7171
   t=1.0: signed slice sum[x=0] = -1.388e-16-1.019e-17j   /(1-t) = nan
```
**B9 `d = 3` check of the uniform pin** (`python3 S/bound3d_main.py`; `Z_L^3`, `Ψ` = adjacency, `m` from `(self_m)`, `M = (gΨ-E-m)⁻¹`, `W = 1`; `K^{(2)} = Θ^{(σ₁σ₂)}M^{(σ₁σ₂)}`, `K^{(n)} = Σ_{F∈TSP(n)} Γ_M(F)` for `n ≥ 3` (design §3 (a)); `B = (g²+1-t)⁻¹ + (L³(1-t))⁻¹`; prints `max_{σ,a}|K^{(n)}|/B^{n-1}`; of the 4 data sets the rows `1-t` = 1e-01, 1e-02 and the last are shown (they contain the extreme ratios of the full output), the full output is `S/out/bound3d_main.txt`)
```
d=3 L=3 q=27 g=0.1 E=0.3: m=-0.14406+0.96057j, Ward row sum=1.000000000000, W=1
  1-t=1e-01: B=9.461e+00  max|K^(n)|/B^(n-1): n=2: 0.675 | n=3: 0.257 | n=4: 0.184 | n=5: 0.098
  1-t=1e-02: B=5.370e+01  max|K^(n)|/B^(n-1): n=2: 0.341 | n=3: 0.062 | n=4: 0.026 | n=5: 0.007
  1-t=1e-05: B=3.804e+03  max|K^(n)|/B^(n-1): n=2: 0.978 | n=3: 0.498 | n=4: 0.510 | n=5: 0.390
d=3 L=4 q=64 g=0.2 E=0.3: m=-0.12491+0.89737j, Ward row sum=1.000000000000, W=1
  1-t=1e-01: B=7.299e+00  max|K^(n)|/B^(n-1): n=2: 0.459 | n=3: 0.135 | n=4: 0.072
  1-t=1e-02: B=2.156e+01  max|K^(n)|/B^(n-1): n=2: 0.292 | n=3: 0.052 | n=4: 0.020
  1-t=1e-05: B=1.587e+03  max|K^(n)|/B^(n-1): n=2: 0.987 | n=3: 0.544 | n=4: 0.600
d=3 L=3 q=27 g=1.0 E=0.3: m=-0.15080+0.66958j, Ward row sum=1.000000000000, W=1
  1-t=1e-01: B=1.279e+00  max|K^(n)|/B^(n-1): n=2: 0.864 | n=3: 0.758 | n=4: 1.155 | n=5: 1.295
  1-t=1e-02: B=4.694e+00  max|K^(n)|/B^(n-1): n=2: 0.958 | n=3: 0.768 | n=4: 1.328 | n=5: 1.568
  1-t=1e-04: B=3.714e+02  max|K^(n)|/B^(n-1): n=2: 0.999 | n=3: 0.747 | n=4: 1.119 | n=5: 1.255
d=3 L=5 q=125 g=0.5 E=0.3: m=-0.06686+0.66385j, Ward row sum=1.000000000000, W=1
  1-t=1e-01: B=2.937e+00  max|K^(n)|/B^(n-1): n=2: 0.285 | n=3: 0.086
  1-t=1e-02: B=4.646e+00  max|K^(n)|/B^(n-1): n=2: 0.349 | n=3: 0.117
  1-t=1e-04: B=8.400e+01  max|K^(n)|/B^(n-1): n=2: 0.962 | n=3: 0.703
```

**Narrative** (prover `claude-sonnet-5-5`, prover-max)
1. Stage 1b of a design ticket (CONTROL H149), resumed after the first run stopped. Deliverables: the probe `RBM3D/Probe/T2360Pins.lean` (396 lines, limit 400; commits `6c44cb4`, `dde4614`, `6a3b821`) and `docs/reports/T2360-design.md` (written in the main worktree, as for T2356). No Lean file in the repository other than the probe (the scratchpad `.lean` files only print axioms and `#check` names). The design report answers K1-K6, its counts, tables and rows are the outputs of B6 and B7; K5 is flagged (16 rows). Stop rule (CONTROL H134): probe 396 ≤ 400 lines, both reports within 300 lines; no stop was triggered.
2. The probe: the target `BAKbound` and its uniform form `BAKBoundAt`; the reduction `BAKbound_of_uniform` (proved; uses the merged `BAflow_real`, `BAflow_lam0_window`, `BAdom`) with its instance `inst_BAKbound`; the case `n = 1` (`BAKBoundAt_one`, proved); the carrier finding (`BAMLoop'`, witness 14 against 15); the class-(g) pins `KernelFacts`, `UniqS`, `IndStepAbs`, `SumZeroAbs`, with the band statements re-derived (`isKLoop_unique_of_UniqS`; `KLindStepAt_iff`, `KLsumZeroAt_iff` by `Iff.rfl`); the BA inputs as interface pins (`BAKsolve`, `BAKward`, `BATreeRep` with `Γ` a parameter); `BATheta_swap`. The unmerged inputs are hypotheses (`U`, `H : UniqS`, `h : BAKsolve d`), no `axiom`, no `sorry`.
3. Finding F1 changes the plan: the merged `BAMLoop` is not the paper's `(eq:KMloop)`; with it the ODE solution misses the tree representation and `(WI_calK)` (B8: 0.32 and 0.67 against sizes 1.2 and 1.64 at `n = 3`), with the paper form both hold to 1e-8. It is not an error of (a); (a′) records it.
4. The numerics of B8 and B9 are Python (3.9.6, `numpy` 2.0.2, `scipy` 1.13.1), not Lean. B8: finite cycles `Z_q`, `d = 1`, `q ≤ 5`, RK4 with 300 steps, errors up to 2.0e-8; they check algebraic identities (tree representation to `n = 6`, Ward to `n = 4`, `(Kn2sol)`, the first sum-zero estimate to `n = 6`), not the bounds. B9: tori `Z_L^3`, `L ≤ 5`, `W = 1`, `n ≤ 5`; it evaluates the tree sum (checked against the ODE only in B8, `d = 1`) and compares with `B^{n-1}`. The `M`-graph rules of design §3 are my reading of `A:552-583`; their only confirmation is the agreement with the ODE.
5. Limits: the row sizes are assumptions with measured end points (B7); the segment classes of B6 are a reading of the files, they are not compiled; the second sum-zero estimate and the molecule decay are not tested; B9 is a finite-size check at `W = 1`, not a limit `N → ∞`; the carrier form of `STKward` does not exist (`grep STKwardgL`: 0), design §7.

### (c) Verified names (run Fri Oct  9 19:56:35 UTC 2026; `lake env lean S/chk_names.lean`, `#check @NAME`, 59 names, exit 0, 0 lines with `error`)
Mathlib: `Complex.conj_ofReal` `Finset.sum_congr` `Matrix.one_apply` `Matrix.transpose_apply` `List.ofFn_succ` `Nat.cast_nonneg` `Nat.cast_zero` `Nat.pos_of_ne_zero` `Nat.sub_self` `Real.rpow_add'` `Real.rpow_nonneg` `Real.rpow_pos_of_pos` `Real.sq_sqrt` `Set.mem_empty_iff_false` `abs_nonneg` `abs_pos` `add_halves` `div_le_div_iff₀` `eventually_ge_atTop` `if_congr` `inv_eq_one_div` `inv_one` `inv_pos` `le_div_iff₀` `lt_of_lt_of_le` `mul_div_assoc` `mul_le_mul` `mul_le_mul_of_nonneg_left` `mul_le_mul_of_nonneg_right` `mul_pow` `one_pos` `pow_le_pow_left₀` `pow_nonneg` `sq_nonneg` `tendsto_rpow_atTop` `Filter.Tendsto.eventually_ge_atTop` `zero_le_one` `eq_comm`.
RBM3D: `BAflow_lam0_window` `BAflow_real` `BAm_norm_le_one` `BAt0_pos` `KLone_le_rpow` `SB_apply` `SB_transpose` `norm_SB_apply_le` `sbKernel_eq_ofReal` `sum_SB_row` `Sizes.L_rpow_le` `StochDomAt.of_eventually_empty` `FlowPinsInst.flow_sz0` `FlowPinsInst.zSeq` `SizesInst.sz0` `Sizes.Bctl` `Sizes.seqP` `Sizes.three_le_L` `Sizes.W_pos` `Sizes.one_le_size` `IsKLoop_iff_IsKLoopS`.
Verified absent from RBM3D (declaration-level grep, 0): the 27 new names of B5; `STKwardgL`.

### (d) Open issues and paper-delta candidates
* Open issues: (1) repair mode of F1 (design §7.1); (2) route G in place for K01, K02, K09a, K09b (§7.2); (3) the TEAM §3 status of K05 and K08, whose proofs the paper only cites (§7.3); (4) the closing conditions of stage K: `BAKsolve`, `BAKward` and a carrier form of `STKward` (§7.4); (5) the old K rows of `T2161-portmap.md:1010-1014` (5 rows, 6.1k central, `:975`) are superseded by the 16 rows.
* Paper-delta candidates (temporary tags; the dispatcher numbers them): `T2360a` the merged `BAMLoop` pairs `σ_i` with `(a_i, a_{i+1})`, `(eq:KMloop)` (`1_2:1003`) and the `M`-loop rule `A:571` with `(a_{i-1}, a_i)`; `T2360b` `(f-internal2)` with `S^{(B)} = I` reads `tΘ^{(σ_i,σ_j)}`, and which region an `M`-edge lies in (`A:570-574`) is read from the figure, design §3 (a) states it combinatorially; `T2360c` `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}` for the symmetric BA `M` (remark; `BATheta_swap`, probe 387); `T2360d` `BATreeRep` (probe 362) states `n ≥ 3` where `tree-representation_BA` states `n ≥ 4` (`A:593`); `n = 3` is `(Kn3sol)` (`1_2:1176`), the same formula with one tree; `T2360e` `BAKBoundAt` (probe 38) reads `≺` of `ML:Kbound` as a loss `C L^τ` with `C` uniform in `L`, `W`, `g ≤ Λ`, `E`, `t` (the merged convention of `KLBoundAt`), stronger than the paper's `≺`; `BAKbound_of_uniform` (probe 110) is the implication.
