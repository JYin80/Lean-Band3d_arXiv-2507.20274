Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:13:30 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `y = N^{-A}` (continuity modulus), `x = (1-t)^{-1}|u-u'| ≤ N y` (premise `1-t ≥ N^{-1+ε/2}`, so `(1-t)^{-1} ≤ N`), `Q = (η_t)^{-1} ≤ N²`, `Xb = 2N²`, `δ = Q²(Xb+1)√y ≤ 3N^6 N^{-A/2}`, `k = zdistInf(STblk x - STblk y) ≤ L`. Sources: RBM2D `Path/NetLift.lean` at `c9a24cf` (read by `git show`), merged `Induction/{Step2Defs,Defs,ContinuityNet,Continuity}.lean`, `Path/NetLift1.lean`, `Defs/{Sizes,Params}.lean`.

### What is to be proved, and how the three conjuncts assemble `STNetLift2`
`STNetLift2` (`Step2Defs.lean:581`): after `κ ε 𝔡 𝔠 sz z (STFlow) s t (0≤s) (s≤t) (t≤lemT z) Cd` and the three per-time hypotheses `STStep2LocalPT ∧ STStep2AvgPT ∧ STStep2DecayPT` (each a `PrecPT`, i.e. already per time over `TimeIcc s t n × V n`), the goal is `STStep2Local ∧ STStep2Avg ∧ STStep2Decay` (each a `Prec`). So no diagonal step (`perTime_of_sections` of `stNetLift_holds`) is needed; each conjunct is the abstract net lift `cont_core` (public, `ContinuityNet.lean:142`) on its own `V n`, the three being independent. Assembly: `⟨local_lift hL, avg_lift hA, stNetLift2_part1 … hD⟩`, premises `0<κ`, `|E_n| < 2-κ/2`, `t_n<1`, `RangeCond (ε/2) t`, `N→∞` from `Green.v3_premises_of_stFlow` + `Admissible` exactly as `stNetLift_holds` (`Continuity.lean:777`). The unused hypotheses are dropped per conjunct. No conjunct is false as the pin stands (checked in (i)–(ii) below): no stop.
Declarations (RBM2D line -> RBM3D):
- `Step2LocalUnif :1343` = merged pin `STStep2Local` (not redefined). `Step2LocalNetLift :1351` -> `Step2LocalNetLift sz E κ τ s t` (shape of `Step1NetLift`: `0<κ → |E n| ≤ 2-κ → 0<τ → 0≤s → s≤t → t<1 → SizeTendsto → RangeCond τ t → STStep2LocalPT → STStep2Local`); `Bandwidth`, `CondStInd` dropped (unused, T2062a/T2074a); no `WO` needed (`STWB` ratio holds for any `lam`).
- `step2LocalNetLift :1518–1595` -> same name, proof by `cont_core` with `V n = Idx d L W × Idx d L W`, `ξ = ‖STGM‖²`, `ζ = STWB(u,k)`, `ε = N^{-1}`, `A = 40`, `Cv = 2`.
- `netLift_llErr_diff :622` -> entry difference of `‖G_u - G_{u'}‖_max ≤ δ`: from public `cont_green_flow_diff` plus `norm_matrix_entry_le_opNorm` (the merged `cont_entry_diff` is `private` in `Continuity.lean`); `llErrMat` is the entry of `STGM`, so `|ξ_u - ξ_{u'}|` with `ξ = ‖·‖²` needs the extra factor `2‖b‖+δ`, `‖b‖ = ‖(G_{u'}-M)_{xy}‖ ≤ N²+1` (`‖G‖_op ≤ Q`, `‖m(E)‖ ≤ 1`). RBM2D used `ξ = |llErr|` (no square) against `M_u^{-1/2}`.
- `netLift_T2_low :1244` -> `N^{-1} ≤ STWB sz n u K` for `0 ≤ u < 1`, every `K`: `STWB = W^{-d}[(g²+(1-u))^{-1}((K+1)^{d-2})^{-1} + (L^d(1-u))^{-1}] ≥ W^{-d}(L^d)^{-1} = N^{-1}` (first term `≥ 0`); `K=0` is `cont_inv_size_le_Bctl`, general `K` new (RBM2D: `M_u^{-1/2} ≥ N^{-1/2}`).
- `netLift_T2_close :1251–1324` -> two closeness facts `ξ_u ≤ ξ_{u'} + N^{-1}` and `ζ_{u'} ≤ 2ζ_u` (ratio: `STWB(u,K) ≤ (1+x)STWB(u',K)`, both terms of `Bparam`; `nl_STWB_ratio` in NetLift1 is `private`, to be recopied; `scaleM_ratio`, `(11/10)^{1/2} ≤ 2` of RBM2D are replaced by `1+x ≤ 11/10 ≤ 2`).
- New (no RBM2D counterpart; RBM2D has Decay and Local only): `STStep2Avg` lift. `ξ = ‖Lloop(true,a) - m(E)‖`, `ζ = Bctl(u)`, `V n = Zd d L` (`k=1` loop), `ξ_u ≤ ξ_{u'} + ‖L_u - L_{u'}‖` (triangle, since `m(E)` is `u`-independent), modulus from `nl_loop_sub` at `k=1` (`private` in NetLift1: recopy; `‖·‖` of the difference, not the difference of norms), `ε = N^{-1} ≤ Bctl` (`cont_inv_size_le_Bctl`), ratio `cont_Bctl_ratio` (public), `A = 6·1+16 = 22`, `Cv = 1`.
- `stNetLift2_holds (d) : STNetLift2 d` by the assembly above.
Finding: everything of NetLift1 beyond `Step2NetLift`, `step2NetLift`, `stNetLift2_part1` is `private` (`grep -n "^private" RBM3D/Path/NetLift1.lean`), so `nl_eta_inv_le`, `nl_loop_sub`, `nl_STWB_ratio`, `nl_STWB_nonneg` needed here must be recopied as `private` helpers of NetLift2 (the ticket's "do not copy" can only apply to the three public names). Not a block.

### (i) Exponent table
| item | value | constraint | slack |
|---|---|---|---|
| Local: time modulus `A_L` | `40` (as `STStep1Weak`) | `N·N^{-A} ≤ 1/10`; `δ(2N²+3+δ) ≤ N^{-1}`, `δ = 3N^{6-A/2}`: exponent `6-A/2+2 ≤ -1` i.e. `A ≥ 18` (+ constants, `N ≥ 2`) | `A-18 = 22`; at `sz0`: `10^{-75.1}` vs `10^{-6.32}` |
| Local: `Cv_L` | `2` | `#V = #Idx² = N²` (`card_Idx`) | `0` (equality) |
| Local: `ε` | `N^{-1}` | `ε ≤ ζ = STWB(u,K)` for all `K`, `0 ≤ u < 1` (zero-mode term `≥ N^{-1}`) | `STWB` at `sz0` `10^{-4.5}…10^{-5.2}` vs `10^{-6.32}`; `1/(1-u) ≥ 1` |
| Local: ratio `ζ_{u'} ≤ 2ζ_u` | `1+x ≤ 11/10` | `x ≤ N^{1-A} ≤ 1/10`, `STWB(u',K) ≤ (1+x)STWB(u,K)` | `2 / (11/10)`; `x ≤ 10^{-246}` at `sz0` |
| Avg: time modulus `A_A` | `22 = 6k+16`, `k=1` | `N·N^{-A} ≤ N^{-1}`; `N·(1·N²·3N^{6-A/2}) ≤ N^{-1}`: `3N^{-2} ≤ N^{-1}` | `N ≥ 3`; `N/3` at `N = 2^21`; `10^{-12.2}` vs `10^{-6.32}` |
| Avg: `Cv_A` | `1` | `#V = L^d ≤ N = W^d L^d` (`W ≥ 1`) | factor `W^d` (`32768` at `sz0`) |
| Avg: `ε`, ratio | `N^{-1}`; `Bctl(u') ≤ (1+x)Bctl(u)` | `N^{-1} ≤ Bctl` (`cont_inv_size_le_Bctl`), `1+x ≤ 2` | as Local |
| `cont_core` net | size `⌈N^{A+1}⌉+1`, mesh `N^{-A-1} ≤ y` | `hA: 0 ≤ A`, `hCv: 0 ≤ Cv`; union `N^{A+2+Cv}` absorbed by `stochDomAt_of_perTimeDomAt` | factor `N`; polynomial in `N` only |
| `‖m(E)‖` , `‖G‖_op` | `≤ 1`, `≤ Q ≤ N²` | `Q = (1-t)^{-1}(Im m)^{-1} ≤ N·N`, `1/c₁ ≤ N`, `c₁ = √(2κ')/2`, `κ' = κ/2` | `N ≥ 1/c₁ ≈ 6.3`; `Q = 1.10` at the instance |
| premises of `STFlow` | `|E_n| < 2-κ/2`, `t_n < 1`, `1-t_n ≥ N^{-1+ε/2}` (`τ = ε/2`) | `t ≤ lemT z` (§29), `0 ≤ s` (so `u ≥ 0`, needed in the floor), `N → ∞` | eventual in `n` only; `∀ n` inputs `s,t` as in the pin |
| `g = sz.lam n` | none | the `ζ` ratio holds for every `g ≥ 0` (`γ = g²` in `cont_inv_add_one_sub_ratio`) | no `WO`, no `𝔡` used |

Replacements of every `d = 2` token of part 2 of the source: `Idx L W` -> `Idx d L W`; `(W*L)^2` -> `(sz.size n)`; `scaleM L W E u` (the `d=2` scale `M_u`, control `M_u^{-1/2}` on `|G-M|`) -> `STWB sz n u K` on `‖G-M‖²` (`ε = N^{-1/2}` -> `N^{-1}`; `netLift_scaleM_le/_ratio` -> `cont_inv_size_le_Bctl`-type floor and `1+x` ratio); `spectralZ/spectralM` -> `zt/mE`; `Hflow L W` -> `Hflow d L W` / `sz.slice n ω`; `Z2 L` occurs only in the loop lemmas (`netLift_gloop_pm`, `Eblk` of part 1), replaced by `Zd d L` and `cont_norm_Eblk_le_one`; `W^{-2}` normalisation of `Eblk` enters only inside `Lloop`, not in the bounds (`‖Eblk‖ ≤ 1`). Dimension-free: `cont_core`, `contGood`, `cont_highProbAt_good`, `Q = N²`, `Xb = 2N²`.

### (ii) One concrete nondegenerate instance (merged `sz0`, `n = 0`, `d = 3`)
Data (`RBM3D/Defs/Sizes.lean:260`, same instance as T2074): `L=4, W=32, lam=1/64, N=(WL)^3=2097152=2^21`, `κ=ε=𝔡=1/10`, `z=1/2+iN^{-4/5}` (`E=1/2`), `s=0`, `t=1/16 ≤ lemT z`. The script evaluates `Bparam`, `STWB`, `Bctl` literally (`Params.lean:36`, `Sizes.lean:214`, `Defs.lean:69`) with `mpmath`, `dps=400`: the premises, the net mesh, the polynomial closeness for both families and, at three times `u ∈ {0, 1/32, 1/16}` with `|u-u'| = N^{-A}`, the floor `N^{-1} ≤ STWB`, the ratio `ζ_{u'} ≤ 2ζ_u` and `STWB(u) ≤ (1+x)STWB(u')` (Local at `K = 0..4`, all checked, printed `K = 0, 4`; `K ≤ L`). `N_min`: smallest power of 2 with three consecutive passes.
Commands (scratch under `scratchpad/T2082/`, no Lean): `python3 .../scratchpad/T2082/chk.py` and `python3 .../scratchpad/T2082/nmin.py`. Output (verbatim):
```
N=2097152  1-t=0.9375 >= N^(-1+eps/2)=10^-6.006 : True
c1=0.15811 Im m=0.96825 1/c1<=N: True ; (eta_t)^-1=(1-t)^-1 Im m^-1=1.1016 <= N^2: True
lam<=1/dd: True ; L^d=64 <= N: True ; #Zd=L^d=64
--- Local: A=40  net mesh N^-(A+1)=10^-259.19  <= N^-A=10^-252.87 ; #V=N^2 <= N^Cv(=2): True ; #net*#V <= N^(A+2+Cv) = 10^278.2
g(x): N*N^-A=10^-246.54<=1/10: True
Local closeness: delta=3N^6N^(-A/2)=10^-88.03; delta(2N^2+3+delta)=10^-75.08 <= N^-1=10^-6.32 : True
  u=0.0      K=0  STWB(u)=10^-4.509  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.9  (1+x)-bound ok:True  all:True
  u=0.0      K=4  STWB(u)=10^-5.182  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.9  (1+x)-bound ok:True  all:True
  u=0.03125  K=0  STWB(u)=10^-4.495  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.9  (1+x)-bound ok:True  all:True
  u=0.03125  K=4  STWB(u)=10^-5.168  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.9  (1+x)-bound ok:True  all:True
  u=0.0625   K=0  STWB(u)=10^-4.481  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.8  (1+x)-bound ok:True  all:True
  u=0.0625   K=4  STWB(u)=10^-5.154  floor N^-1=10^-6.322 ok:True  ratio-1=10^-252.8  (1+x)-bound ok:True  all:True
--- Avg: A=22  net mesh N^-(A+1)=10^-145.40  <= N^-A=10^-139.08 ; #V=L^d=64 <= N^Cv(=1): True ; #net*#V <= N^(A+2+Cv) = 10^158.0
g(x): N*N^-A=10^-132.75<=1/10: True
Avg closeness: N*(1*N^2*delta)=10^-12.17 <= N^-1=10^-6.32 : True
  u=0.0      K=0  STWB(u)=10^-4.509  floor N^-1=10^-6.322 ok:True  ratio-1=10^-139.1  (1+x)-bound ok:True  all:True
  u=0.03125  K=0  STWB(u)=10^-4.495  floor N^-1=10^-6.322 ok:True  ratio-1=10^-139.0  (1+x)-bound ok:True  all:True
  u=0.0625   K=0  STWB(u)=10^-4.481  floor N^-1=10^-6.322 ok:True  ratio-1=10^-139.0  (1+x)-bound ok:True  all:True
Local A=40 : smallest power of 2 with 3 consecutive passes: 2^1 ; sz0 n=0 has N=2^21
Avg A=22 : smallest power of 2 with 3 consecutive passes: 2^3 ; sz0 n=0 has N=2^21
```
Reading: every deterministic premise holds at once at `sz0` with slack `2^18` or more (`N_min ≤ 2^3`, other eventual premises `N ≥ 1/c₁ ≈ 6.3`); `STFlow` data and `0 ≤ s ≤ t ≤ lemT z` are the merged `flow_z0`, `sInst`, `tInst` (`Step2Defs.lean:1116` already applies `STNetLift2` there). The net size (`10^{278}`, `10^{158}`) is a proof-internal union bound, not a witness. `STStep2LocalPT`, `STStep2AvgPT` (and `STStep2DecayPT`) stay hypotheses of the compiled instance (stochastic inputs of the Step 2 chain, ST2-04). External hypotheses: none (every premise is deterministic, or the per-time statement being lifted); the only limit is `N → ∞` (`sz0_tendsto`).

### Verdicts
- `step2LocalNetLift` / `Step2LocalNetLift` (`STStep2LocalPT → STStep2Local`): **PASS** (hypothesis set nonempty at `sz0`; exponents close with slack above; no dimension-specific input).
- `STStep2Avg` lift (new, `STStep2AvgPT → STStep2Avg`): **PASS** (same).
- `stNetLift2_holds : STNetLift2 d`: **PASS** (assembly of the three conjuncts; premises as `stNetLift_holds`; `STNetLift2` is true as stated, no stop).
- Findings (not blocks): (1) the private helpers of NetLift1/Continuity listed above must be recopied as `private` in NetLift2; (2) the squared control `‖G-M‖²` needs the factor `2‖b‖+δ` that RBM2D's `|llErr|` form did not (A=40 covers it); (3) `STNetLift2`'s owed registry line can go on merge, `STStep2LocalPT`, `STStep2AvgPT` are added next to `STStep2DecayPT` (`Axioms.lean:138`).

## (a′) Preflight corrections — Sat Oct  3 22:21:48 UTC 2026
No mistake in (a). One implementation choice differs from the table: the Avg family uses the modulus `A = 40` (as Local), not `6k+16 = 22`, so that one eventual fact `15 N^9 N^{-A/2} ≤ N^{-1}` serves both; `A` is a proof-internal parameter (the net size is polynomial in `N` either way), the slack only grows (`N·N^{-A} ≤ 1/10` and `3 N^9 N^{-20} ≤ N^{-1}`).

## (b) Script output — Sat Oct  3 22:21:48 UTC 2026

### b.1 Build and axioms
```
$ lake build RBM3D.Path.NetLift2   (worktree RBM3D-wt/T2082, branch t/T2082)
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3726 jobs).
$ lake build   (full library, root #assert_rbm_axioms)
Build completed successfully (3819 jobs).
lake build  12.30s user 6.79s system 99% cpu 19.180 total
$ lake env lean <scratch>/ax.lean
'RBM.Ind.step2LocalNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step2AvgNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stNetLift2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Path/NetLift2.lean | wc -l
0
```

### b.2 Registry pre-check (ST1-COMMON item 8): scratch file `import RBM3D`, `import RBM3D.Path.NetLift2`, `#assert_rbm_axioms`
```
$ lake env lean <scratch>/pre.lean ; exit code 0
1:axiom audit: 2543 theorems, 1075 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
2:All within [propext,
61:  RBM.Gauss.Sizes.STNetLift2: 1 [no certificate]
62:  RBM.Gauss.Sizes.STStep2DecayPT: 1 [no certificate]
63:  RBM.Gauss.Sizes.STStep2LocalPT: 0 [no certificate]
64:  RBM.Gauss.Sizes.STStep2AvgPT: 0 [no certificate]
68:  RBM.Gauss.Sizes.STStep2: 2 [no certificate]
101:premises found by scanning: 83 (borrowed 2, owed 67, structural 14).
102:registry: 5 borrowed + 89 owed + 36 structural; 47 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
118: RBM.Gauss.Sizes.STStep2LocalPT,
119: RBM.Gauss.Sizes.STStep2AvgPT,
```
Registry edit (`RBM3D/Test/Axioms.lean`): two owed lines `STStep2LocalPT`, `STStep2AvgPT` after `STStep2DecayPT` (lines 139-140). The `STNetLift2` line is kept: its count is 0 with `import RBM3D` alone and 1 once `RBM3D.Path.NetLift2` is imported (the only new theorem mentioning it is `stNetLift2_holds`, whose type is the pin), so removing the line is not tested here; the retained `STNetLift` line after `stNetLift_holds` is the precedent.
```
$ git diff --stat main...t/T2082
 RBM3D/Path/NetLift2.lean | 757 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   2 +
 2 files changed, 759 insertions(+)
$ git log --oneline -1
727236b T2082: ST2-19 Path/NetLift2 (step2LocalNetLift, step2AvgNetLift, stNetLift2_holds)
```

### b.3 Target statements (extracted by script) and the pin
```
$ lake env lean <scratch>/chk.lean   (#check, #print of the pin)
@step2LocalNetLift : ∀ {d : ℕ} (sz : Gauss.Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), Step2LocalNetLift sz E κ τ s t
@step2AvgNetLift : ∀ {d : ℕ} (sz : Gauss.Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), Step2AvgNetLift sz E κ τ s t
stNetLift2_holds : ∀ (d : ℕ), STNetLift2 d
def RBM.Gauss.Sizes.STNetLift2 : ℕ → Prop :=
fun d =>
  ∀ (κ ε 𝔡 : ℝ),
    0 < κ →
      0 < ε →
        0 < 𝔡 →
          ∀ (𝔠 : ℝ) (sz : Gauss.Sizes d) (z : ℕ → ℂ),
            sz.STFlow κ ε 𝔠 𝔡 z →
              ∀ (s t : ℕ → ℝ),
                (∀ (n : ℕ), 0 ≤ s n) →
                  (∀ (n : ℕ), s n ≤ t n) →
                    (∀ (n : ℕ), t n ≤ lemT (z n)) →
                      ∀ (Cd : ℝ),
                        sz.STStep2LocalPT (STflowE z) s t →
                          sz.STStep2AvgPT (STflowE z) s t →
                            sz.STStep2DecayPT Cd (STflowE z) s t →
                              sz.STStep2Local (STflowE z) s t ∧
                                sz.STStep2Avg (STflowE z) s t ∧ sz.STStep2Decay Cd (STflowE z) s t
$ sed -n 526,538p RBM3D/Path/NetLift2.lean
def Step2LocalNetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    STStep2LocalPT sz E s t → STStep2Local sz E s t

/-- **The net lift of `(Gt_avgbound_flow)`**: `STStep2AvgPT → STStep2Avg` under the premises of
`Step2LocalNetLift`.  New at `d ≥ 3`: RBM2D has no counterpart (paper-delta candidate `T2082b`). -/
def Step2AvgNetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    STStep2AvgPT sz E s t → STStep2Avg sz E s t

/-- The eventual numerical facts of the two lifts, at the common modulus `A = 40`:
$ sed -n 586p;627p;688p RBM3D/Path/NetLift2.lean
theorem step2LocalNetLift (sz : Sizes d) : ∀ E κ τ s t, Step2LocalNetLift sz E κ τ s t := by
theorem step2AvgNetLift (sz : Sizes d) : ∀ E κ τ s t, Step2AvgNetLift sz E κ τ s t := by
theorem stNetLift2_holds (d : ℕ) : STNetLift2 d := by
```

### b.4 Compiled nonempty instances (`d = 3`, `sz0`, `n = 0`; `RBM3D/Path/NetLift2.lean` lines 716-757)
```

/-- `Step2LocalNetLift` at the flow of the instance (`κ = τ = (1/10)/2`, `s ≡ 0`, `t ≡ 1/16`). -/
example : Step2LocalNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step2LocalNetLift sz0 _ _ _ _ _

/-- `step2LocalNetLift`, fully applied: every hypothesis (`0 < κ`, `|E_n| ≤ 2 - κ`, `0 < τ`,
`0 ≤ s ≤ t < 1`, `N → ∞`, `RangeCond`) is discharged; `STStep2LocalPT` stays the hypothesis of the
implication. -/
example (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst :=
  step2LocalNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2 hL

/-- `Step2AvgNetLift` at the flow of the instance. -/
example : Step2AvgNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step2AvgNetLift sz0 _ _ _ _ _

/-- `step2AvgNetLift`, fully applied: `STStep2AvgPT` stays the hypothesis of the implication. -/
example (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst) :
    STStep2Avg sz0 (STflowE z0) sInst tInst :=
  step2AvgNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2 hA

/-- `stNetLift2_holds` at `d = 3`: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`); the three per-time statements stay
hypotheses, at an arbitrary constant `C_d`. -/
example (Cd : ℝ) (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst)
    (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst)
    (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
      STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hL hA hD

end Instances

end RBM.Ind
```

### b.5 Name-clash grep and ports
```
$ grep -rn "Step2LocalNetLift\|Step2AvgNetLift\|step2AvgNetLift\|step2LocalNetLift\|stNetLift2_holds" RBM3D RBM3D.lean | grep -v Path/NetLift2.lean   (main worktree state plus this branch)
RBM3D/Test/Axioms.lean:139:   `RBM.Gauss.Sizes.STStep2LocalPT, -- `(Gt_bound_flow)` per time (`1_2:1343`): hypothesis of `step2LocalNetLift`
RBM3D/Test/Axioms.lean:140:   `RBM.Gauss.Sizes.STStep2AvgPT, -- `(Gt_avgbound_flow)` per time (`1_2:1345`): hypothesis of `step2AvgNetLift`/
RBM3D/Path/NetLift1.lean:26:(`:1387-1511`, `end MainT1`).  Part 2 (ST2-19) is `Step2LocalUnif` (`:1343`), `Step2LocalNetLift`
RBM3D/Path/NetLift1.lean:27:(`:1351`), `netLift_T2_low`, `netLift_T2_close` (`:1244-1324`) and `step2LocalNetLift`
RBM3D/Induction/Step2Defs.lean:579:RBM2D `Path/NetLift.lean`, `Step2NetLift`, `Step2LocalNetLift`): the per-time conclusions give the
$ grep -rn "nl2_\|nl2Word" RBM3D | grep -v Path/NetLift2.lean | wc -l
       0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/NetLift.lean
 RBM2D/Path/NetLift.lean | 1784 -----------------------------------------------
 1 file changed, 1784 deletions(-)
$ RBM2D Step2LocalNetLift / Step2LocalUnif (c9a24cf:RBM2D/Path/NetLift.lean:1343-1356)
def Step2LocalUnif (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDomAt (Sizes.seqP d) d.size
    (U := fun n => TimeIcc s t n × Idx (d.L n) (d.W n) × Idx (d.L n) (d.W n))
    (fun n p ω => llErrMat (d.L n) (d.W n) (E n) p.1 (Sizes.seqHflow d n p.1 ω) p.2.1 p.2.2)
    (fun n p _ => (scaleM (d.L n) (d.W n) (E n) p.1)⁻¹ ^ ((1 : ℝ) / 2))

/-- The net lift for (`Gt_bound_flow`): `Step2LocalPT` implies `Step2LocalUnif`, under the same
hypotheses as `Step2NetLift`. -/
def Step2LocalNetLift (E : ℕ → ℝ) (κ c τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    Tendsto d.size atTop atTop →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    Step2LocalPT d E s t → Step2LocalUnif d E s t

```

### b.6 Narrative
- Targets (all in `RBM3D/Path/NetLift2.lean`, imports `RBM3D.Path.NetLift1`): `Step2LocalNetLift` (:526, RBM2D `:1351`), `step2LocalNetLift` (:586, RBM2D `:1518-1595`), `Step2AvgNetLift` (:533), `step2AvgNetLift` (:627), `stNetLift2_holds : STNetLift2 d` (:688, exactly the pin of `Step2Defs.lean:581`, see `#check` above).
- `Step2LocalUnif` (RBM2D `:1343`) is the merged pin `STStep2Local`; not redefined.
- Assembly of `stNetLift2_holds`: `⟨step2LocalNetLift …, step2AvgNetLift …, stNetLift2_part1 …⟩`, premises from `Green.v3_premises_of_stFlow` as in `stNetLift_holds`; no diagonal step (all three hypotheses are already `PrecPT`). `0 ≤ s`, `t ≤ lemT z` are the pin's hypotheses (DECISIONS §29); the lifts take `∀ n` premises on `s, t, E` and use eventual-in-`n` facts only for `N`-size inequalities.
- `step2LocalNetLift`: `cont_core` with `V n = Idx × Idx`, `A = 40`, `Cv = 2`, `ε = N^{-1}`, `ξ = ‖STGM‖²`, `ζ = STWB_{u,K}`; `hlow` is `nl2_STWB_low` (RBM2D `netLift_T2_low :1244`, general `K`, new), `hclose` is `nl2_loc_close` (RBM2D `netLift_T2_close :1251`, with `nl2_entry_diff` = `netLift_llErr_diff :622`).
- `step2AvgNetLift` (no RBM2D source): `cont_core` with `V n = Zd d L`, `A = 40`, `Cv = 1`, `ε = N^{-1}`, `ξ = ‖𝓛^{(1)}_{u,+,a} - m(E)‖`, `ζ = Bctl(u)`; `hlow` is `cont_inv_size_le_Bctl`, `hclose` is `nl2_avg_close` (`nl2_loop_sub` at `k = 1` plus the triangle inequality, `cont_Bctl_ratio`).
- Neither lift uses `(eq:WO)`: the control `STWB`/`Bctl` has no `ℓ_u`, so the ratio `STWB_{u'} ≤ (1+x) STWB_u` holds for every `ĝ ≥ 0`. Hence `Step2LocalNetLift`/`Step2AvgNetLift` have no `sz.WO 𝔡` premise (unlike `Step2NetLift`, T2074b).
- Recopied as `private` because NetLift1/Continuity keep them private: `nl2Word`, `nl2_word_norm`, `nl2_word_diff`, `nl2_loopFine_eq`, `nl2_loop_sub` (copies of NetLift1 `nl_*`, section 1), `nl2_STWB_nonneg`, `nl2_eta_inv_le`, `nl2_STWB_ratio` (NetLift1), `nl2_STGM_eq`, `nl2_entry_diff` (Continuity `cont_STGM_eq`, `cont_entry_diff`). The ticket's "do not copy" is kept for the merged public `ContinuityNet` material (`cont_core`, `cont_green_flow_diff`, `cont_Bctl_ratio`, `cont_inv_size_le_Bctl`, `cont_highProbAt_good` are used, not copied).
- Squared control: `‖STGM‖² ≤ ‖STGM'‖² + N^{-1}` costs `δ(2‖b‖+δ) ≤ 5N²δ` with `‖b‖ ≤ N²+1` (`nl2_entry_le`, `norm_mE`); one eventual fact `15 N^9 N^{-A/2} ≤ N^{-1}` (`nl2_eventual`, `cont_gap`) closes it for both families.
- `d = 2` tokens of the part-2 source (by `grep -o` on `:1244-1324`, `:1518-1595`, `:622-700`: `Z2` 2+2+3, `scaleM` 17 in `:1244-1324`, `spectralM`/`spectralZ`, `Hflow`, `Idx`, `W * L`) are replaced as listed in (a): `Z2 (W*L)` and `netLift_card_Z2` by `sz.card_Idx`/`card_BlockIndex`, `Z2 L` in the loop lemmas by `Zd d L`, `scaleM` by `STWB`/`Bctl`, `spectral*` by `mE`/`zt`; none has `1/5` or `ellT`.
- External hypotheses: none. Per-time statements `STStep2LocalPT`, `STStep2AvgPT`, `STStep2DecayPT` are hypotheses of the instance (ST2-04 pins).

## (c) Verified Mathlib / project names used (all compile in this file)
- Mathlib: `Real.rpow_neg_one`, `Real.rpow_two`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_nonneg`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `abs_norm_sub_norm_le`, `norm_sub_le`, `norm_add_le`, `sub_sub_sub_cancel_right`, `tendsto_natCast_atTop_iff`, `Filter.Tendsto.eventually_ge_atTop`.
- Project (merged): `ContinuityNet.{cont_core, cont_highProbAt_good, cont_green_flow_diff, cont_norm_green_le, cont_eta_le_abs_im, cont_norm_spectralZ_sub, cont_abs_sqrt_sub_sqrt_le, cont_norm_Xmat_le, cont_norm_blockMat_Xmat_le, cont_Gres_true_eq_green, cont_inv_add_one_sub_ratio, cont_Bctl_ratio, cont_inv_size_le_Bctl, cont_sqrt_abs_le, cont_bulk, cont_gap, cont_pow_mul_rpow, cont_norm_Eblk_le_one}`, `norm_matrix_entry_le_opNorm`, `norm_matrix_trace_le_card_mul`, `norm_Gsig_le_inv_eta`, `norm_mE`, `Green.v3_premises_of_stFlow`, `stNetLift2_part1`.
- Verified absent (as public, so recopied): `nl_loop_sub`, `nl_STWB_ratio`, `nl_STWB_nonneg`, `nl_eta_inv_le` (NetLift1, all `private`), `cont_entry_diff`, `cont_STGM_eq` (Continuity, `private`).

## (d) Open issues and paper-delta candidates
- `T2082a`: `Step2LocalNetLift` drops RBM2D's `c`, `Bandwidth d c`, `CondStInd d E s t` (unused by the proof; as `T2074a`/`T2062a`) and the `Step2LocalUnif` form is the merged pin `STStep2Local` (squared entry, control `STWB_{u,|[x]-[y]|}` at `d ≥ 3` in place of `M_u^{-1/2}`).
- `T2082b`: `STStep2Avg` lift has no RBM2D counterpart (new at `d ≥ 3`); the `(Gt_avgbound_flow)` net lift is the standard argument of `1_2:1400` applied to `‖𝓛^{(1)}_{u,+,a} - m(E)‖` against `Bctl`.
- `T2082c`: the Local/Avg lifts need no `(eq:WO)`, whereas `step2NetLift` does (T2074b); the control of Local/Avg has no `ℓ_u`.
- Registry: `STStep2LocalPT`, `STStep2AvgPT` added as owed (ST2-04). `STNetLift2` stays listed (see b.2); the dispatcher decides whether the line can go.
- `STNetLift2` is proved for every `d` (no `3 ≤ d` used); the three per-time hypotheses are the only stochastic inputs.
