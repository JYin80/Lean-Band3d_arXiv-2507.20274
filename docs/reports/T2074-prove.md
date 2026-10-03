Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 20:36:48 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `y = N^{-A}` (continuity modulus), `x = (1-t)^{-1}|u-u'| ≤ N y` (premise `1-t ≥ N^{-1+ε/2}` gives `(1-t)^{-1} ≤ N`), `g = sz.lam n ≤ 𝔡⁻¹` (eventually, `WO`), `k = zdistInf(a₀-a₁) ≤ L`. Sources: RBM2D `Path/NetLift.lean` at `c9a24cf`; merged `Induction/{Step2Defs,ContinuityNet,Continuity}.lean`.

### What is proved: part 1 of `STNetLift2` and the cut line
`STNetLift2` (`Step2Defs.lean:581`) has hypotheses `STStep2LocalPT ∧ STStep2AvgPT ∧ STStep2DecayPT` and conclusion `STStep2Local ∧ STStep2Avg ∧ STStep2Decay`. Part 1 = the third conjunct, from `STStep2DecayPT sz Cd (STflowE z) s t` alone (`STStep2DecayPT :287`, `STStep2Decay :263`; the control `ζ` and `ξ = ‖Lloop - STKloop‖` are the same in both; only `PrecPT` against `Prec`). Proposed name `stNetLift2_part1`: same quantifiers and premises as `STNetLift2`, minus the two unused per-time hypotheses and conjuncts. `STStep2Avg` has no counterpart in RBM2D `Path/NetLift.lean` (Decay and Local only): it belongs to ST2-19.
RBM2D cut (lines of `c9a24cf:RBM2D/Path/NetLift.lean`): part 1 = `1–1242` (module doc, Core, Good, Resolvent, Modulus, GreenFlow, Spectral, ThetaMod, LlLk, LkErr, Scalars, Scalars2, Ratio, CloseT1, `netLift_bulk :1230`), `Step2NetLift :1334`, Assembly `1359–1380` (`netLift_gap`, `netLift_pow_mul_rpow`), `step2NetLift :1387`–`end MainT1 :1511`. Part 2 (ST2-19) = `Step2LocalUnif :1343`, `Step2LocalNetLift :1351`, `netLift_T2_low :1244`, `netLift_T2_close :1251–1324`, `step2LocalNetLift :1518–1595` (`netLift_T2_*` are used only at `:1585, :1590`). The ticket's "`1334–1518`" ends at the first line of part 2 (`:1518` is `theorem step2LocalNetLift`); part 1 ends at `:1511`. `netLift_bulk` is shared (`cont_bulk` is merged in `ContinuityNet`).

### (i) Exponent table
| item | value | constraint | slack |
|---|---|---|---|
| time modulus `A` (control-`D`, `D>0` arbitrary) | `A = 4D + 40` (RBM2D `:1396`) | needs `N y ≤ 1/10`; `6N^{11-A/2} + N^{2-A} ≤ N^{-D}`: `A > 2D + 22`; ratio below | `A - (2D+22) = 2D+18`; `11-A/2 = -2D-9`, so `6N^{11-A/2} = 6N^{-D-9}·N^{-D}` |
| net size / mesh (`cont_core`) | `netSize(A+1,N) = ⌈N^{A+1}⌉+1`, mesh `≤ N^{-A-1} ≤ y` | `1/netSize ≤ y` (`cont_exists_close`) | factor `N` |
| `#V n` exponent `Cv` | `3` (`d=2`: `2`) | `#V = (2^2)(L^d)^2 = 4 L^{2d} ≤ 4N^2 ≤ N^{Cv}`; RBM2D had `σ` fixed so `L^4 ≤ N^2` | `N ≥ 4`; at `n=0`: `16384 ≤ N^3 = 2^63` |
| `ε n` (lower floor) | `N^{-D}` | `ε ≤ ζ`: `ζ ≥ W^{-D} ≥ N^{-D}` (first term `≥ 0`: `(1-s)/(1-u) ≥ 0`, `Bctl, STWB, exp ≥ 0`; `W ≤ N` since `N=(WL)^d`, `L,d ≥ 1`) | `N^{-1} ≤ W^{-1}` at `D=1`; factor `L^d` |
| loop modulus (`‖L_u-L_{u'}‖`, `k=2`) | `N·2·Q²·(Q²(Xb+1)√y) ≤ 6 N^{11-A/2}`, `Q=N²`, `Xb=2N²` | `+` `K` part `≤ N^{-D}` | see row 1 |
| `K` modulus | `‖K_u-K_{u'}‖ ≤ W^{-d}|u-u'|(1-u)⁻¹(1-u')⁻¹ ≤ N² y` | `K^{(2)} = W^{-d} m₁m₂ Θ_{u m₁m₂}(a₀,a₁)` (`KLK_two`), `‖u m₁m₂‖ = u < 1` as `‖m(σ)‖=1`; resolvent identity `Θ_ζ-Θ_ξ = (ζ-ξ)Θ_ζ S^B Θ_ξ`, `‖S^B‖=1`, `‖Θ_ζ‖ ≤ (1-‖ζ‖)⁻¹` | exponent `2-A = -4D-38` against `-D` |
| ratio `ζ_{u'} ≤ 2ζ_u` | `((1-u)/(1-u'))^{Cd}` and `(1+x)^{|Cd|}` (RBM2D: `(η_s/η_u)^4`); `Bctl(u')^{1/5} ≤ (1+x)^{1/5}Bctl(u)^{1/5}` (`cont_Bctl_ratio`); `STWB(u',k) ≤ (1+x) STWB(u,k)` (both terms of `Bparam`, `cont_inv_add_one_sub_ratio`); `exp(-√(k/ℓ_{u'})) ≤ e^{δ} exp(-√(k/ℓ_u))` | `(1+x)^{|Cd|+6/5} e^{δ} ≤ 2`; `δ ≤ √(k|ℓ_u-ℓ_{u'}|)`, `|ℓ_u-ℓ_{u'}| ≤ g(1-t)⁻¹√|u-u'|` (new: `ellT` carries `g`), so `δ ≤ √(𝔡⁻¹ L N)·N^{-A/4} ≤ √10 N^{1-A/4}` | eventually in `n` for every fixed real `Cd` (both signs): `x ≤ N^{1-A}` vs `1/(|Cd|+2)`; the `+W^{-D}` term is not multiplied (`ζ_{u'} ≤ 2F_u + W^{-D} ≤ 2ζ_u`) |
| `ε` against `κ`: `κ' = κ/2`, `τ = ε/2` | `c₁ = √(2κ')/2`, `1/c₁ ≤ N` | `|E_n| < 2-κ'` and `1-t ≥ N^{-1+τ}` from `STFlow`, `t ≤ lemT z` (`v3_premises_of_stFlow`, as `stNetLift_holds`) | `N → ∞` from `Admissible` |
| `(η_t)⁻¹ ≤ Q = N²` | `(1-t)⁻¹ (Im m)⁻¹ ≤ N·N` | `1/c₁ ≤ N` | `N ≥ 1/c₁ ≈ 6.3` |
| `D`-dependence of the pin | the control's `D` fixes `A, ε`; the domination's own `D'` is absorbed by `hPT` / `HighProbAt` in `cont_core` | `∀ D>0`, `∀ D'>0` | none needed |

Changes against RBM2D (every `d=2` token of this part): `Z2 L`, `Idx L W` → `Zd d L`, `Idx d L W`; `(WL)^2` → `N = (WL)^d`; `W^2` → `W^d` (`K` has `W^{-d}`, not `W^{-2}`); `zdist2` (`ℓ¹`-type) → `zdistInf`; `scaleM⁻²·(η_s/η_u)^4` → `((1-s)/(1-u))^{Cd}·Bctl^{1/5}·STWB` (`scaleM_*`, `netLift_scaleM_diff/_ratio` have no analogue: replaced by `Bparam` ratios); `ellT L u` → `ellT L g u`; only `σ=(-,+)` → all `σ ∈ {±}²` (`Cv: 2→3`; `m₁m₂ ∈ {1, m², conj m²}` times `u`, norm `u`); `Bandwidth`, `CondStInd` unused by the proof (dropped, as T2062 for `Step1NetLift`). Independent of `d`: `cont_core`, `contGood`, `cont_highProbAt_good`, the Green-function moduli (`cont_green_flow_diff`, `cont_loopAbs_diff` proves its trace bound for the word difference before taking `|‖·‖-‖·‖|`, `Continuity.lean:219–222`), `Q=N²`, `Xb=2N²`.

### (ii) One concrete nondegenerate instance (merged `sz0`, `n = 0`, `d = 3`)
Data: `L=4, W=32, lam=1/64, N=(WL)^3=2097152`, `κ=ε=𝔡=1/10`, `z=1/2+i N^{-4/5}`, `s=0`, `t=1/16`, `D=1`, `Cd ∈ {4,-3}`, `A=44`. Numeric check (high precision, `mpmath`, `dps=600`); the ratio check evaluates `ζ` of `STStep2DecayPT` literally (`Bparam`, `Bctl`, `STWB`, `ellT` with `g=lam`) at `|u-u'| = N^{-A}`, `u ∈ {0,1/64,1/32,1/16}`, every `k = 0..6` (`zdistInf ≤ L/2 = 2` at `L=4`).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2074/chk.py`
Output (verbatim):
```
L,W,lam,N = 4 32 0.015625 2097152
E=lemE(z)=0.5  t0=lemT(z)=0.9999909488
0<=s<=t<=t0: True  1-t= 0.9375  >= N^(-1+eps/2): True
kappa'=0.05 tau=0.05 c1=0.15811388 ImmE=0.96824584  c1<=Imm:True  1/c1<=N:True |E|<=2-kappa':True
WO: W^(-d/2+dd)=0.0078125 <= lam=0.015625 <= 1/dd=10.0 : True
A=4D+40=44.0 ; net exponent A+1=45.0 ; netSize=ceil(N^(A+1))+1 ~ 10^284.47335 ; mesh 1/netSize ~ 10^-284.47335 ; N^-A ~ 10^-278.15172
mesh<=N^-A: True
#net points = netSize+1 ~ 10^284.473 ; #V=4 L^(2d)=16384 ; N^3=9223372036854775808 ; 4L^(2d)<=N^Cv(=3): True
Q=eta_t^-1=1.1016486 <= N^2:True
(g1) N*N^-A = 10^-271.83 <= 1/10
(g2) 6N^(11-A/2)=10^-68.7598 ; N^2*N^-A=10^-265.508 ; sum <= N^-D=10^-6.32163 : True
(g5) N^-D<=W^-D: True
Cd=4.0: max zeta(u')/zeta(u) over u in {0,1/64,1/32,1/16}, k=0..6, |u-u'|=N^-A : 1.0 - 1 = 10^-281.256
Cd=-3.0: max zeta(u')/zeta(u) over u in {0,1/64,1/32,1/16}, k=0..6, |u-u'|=N^-A : 1.0 - 1 = 10^-281.256
Cd=4.0: (1+x)^(|Cd|+6/5)*exp(delta) = 1 + 2.65409e-66 <= 2 ; x=N^(1-A)=10^-271.83, delta<=10^-65.5761
Cd=-3.0: (1+x)^(|Cd|+6/5)*exp(delta) = 1 + 2.65409e-66 <= 2 ; x=N^(1-A)=10^-271.83, delta<=10^-65.5761
Cd=4.0: smallest power of 2, N_min = 2^2, passes (g1)-(g4) from there (3 consecutive checked); N(sz0,0)=2^21 slack factor 2^19
Cd=-3.0: smallest power of 2, N_min = 2^2, passes (g1)-(g4) from there (3 consecutive checked); N(sz0,0)=2^21 slack factor 2^19
Cd=100.0: smallest power of 2, N_min = 2^2, passes (g1)-(g4) from there (3 consecutive checked); N(sz0,0)=2^21 slack factor 2^19
```
Reading of the output: every hypothesis of part 1 holds at once (`STFlow`: `|Re z| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1`, `WO`, `Bandwidth 1/6` as merged; `0 ≤ s ≤ t ≤ lemT z = 0.99999`; `1-t = 15/16 ≥ N^{-9/10}`). Net size `⌈N^{45}⌉+1 ≈ 10^{284.5}` (proof-internal union bound, not a witness), continuity modulus `N^{-44} ≈ 10^{-278.2}`; the loop modulus is `10^{-68.8}` and the `K` modulus `10^{-265.5}` against the floor `N^{-1} = 10^{-6.3}`; the control moves by a factor `1 + 10^{-281}` (max over the grid, both `Cd` signs). The last three lines show `N_min = 2^2` for the polynomial inequalities (`g1`-`g4`, with `L ≤ N`, `z ≤ N`); the other eventual premises (`N ≥ 1/c₁ ≈ 6.3`, `N ≥ 4`) are at most `2^3`, so `N = 2^21` has slack `2^18`. The ticket's nonempty instance at `d=3` is the merged `sz0, z0, flow_z0, sInst = 0, tInst = 1/16` (`Step2Defs.lean:1116` already applies `STNetLift2` at them); `STStep2DecayPT` stays a hypothesis of the instance (stochastic input of ST2-04's chain).
External hypotheses: none (every premise is deterministic or the per-time `STStep2DecayPT` itself, which is the statement being lifted); no limit computation needed beyond `N → ∞` (`sz0_tendsto`).

### Verdicts
- `stNetLift2_part1` (`Step2NetLift` port; `STStep2DecayPT → STStep2Decay` with the premises of `STNetLift2`): **PASS** (hypothesis set nonempty at `sz0`; exponents close with the slack above; statement true for every real `Cd`, both signs).
- Finding (not a block): the ticket's cut end `1518` should read `1511` (`end MainT1`); `Step2LocalUnif/Step2LocalNetLift/step2LocalNetLift` and `netLift_T2_*` go to ST2-19.
## (b) Script output — written Sat Oct  3 20:52:53 UTC 2026

Branch `t/T2074`, commit `83896d8`, files `RBM3D/Path/NetLift1.lean` (new), `RBM3D/Test/Axioms.lean` (one registry line). Scratch: `scratchpad/T2074/`.

### b.1 Build, hygiene, scope
```
$ lake build RBM3D.Path.NetLift1 (tail)
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3725 jobs).
exit=0
$ lake env lean RBM3D/Path/NetLift1.lean | wc -l   (0 = no error, no warning)
       0
$ lake build   (whole library; the root import of the new module is added by the hub at merge) (tail)
Build completed successfully (3793 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Path/NetLift1.lean
0
$ git diff main...t/T2074 --stat
 RBM3D/Path/NetLift1.lean | 908 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   1 +
 2 files changed, 909 insertions(+)
$ wc -l RBM3D/Path/NetLift1.lean
     908 RBM3D/Path/NetLift1.lean
```

### b.2 #print axioms of the public declarations
```
$ lake env lean ax.lean   # import RBM3D.Path.NetLift1; #print axioms of the three public names
'RBM.Ind.step2NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.Step2NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stNetLift2_part1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Registry pre-check (DECISIONS §20, ST1-COMMON item 8)
```
$ cat precheck.lean; lake env lean precheck.lean | grep "axiom audit\|premises found\|STNetLift\|STStep2DecayPT"
import RBM3D
import RBM3D.Path.NetLift1
#assert_rbm_axioms
axiom audit: 2513 theorems, 1058 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STNetLift: 2 [no certificate]
  RBM.Gauss.Sizes.STNetLift2: 0 [no certificate]
  RBM.Gauss.Sizes.STStep2DecayPT: 1 [no certificate]
premises found by scanning: 82 (borrowed 2, owed 67, structural 13).
registry: 5 borrowed + 87 owed + 35 structural; 45 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
 RBM.Gauss.Sizes.STNetLift,
 RBM.Gauss.Sizes.STNetLift2,
exit=0
$ git diff main...t/T2074 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.Gauss.Sizes.STStep2DecayPT, -- `(Eq:Gdecay_w)` per time (`1_2:1349-1351`): hypothesis of `stNetLift2_part1`/`step2NetLift`; proved by the Step 2 chain ST2-04 (T2074, DECISIONS §20 rule: owed)
```

### b.4 Target statements, extracted from the file by script (proofs elided)
```
$ python3 extract.py Step2NetLift step2NetLift stNetLift2_part1
L697: def Step2NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ 𝔡 : ℝ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
L706: theorem step2NetLift (sz : Sizes d) : ∀ E κ τ 𝔡 s t Cd, Step2NetLift sz E κ τ 𝔡 s t Cd := by
L853: theorem stNetLift2_part1 (d : ℕ) :
L854:     ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
L855:       ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
L856:         ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
L857:           ∀ Cd : ℝ, STStep2DecayPT sz Cd (STflowE z) s t → STStep2Decay sz Cd (STflowE z) s t := by
```

### b.5 Compiled nonempty instances (section 6 of the file; `sz0`, `d = 3`, `n = 0`, `N = 2097152`)
```
$ sed -n 880,908p RBM3D/Path/NetLift1.lean

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `Step2NetLift` at the flow of the instance (`κ = τ = (1/10)/2`, `𝔡 = 1/10`, `s ≡ 0`,
`t ≡ 1/16`): `step2NetLift` applies for every `C_d`. -/
example (Cd : ℝ) : Step2NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) (1 / 10) sInst tInst Cd :=
  step2NetLift sz0 _ _ _ _ _ _ _

/-- `step2NetLift`, fully applied: every hypothesis (`0 < κ`, `|E_n| ≤ 2 - κ`, `0 < τ`,
`0 ≤ s ≤ t < 1`, `N → ∞`, `(eq:WO)`, `RangeCond`) is discharged; the per-time family
`STStep2DecayPT` stays the hypothesis of the implication. -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  step2NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) (1 / 10) sInst tInst Cd
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto flow_z0.1.2.2.2.2 RBM.Green.Instance.premises.2.2.2.2 hD

/-- `stNetLift2_part1` at `d = 3`: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`). -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_part1 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hD

end Instances

end RBM.Ind
```

### b.6 Name-clash grep of the new public names, and port sources
```
$ git grep -nw "Step2NetLift\|step2NetLift\|stNetLift2_part1" main -- "RBM3D/*.lean"   (main = a84c579, the base of the branch)
main:RBM3D/Induction/Step2Defs.lean:579:RBM2D `Path/NetLift.lean`, `Step2NetLift`, `Step2LocalNetLift`): the per-time conclusions give the
$ git grep -c "RBM.Ind.NetLift1\|namespace RBM.Ind" main -- "RBM3D/*.lean" | head -3   (namespace RBM.Ind already used by T2047/T2062)
main:RBM3D/Induction/ConArg.lean:2
main:RBM3D/Induction/ConArgDet.lean:1
main:RBM3D/Induction/Continuity.lean:2
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   (RBM2D HEAD); the port source is c9a24cf
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/NetLift.lean
 RBM2D/Path/NetLift.lean | 1784 -----------------------------------------------
 1 file changed, 1784 deletions(-)
$ git -C ../RBM2D --no-optional-locks cat-file -e c9a24cf:RBM2D/Path/NetLift.lean && echo present-at-c9a24cf; git -C ../RBM2D --no-optional-locks cat-file -e HEAD:RBM2D/Path/NetLift.lean || echo absent-at-HEAD
present-at-c9a24cf
fatal: path 'RBM2D/Path/NetLift.lean' does not exist in 'HEAD'
```

### b.7 `d = 2` tokens: source code (comments stripped, lines 1-1511) against the port (comments stripped)
```
$ python3 tokens.py
'Z2 '                src(c9a24cf:1-1511)= 15  port=  0
'zdist2'             src(c9a24cf:1-1511)=  6  port=  0
'scaleM'             src(c9a24cf:1-1511)= 59  port=  0
'spectralM'          src(c9a24cf:1-1511)= 42  port=  0
'spectralZ'          src(c9a24cf:1-1511)= 28  port=  1
'Bandwidth'          src(c9a24cf:1-1511)=  2  port=  0
'CondStInd'          src(c9a24cf:1-1511)=  2  port=  0
'etaT E s / etaT'    src(c9a24cf:1-1511)= 16  port=  0
'^ 2)'               src(c9a24cf:1-1511)= 34  port=  3
'Idx (d.L'           src(c9a24cf:1-1511)=  5  port=  0
```

### b.8 Narrative (cut line, reuse, differences; every number above is script output)

- **Cut line (against RBM2D `c9a24cf:RBM2D/Path/NetLift.lean`).** Ported/replaced, part 1: `Step2NetLift` (`:1334`), `step2NetLift`
  (`:1387-1511`), `netLift_T1_close` (`:1111`), `netLift_zeta_ratio` (`:974`), `netLift_exp_ell_diff` (`:916`), `netLift_ellT_diff` (`:909`),
  `netLift_one_div_sqrt_diff` (`:884`), `netLift_Kpm_diff` (`:707`), `netLift_Theta_diff` (`:595`), `netLift_gloop_diff` (`:661`).
  Reused from the merged ST-1 net lift (not copied): `netLift_core`, the good event, `netLift_green_diff`, `netLift_green_flow_diff`,
  `netLift_norm_*`, `netLift_bulk`, `netLift_gap`, `netLift_pow_mul_rpow`, `netLift_sqrt_rpow`, `netLift_sqrt_abs_le`
  (`cont_core`, `contGood`, `cont_highProbAt_good`, `cont_green_flow_diff`, `cont_bulk`, `cont_gap`, `cont_pow_mul_rpow`, `cont_sqrt_abs_le`).
  Replaced by `Bctl`/`STWB` ratios (no analogue at `d ≥ 3`): `netLift_scaleM_*`, `netLift_im_le_scaleM`, `netLift_abs_exp_neg_sub_exp_neg_le`.
  Part 2 (ST2-19), not in this file: `Step2LocalUnif` (`:1343`), `Step2LocalNetLift` (`:1351`), `netLift_llErr_diff` (`:622`),
  `netLift_T2_low` (`:1244`), `netLift_T2_close` (`:1251`), `step2LocalNetLift` (`:1518-1595`). The ticket's end `1518` is `:1511`
  (`end MainT1`) as section (a) says.
- **Part of `STNetLift2` proved.** The third conjunct, as `stNetLift2_part1` (b.4): `STStep2DecayPT → STStep2Decay`, with the quantifiers
  and premises of `STNetLift2` and without the two other per-time hypotheses; `STStep2Local`, `STStep2Avg` are ST2-19. No hypothesis of
  `STNetLift2` is dropped other than the two unused ones; no `3 ≤ d` is needed (`nl_one_le_d` derives `1 ≤ d` from `SizeTendsto`).
- **Reuse of T2062 private lemmas.** `cont_word_diff`, `cont_loopAbs_diff`, `contWord`, `cont_eta_inv_le` are `private` in `Continuity.lean`
  and cannot be imported; copied as `nl_*` (`nl_loop_sub` states the norm of the difference, not the difference of the norms).
- **Steps changed at `d ≥ 3`.** (1) All four sign patterns, `#V = 4 (L^d)² ≤ N³`, `Cv = 3`. (2) `𝒦^{(2)}` modulus from `KLK_two`, `norm_Theta_le`,
  `Theta_sub_Theta`, `norm_SB`: `(1-t)⁻² |u-u'|`. (3) Control ratio `nl_zeta_ratio`: `(1+x)^{|C_d|} (1+x)^{1/5} (1+x) e^δ ≤ 2` with
  `x = N·N^{-A}`, `δ = √(ĝ k (1-t)⁻¹ |u-u'|^{1/2}) ≤ 1/4`, valid for `C_d` of either sign (`nl_rpow_ratio`); additive `W^{-D}` not multiplied.
  (4) `ĝ ≤ 𝔡⁻¹` (from `(eq:WO)`) is used for `δ`; this is why `Step2NetLift` carries `sz.WO 𝔡` (T2074b).
- **Exponents** (`A = 4D + 40`, `Cv = 3`, `ε = N^{-D}`): eventual conditions `evgx`, `evgδ`, `evg3`, `ev4` of the proof; gaps as in section (a) (i).
- **Registry.** `STStep2DecayPT` is assumed by `stNetLift2_part1` and proved by no theorem: classified owed (b.3, one line, §20 rule); the
  pre-check without the line printed an `axiom audit` error naming exactly this premise (tool log); with the line it exits 0 (b.3).
- **Instances.** b.5: `step2NetLift` and `stNetLift2_part1` at `sz0`, `d = 3`, `κ = ε = 𝔡 = 1/10`; only `STStep2DecayPT` stays a hypothesis.

## (c) Verified Mathlib names used (all compile in b.1; present by `lake build`)
`Real.sqrt_eq_rpow`, `Real.exp_mul`, `Real.add_one_le_exp`, `Real.exp_one_lt_d9`, `abs_max_sub_max_le_max`, `abs_min_sub_min_le_max`,
`Real.inv_rpow`, `Real.rpow_neg`, `Real.mul_rpow`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_nonpos`, `Real.sqrt_le_iff`, `le_self_pow₀`,
`Finset.single_le_sum`, `Finset.sup_le`, `tendsto_natCast_atTop_iff`, `Real.rpow_natCast`, `Fintype.card_fun`, `Fintype.card_bool`.
Project names reused: `cont_core`, `contGood`, `cont_highProbAt_good`, `cont_green_flow_diff`, `cont_bulk`, `cont_gap`, `cont_pow_mul_rpow`,
`cont_sqrt_abs_le`, `cont_abs_sqrt_sub_sqrt_le`, `cont_inv_add_one_sub_ratio`, `cont_Bctl_ratio`, `cont_inv_size_le_Bctl`,
`cont_inv_le_const_mul_inv`, `cont_norm_blockMat_Xmat_le`, `Green.v3_premises_of_stFlow`, `KLK_two`, `Theta_sub_Theta`, `norm_Theta_le`, `norm_SB`,
`norm_mSigma`, `sum_norm_row_le`, `zdist_le_L`.

## (d) Open issues and paper-delta candidates
- `T2074a`: `Bandwidth d c` and `CondStInd d E s t` of RBM2D's `Step2NetLift` are not used by its proof and are dropped (as T2062a / RBM2D T2070b for Step 1).
- `T2074b`: `Step2NetLift` carries `sz.WO 𝔡` (not in RBM2D, where the control had no `ĝ`); `stNetLift2_part1` gets it from `STFlow` (`Admissible`), the pin is unchanged.
- `T2074c`: `stNetLift2_part1` is the decay conjunct only (hypothesis `STStep2DecayPT` alone); `STNetLift2` closes with ST2-19 and `STStep2Local ∧ STStep2Avg`.
- Registry: one line added (`STStep2DecayPT`, owed). ST2-19 will probably add `STStep2LocalPT` and `STStep2AvgPT` next to it (same file, adjacent lines: a textual merge conflict is possible).
- RBM2D `HEAD` (`9e0f275`) no longer has `Path/NetLift.lean` (b.6); the port reads `c9a24cf` as the ticket says.
- Nothing was blocked; no hypothesis of the targets was added to a pin or weakened; no frozen signature changed.
