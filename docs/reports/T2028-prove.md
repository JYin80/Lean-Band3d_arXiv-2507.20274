Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:30:47 UTC 2026 (`date -u`)

Notation: `x=1-t`, `a_u=W^{-d}B_{u,0}` (merged `Bctl`), `g=ilambda` (`sz.lam`), `N=(WL)^d`; every `≺` is `Prec`/`PrecPT` at scale `N`. Paper = `paper/tex/` (`1_2`, `3_5`); RBM2D lines at `c9a24cf`; probe = `752e027:RBM3D/Probe/T2015Pins.lean`. `SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad` (Python scripts only: `t2015_expo.py`, `t2015_inst.py` = T2015 (a)(ii) re-run; `t2028_bridge.py` new).

### (i) Exponent table

**A. ST pins** (probe lines 161-501). Instance numbers: `d=3, W=2^5, L=8, N=2^24, g=2^-6, 𝔡=1/4, 𝔠=1/5, κ=ε=1/10`.

| pin (probe line) | paper | states; constants in order | constraint and slack |
|---|---|---|---|
| `STFlow` (399) | `eq:WO` 1_2:363, `Main_DEL_COND` 359, `eq:spectral_domain` 380 | `Admissible 𝔠 𝔡` (𝔠,𝔡>0, N→∞, `W≥N^𝔠`, `W^{-d/2+𝔡}≤g≤𝔡^{-1}`) and `∀n locDomain κ ε` (`|Re z|≤2-κ`, `N^{-1+ε}≤Im z≤1`) | `W^{-d/2+𝔡}=0.01314 ≤ g=0.01562`; `𝔠=0.2 ≤ 5/24`; `η=2^-14` vs `N^{-1+ε}=3.1e-7` |
| `STMainInd` (407) | `lem:main_ind` 1_2:1256-1330, `con_st_ind` 1296 | `κ,ε,𝔡` → `𝔠_d∈(0,10^-2]` → `𝔠,sz,z,s,t≤lemT z`; (a)-(d) at `s`, `a_t^{𝔠_d}≤x_t/x_s<1`; conclusions at `t` | instance A: `x_s/x_t=1.02094 ≤ a_t^{-𝔠}=1.02326` (`𝔠_d=10^-2`) |
| `STGbEXPii/ij/av` (421-442) | `lem_GbEXP` 3_5:14-40 (`GiiGEX` 21, `GijGEX` 24, `GavLGEX` 33) | `κ,ε,𝔡` → `𝔠,sz,z`, `0≤t≤lemT z`, `ε₀>0`; av: `W^{-d/2}≤Ψ≤W^{-ε₀}` | `Ψ`: `0.0055 ≤ 0.1 ≤ W^{-ε₀}=0.5` at `ε₀=0.2` |
| `STConArg` (447) | `lem_ConArg` 3_5:42-62 | `ε₁≤s≤t<1`, `C₀`; `(a_s η_s/η_t)^{k-1}`, `η_s/η_t=x_s/x_t` exactly | T2015 row 8, 13 (a)(i) |
| `STStep1` (462) | `lRB1` 1_2:1321, `Gtmwc` 1327 | `𝔠_d∈(0,10^-2]`; uses (a), (c), `STKbound`, `con_st_ind` | closes iff `𝔠_d≤1/2`: slack `0.49` |
| `STBootstrap`, `STNetLift` | 3_5:64-66 | forbidden-region bound `a_s^{3/8}` vs threshold `a_s^{1/4}` | ratio `a_s^{1/8}=0.75` at `a_s=0.0999` (small only as `N→∞`) |
| `STKbound` (`ML:Kbound`) | `eq:bcal_k` 1_2:1056 | `max|𝒦^{(k)}|≺a_τ^{k-1}`, deterministic | KL7; `Θ/B∈[0.2478,0.9974]` (T2015 row 18) |
| scale `N` | D23 | `W^τ ≤ N^{τ/d}`; `N^τ ≤ W^{τ/𝔠}`; here `W=N^{5/24}` | `W^{-ε₀}=0.5 ≤ N^{-𝔠ε₀}=0.5141` (`W≥N^𝔠`) |

**B. RBM2D Green pins (`Green/Pins.lean`) against the ST pins.** Provable direction in the last column (what 1b can prove at S1-07 from definitions + merged `perTimeOfStochDomAt`, `stochDomAt_of_perTimeDomAt` (card `≤N^C`), `perTimeDomAt_iff_forall_section`).

| RBM2D (line) | ST counterpart | differences found | direction |
|---|---|---|---|
| `GijOmegaSeq` 68, `GijSeq` 94 | `STGijGEX` (3_5:24) | (1) `PerTimeDomAt` (union outside `P`, `Unit×V`) vs `Prec` (union inside); (2) RBM2D `offSq=0` on diagonal vs subtype `p.1≠p.2`; (3) RHS: `gexRHS` (`Path/Step2Vocab:81`) has one orientation `S(b,a)` (swapped, T2066a), `zdist2`, `W^{-2}`; `STgexRHS` has both `σ`, `zdistInf`, `W^{-d}`: `STRHS = S(a,b)+S(b,a)+W^{-d}1 ≥ gexRHS(b,a)` (script `orientation` True; `S(a,b)≠S(b,a)`: 0.4362 vs 0.5756) | `GijOmegaSeq ⇒ STGijGEX` (RHS monotone, union bound `C=2`, `|Idx²|=N²`); converse not derivable |
| `GiiOmegaSeq` 77, `GiiSeq` 102 | `STGiiGEX` (3_5:21) | RBM2D diagonal `|G_pp-m|²` vs paper/ST all entries `‖G-M‖²_max` | `STGiiGEX ⇒ GiiOmegaSeq` (restrict to `x=y`); converse needs `GijGEX` plus loop floor: `max𝓛^{(2)}_{(-,+)} ≥ W^{-2d}Σ_{x∈a}|G_xx|² ≥ W^{-d}(1-W^{-ε₀})²` on `Ω` (`0.25` at instance; RBM2D `norm_loopPM_eq` 406 normalization `(W^{-d})²Σ|G|²`) |
| `AsGMcSeq` 85, `AsGMcPT` 246 | hypothesis of `STGavLGEX`; shape of `STLocalMax` | PerTime vs `Prec` on `Idx²` | iff, union bound `C=2` |
| `LoopDetSeq` 111, `GavLDetSeq` 119 | hyp./concl. of `STGavLGEX` | `|𝓛_{(+,-),(a,b)}|=|𝓛_{(-,+),(b,a)}|` (script True), same `max`; `tr((G-M)E_a)=𝓛^{(1)}_{+,a}-m(E)`; `Ψ`: `0≤Ψ≤N^{-a}` vs `W^{-d/2}≤Ψ≤W^{-ε₀}` | V3-av `⇒ STGavLGEX` with `a=𝔠ε₀`; converse needs the loop floor |
| `GbEXPHypV3` 152, `GbEXPV3Theorem` 166 | `STGbEXP` (442) | parametrization `(E,t)` with `RangeCond δ`, `|E|<2-κ`, `t<1` vs `(z,STFlow,t≤lemT z)`: `z=(E+(1-t₀)mE E)/√t₀`, `t₀=max(t,0.9)` gives `m(z)=√t₀ m(E)`, `lemE z=E`, `lemT z=t₀≥t` (script 12/12), `κ'=κ/2`, `ε<δ`; conversely `|lemE z|≤|Re z|` (merged `abs_lemE_le`). `STFlow` needs `∀n locDomain` but `RangeCond` is eventual: change finitely many `n` (`StochDomAt` is eventual in `n`). **R1:** `d≥3` needs `sz.WO 𝔡` (`ilambda`, `eq:WO`; RBM2D has no `g`): `SizeTendsto → Bandwidth` becomes `sz.Admissible 𝔠 𝔡`, new constant `𝔡` after `𝔠` | `V3Theorem (Admissible form) ⇒ STGbEXP` (needs rows above); `STGbEXP ⇒` V3 diagonal pieces only |
| `gijGEXPTSwap_giiGEXPT_of_V3` 260, `GijGEXPTSwap` 227, `GiiGEXPT` 236 | no ST counterpart (PT over `TimeIcc`) | via `perTime_timeIcc_of_forall_seq` 187, `perSeq_of_perTime_timeIcc` 205 (generic, copy) | port as is |
| `v3_premises_of_mainIndHyp` 293 | `STFlow` | `MainIndHyp` (RBM2D `Induction/Defs:229`) not ported: restate on `STFlow` (`Admissible`, `|E|≤2-κ`) | restate |
| `Green/Pins` d=2 tokens (portmap P.6) | | :370 `W⁻²`→`W^{-d}`; :408, :415 `(W⁻¹²)²`→`(W^{-d})²`; `Z2/zdist2` (32 tokens)→`Zd d/zdistInf`; `Instance` 485-593 (`W=1`, `L`) → probe `sz0/sz1` | replaced |

**C. Registry classes** (DECISIONS §19; `Test/Axioms.lean` scan lists a `Prop` assumed by some theorem and concluded by none). Signed: `STKbound` owed (KL7); `STLK STLmax STDecay STDecayStrong STLocalMax STExp2` owed (ST-6); `STConStInd STFlow` structural. If the full build also reports them (the probe's `inst_*` take them as hypotheses): `STGbEXP`, `GbEXPV3Theorem`, `GbEXPHypV3` owed S1-30 (`gbEXPV3`, portmap P.7); `STConArg` S1-32; `STNetLift` S1-34; `STBootstrap` S1-36; `STStep1` S1-35/S1-36 (P.7 rows); `AsGMcPT` owed (RBM2D proves it at `Path/GoodSet.lean:442`, ST-2 file); `STMainInd`: DECISIONS §19 silent (ST-6 chain end), dispatcher to sign; `GavLGEXRandHyp` 173: no occurrence in RBM2D outside `Green/Pins.lean` (`git grep c9a24cf`), no P.7 ticket: dispatcher to sign.

### (ii) One concrete nondegenerate instance
```
$ python3 $SP/t2015_expo.py | grep -E "^(N=2|Main_DEL|z=0.5|m\(z\)|[1-4]: |c=0.0100|extreme)"
N=2^24  W=N^0.2083  W^-d/2+dd=2^-6.25 <= g=2^-6 <= 1/dd=4.0: True
Main_DEL_COND W>=N^cW (cW=0.20): True ; W^tau = N^(0.2083 tau)
z=0.5+i2^-14 in D_{kap,eps}: |E|<=1.9:True, N^(-1+eps)<=eta<=1:True
m(z)=-0.249992+0.968215i  t0=|m|^2=0.999936965  1-t0=6.3035e-05  eta/(Im m+eta)=6.3035e-05  E_flow=-2Re m/|m|=0.500000
1:       3.000e-01  1.000     1.0184e-04 5.375e-04 1.250e-01 1.987e-07 5.03e+06
2:       6.104e-05  2.000     1.0098e-01 5.330e-01 1.250e-01 9.766e-04 1.02e+03
3:       1.907e-06  8.000     1.5528e-01 8.196e-01 1.250e-01 3.125e-02 32
4:       3.873e-07  8.000     2.7870e-01 1.471e+00 1.250e-01 1.539e-01 6.5
c=0.0100: all closure checks (ell-ratio<=(x_s/x_u)^1/2, a_s<=a_u<=a_t, a_s x_s/x_u<=a_u^1/2, >=W^-d, <=a_t^(1-c)) over 4 regimes x 3 steps x 3 u: True
extreme g=W^(-d/2+dd): a(x=N^-0.9)=3.659e-01 a(0.3)=1.019e-04
extreme g=1/dd: a(x=N^-0.9)=1.895e-01 a(0.3)=2.071e-06
$ python3 $SP/t2015_inst.py | grep -E "^(A:|B:)|deterministic hypotheses"
A: t=t0(z), regime 2: s=0.999935645 t=0.999936965 x_s/x_t=1.02094 (<= a_t^-c=1.02326) a_s=9.9850e-02 a_t=1.0029e-01 ell_s=1.948 ell_t=1.968
  deterministic hypotheses: {'WO': True, 'Bandwidth': True, 'kappa': True, 'eps_le_s': True, 's_le_t_lt_1': True, 't_le_t0': True, 'con_st_ind': True, 'range': True, 'one_minus_s_ge_g2': False}
B: regime 1 (1-t>=g^2): s=0.674004896 t=0.700000000 x_s/x_t=1.08665 (<= a_t^-c=1.09628) a_s=9.3726e-05 a_t=1.0184e-04 ell_s=1.000 ell_t=1.000
  deterministic hypotheses: {'WO': True, 'Bandwidth': True, 'kappa': True, 'eps_le_s': True, 's_le_t_lt_1': True, 't_le_t0': True, 'con_st_ind': True, 'range': True, 'one_minus_s_ge_g2': True}
$ python3 $SP/t2028_bridge.py          # Green pins (R1 form) at E in {0.5, 1.89, -1.89}, t in {0, 0.3, 0.9, 1-2e-6}; flags = lemE, lemT=t0, lemT>=t, |E|<2-κ, RangeCond δ=0.2, |Re z|<=2-κ/2, N^(-1+ε)<=Im z<=1
N=2^24.0  W>=N^cW: True  (eq:WO) W^(-d/2+dd)=0.01314<=g=0.01562<=1/dd=4: True
RangeCond: N^(-1+dl)=1.660e-06 ; domain floor N^(-1+eps)=3.146e-07
E=+0.50 t=0.0000000 t0=0.9000000 z=0.500694+1.021e-01 i lemE-E=0.0e+00 lemT-t0=-1.1e-16 conds 1111111
E=+0.50 t=0.9999980 t0=0.9999980 z=0.500000+1.936e-06 i lemE-E=0.0e+00 lemT-t0=0.0e+00 conds 1111111
E=+1.89 t=0.0000000 t0=0.9000000 z=1.892623+3.448e-02 i lemE-E=0.0e+00 lemT-t0=-1.1e-16 conds 1111111
E=+1.89 t=0.9999980 t0=0.9999980 z=1.890000+6.541e-07 i lemE-E=-2.2e-16 lemT-t0=0.0e+00 conds 1111111
all ST-parametrization conditions (lemE z=E, lemT z>=t, |E|<2-kap, RangeCond dl, locDomain kap/2 eps): True
reverse: z=0.5+i2^-14: lemE=0.500000 |lemE|<=2-kap/2:True  1-t0=6.303e-05>=N^(-1+dl):True  t0<1:True
av part: W^(-d/2)=0.005524<=Psi=0.1<=W^-e0=0.5<=N^(-cW e0)=0.5141: True ; (1-W^-e0)^2=0.250 (loop lower bound factor)
union bound index sizes: |Idx^2|=N^2=2^48 (C=2), |Zd^2 x Bool^2| = 4 L^(2d) <= N (C=1): True
orientation: Lpm(a,b)=S1(a,b)=sum|G_yx|^2 and Lmp(a,b)=Lpm(b,a)=sum|G_xy|^2: True
asymmetry sum|G_xy|^2 vs sum|G_yx|^2 over blocks (0,1): 0.4362 vs 0.5756
```
Instance: `d=3, W=32, L=8, N=2^24` (`W≥N^{1/5}`, `eq:WO` with `𝔡=1/4`), `κ=1/10`, `ε=1/10`, `δ=1/5`, `ε₀=1/5`, `Ψ=0.1`; `s,t` of instance A (`s≥ε`, `s<t=t₀<1`); no `N=0`, empty index or collapsed window. The Green pins and the ST pins share the same `(E,t)` at every row (`z` above); at `t=1-2e-6` the slack to `N^{-1+δ}=1.66e-6` is a factor 1.2 and `Im z=6.5e-7` vs `N^{-1+ε}=3.1e-7` a factor 2. The external hypothesis `STKbound` (KL7, owed): limit table of T2015 (a)(ii), `Θ_t(0,0)/B_{t,0}` in `[0.2478, 0.9974]` for `L→∞` at `g=2^-6`, `d=3` (T2015 report, `python3 $SP/t2015_theta.py`, not re-run here: only `STKbound`'s shape is pinned by this ticket).

### Verdicts
* Target 1 (`Induction/Defs.lean`, probe 161-501 copied): **PASS** (rows A; instances A, B; every constraint holds with the slack shown).
* Target 2 (`Green/Pins.lean`): **PASS**, with the forced statement changes **R1** (`Admissible 𝔠 𝔡` for `SizeTendsto → Bandwidth`, new `𝔡`; paper-delta candidate), the `d`-dependent tokens of table B, and the bridge directions of table B (the literal `↔` holds only for `AsGMc` (iff) and the parametrization; `Gij` and `Gii` bridge in one direction each, reasons in the table).
* Target 3 (registry): **PASS**; classes in C; `STMainInd`, `GavLGEXRandHyp` need the dispatcher's class if the build reports them.
## (a′) Preflight corrections — Sat Oct  3 06:39:17 UTC 2026 (`date -u`)

* No verdict of (a) changes.  Three precisions, each checked in the files:
* Table B row `GiiOmegaSeq` and the Target 2 verdict ("`Gij` and `Gii` bridge in one direction each"): the converse `GiiOmegaSeq ∧ GijOmegaSeq ⇒ STGiiGEX` is proved (`stGiiGEX_of_omegaSeq`: loop floor, `L^∞` ball count `≤ 3^d`); `Gii` bridges both ways, `Gij` one way (the right side `STgexRHS` has the extra `σ = (+,-)` terms).
* Row `GbEXPHypV3`: `V3 ⇒ STGbEXP` uses the map `E = lemE z`, `κ ↦ κ/2`, `δ = ε/2` (`v3_premises_of_stFlow`); the construction `z = (E+(1-t₀)mE E)/√t₀` of (a) is for the converse `STGbEXP ⇒ V3`, not proved here.  The window `WO` inside `Admissible` is used by no proof of this ticket (only `0 < 𝔠`, `N → ∞`, `W ≥ N^𝔠`).
* Section C: the RBM2D derivation of `AsGMcPT` is `Path/GoodSet.lean:439` (`goodSet_asGMc`, private); `:442` is the last line of its statement.

## (b) Script output (worktree `RBM3D-wt/T2028`, branch `t/T2028`, commit `f9fce58`, generated Sat Oct  3 06:36:40 UTC 2026)

### b.1 Build, registry pre-check, axioms, hygiene
```
$ lake build RBM3D.Induction.Defs RBM3D.Green.Pins   # then: exit, #warning lines, #error lines, last line
exit=0 warnings=0 errors=0
Build completed successfully (3313 jobs).
$ lake build   # full library: root #assert_rbm_axioms; the root file does not yet import the two new modules (hub, at merge)
exit=0 errors=0 warnings-in-new-files=0
Build completed successfully (3728 jobs).
$ registry pre-check (DECISIONS §20, scratch file outside the repository): lake env lean precheck.lean
exit=0
scratch file: import RBM3D; import RBM3D.Induction.Defs; import RBM3D.Green.Pins; #assert_rbm_axioms
axiom audit: 1137 theorems, 465 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 22 (borrowed 3, owed 14, structural 5).
registry: 11 borrowed + 18 owed + 15 structural; 22 registered premise(s) carry nothing yet: [RBM.Th
$ #print axioms of every public declaration of the two files (list of names from the Lean environment, names.lean)
exit=0 public declarations: 161 (Induction/Defs 73, Green/Pins 88); standard axioms only: 161; other: 0
$ grep forbidden tokens; git diff --name-only main...t/T2028
forbidden tokens (sorry|admit|native_decide|axiom): Induction/Defs 0, Green/Pins 0
RBM3D/Green/Pins.lean RBM3D/Induction/Defs.lean RBM3D/Test/Axioms.lean 
```
### b.2 Target 1: the copied probe text (script diffdefs.py; `bind1` of the T2015 report b.2 applied to probe 161-501 and 503-848)
```
$ python3 diffdefs.py RBM3D/Induction/Defs.lean
sections 1, 1b, 2 (probe 161-501): probe lines 341, new lines 341, differing hunks 0
section 3 (probe 503-848): probe lines 346, new lines 346, differing hunks 0
```
### b.3 Target statements of `Green/Pins.lean` (script stmts.py; `def`: whole declaration, `theorem`: up to `:=`; `sz : Sizes d`, `d` are section variables)
```lean
L210 GbEXPHypV3 (κ 𝔠 𝔡 δ : ℝ) : Prop := sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t
         n < 1) → sz.RangeCond δ t → ∀ c > (0 : ℝ), GijOmegaSeq sz E t c ∧ GiiOmegaSeq sz E t c ∧ (AsGMcSeq sz E t c →
         GijSeq sz E t ∧ GiiSeq sz E t ∧ ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) → (∀ᶠ n : ℕ in atTop, Ψ n ≤
         ((sz.size n : ℕ) : ℝ) ^ (-a)) → LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ)
L224 GbEXPV3Theorem (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → GbEXPHypV3 sz κ 𝔠 𝔡 δ
L283 GijGEXPTSwap (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop := sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) ×
         Idx d (sz.L n) (sz.W n)) (fun n p ω => if p.2.1 = p.2.2 then 0 else ‖Gt sz n (E n) p.1 true ω p.2.1 p.2.2‖ ^ 2)
         (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω) (STblk sz n p.2.2) (STblk sz n p.2.1))
L290 GiiGEXPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop := sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n)) (fun n
         p ω => ‖Gt sz n (E n) p.1 true ω p.2 p.2 - mE (E n)‖ ^ 2) (fun n p ω => maxLoopPM d (sz.L n) (sz.W n) (E n) p.1
         (sz.seqHflow n p.1 ω))
L297 AsGMcPT (E : ℕ → ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop := sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) ×
         Idx d (sz.L n) (sz.W n)) (fun n p ω => llErrMat d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω) p.2.1 p.2.2)
         (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c))
L310 gijGEXPTSwap_giiGEXPT_of_V3 {κ 𝔠 𝔡 δ c : ℝ} {E s t : ℕ → ℝ} (hV3 : GbEXPHypV3 sz κ 𝔠 𝔡 δ) (hA : sz.Admissible 𝔠 𝔡) (hE
         : ∀ n, |E n| < 2 - κ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1) (hR : sz.RangeCond δ t) (hc :
         0 < c) (hAs : AsGMcPT sz E s t c) : GijGEXPTSwap sz E s t ∧ GiiGEXPT sz E s t
```
The bridges, one line each (script stmts.py, statements cut at 124 characters; full statements in the file):
```lean
L743 asGMcSeq_iff_prec (E t : ℕ → ℝ) (c : ℝ) : AsGMcSeq sz E t c ↔ sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n …
L767 asGMcPT_iff_forall_prec {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (c : ℝ) : AsGMcPT sz E s t c ↔ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.I …
L976 gavLDetSeq_iff_prec (E t Ψ : ℕ → ℝ) : GavLDetSeq sz E t Ψ ↔ sz.Prec (U := fun n => Zd d (sz.L n)) (fun n a ω => ‖Lloop sz n  …
L1001 loopDetSeq_of_prec {E t Ψ : ℕ → ℝ} (h : sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω) (fun n _ _ …
L1012 prec_maxLoop2_of_loopDetSeq {E t Ψ : ℕ → ℝ} (h : LoopDetSeq sz E t Ψ) : sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop …
L794 stGijGEX_of_gijOmegaSeq {E t : ℕ → ℝ} {c : ℝ} (h : GijOmegaSeq sz E t c) : STGijGEX sz E t c
L831 giiOmegaSeq_of_stGiiGEX {E t : ℕ → ℝ} {c : ℝ} (h : STGiiGEX sz E t c) : GiiOmegaSeq sz E t c
L871 stGiiGEX_of_omegaSeq {E t : ℕ → ℝ} {c 𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (hE : ∀ n, |E n| ≤ 2) (hc : 0 < c) (hii : GiiOmegaSe …
L1098 stGavLGEX_of_v3 {κ 𝔠 𝔡 δ : ℝ} (hV3 : GbEXPHypV3 sz κ 𝔠 𝔡 δ) (hA : sz.Admissible 𝔠 𝔡) {E t : ℕ → ℝ} (hE : ∀ n, |E n| < 2 - κ) …
L1049 v3_premises_of_stFlow {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε) (h : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (h1 : ∀ n, t …
L1129 stGbEXPii_of_v3 (h : GbEXPV3Theorem d) : STGbEXPii d
L1137 stGbEXPij_of_v3 (h : GbEXPV3Theorem d) : STGbEXPij d
L1144 stGbEXPav_of_v3 (h : GbEXPV3Theorem d) : STGbEXPav d
L1152 stGbEXP_of_v3 (h : GbEXPV3Theorem d) : STGbEXP d
```
### b.4 Statements of the ported declarations against RBM2D at `c9a24cf` (script diffpins.py, ST1-COMMON item 6; RBM2D text renamed R1-R3, `BlockIndex -> Idx`, `spectralM -> mE`, then compared token by token; only the differing declarations are listed)
```
$ python3 diffpins.py RBM3D/Green/Pins.lean | grep -v "^=="
!= GbEXPHypV3: [--]{+𝔡+}
!= GbEXPV3Theorem: [--]{+(d : ℕ)+}
!= GavLGEXRandHyp: [--]{+𝔡+}
!= gijGEXPTSwap_giiGEXPT_of_V3: [--]{+𝔡+} | [--]{+𝔡+} | [-(hN-]{+(hA+} | [-SizeTendsto d) (hW : Bandwidth d 𝔠)-]{+sz.Admissible 𝔠 𝔡)+}
!= greenBlk_time_zero: [-(Idx-]{+(Vtx+} | [-(Idx-]{+(Vtx+}
!= diag_entry_sq_time_zero: [-Idx-]{+Vtx+}
!= norm_loopPM_eq: [-((W-]{+(((W+} | [-2-]{+2)+}
!= offSq_le_gexRHS_swap_W1: [-q.1 p.1-]{+(split d L 1 q).1 (split d L 1 p).1+}
!= greenBlk: [-(Idx-]{+(Vtx+} | [-(Idx-]{+(Vtx+}
!= RangeCond: [-(τ-]{+(δ+}
identical after renaming: 30 of 40
$ python3 d2tokens.py   # d = 2 tokens of Green/Pins (portmap P.1 row 58: W^2:1, W^-2:4, Z2/zdist2:32)
RBM2D tokens (code lines): Z2 (type of block labels): 22, zdist2 (L^2 distance): 10, W ^ 2 (block size): 1, (W⁻¹ ^ 2) ^ 2 (inv2): 3, Fin W × Fin W (block offsets): 6, BlockIndex: 20, Sizes / d.L n (d : Sizes): 98
RBM3D tokens (code lines): Zd d: 87, zdistInf: 50, W ^ d: 16, (W⁻¹ ^ d) ^ 2: 1, Fin (W ^ d): 5, Idx d / Vtx d: 149, sz.L n / sz.W n: 287
remaining d=2 tokens in the new file (Z2, zdist2, W ^ 2, (W⁻¹ ^ 2) ^ 2, Fin W × Fin W): none
`^ 2` in the new file: 58 (squares of norms/loops, dimension-free: `‖G‖ ^ 2`, `Ψ ^ 2`, `(W^d)⁻¹ ^ 2`)
```
### b.5 Compiled nonempty instances (script: theorem names and first lines of section 9 of `Green/Pins.lean`, namespace `RBM.Green.Instance`; `Induction/Defs.lean` section 3 holds the probe instances (`inst_mainInd` ... `inst_step1_lowg`): 13 theorems `inst_*` by grep)
```
theorems in section 9: 23
L1426 premises : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, |STflowE z0 n| < 2 - (1 / 10) / 2) ∧ (∀ n, 0 ≤ tInst n) ∧ (∀ n, tInst n < 1) ∧ sz0.RangeCond ((1 / 10) / 2) tInst
L1605 inst_bridges_time_zero {c : ℝ} (hc : 0 < c) (Ψ : ℕ → ℝ) : STGijGEX sz0 (STflowE z0) (fun _ => 0) c ∧ STGiiGEX sz0 (STflowE z0) (fun _ => 0) c ∧ GiiOmegaSeq sz0 (STflowE z0) (fun _ => 0) c ∧ sz0.Prec (U := fun n => Idx 3 (sz0.L n) 
L1442 inst_gijGEXPTSwap (hV3 : GbEXPHypV3 sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)) (hAs : AsGMcPT sz0 (STflowE z0) sInst tInst (1 / 40)) : GijGEXPTSwap sz0 (STflowE z0) sInst tInst ∧ GiiGEXPT sz0 (STflowE z0) sInst tInst
L1540 inst_stGbEXP_of_v3 (h : GbEXPV3Theorem 3) : STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGavLGEX sz0 (STflowE z0) tInst (1 / 20)
premises, rangeCond_sInst, inst_gijGEXPTSwap, inst_perTime_timeIcc, inst_perSeq, inst_asGMcSeq_iff, inst_stGijGEX, inst_giiOmegaSeq, inst_stGiiGEX, inst_gavLDetSeq_iff, inst_loopDetSeq, inst_hyp, inst_stGavLGEX, inst_stGbEXP_of_v3, inst_conclusions_time_zero, inst_norm_loopPM_eq, inst_time_zero_checks, inst_gexRHS_checks, inst_offSq_W1, inst_perTimeDomAt_of_nonpos, inst_bridges_time_zero, inst_asGMcPT_iff, inst_prec_maxLoop2
```
### b.6 Name clashes, RBM2D sources, registry diff
```
$ python3 clash2028.py names.out   # full names vs main and every other branch t/T20xx
public declarations of the two new files: 161; refs scanned: main + 37 branches; files parsed: 124
full-name clashes with library files: 0 (unmerged probe RBM3D/Probe/T2015Pins.lean on t/T2015 excluded: 36 of the same declarations, it is their source)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the three source files>   # first line: RBM2D HEAD
9e0f275
 RBM2D/Green/Pins.lean      | 363 ++++++---------------------------------------
 RBM2D/Path/Step2Props.lean | 184 ++++++-----------------
 RBM2D/Path/Step2Vocab.lean |  57 ++-----
 3 files changed, 103 insertions(+), 501 deletions(-)
$ git diff -U0 1892ec6 HEAD -- RBM3D/Test/Axioms.lean   # the registry diff, grouped by list
 1 file changed, 20 insertions(+), 2 deletions(-)
added lines 20, removed lines 2 (the two lines that closed the lists, rewritten); old entries kept: True; borrowedProps unchanged: True
owedProps += S.STKbound, S.STLK, S.STLmax, S.STDecay, S.STDecayStrong, S.STLocalMax, S.STExp2, S.STMainInd, S.STConArg, S.STStep1, S.STBootstrap, S.STNetLift, S.STForbidden, G.GbEXPV3Theorem, G.GijOmegaSeq, G.AsGMcPT
structuralProps += S.STConStInd, S.STFlow
(S. = RBM.Gauss.Sizes., G. = RBM.Green.; one line and one comment per name)
```

### b.7 Narrative (every number above comes from the scripts; names and lines from the files)
* `Induction/Defs.lean` (735 lines): module header, probe 161-501, probe 503-848; b.2: 0 differing hunks.  Imports are those of `bind1`; instance namespace `RBM.Gauss.InductionDefsInst`.
* `Green/Pins.lean` (1643 lines): sections 1-4 port RBM2D sections 1-4; the matrix-level vocabulary of RBM2D `Path/Step2Vocab`, `Path/Step2Props` (`llErrMat loopPM greenBlk avgErr maxLoopPM gexRHS`, `Sizes.RangeCond`) is defined there, since an ST-1 file does not import ST-2; section 8 ports RBM2D section 5 (`norm_loopPM_eq` in the `Fin (W^d)` block form; RBM2D `inv_W2_le_maxLoopPM` is the private loop floor); section 9 replaces RBM2D's `Instance` (`W = 1`) by the section-3 data `sz0`, `z0`.
* The pairs (RBM2D form, ST pin) and the bridges proved (all in `Green/Pins.lean`, section 7):
  * `AsGMcSeq ↔ Prec ‖G-M‖ ≺ W^{-c}` (hypothesis of `STGavLGEX`): `asGMcSeq_iff_prec`; `AsGMcPT ↔` the same at every `u ∈ [s,t]`: `asGMcPT_iff_forall_prec`.
  * `GavLDetSeq ↔ Prec |𝓛^{(1)} - m| ≺ Ψ²`: `gavLDetSeq_iff_prec`; `LoopDetSeq ↔ Prec max 𝓛 ≺ Ψ²`: `loopDetSeq_of_prec`, `prec_maxLoop2_of_loopDetSeq`.
  * `GijOmegaSeq ⇒ STGijGEX`: `stGijGEX_of_gijOmegaSeq` (one way); `STGiiGEX ⇒ GiiOmegaSeq`: `giiOmegaSeq_of_stGiiGEX`; `GiiOmegaSeq ∧ GijOmegaSeq ⇒ STGiiGEX`: `stGiiGEX_of_omegaSeq`.
  * `GbEXPHypV3` (third clause) `⇒ STGavLGEX`: `stGavLGEX_of_v3`; `GbEXPV3Theorem d ⇒ STGbEXP d`: `stGbEXP_of_v3` (parts `stGbEXPii/ij/av_of_v3`); data map `(z, STFlow, t ≤ lemT z) ↦ (E, t)`: `v3_premises_of_stFlow`.
  * Not bridged (no ST counterpart): `GijSeq`, `GiiSeq` (no indicator under (asGMc)), `GijGEXPTSwap`, `GiiGEXPT` (consumer shapes), `GavLRandSeq`, `GavLGEXRandHyp`.
* Proof of `stGiiGEX_of_omegaSeq`: per-time ⇒ uniform by the union bound (`Path.stochDomAt_of_perTimeDomAt`, `|Idx| = N`, `|Idx²| = N²`); for `Ω(t,c)` with `W^{-c} ≤ 1/2` the diagonal entries give `W^{-d} ≤ 4 max 𝓛` (from `𝓛_{(+,-),(a,b)} = W^{-2d} Σ_{y∈[b],x∈[a]} |G_{yx}|²`); the unit ball has `≤ 3^d` points, so `gexRHS ≤ (9^d + 4) max 𝓛`; `9^d + 4 ≤ N^{τ/2}` eventually.
* Statement differences to RBM2D (b.4): R1 (`Admissible`, constant `𝔡`), R2 (`BlockIndex` replaced by `Idx d L W` in entries and by `Vtx d L W` in `greenBlk`; block label `STblk`/`split`), parameter name `τ` of `RangeCond` is `δ`, a parenthesis in `norm_loopPM_eq`; the other 30 of 40 statements are identical after the renaming; d = 2 tokens: none left (b.4).
* Registry (b.6): the nine names signed in DECISIONS §19 and the names the pre-check reported (22 found: borrowed 3, owed 14, structural 5, as in b.1); names without a §19 class (`STMainInd`, `STConArg`, `STStep1`, `STBootstrap`, `STNetLift`, `STForbidden`, `AsGMcPT`) are owed by the rule "unsure: owed" of DECISIONS §20, with the proving ticket in the comment.

## (c) Verified Mathlib names (script names2028.py: `#check @name` elaborates; the file has 154 verified Mathlib/core names, the non-elementary ones are listed)
Complex.mul_conj' : ∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑‖z‖ ^ 2
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Equiv.sum_comp : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : Add
Finset.card_le_three : ∀ {α : Type u_1} [inst : DecidableEq α] {a b c : α}, {a, b, c}.card ≤ 3
Finset.exists_mem_eq_sup' : ∀ {α : Type u_1} {ι : Type u_2} [inst : LinearOrder α] {s : Finset ι} (H : s.Nonempty) (f
Finset.sum_pair : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι] {a b 
Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s 
Finset.sum_eq_single : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f : ι → M} (a : ι), (
Fintype.card_piFinset : ∀ {ι : Type u_1} {α : ι → Type u_2} [inst : DecidableEq ι] [inst_1 : Fintype ι] (s : (i : ι) 
Fintype.card_subtype_le : ∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) [inst_1 : Fintype { a // p a }], Fintype
Fintype.mem_piFinset : ∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {δ : α → Type u_2} {t : (a : α) →
Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_1 : Fintype α₂] [i
Matrix.conjTranspose_nonsing_inv : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Com
Matrix.inv_submatrix_equiv : ∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [ins
Matrix.nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Co
Matrix.mul_diagonal : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintyp
Matrix.trace_mul_comm : ∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : Add
Matrix.trace_sub : ∀ {n : Type u_1} {R : Type u_2} [inst : Fintype n] [inst_1 : AddCommGroup R] (A B : Matrix n n R), (
Matrix.trace_smul : ∀ {n : Type u_1} {α : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : AddCommMonoid R] [inst_2
Matrix.sub_mul : ∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type u_1} [inst : NonUnitalNonAssocRing α] [inst
Matrix.smul_mul : ∀ {l : Type u_2} {m : Type u_3} {n : Type u_4} {R : Type u_5} {α : Type u_1} [inst : AddCommMonoid α
Matrix.isHermitian_zero : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α], IsHermitian 0
Nat.le_mul_of_pos_left : ∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
Nat.cast_sub : ∀ {R : Type u_1} [inst : AddGroupWithOne R] {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
Real.le_sqrt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (x ≤ √y ↔ x ^ 2 ≤ y)
Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
ZMod.natCast_zmod_val : ∀ {n : ℕ} [NeZero n] (a : ZMod n), ↑a.val = a
ZMod.val_lt : ∀ {n : ℕ} [NeZero n] (a : ZMod n), a.val < n
tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ y) atTop atTop
tendsto_rpow_neg_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ (-y)) atTop (nhds 0)
tendsto_atTop_mono' : ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄, f₁ ≤ᶠ[l] f₂
ite_eq_left : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
ite_eq_right : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
Deprecated in this Mathlib (warning seen): `if_pos`, `if_neg` (use `ite_eq_left`, `ite_eq_right`), `ite_cond_eq_true`, `ite_cond_eq_false`, `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`); absent: `Real.rpow_le_rpow_of_exponent_nonpos`.

## (d) Open issues and paper-delta candidates
* **T2028a (R1)**: `GbEXPHypV3`, `GbEXPV3Theorem`, `gijGEXPTSwap_giiGEXPT_of_V3` take `sz.Admissible 𝔠 𝔡` (with `(eq:WO)`, `1_2:363`) in place of RBM2D's `SizeTendsto d → Bandwidth d 𝔠`, and carry the constant `𝔡` after `𝔠`: the paper's `lem_GbEXP` is stated "in the setting of the random band matrix model" (`3_5:14`), whose hypotheses include `(eq:WO)` (`1_2:357-363`), and RBM2D has no coupling.  This is the one statement change beyond renaming; ST1-COMMON item 6 says "stop and report": the dispatcher confirms or rules (no bridge uses `WO`, so dropping it changes no proof here).
* **T2028b**: `GijOmegaSeq`/`GijSeq`/`GijGEXPTSwap` keep RBM2D's one-orientation right side `gexRHS … [y] [x]` (the `σ = (-,+)` half of `3_5:24`, RBM2D T2066a), stronger than the displayed (GijGEX); `stGijGEX_of_gijOmegaSeq` shows it implies the paper's.  S1-16 (port of RBM2D `offSq_le_gexRHS_blk`) decides if the `d ≥ 3` chain proves it; if only the symmetric right side is provable, replace `gexRHS` by `STgexRHS` (then `GijOmegaSeq ↔ STGijGEX`).
* **T2028c**: the clause (`GavLGEX`) of `GbEXPHypV3` has `0 ≤ Ψ`, `Ψ ≤ N^{-a}` (RBM2D) while the paper has `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` (`3_5:27`): the Lean clause is the stronger one (needs the floor of S1-27); `stGavLGEX_of_v3` takes `a = 𝔠 ε₀`.
* **T2028d**: `RangeCond` (RBM2D T2005, not in the paper) is kept in the (E,t) form; `v3_premises_of_stFlow` derives it from `Im z ≥ N^{-1+ε}` with `δ = ε/2` (`lemma28_quant`: `t₀ ≥ 1/16`).
* **T2028e** (diagonal-only (`GiiGEX`)): `GiiOmegaSeq` (`Green/Pins.lean:141`), `GiiSeq` (:164) and `GiiGEXPT` (:290) bound only the diagonal `|G_pp − m|²`, while (`GiiGEX`) (`3_5:21`) bounds `1(Ω(t,ε₀)) ‖G_t − M‖²_max` (all entries).  In `GbEXPHypV3` the conjunction `GiiOmegaSeq ∧ GijOmegaSeq` implies the paper's form by `stGiiGEX_of_omegaSeq` (`Green/Pins.lean:871`, under `Admissible`, `|E| ≤ 2`).  `GiiSeq` and `GiiGEXPT` alone are weaker than the paper's display; their only consumer is `gijGEXPTSwap_giiGEXPT_of_V3` (:310, output `GijGEXPTSwap ∧ GiiGEXPT`), which returns them paired with the off-diagonal forms; no RBM3D module outside `Green/Pins.lean` uses them yet (Repair grep).  (In RBM2D the clause matched its paper's diagonal display.)  Per-time `PrecPT` vs the paper's uniform `≺`: equivalent on these finite index sets via `asGMcSeq_iff_prec` (:743), `gavLDetSeq_iff_prec` (:976), and the union bound `|Idx²| ≤ N²` (`card_Idx_prod_le`, :731).
* **T2028f** (indicator-free clause): the third clause of `GbEXPHypV3` (:210), `AsGMcSeq c → GijSeq ∧ GiiSeq ∧ …`, i.e. (`GijGEX`) and (`GiiGEX`) without `1(Ω)` under (`asGMc`), is not displayed in `lem_GbEXP` (`3_5:14-40`; the paper displays the indicator forms (`GiiGEX`), (`GijGEX`) and (`GavLGEX`) under (`initialGT2`)).  It is RBM2D's reading, kept as ported; no signed DECISIONS/paper-deltas entry covers it (Repair grep), and no theorem in `Green/Pins.lean` derives it from the indicator forms plus (`asGMc`).  It is part of the pin `GbEXPV3Theorem` and is used by `gijGEXPTSwap_giiGEXPT_of_V3`.
* Classes: the seven owed names without a §19 class (above) are the dispatcher's to confirm.  `GavLGEXRandHyp`, `GavLRandSeq` are ported but no theorem takes them as a hypothesis, so the scan does not report them (no P.7 ticket proves them).
* `GbEXPV3Theorem d` has no `3 ≤ d` guard, like the signed ST pins (`STMainInd` alone has it); its truth for `d < 3` is not claimed.
* RBM2D `Green/Pins.lean`, `Path/Step2Vocab.lean`, `Path/Step2Props.lean` changed after `c9a24cf` (b.6 diff-stat); the port follows `c9a24cf` as ST1-COMMON item 1 says.
* Merge: the hub adds `import RBM3D.Induction.Defs` and `import RBM3D.Green.Pins` (the latter imports the former); registry conflicts in the three tables are unions (DECISIONS §20).

## Repair (audit round 1 RETURN) — Sat Oct  3 07:58:53 UTC 2026 (`date -u`)
Report-only: no `.lean` file changed; branch `t/T2028` stays at `f9fce58`.  Items 1–2 of "Required for resubmission": candidates T2028e, T2028f added to (d).  Evidence:
```
$ grep -n "^def GiiSeq\|^def GiiGEXPT\|^def GiiOmegaSeq\|^def GbEXPHypV3\|^theorem asGMcSeq_iff_prec\|^theorem gavLDetSeq_iff_prec" RBM3D/Green/Pins.lean   # in RBM3D-wt/T2028
141:def GiiOmegaSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
164:def GiiSeq (E t : ℕ → ℝ) : Prop :=
210:def GbEXPHypV3 (κ 𝔠 𝔡 δ : ℝ) : Prop :=
290:def GiiGEXPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
743:theorem asGMcSeq_iff_prec (E t : ℕ → ℝ) (c : ℝ) :
976:theorem gavLDetSeq_iff_prec (E t Ψ : ℕ → ℝ) :
$ git -C RBM3D-wt/T2028 grep -n "GiiGEXPT\|GiiSeq" t/T2028 -- 'RBM3D/*.lean' ':!RBM3D/Green/Pins.lean'; echo "exit=$?"
exit=1
$ grep -n -i "without the indicator\|GijSeq\|GiiSeq\|asGMc" docs/DECISIONS.md docs/paper-deltas.md; echo "exit=$?"
exit=1
```
