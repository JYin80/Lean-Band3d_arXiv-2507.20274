Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 07:17:30 UTC 2026

### (i) Exponent table
Notation: `N = sz.size`, `ℓ = zdistInf(a₁−a₂)`, `B(a) = {b : zdistInf(b−a) ≤ ρ}`, `η = etaT E t`, `A = max_{x,y}‖STGM x y‖`, `d ≥ 3`.
Facts used: `0 ≤ t ≤ lemT z < 1` (`lemT_lt_one`, `Im z ≥ N^{-1+ε} > 0` from `locDomain`), `|E| < 2` (`abs_lemE_lt_two`), `‖mE‖ = 1` (`norm_mE`).

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `Φ`-comparison, target 3(c) | `Φ(\|b₁−b₂\|) ≤ K(ρ)Φ(ℓ)` for `zdistInf(b_i−a_i) ≤ ρ`, `K(ρ)=max(C₁2^{C₂}, Cc(2), Cc(2)C₁(4ρ+2)^{C₂})`. Triangle `ℓ ≤ 2ρ+\|b₁−b₂\|` (`zdist_add_le`, `Lattice.lean:38`): `ℓ ≥ max(4ρ,2)` ⇒ `\|b₁−b₂\| ≥ ℓ/2 ≥ 1`, antitone + 2nd relation at `(ℓ/2, ℓ)`; `ℓ ≤ 2`: `Φ(\|b₁−b₂\|) ≤ Φ(0) ≤ Cc(2)Φ(ℓ)`; `2<ℓ<4ρ`: `Φ(0) ≤ Cc(2)Φ(1) ≤ Cc(2)C₁ℓ^{C₂}Φ(ℓ)`. `Cc(2) ≥ 1` is forced (`Φ0 ≥ Φ1 > 0`). Also `W^{-d}1(ℓ≤ρ) ≤ C₃²Φ(0)² ≤ C₃²K²Φ(ℓ)²`. Result `ξ² ≤ K²(2(2ρ+1)^{2d}N^τ + C₃²)Φ(ℓ)²`, all factors polynomial in `ρ+1 ≤ N^{τ'}` | script: ratios `1.00/1.73/2.23/2.23` vs `K = 13.9/124.7/346.4/1676.6` at `ρ = 0/1/2/5` (`LWPhiB`, `C₁=C₂=2`, `Cc(C)=√(C+1)`); instance `Φ0 ≡ W^{-1}`: ratio 1, `K(1)=max(8,1,72)=72` |
| 2 | Ward bound, `lwXi_ward_sum` | `Σ_{a₂}lwXiSq ≤ 2(2ρ+1)^{2d}(W^dη)⁻¹(1+A) + (2ρ+1)^d W^{-d}`: two `(2ρ+1)^d` ball counts (`DecayLoopB_card_ball`, `DecayLoopB.lean:282`, `ρ ≥ 0`: `B(a₁)` and `#{a₂ : zdistInf(b₂−a₂) ≤ ρ}`), two charges, `Σ_{b₂}‖𝓛^{(2)}‖ = (W^dη)⁻¹ Im 𝓛^{(1)}_{+,b₁}` (`𝓛^{(2)}_{(s,!s)} ≥ 0`), `\|𝓛^{(1)}\| ≤ ‖m‖+A = 1+A` | script: `ρ=0`: `0.534 ≤ 0.831`, `ρ=1`: `283.4 ≤ 518.2` (L=3, η=.5); `ρ=1, L=5` (ball 27 of 125 blocks): `287.4 ≤ 490.6` |
| 2a | orientation / Ward cases | literal value `𝓛^{(2)}_{(s,!s),(b₁,b₂)} = W^{-2d}Σ_{x∈b₁,y∈b₂}\|G(s)_{yx}\|²` (indices `(y,x)`, not `(x,y)`; the same row sums as `G(±)` commute). `sum_gloop_two_ward` (`ConArgDet.lean:235`) is the `[true,false]` sum over the last label only; `[false,true]`, `[b₁,b₂]` needs rotation (`cad_gloop_rotate`) + head sum (`cad_sum_gloop_head`, private there) + `G(+)G(−)=G(−)G(+)` | Ward error `8e-17` for both charges |
| 2b | target 3(b) | event `‖G−M‖_max ≤ N^{𝔠ε₁}W^{-ε₁} ≤ 1` (`size_rpow_le_W_rpow`, `W ≥ N^𝔠`) ⇒ `A ≤ 1`; `W^{-d} ≤ (W^dη)⁻¹` as `η ≤ (1−t)Im m ≤ 1`; bound `≤ 5(2ρ+1)^{2d}(W^dη)⁻¹ ≤ N^{τ'}(W^dη)⁻¹` for `2dτ<τ'` | instance: `N^{1/120}W^{-1/20} = 1.1290/1.1892 = 0.949`; `η_t = 0.9077` |
| 3 | radii of `lwXi_gexRHS_le` | `zdistInf(a'−a) ≤ 1+R`, `zdistInf(a−b) ≤ 2R+1` (if `zdistInf([x]−[y]) ≤ 1`) against `ρ`, with `zdistInf ≤ zdistD ≤ R`, `R ≥ 0`: need `2R+1 ≤ ρ`, which gives `1+R ≤ ρ` | slack `R` for the first, 0 for the second; script: min `lwXiSq/STgexRHS`: `1.000` (`R=0`, tight), `7.78` (`L=5, R=1`) |
| 4 | indicator, targets 4, 5 | `Ω(t,W^{-ε₁/2})` w.h.p. at `τ = 𝔠ε₁/2`: `N^τW^{-ε₁} ≤ W^{-ε₁/2} ⟺ N^τ ≤ W^{ε₁/2}`, from `N^τ ≤ W^{τ/𝔠}` (`size_rpow_le_W_rpow`) | exponent slack 0 at `W = N^𝔠`; `sz0`, n=0: `1.0625 ≤ 1.0905` |
| 5 | radii for LW-02 | `R=(log W)^{3/2}`, `ρ=2R+1` (target 6: `C=2,K=3/2,C'=1`): `log W ≤ log N` (`W ≤ W^d ≤ N`; `d=0` is excluded by `SizeTendsto`), `(log N)^{3/2}=o(N^τ)`. `R=(log W)^{3/2}` is the radius of the only merged tail `lwTail_log32` (`LWSizeClaim.lean:1285`; T2170 (a) row 6a). The paper's pair `((log W)^{1+ε₁},(log W)^{1+2ε₁})` has `2R+1 ≤ ρ` only for `log W ≥ 3^{1/ε₁}`; and `ρ_paper < (log W)^{3/2}` for `log W > 1` (`1+2ε₁<3/2`). Choice: `ρ = 2(log W)^{3/2}+1` | `ρ0+1 ≤ N^τ` from n≥0 (`τ=.5,.2`), n≥5 (`.1`), n≥316 (`.05`); tail `(log W)^{1/2} ≥ 2VD'/c` is LW-02's eventual condition, not a premise of any target |
| 6 | target 5 | `STmaxLoop2 = sup‖𝓛_{(−,+),(a,b)}‖ ≤ N^τ sup Φ(\|a−b\|)² ≤ N^τΦ(0)²` (`LWLoop2` at `s=false`: `![false,!false]=![false,true]`; antitone, `Φ>0` eventually); square root | instance limits (lesson 14), `Bctl/W^{-2}`: `3.4e-2` (n=0), `2.1e-7` (n=10), `3.3e-22` (n=1e4); entry law `Bctl^{1/4}/W^{-ε₁}`: `9.0e-2`, `2.0e-5`, `9.0e-16` (shapes of `STLmax` at `k=2`, `STStep1Weak`) |
| 7 | consumer composition | `GtoAG` at `Ψ = max(1,C₃)N^τΦ(0)`: `‖G_{xy}‖,‖G_{xx}−m‖ ≤ N^τΦ(0) ≤ Ψ` (target 5); `W^{-d/2} ≤ C₃Φ(0) ≤ Ψ` (`LWClass`); `ξ = N^τ lwXiVar`, `c = N^τ ≥ 0` (target 4). Extra `N^{τ(\|ord Γ−auxOrd Γ\|+#aux edges)}`, finite for a fixed graph, absorbed (τ arbitrary); with `LWAnp` exponents add `(ord−auxOrd)+(auxOrd−p)=ord−p` (T2170 (a) row 7) | exact |

Consumer check (§45 O2): `LWAnp`, `LWAnpKey`, `LWAnpKeyGh` premise `LWXi sz (STflowE z) t Φ ξ` ← target 3 at `ξ = lwXiVar … ρ` (with `LWPsiAll`, `LWLoop2`, entry premise, radius premise of row 5). `LWGtoAG`: `hG`, `hGd` ← target 5; `hξ` ← target 4 + `lwGbyXi_hxi`; window ← `LWClass`. `LWMoment`: `LWAssm` supplies `LWPsiAll := ⟨ε₀>0, LWClass, LWPsiRel⟩`, `LWLoop2`, entry law `:= LWInit.1`, `ε₁ := ε₀`. `LWtermEXP` (LW-14): `Φ n r := max(W^{-d/2}, √Bctl)` const in `r`, `LWLoop2` from `STLmax` at `k=2`, entry law from `STLocalEntry`; checked by LW-14, not here.

### (ii) One concrete nondegenerate instance
Targets 3-6 at the merged `sz0` data: `d=3`, `L=4(n+1)`, `W=(2(n+1))^5`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z0`, `t≡1/16`, `Φ0≡W^{-1}` (`C₁=C₂=2, C₃=1, Cc≡1, ε₀=1/20`), `ε₁=1/20`, `R0=(log W)^{3/2}`, `ρ0=2R0+1`. Hypotheses held at once (columns below): `W ≥ N^{1/6}`, `0 ≤ t ≤ lemT z0`, `|lemE|<2`, `R0 ≥ 0`, `2R0+1 ≤ ρ0`, row 4 inequalities, `ρ0+1 ≤ N^τ` eventually. `ρ0 > L/2` (ball = whole torus) for `n ≤ 152`, local (`ρ0 ≤ L/2`) from `n = 153`; every hypothesis holds at every `n`. Stays a hypothesis: `LWLoop2 sz0 …`, entry law (stochastic inputs; limits in the last block). Targets 2: random Hermitian `H`, variance `W^{-d}SB`, `SB=2^{-zdistD}` normalized, `z=E+iη`.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2185/preflight.py`
```
[run1 L=3,W=2] N=216 E=0.3 eta=0.5: trace-vs-entry-expansion err=2e-18; L2(+-),(-+) min Re=2.2e-03 max|Im|=2e-17; Ward err (+-)/(-+)=8e-17/8e-17
   |m|=1.000000 A=max|G-M|=0.412 max|L1|=0.826<=1+A: True
   xi symmetry err (rho=0,1,2,5)=3e-17; min_a lwXiSq(a,a)*W^d at rho=0 = 2.203 (>=1)
   gexRHS_le R=0,rho=1: 729 quadruples, min lwXiSq/STgexRHS=1.000; R=1,rho=3: 35721 quadruples, min lwXiSq/STgexRHS=1.000
   ward_sum lhs<=rhs: rho=0: 0.5341<=0.8311 True; rho=1: 283.4<=518.2 True; rho=2: 283.4<=1.105e+04 True;  (info) max_(x!=y)|G_xy|^2/lwXiSq_1([x],[y])=0.006
[run2 L=3,W=2] N=216 E=0.3 eta=0.02: trace-vs-entry-expansion err=3e-17; L2(+-),(-+) min Re=1.1e-01 max|Im|=4e-15; Ward err (+-)/(-+)=4e-14/5e-14
   |m|=1.000000 A=max|G-M|=1.753 max|L1|=1.292<=1+A: True
   xi symmetry err (rho=0,1,2,5)=2e-16; min_a lwXiSq(a,a)*W^d at rho=0 = 4.058 (>=1)
   gexRHS_le R=0,rho=1: 729 quadruples, min lwXiSq/STgexRHS=1.000; R=1,rho=3: 35721 quadruples, min lwXiSq/STgexRHS=1.000
   ward_sum lhs<=rhs: rho=0: 15.62<=34.53 True; rho=1: 8472<=2.509e+04 True; rho=2: 8472<=5.377e+05 True;  (info) max_(x!=y)|G_xy|^2/lwXiSq_1([x],[y])=0.009
[run3 L=5,W=2] N=1000 E=0.3 eta=0.5: trace-vs-entry-expansion err=2e-19; L2(+-),(-+) min Re=3.1e-04 max|Im|=6e-17; Ward err (+-)/(-+)=2e-16/2e-16
   |m|=1.000000 A=max|G-M|=0.337 max|L1|=0.800<=1+A: True
   xi symmetry err (rho=0,1,2,5)=9e-16; min_a lwXiSq(a,a)*W^d at rho=0 = 2.206 (>=1)
   gexRHS_le R=0,rho=1: 15625 quadruples, min lwXiSq/STgexRHS=1.000; R=1,rho=3: 765625 quadruples, min lwXiSq/STgexRHS=7.780
   ward_sum lhs<=rhs: rho=0: 0.5215<=0.7933 True; rho=1: 287.4<=490.6 True; rho=2: 6047<=1.046e+04 True;  (info) max_(x!=y)|G_xy|^2/lwXiSq_1([x],[y])=0.007
[row1] L=9 W=2 g=0.05 t=0.0625 c0=0.1 K=9: antitone=True rel1(C=2)=True rel2=True W^-d<=C3^2Phi(0)^2: True
   rho=0: ratio 1.00<=K=13.9 True; xiPhi2/Phi(l)2 2.13<=576 True | rho=1: ratio 1.73<=K=124.7 True; xiPhi2/Phi(l)2 1.69e+03<=2.27e+07 True | rho=2: ratio 2.23<=K=346.4 True; xiPhi2/Phi(l)2 3.94e+04<=3.75e+09 True | rho=5: ratio 2.23<=K=1676.6 True; xiPhi2/Phi(l)2 1.3e+06<=9.96e+12 True
[row1] L=9 W=2 g=0.05 t=0.9 c0=0.1 K=9: antitone=True rel1(C=2)=True rel2=True W^-d<=C3^2Phi(0)^2: True
   rho=0: ratio 1.00<=K=13.9 True; xiPhi2/Phi(l)2 2.01<=576 True | rho=1: ratio 1.73<=K=124.7 True; xiPhi2/Phi(l)2 1.69e+03<=2.27e+07 True | rho=2: ratio 2.23<=K=346.4 True; xiPhi2/Phi(l)2 3.94e+04<=3.75e+09 True | rho=5: ratio 2.23<=K=1676.6 True; xiPhi2/Phi(l)2 1.3e+06<=9.96e+12 True
[instance sz0] d=3 L=4(n+1) W=(2(n+1))^5 lam=(2(n+1))^-6, kappa=eps=dd=1/10, c=1/6, eps1=eps0=1/20, t=1/16, rho0=2(log W)^1.5+1, R0=(log W)^1.5
  n L W N | W>=N^(1/6) t<=lemT |lemE|<2 eta_t | N^(c eps1)W^-eps1<=1 | N^(c eps1/2)<=W^(eps1/2) | rho0 R0 2R0+1<=rho0 | L/2 rho0<=L/2
     0     4 3.200e+01 2.097e+06 True True True 0.9077 | True True | 13.90 6.45 True | 2.0 False
    50   204 1.104e+10 1.143e+37 True True True 0.9077 | True True | 223.41 111.20 True | 102.0 False
   153   616 2.772e+12 4.977e+45 True True True 0.9077 | True True | 307.71 153.36 True | 308.0 True
  1000  4004 3.216e+16 2.135e+60 True True True 0.9077 | True True | 469.67 234.34 True | 2002.0 True
  target 6 premise rho0+1<=N^tau holds from (first n with a 50-window of successes): tau=0.5: n>=0; tau=0.2: n>=0; tau=0.1: n>=5; tau=0.05: n>=316
  external premises at sz0, t=1/16 (Bctl = W^-d B_{t,0}):  n, Bctl/W^-2 (LWLoop2 scale), Bctl^(1/4)/W^-eps1 (entry law)
   n=0: 3.385e-02   9.017e-02
   n=10: 2.070e-07   2.035e-05
   n=10000: 3.332e-22   8.979e-16
  paper radii R=(log W)^(1+e1), rho=(log W)^(1+2e1): 2R+1<=rho once (log W)^e1>=3, i.e. log W>=3^(1/e1): e1=1/20 -> 3.49e+09, e1=1/10 -> 5.9e+04; chosen R=(log W)^1.5, rho=2R+1 has no such threshold
```

### Verdict
- Target 1 (vocabulary `lwXiSq`, `lwXiVar`): PASS. Target 2 (`lwXiVar_nonneg`, `lwXiVar_symm`, `lwXiSq_ge_W`, `lwXi_gexRHS_le`, `lwXi_ward_sum`): PASS; the prover must use the literal orientation of row 2a and the `[false,true]` Ward step.
- Target 3 (`lwXiClaim_holds`): PASS (rows 1, 2, 2b). Target 4 (`lwGbyXi_holds`, `lwGbyXi_hxi`): PASS (rows 3, 4). Target 5 (`lwEntryPsi_holds`): PASS (rows 4, 6). Target 6 (`lwXiRad_holds`): PASS (row 5).
- No hypothesis set is empty or collapsed, no exponent fails to close, no external input is missing.

## (b) Script output (stage 1b, Sonnet 5.5; branch `t/T2185`, commit `7435b5a`, committed 14:42:54 UTC; this stage started 14:21:51 UTC; the outputs below were taken between 14:43 and 14:44 UTC, all per `date -u`)

### Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2185`)
```
$ lake build RBM3D.Graph.AuxGraph2 2>&1 | tail -1
Build completed successfully (3845 jobs).
$ lake build RBM3D.Graph.AuxGraph2 2>&1 | grep -c "AuxGraph2.lean"   # warning/error lines naming the file
0
$ lake build 2>&1 | tail -1   # whole library (root import is added by the hub at merge)
Build completed successfully (3989 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Graph/AuxGraph2.lean   # word-boundary form `\bsorry\b|\badmit\b`
0
$ wc -l RBM3D/Graph/AuxGraph2.lean
    1500 RBM3D/Graph/AuxGraph2.lean
```

### Axioms of the new public declarations (`lake env lean scratch/axioms.lean`, `#print axioms RBM.Graph.<name>`)
```
'RBM.Graph.lwXiVar_nonneg' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiVar_symm' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiSq_ge_W' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXi_gexRHS_le' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXi_ward_sum' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiClaim_holds' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwGbyXi_holds' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwGbyXi_hxi' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwEntryPsi_holds' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiRad_holds' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiSq' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiVar' : [propext, Classical.choice, Quot.sound]
```

### Registry pre-check (CLAUDE.md §20 (2); uncommitted file `import RBM3D` + `import RBM3D.Graph.AuxGraph2` + `#assert_rbm_axioms`)
```
$ lake env lean scratch/precheck.lean ; echo "exit: $?"      ->  exit: 0
axiom audit: 5403 theorems, 1908 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
(`Test/Axioms.lean:403-407` throws on any premise no ledger lists, so exit 0 means none; `Test/Axioms.lean` is not touched: the two definitions are data, the four `Prop`s are proved by their `*_holds`)
```

### The two definitions and the four `Prop`s against the check file `docs/tickets/checks/T2185-check.lean` (script `diffdefs.py`: docstring + declaration block, namespace line stripped)
```
lwXiSq check lines: 10 lean lines: 10 IDENTICAL
lwXiVar check lines: 4 lean lines: 4 IDENTICAL
LWXiClaim check lines: 16 lean lines: 16 IDENTICAL
LWGbyXi check lines: 18 lean lines: 18 IDENTICAL
LWEntryPsi check lines: 15 lean lines: 15 IDENTICAL
LWXiRad check lines: 5 lean lines: 5 IDENTICAL
ALL IDENTICAL
```

### Target statements extracted from `RBM3D/Graph/AuxGraph2.lean` by script (`extract.py`; docstrings omitted; the six pinned blocks above are byte-identical to the check file)
```
== definitions (docstrings omitted) ==
def lwXiSq {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
    ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0)
def lwXiVar {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  Real.sqrt (lwXiSq sz E t ρ n a₁ a₂ ω)
def LWXiClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) →
            LWXi sz (STflowE z) t Φ (lwXiVar sz (STflowE z) t ρ)
def LWGbyXi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₁ : ℝ, 0 < ε₁ →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ ρ R : ℕ → ℝ, (∀ n, 0 ≤ R n) → (∀ n, 2 * R n + 1 ≤ ρ n) →
          Prec sz (U := fun n => {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ×
              (Zd d (sz.L n) × Zd d (sz.L n)) // q.1.1 ≠ q.1.2 ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n})
            (fun n q ω => ‖Gt sz n (STflowE z n) (t n) true ω q.1.1.1 q.1.1.2‖)
            (fun n q ω => lwXiVar sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω)
def LWEntryPsi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => Φ n 0)
def LWXiRad : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ C C' K : ℝ, 0 ≤ C → 0 ≤ C' → 0 ≤ K →
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      C * Real.log ((sz.W n : ℕ) : ℝ) ^ K + C' + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ
== theorems ==
theorem lwXiVar_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    0 ≤ lwXiVar sz E t ρ n a₁ a₂ ω := Real.sqrt_nonneg _
theorem lwXiVar_symm (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwXiVar sz E t ρ n a₁ a₂ ω = lwXiVar sz E t ρ n a₂ a₁ ω := by
theorem lwXiSq_ge_W (hρ : 0 ≤ ρ n) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ lwXiSq sz E t ρ n a a ω := by
theorem lwXi_gexRHS_le {R : ℝ} (hR : 0 ≤ R) (hρ : 2 * R + 1 ≤ ρ n)
    (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hx : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R)
    (hy : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R) :
    STgexRHS sz n (E n) (t n) ω (STblk sz n x) (STblk sz n y) ≤ lwXiSq sz E t ρ n a b ω := by
theorem lwXi_ward_sum (hE : |E n| < 2) (ht1 : t n < 1) (hρ : 0 ≤ ρ n) (ω : sz.SeqΩ) {A : ℝ}
    (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (E n) (t n) ω x y‖ ≤ A) (a₁ : Zd d (sz.L n)) :
    ∑ a₂, lwXiSq sz E t ρ n a₁ a₂ ω ≤
      2 * (2 * ρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (t n))⁻¹ * (1 + A)) +
        (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
theorem lwXiClaim_holds (d : ℕ) : LWXiClaim d := by
theorem lwGbyXi_holds (d : ℕ) : LWGbyXi d := by
theorem lwGbyXi_hxi {d : ℕ} (sz : Sizes d) (E t ρ R : ℕ → ℝ) (n : ℕ)
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), x ≠ y →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖Gt sz n (E n) (t n) true ω x y‖ ≤ c * lwXiVar sz E t ρ n a b ω) :
    (∀ a b : Zd d (sz.L n), 0 ≤ (fun a b : Zd d (sz.L n) => c * lwXiVar sz E t ρ n a b ω) a b) ∧
    (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), x ≠ y →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖(lwSampleData sz n (zt (E n) (t n)) (t n) M S Sp ω).G x y‖ ≤
        (fun a b : Zd d (sz.L n) => c * lwXiVar sz E t ρ n a b ω) a b) :=
theorem lwEntryPsi_holds (d : ℕ) : LWEntryPsi d := by
theorem lwXiRad_holds : LWXiRad := by
== instances (examples) ==
1347: /-- **Instance 1** (target 2): `W^{-d} ≤ ξ([a],[a])²`, `ξ([a],[a]) > 0`, at every size, block and sample. -/
1358: /-- **Instance 1** (target 2): the first conjunct of `LWXi` for `lwXiVar` at `n = 0`. -/
1365: /-- **Instance 1** (target 2, `(eq:Gbyxi)`): `lwXi_gexRHS_le` at `n = 0` for two distinct points, with the blocks
1379: /-- **Instance 1** (target 2, the Ward part): `lwXi_ward_sum` at `n = 0`, `A` the sum of the entries of `G_t - M`
1390: /-- **Instance 2** (target 3, `claim:xi`): `LWXi` for `ξ = lwXiVar` at the merged data; the premises `LWLoop2` and the
1399: /-- **Instance 3** (the consumer): the merged `LWAnp` (`h`, owed to LW-02) fed with `ξ = lwXiVar`. -/
1421: /-- **Instance 4** (target 4, `(eq:Gbyxi)` off the diagonal): the index set is nonempty at every size, and
1439: /-- **Instance 5** (target 5, `(eq:Gbyxi)` entrywise): `‖G_t - M‖_max ≺ Φ0(0)` at the merged data. -/
1448: /-- **Instance 6** (`lwGbyXi_hxi`): the premises `hξ0`, `hξ` of the merged `lwGtoAG_holds` for
1465: /-- **Instance** (target 6): the radii `R0`, `ρ0` are `N^{o(1)}` along `sz0`. -/
```
The instances are the `example`s listed last; all compile in the build above (no `sorry`).  Hypotheses left in the instances (another gate's stochastic
inputs, CLAUDE.md §4 step 2): `LWLoop2 sz0 (STflowE z0) tInst Φ0`, the entry law `‖G_t - M‖_max ≺ W^{-1/20}` (`auxGraph2_Entry`), `LWAnp 3` (instance 3), the graph-side
data of `lwGtoAG_holds` and the sample event `h` (instance 6).  Their limits at `sz0` are the script output of section (a) (rows 6 and the last block: `Bctl/W^-2 = 3.4e-2, 2.1e-7, 3.3e-22`
at n = 0, 10, 1e4; entry-law ratio `9.0e-2, 2.0e-5, 9.0e-16`).  Nondegenerate data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `x != y` with blocks `[x]`, `[y]` (instances 1, 4), index set of target 4 nonempty at every `n`.

### Name-clash grep and ports
```
$ for n in lwXiSq lwXiVar LWXiClaim LWGbyXi LWEntryPsi LWXiRad lwXiVar_nonneg lwXiVar_symm lwXiSq_ge_W lwXi_gexRHS_le lwXi_ward_sum lwXiClaim_holds lwGbyXi_holds lwGbyXi_hxi lwEntryPsi_holds lwXiRad_holds auxGraph2_ AuxGraph2; do grep -rlw "$n" RBM3D <main>/RBM3D <main>/docs/tickets/checks | grep -v "AuxGraph2.lean\|T2185-check.lean"; done | sort | uniq -c
(empty: 0 files)
$ grep -c "LocCost\|scost\|locCost" RBM3D/Graph/AuxGraph2.lean          -> 0
$ grep -nE "^private (theorem|def|lemma|abbrev|noncomputable def) " RBM3D/Graph/AuxGraph2.lean | grep -v auxGraph2_      -> (empty: every private helper has the prefix)
$ git diff --stat main...t/T2185          ->  RBM3D/Graph/AuxGraph2.lean | 1500 +++  (1 file changed; the only file of the branch)
$ grep -rn "theorem gloop_two_plus_minus_nonneg" RBM3D | wc -l   ->  0
```
Ports: none from RBM1D/RBM2D (no light-weight graph layer there; no `git diff --stat` for them).  Copies inside RBM3D of declarations that are `private` there (also in the module docstring):
`Path/LemDecCalE.lean:109-142` (lattice `zdistInf` helpers), `Green/Pins.lean:377-400` (`trace_pm_formula`), `Green/Pins.lean:350-364` (`gres_blockMat_true`),
`Induction/ConArgDet.lean:141-163` (`Gres_true/false/conjTranspose`); line numbers are those of the worktree at the branch base `7771372`.

### Narrative
- Routes are the ticket's.  Target 3 is two `auxGraph2_prec_of_imp` bad-set implications into `LWLoop2` (conjunct 2) and into the entry law (conjunct 3);
  target 4 pulls back along `q ↦ ⟨q.1.1, q.2.1⟩` (the pair `(x, y)` with its proof of `x ≠ y`) inside the implication (no separate `precomp_param`); target 5 uses `StochDomAt.of_subset_union`
  (bad sets of `(GiiGEX)` and of `LWLoop2`); indicator removal is `Unif.stochDom_of_indicator` with `Ω(t, W^{-ε₁/2})` w.h.p. from `Prec.whp` at `τ = 𝔠 ε₁/2`.
- Ward for both charges is proved here (`auxGraph2_rowsum_ward`, `auxGraph2_rowsum_norm_le`): `sum_gloop_two_ward` covers `[true,false]` over the last label only
  (section (a) row 2a); the literal orientation `W^{-2d} Σ_{v∈[b],w∈[a]} |G(s)_{vw}|^2` is `auxGraph2_trace_pm_formula`.  `lwXi_ward_sum` needs `t n < 1`, not `0 ≤ t n`.
- `K(ρ)` of row 1 is used as `K₀ (4ρ+2)^{C₂}`, `K₀ = C₁ 2^{C₂} + Cc 2 + Cc 2 C₁` (each of the three terms of the `max` is `≤` it); `Cc 2 > 0` is derived at each `n`
  from `0 < Φ n 0 ≤ Cc 2 Φ n 0` (relation at `ℓ = 0`, class positivity), so no premise is added.  Exponents: `LWLoop2` at `τ/2`, radii at `τ/8` powers of `u = N^{τ/8}`, entry law at `𝔠 ε₁/2`.
- `lwXiRad_holds`: `d = 0` is excluded by `SizeTendsto` (`N = 1`); `log W ≤ log N` from `W ≤ (WL)^d`; `isLittleO_log_rpow_rpow_atTop`.
- `lwGbyXi_hxi` has no pin in the check file; its form is the ticket's description (`D.G = Gt` by `rfl`); instance 6 applies `lwGtoAG_holds` with `hξ0`, `hξ` supplied by it.
- `hd : 3 ≤ d` enters through `stGbEXP_holds hd` (targets 4, 5); `κ, ε > 0` through `v3_premises_of_stFlow`; no hypothesis was added to a pin.

## (c) Verified Mathlib / merged names used (all `#check`ed by `lake env lean scratch/mathlib_check.lean`: 119 names, exit 0, 0 error lines; grouped by namespace)
```
Bool: false_eq_true, not_false, not_true
Complex: I, conj_conj, mul_conj', norm_natCast, norm_real, ofReal_sum, star_def, sub_conj
Finset: card_filter, card_univ, filter_congr, le_sup, mem_filter, mem_univ, mul_sum, single_le_sum, sum_add_distrib, sum_comm, sum_congr, sum_const, sum_filter, sum_ite_eq, sum_ite_eq', sum_le_sum, sum_le_sum_of_subset_of_nonneg, sum_nonneg, sum_pair, sup'_le, sup_congr, sup_le
Matrix: conjTranspose_apply, conjTranspose_nonsing_inv, conjTranspose_one, conjTranspose_smul, conjTranspose_sub, cons_val_succ, cons_val_zero, diag_apply, diagonal, diagonal_apply, inv_submatrix_equiv, mul_apply, mul_assoc, mul_diagonal, mul_one, mul_smul, nonsing_inv_eq_ringInverse, of, of_apply, one_apply, smul_apply, smul_mul, sub_mul, submatrix_apply, sum_apply, trace, trace_mul_comm, trace_mul_cycle, trace_smul, trace_sub, trace_sum
MeasureTheory: Measure, measure_mono
Nat: cast_le, cast_nonneg, cast_pos, cast_zero, eq_zero_of_le_zero, eq_zero_or_pos, le_mul_of_pos_right, le_self_pow, one_le_cast, pos_of_ne_zero
Real: log, log_le_log, log_nonneg, mul_rpow, norm_of_nonneg, one_le_rpow, rpow_add, rpow_le_one_of_one_le_of_nonpos, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_mul, rpow_natCast, rpow_neg, rpow_nonneg, rpow_pos_of_pos, sq_sqrt, sqrt, sqrt_le_iff, sqrt_nonneg, sqrt_pos
Set: Ici, indicator, mem_Ici
ZMod: nontrivial_iff
(root): abs_nonneg, div_le_div_iff₀, inv_anti₀, inv_pos, isLittleO_log_rpow_rpow_atTop, le_abs_self, le_mul_of_one_le_right, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_pos, not_tendsto_atTop_of_tendsto_nhds, pow_le_pow_left₀, pow_le_pow_right₀, pow_lt_pow_left₀, pow_nonneg, sq_nonneg, tendsto_const_nhds, tendsto_rpow_atTop, zero_le_one
```
Merged RBM3D names used (`#check`ed with `lake env lean scratch/merged_check.lean`, exit 0, no unknown identifier): `RBM.Green.stGbEXP_holds`, `RBM.Green.v3_premises_of_stFlow`, `RBM.Ind.PerTimeCalc.Unif.stochDom_of_indicator`, `RBM.StochDomAt.of_subset_union`,
`RBM.Gauss.HighProbAt.mono`, `RBM.Gauss.Sizes.Prec.whp`, `RBM.Gauss.Sizes.size_rpow_le_W_rpow`, `RBM.Gauss.Sizes.tendsto_size`, `RBM.Ind.DecayLoopB_card_ball`, `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`,
`RBM.trace_green_sub_trace_green_conj'`, `RBM.green_sub_green`, `RBM.Gauss.etaT_pos`, `RBM.Gauss.etaT_eq_zt_im`, `RBM.mE_im_pos`, `RBM.mE_im`, `RBM.norm_mE`, `RBM.zdistD_zero`, `RBM.abs_lemE_lt_two`, `RBM.Gauss.LWInst.{Φ0, psiAll0, tInst_range, inst_Anp, one_le_W}`, `RBM.Graph.lwGtoAG_holds`.
Names verified absent: `gloop_two_plus_minus_nonneg` (the RBM2D name; the only RBM3D hit is a comment, `Path/StepDecompLoop.lean:663`), so the sign of `𝓛^{(2)}_{(s,!s)}` is proved here (`auxGraph2_loop2_real`).

## (d) Open issues and paper-delta candidates
- No correction of section (a) is needed (no (a′)); no obstruction; no pin, signature or hypothesis changed; the file scope is the one new file (`Test/Axioms.lean` untouched).
- `LWXi` stays in the owed ledger: still a premise of `LWAnp`, `LWAnpKey`, `LWAnpKeyGh`; T2185 proves it only for `ξ = lwXiVar` (instance 2, 3).  The consumer (LW-02, LW-13, LW-14) must supply the radius premise `ρ + 1 = N^{o(1)}` (target 6 gives it for `ρ0 = 2 (log W)^{3/2} + 1`, `R0 = (log W)^{3/2}`) and the stochastic inputs `LWLoop2`, the entry law.
- T2185a: `ξ²` sums the two charges `![true,false]`, `![false,true]` (the paper takes the maximum, `7_8:882`; equivalent up to the factor 2).
- T2185b: the radius `ρ` of `(eq:xia1a2)` is a parameter with `ρ + 1 = N^{o(1)}`, the ball is `zdistInf` on blocks; for LW-02 `R = (log W)^{3/2}`, `ρ = 2 (log W)^{3/2} + 1` in place of `(log W)^{1+ε₁}`, `(log W)^{1+2ε₁}` (`2R + 1 ≤ ρ` needs `(log W)^{ε₁} ≥ 3` for the paper's pair; section (a) row 5).
- T2185c: `(eq:Gbyxi)` is split into `‖G - M‖_max ≺ Ψ_t(0)` (all entries, `(GiiGEX)` + `(LW_assm)`) and `|G_{xy}| ≺ ξ(a,b)` uniformly on the `R`-balls with `2R + 1 ≤ ρ` (no `W^{-D}`: confinement is LW-11a's tail).
- T2185d: `claim:xi` uses besides `(LW_assm)`, `(eq:Psi)` and Ward only `‖G_t - M‖_max ≺ W^{-ε₁}` (for `|𝓛^{(1)}| ≤ 1 + A`).
- Observation: `lwXi_ward_sum` is stated without `0 ≤ t n` (a strengthening of the ticket's `0 ≤ t n < 1`); the registry pre-check lists no name.
