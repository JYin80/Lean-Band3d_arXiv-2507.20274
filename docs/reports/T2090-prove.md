Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 00:42:58 UTC 2026

### (i) Exponent table (d = 3 numbers where a number is given; `a := a_s = sz.Bctl n (s n) = W^{-d}B_{s,0}`, `c₀ := min(2𝔠𝔡, τ)`, `τ = ε/2`)

Assembly of `step1` (`STStep1Loop ∧ STStep1Weak`): S1Std from the flow (`s1_std_of_stFlow`); `h55` from `STLK s`, `STKbound`; for a time sequence `u ∈ [s,t]` apply `STGbEXPii d`, `STGbEXPij d` at time `u` (`0 ≤ u ≤ lemT z`, `ε₀ = c'`) and `s1_LI` (k = 2) to get `1(‖G_u-M‖ ≤ 2a^{1/4}) ‖G_u-M‖ ≺ f := (2·3^d) a^{7/15}` (`s1_wl_det`); at the net points `θ_k` the forbidden region `forbidden_region` (`x ∉ [a^{1/4}/2, 2a^{1/4}]`); `gopbound` (C = 1) moves it to all `u ∈ [s,t]` (`x_u ∉ {a^{1/4}}`); `stepOneBootstrap` with `hinit` from `STLocalMax s` gives w.h.p. `x_u < a_s^{1/4}` for all `u`; then `a_s^{1/4} ≤ a_u^{1/4}` (`STBctl_mono`) gives `STStep1WeakPT`, and `{x_u < a^{1/4}} ⊆ {‖G_u‖_max ≤ 2}` removes the indicator in `s1_LI`, giving `STStep1LoopPT`; `step1NetLift` (T2062) turns both into `STStep1Loop`, `STStep1Weak`.

| row | value | constraint | slack |
|---|---|---|---|
| c₀ | min(2𝔠𝔡, τ); instance 1/30 | > 0 | 1/30 |
| τ₀ = ε_net = c' | c₀/8 (instance 1/240) | F3 `N^{τ₀} a^{1/2} < a^{1/4}`: from `a ≤ 2N^{-c₀}` need `N^{c₀/8} > 2^{1/4}` | exponent c₀/8 |
| F4 (net gap) | `2·3^d a^{7/15} ≤ N^{-ε} a^{1/4}/2` | `a^{13/60} ≤ 2^{13/60} N^{-13c₀/60}` and `13/60 > 1/8` | exponent 11c₀/120 (and a constant 4·3^d absorbed once N large) |
| F5 (`Ω(u,c')`, also `‖G‖_max ≤ 2`) | `2a^{1/4} ≤ W^{-c'}` | `W^{-c'} ≥ N^{-c₀/(8d)}`, `a^{1/4} ≲ N^{-c₀/4}`, `1/4 > 1/(8d)` | exponent c₀(1/4 - 1/(8d)) = 5c₀/24 at d = 3 |
| F6 (net finer than a/2) | `N^{-1} ≤ a^{1/4}/2` | `N^{-1} ≤ a` (needs `0 ≤ s`), `N^{3/4} ≥ 2` | exponent 3/4 |
| F7 | `a^{1/4} ≤ 1` | `a → 0` | eventual |
| F8 | `W^{-d} ≤ a^{14/15}` | `W^{-d} ≤ (𝔡⁻²+1) a` (needs `0 ≤ s`, `lam ≤ 𝔡⁻¹`), `(𝔡⁻²+1) a^{1/15} ≤ 1` | eventual; 𝔡⁻²+1 = 101 at 𝔡 = 1/10 |
| ratio | `a(1-s)/(1-u) ≤ a^{1-𝔠_d} ≤ a^{14/15}` | `𝔠_d ≤ 1/15`, `a ≤ 1`, con_st_ind | 1/15 - 1/100 = 17/300 |
| weak-law exponent | loop `g = a^{14/15}`, `√g = a^{7/15}` vs threshold `a^{1/4}` | `7/15 > 1/4` | 13/60 |
| constant `C_d` | `2·3^d` (54), root of `2·9^d + 1` (1459, √ = 38.20) | `(2·3^d)² = 4·9^d ≥ 2·9^d + 1` | 2·9^d - 1 (1457) |
| `s1_gexRHS_le` constants | `2·9^d` = (2 orientations)·(3^d)·(3^d) | ball `‖·‖_∞ ≤ 1` in `Z_L^d` has ≤ 3^d points | exact |
| net constant `C'` | `2C + 14 = 16` at `C = 1` (`gopbound` proof, `Continuity.lean:527-530`); mesh `1/netSize ≤ N^{-16}`; `#net ≤ N^{C'+1} = N^{17}` | `|u-u'| ≤ N^{-16}` ⇒ resolvent entries differ ≤ `N^{-1}`; `u ≤ 1 - 1/N` | `t ≤ 1 - N^{-1+τ} < 1 - N^{-1}` for τ > 0; independent of d |
| union-bound counts | `|Idx| = N`; `|{p₁≠p₂}| ≤ N²`; `|(σ,a)| = 2^k L^{dk} ≤ N^{2k}` (k = 2: ≤ N⁴); `|Z_L^d| = L^d ≤ N` | `L^d ≤ (WL)^d`, `2 ≤ N` | exponents d-free |
| bootstrap band | `a_lo = a^{1/4}/2 < b = 2a^{1/4}` | `a > 0`; `x_net < a_lo ⇒ x_u < a_lo + N^{-1} ≤ a^{1/4}`; `x_net > b ⇒ x_u > b - N^{-1} > a^{1/4}` | F6 |
| initial | `‖G_s-M‖ ≺ a^{1/2}` (`STLocalMax s`) | F3 | as F3 |
| S1Std range | `𝔠_d ∈ (0, 1/100]` | ≤ 1/15 | above |

§29 checks. `0 ≤ s` is used exactly in F6 (`N^{-1} ≤ Bctl`), F8 (`STBctl_ge`), `h55` (u < 1/2 branch) and `0 ≤ u` for `gopbound`/`STGbEXP` at time `u`; `s < t` is not needed (only `s ≤ t`; window length `t - s ≤ 1` from `0 ≤ s, t < 1`); `t ≤ lemT z` is used for `STGbEXPii/ij` at `u ≤ t` and for `RangeCond`, `t < 1`; the pointwise facts (`hs0, hst, ht1`, net membership, `t-s ≤ 1`) are `∀ n`, the facts needing `a → 0`, `lam ≤ 𝔡⁻¹`, `STConStInd` (F3-F8, ratio) are `∀ᶠ n`. All constants (`c₀/8`, `2·3^d`, `2·9^d+1`, `𝔡⁻²+1`, `C' = 16`) depend only on `d, 𝔠, 𝔡, τ`, none on `W, L, λ`.

### (ii) One concrete nondegenerate instance
`sz0` (`d = 3`, `Defs/Sizes.lean:260-265`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `τ=ε/2`, `𝔠_d=1/100`, `s≡0`, `t≡1/16`, `E_n=lemE z_n`, `z_n = 1/2 + i N^{-4/5}`; merged file `Step1Setup.lean:1142` states `S1Std` is discharged at these data (`s1Std_sz0`). The `∀ᶠ` rows fail at n = 0, 1 (F4 only) and hold from n = 2 (N = 8.1e14, not astronomical; checked numerically for every n in [2, 3999], not proved for all n). The two external hypotheses `STGbEXPii`, `STGbEXPij` (`lem_GbEXP`, not proved here) are the antecedents; limit computation below (orders only, loop normalisation not re-derived): `|m(1/2)| = 1` and the `k=1` loop tends to `m`, the `k=1` bound is `1`; `STLocalEntry` scale `W^{-3}B_{u,K}` vs the loop scale `a_u = W^{-3}B_{u,0}` of the GbEXP right sides has ratio `≤ 1` (1.0000 at K = 0, 0.1434 at K = 6); the chain gives `54 a^{7/15} = 1.93e-4 ≤ N^{-ε} a^{1/4}/2 = 5.2e-4`, consistent. At `u = 0`, `seqHflow = 0` (`Step1Setup.lean:1339`) so `G_0 = m`, both left sides vanish.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2090/preflight.py`
```
c0=min(2*c*d,tau)=0.033333  e0=tau0=eps=c'=c0/8=0.004167  C_d=2*3^d=54  2*9^d+1=1459  sqrt=38.197
all rows below hold for every n in [2,3999]; failing rows at n<2: {0: ['F4 54 a^(7/15) <= N^-e0 a^(1/4)/2'], 1: ['F4 54 a^(7/15) <= N^-e0 a^(1/4)/2']}
n=2: L=12 W=7776 lam=2.143e-05 N=812479653347328 a_s=2.1281e-12 a_s^(1/4)=1.2078e-03
  F3 N^e0 a^(1/2) < a^(1/4)                  log-lhs= -13.295 log-rhs=  -6.719 slack=  6.576
  F4 54 a^(7/15) <= N^-e0 a^(1/4)/2          log-lhs=  -8.553 log-rhs=  -7.555 slack=  0.998
  F5 2a^(1/4) <= W^-c1                       log-lhs=  -6.026 log-rhs=  -0.037 slack=  5.988
  F6 1/N <= a^(1/4)/2                        log-lhs= -34.331 log-rhs=  -7.412 slack= 26.919
  F7 a^(1/4) <= 1                            log-lhs=  -6.719 log-rhs=   0.000 slack=  6.719
  F8 W^-3 <= a^(14/15)                       log-lhs= -26.876 log-rhs= -25.084 slack=  1.792
  ratio u=0.00000 a(1-s)/(1-u)<=a^(14/15)    log-lhs= -26.876 log-rhs= -25.084 slack=  1.792
  ratio u=0.03125 a(1-s)/(1-u)<=a^(14/15)    log-lhs= -26.844 log-rhs= -25.084 slack=  1.760
  ratio u=0.06250 a(1-s)/(1-u)<=a^(14/15)    log-lhs= -26.811 log-rhs= -25.084 slack=  1.727
  conStInd a_t^(1/100)<=(1-t)/(1-s)          log-lhs=  -0.268 log-rhs=  -0.065 slack=  0.204
n=2 N=812479653347328  C'=16  netSize=N^16+2 (239 digits)  #net pts=netSize+1 <= N^17: True
mesh 1/netSize=2.773e-239 <= N^-16=2.773e-239 : True
forbidden band [a/2,2a] with a=a_s^(1/4): [6.0390e-04, 2.4156e-03];  N^-1=1.231e-15  N^-1/(a/2)=2.038e-12 (needs <=1)
u=0     k=0  theta-u=0.00e+00  <=1/netSize: True  <=N^-16: True ; u<=1-1/N: True
     a_u^(1/4)=1.2078e-03 >= a_s^(1/4)=1.2078e-03: True
u=1/32  k=643328  theta-u=-1.73e-240  <=1/netSize: True  <=N^-16: True ; u<=1-1/N: True
     a_u^(1/4)=1.2174e-03 >= a_s^(1/4)=1.2078e-03: True
u=1/16  k=286656  theta-u=-3.47e-240  <=1/netSize: True  <=N^-16: True ; u<=1-1/N: True
     a_u^(1/4)=1.2274e-03 >= a_s^(1/4)=1.2078e-03: True
transfer: x_net<a/2 => x_u<a/2+1/N<=a (margin 6.039e-04); x_net>2a => x_u>2a-1/N=2.4156e-03>a
counts: |Idx|=N=812479653347328 ; |Z_L^d|=L^3=1728 <= N: True ; |{(sigma,a)}|,k=2 = 4 L^6 = 11943936 <= N^4: True ; |{p: p1!=p2}| <= N^2
|m(1/2)|=1.000000000000 (k=1 loop -> m: RHS of (lRB1) k=1 is ((1-s)/(1-u))^0 a^0 = 1)
n=2,u=1/16: W^-3 B_{u,K=0}=2.2699e-12  vs  Bctl(u)=W^-3 B_{u,0}=2.2699e-12  ratio=1.0000 (<=1: LocalEntry |G-M|^2 <~ W^-d B_{u,K} <= loop^(2) scale a_u of GiiGEX/GijGEX)
n=2,u=1/16: W^-3 B_{u,K=6}=3.2540e-13  vs  Bctl(u)=W^-3 B_{u,0}=2.2699e-12  ratio=0.1434 (<=1: LocalEntry |G-M|^2 <~ W^-d B_{u,K} <= loop^(2) scale a_u of GiiGEX/GijGEX)
weak-law chain at u: sqrt(2*9^3+1)=38.197 <= 2*3^3=54; GbEXP-derived bound 54*a_s^(7/15)=1.9295e-04 vs threshold a_s^(1/4)/2=6.0390e-04 (N^e0 slack 8.6671e-01)
```

### Verdicts
- `step1TargetV3_holds (d) : Step1TargetV3 d` (with the ported `WeakLawSeq`, `Net`, `Bootstrap`, `step1`): **PASS**. Every row closes with positive slack; all exponents of the net and union bounds are d-free because `|Idx| = N` and `L^d ≤ N`; the only d-dependent constants are `2·3^d`, `2·9^d + 1` and `W^{-d}`. No statement false at d ≥ 3 found.
- Caveats (not blockers): `STGbEXPii`, `STGbEXPij` stay hypotheses (the implication's antecedents); the instance script is numerical at n = 2 and over n ≤ 3999, not a proof for all n.

## (b) Script output — report assembled Sun Oct  4 01:14:28 UTC 2026

Sole files: `RBM3D/Induction/Step1.lean` (new); `RBM3D/Test/Axioms.lean` untouched (no registry line appended, see the registry paragraph).  Every output below is for the HEAD printed first.

```
$ date -u
Sun Oct  4 01:09:43 UTC 2026
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2090 rev-parse --short HEAD; git status --short   # (empty = clean)
7aea0e5
$ git diff --stat main...t/T2090
 RBM3D/Induction/Step1.lean | 750 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 750 insertions(+)
$ lake build RBM3D.Induction.Step1 2>&1 | tail -2        # in /Users/junyin/Lean_proof/RBM3D-wt/T2090
Build completed successfully (3332 jobs).
$ lake build 2>&1 | tail -1     # whole library, root `#assert_rbm_axioms` included (the root does not import the new module; the hub adds it at merge)
Build completed successfully (3833 jobs).
```

`#print axioms` of every named declaration of the file (17: the target, 11 private lemmas of `RBM.Ind`, 5 private helpers of `RBM.Ind.Step1Inst`; script `axioms.py`: scratch copy of the file with one `#print axioms` per declaration):
```
declarations printed: 17; depending on exactly [propext, Classical.choice, Quot.sound]: 17; other lines: 0
'RBM.Ind.step1TargetV3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Registry (ST1-COMMON item 8, DECISIONS §20): this file introduces no `Prop`-valued predicate, so no registry line is appended.  `Step1TargetV3` (registered owed, T2079) is now proved by `step1TargetV3_holds`; its line in `RBM3D/Test/Axioms.lean` can go once this merges.  Pre-check (scratch file outside the repository: `import RBM3D`, `import RBM3D.Induction.Step1`, `#assert_rbm_axioms`):
```
$ lake env lean registry_check.lean 2>&1 | ...
axiom audit: 2947 theorems, 1136 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 80 (borrowed 2, owed 63, structural 15).
registry: 5 borrowed + 92 owed + 37 structural; 54 registered premise(s) carry nothing yet: [...]
exit code: 0
python3: `RBM.Ind.Step1TargetV3` occurs in the "carry nothing yet" list of that output: True
```

Target statement, extracted from the file by script (`extract_target.py`; proof removed) and compared with the ticket (line 7):
```
-- step1TargetV3_holds (Step1.lean:525), statement up to `:=`
theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d
-- the pin it proves (Step1Setup.lean:149-150)
def Step1TargetV3 (d : ℕ) : Prop :=
  STGbEXPii d → STGbEXPij d → STStep1 d
-- ticket line 7 states: theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d
-- identical text in the file (script `==`): True
```

Compiled nonempty instances (script `inst.py`; `d = 3`; the first endpoint instance verbatim, the others by line).  `STGbEXPii 3`, `STGbEXPij 3`, `STKbound`, `STLK`, `STLocalMax` are other gates' pins and stay hypotheses; `STFlow`, `0 ≤ s`, `s ≤ lemT`, `s < t`, `t ≤ lemT`, `STConStInd`, `S1Std` are discharged; windows `[0,1/16]` (positive length), `[1/32,1/16]`; sizes `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `sz1` (`lam = W^{-3/2+1/10}`), `sz2` (`lam = 10`):
```
examples in the file: 17
line | applies | data
 566 | step1TargetV3_holds          | sz0 sInst tInst
 578 | step1TargetV3_holds          | sz1 sInst tInst
 607 | step1TargetV3_holds          | sz2 sInst tInst
 618 | step1TargetV3_holds          | sz0 fun _ => 1 / 32 fun _ => 1 / 16
 651 | s1_card_loops                | sz0
 657 | s1Net_mem                    | sz0 sInst tInst
 660 | s1_exists_close              | sz0 sInst tInst
 666 | s1x_continuousOn             | sz0
 672 | s1_perTime_timeIcc           | sz0 sInst tInst
 682 | s1_wl_seq                    | sz0 sInst tInst fun _ => 1 / 32
 692 | s1_forb                      | sz0 sInst tInst
 699 | s1_boot                      | sz0 sInst tInst
 706 | s1_weakPT                    | sz0 sInst tInst
 710 | s1_loopPT                    | sz0 sInst tInst
 720 | s1_weakPT,s1_loopPT          | sz0 fun _ => 1 / 16
 731 | s1_weakPT,s1_loopPT          | sz0 fun _ => 1 / 2
 745 | step1TargetV3_holds,stStep1_of_target | 

-- the first endpoint instance, verbatim (Step1.lean:566-574):
example (hii : STGbEXPii 3) (hij : STGbEXPij 3)
    (hK : STKbound sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  step1TargetV3_holds 3 hii hij (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 100) (by norm_num) le_rfl (1 / 6) sz0 z0 flow_z0 sInst tInst
    (fun _ => le_rfl) zero_le_lemT (fun n => by simp only [sInst, tInst]; norm_num)
    sixteenth_le_lemT hK hLK hLoc (conStInd_inst (by norm_num))
```

Name clash (CLAUDE.md §5.2): public new names (the theorem and the namespace of the examples) searched as words in `main:RBM3D/`:
```
$ for n in step1TargetV3_holds Step1Inst; do git -C /Users/junyin/Lean_proof/RBM3D grep -n -w -F -e $n main -- RBM3D | wc -l; done   # public new names: the theorem; the instance namespace
step1TargetV3_holds: 0
Step1Inst: 0
$ git -C /Users/junyin/Lean_proof/RBM3D rev-parse --short main
6583ca2
$ git -C /Users/junyin/Lean_proof/RBM3D ls-tree --name-only main RBM3D/Induction/ | grep -c "Induction/Step1.lean"
0
```

Ports (RBM2D `c9a24cf`, `RBM2D/Induction/Step1.lean:967-1515`; RBM1D is not read: its citations in the docstrings (`Hierarchy/Step1.lean`, `Gauss/DominationHolder.lean`, commit `86573b9`) are copied from the RBM2D docstrings of `s1_forb`, `s1Net`, `s1_weakPT`, `s1_loopPT`):
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks rev-parse --short c9a24cf
c9a24cf
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Step1.lean
 RBM2D/Induction/Step1.lean | 259 ++++++++++-----------------------------------
 1 file changed, 56 insertions(+), 203 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h   # HEAD of RBM2D
9e0f275
```

Statement diff against RBM2D (ST1-COMMON item 6), script `literals.py` on the numeric literals of each ported statement (`abbrev` bodies included); residual differences are listed in the narrative:
```
numeric literals of the statements: only in RBM2D (c9a24cf:line) | only in Step1.lean (line)
s1f                 981 | 6          -> s1f                    99 | 2 3
s1a                 978 | -          -> s1a                    95 | -
s1_card_loops      1004 | -          -> s1_card_loops         104 | 2
s1_wl_seq          1027 | 2          -> s1_wl_seq             130 | 0 0
s1Net              1107 | -          -> s1Net                 224 | -
s1Net_mem          1110 | -          -> s1Net_mem             228 | -
s1_exists_close    1116 | -          -> s1_exists_close       235 | -
s1_forb            1139 | 2          -> s1_forb               262 | 0 0
s1x_continuousOn   1246 | -          -> s1x_continuousOn      372 | -
s1_boot            1274 | 2          -> s1_boot               398 | 0 0
s1_weakPT          1311 | 2          -> s1_weakPT             431 | 0 0
s1_loopPT          1334 | 2          -> s1_loopPT             474 | 0 0
step1              1378 | -          -> step1TargetV3_holds   525 | -
```

`d = 2` tokens of `Step1:967-1515` (ST1-COMMON item 2; classes of the portmap row: W2, L2, N2, inv2, d=2, Z2, zd2, 1/5, scal, ex30; script `tokens.py`, regexes in the script, code outside comments):
```
RBM2D Step1.lean:967-1515 at c9a24cf, code outside comments, token counts per declaration:
  s1a{scal:1} s1f{scal:1} s1_card_block2{N2:1} s1_card_loops{W2:1,L2:3,N2:1,Z2:2} s1_wl_seq{N2:2,Z2:2,scal:10} s1_forb{scal:8} s1x_continuousOn{scal:2} s1_card_idx{N2:1,Z2:2} s1_boot{N2:2,scal:1} s1_weakPT{scal:7} s1_loopPT{Z2:2,scal:12} s1chk_range{N2:1} s1chk_condStInd{scal:5,ex30:3}
TOTAL: W2=1 L2=3 N2=8 inv2=0 d=2=0 Z2=8 zd2=0 1/5=0 scal=47 ex30=3
RBM3D/Induction/Step1.lean, code outside comments, same regexes: W2=0 L2=0 N2=0 inv2=0 d=2=0 Z2=0 zd2=0 1/5=0 scal=0 ex30=0
```
Disposition: `L·L ≤ N`, `W^2` -> `L^d ≤ (W L)^d = N` (`s1_card_loops`); `Z2 L` -> `Zd d L`; the `N^2`, `N` counts of `Unit × Block`, `Unit × Block²` (`s1_card_block*`, `s1_card_idx`, `hC` of `s1_boot`) are not needed (`Prec.whp`); `s1Ms`, `scaleM`, `ellT`, `spectralZ`, `loopAbs`, `gMax` -> `s1B` (`sz.Bctl n s`), `zt`, `Lloop`, `STomegaC`; the exponent `30` of `Checks` -> `𝔠_d` (`STConStInd`); `Checks` -> section 5.

DECISIONS §29 evidence (script `s29.py`: line numbers of code outside comments, final file; instances are lines 554-end):
```
code (outside comments) of the module proper = lines 1-553; instances = lines 554-751
(1) `0 ≤ s`: S1Std.hs0 (and hs0 of the pin) used at lines [270, 336, 526, 527, 531, 535, 537]
    `t < 1`: S1Std.ht1 used at lines [270, 422, 448, 537] ; `t ≤ lemT z`: htT at [526, 527, 532, 536]
    `s < t` used only as `s ≤ t`: occurrences of `hst`: [228, 230, 282, 313, 456, 463, 499, 526, 527, 537]
(2) `ℓ`/ilambda/lam in the code: none
(3) `L^d ≤ W^K` form in the code: none ; the count used: L ^ d ≤ size at lines [112]
(4) eventual facts (`filter_upwards` / `∀ᶠ`) at lines [149, 153, 156, 165, 293, 303, 308, 413, 487]
    pointwise facts (`∀ n`, `Eventually.of_forall`) at lines [421, 425, 442, 506]
constants in the code: `2 * (3 : ℝ) ^ d` at [100, 190, 195, 196] ; `2 * ((3 : ℝ) ^ d) ^ 2 + 1` at [193, 200, 205, 207] ; W, L, lam in these lines: none (see (2))
```

Hygiene:
```
$ grep -n -E "sorry|admit|native_decide|^\s*axiom |decide" RBM3D/Induction/Step1.lean; echo "grep exit $?"
grep exit 1
$ git diff --name-only main...t/T2090
RBM3D/Induction/Step1.lean
$ grep -n "^import" RBM3D/Induction/Step1.lean
6:import RBM3D.Induction.Step1Setup
7:import RBM3D.Induction.Continuity
$ wc -l RBM3D/Induction/Step1.lean
     750 RBM3D/Induction/Step1.lean
```

### Narrative
* **File.** `RBM3D/Induction/Step1.lean` (750 lines; imports `Step1Setup`, `Continuity`).  Public: `step1TargetV3_holds` (line 525) only.  Private in `RBM.Ind`: `s1x`,
  `s1a`, `s1f`, `s1_card_loops`, `s1_wl_seq`, `s1Net`, `s1Net_mem`, `s1_exists_close`, `s1_forb`, `s1x_continuousOn`, `s1_boot`, `s1_weakPT`, `s1_perTime_timeIcc`,
  `s1_loopPT`.  Section 5: the instances (17 `example`s, 5 private helpers).  No hypothesis added, no signature changed; nothing of the ticket was false at `d ≥ 3` as
  ported.
* **Assembly** (`Step1.lean:525-538`): `s1_std_of_stFlow` (T2079) gives `S1Std` from `STFlow`, `0 ≤ s ≤ t ≤ lemT z`, `STConStInd`; `s1_h55` gives `S1H55` from `STLK s`,
  `STKbound`; the pins `STGbEXPii`, `STGbEXPij` are specialised to `E = STflowE z`, every `u ∈ [s,t]` (so `0 ≤ u ≤ t ≤ lemT z`) and every `ε₀ > 0` (`hGii`, `hGij`);
  `step1NetLift` (`Continuity.lean:605`, T2062) at `κ`, `τ = ε/2` lifts `s1_loopPT`, `s1_weakPT` to `STStep1Loop`, `STStep1Weak`.
* **Per-time chain.** `s1_wl_seq`: `Prec.whp` of the two pins at `ε₀ = c'` (`s1_F5`), `s1_highProb_of_pt` of `s1_LI` at `k = 2` with `s1_ratio_ev` (`#((σ,a)) ≤ N^4`),
  then `s1_wl_det`: `1(‖G_u-m‖_max ≤ 2a_s^{1/4}) ‖G_u-m‖_max ≺ 2·3^d a_s^{7/15}`.  `s1_forb`: net `s1Net` (`#net ≤ N^{C'+1}`), `PerTimeCalc.Unif.forbidden_region`
  (`PerTimeCalc.lean:680`, `s1_F4`), `gopbound` (`Continuity.lean:527`) at `C = 1`, `s1_F6`.  `s1_boot`: `stepOneBootstrap` (`PerTimeCalc.lean:808`); initial event =
  `Prec.whp` of `STLocalMax` with `s1_F3`; continuity `s1x_continuousOn`.  `s1_weakPT`: `STBctl_mono`.  `s1_loopPT`: `stochDom_of_indicator`, `s1_gMax_le`, `s1_F7`,
  `s1_LI` over `TimeIcc`.
* **`d`-dependence.** The `d`-dependent quantities are `2·3^d` (`s1f`; `s1_F4`), `2·9^d + 1 ≤ (2·3^d)²` (`s1_wl_det`; `h9`, `h6` in `s1_wl_seq`) and `L^d ≤ (W L)^d = N`
  (`s1_card_loops`); the net exponent `C'+1` is the witness of `gopbound` (`2C + 14`, `Continuity.lean:529`) and the mesh bound `N^{-1} ≤ a_s^{1/4}/2` is `s1_F6`; no `W`,
  `L`, `lam` occurs in a constant; `d ≥ 3` is not used.
* **Residual differences from RBM2D** (literal diff above): (i) `hG : GbEXPHypV3 d (κ/2) c τ` (the literal `2`) becomes `hGii`, `hGij` (literals `0 0` = `ε₀ > 0`), window
  instances of the two pins (T2079a); (ii) `s1f`: `6` → `2·3^d`; (iii) `s1_card_loops` takes `2 ≤ N`, supplied eventually (RBM2D derived it from `3 ≤ L`; `N = 1` at `d =
  0`); (iv) `S1Std`, `InitLocal`, `Step1LoopPT/WeakLawPT` are `S1Std sz κ 𝔠 𝔡 τ 𝔠d`, `STLocalMax`, `STStep1LoopPT/WeakPT` (T2079c); (v) `step1` per sequence is the pin
  `Step1TargetV3 d` (T2079a); (vi) dropped: `s1_card_block*` (`:983-1000`), `s1_card_idx` (`:1267`), because `STGiiGEX`, `STGijGEX`, `STLocalMax` are `Prec` (union over
  `(x,y)` inside `P`) and `Prec.whp` gives their events without counting (so two counts of (a), `|Idx| = N`, `|{p₁≠p₂}| ≤ N²`, are not used; `#((σ,a)) ≤ N^4` is); (vii)
  `Checks` → section 5; (viii) new private `s1_perTime_timeIcc` (`Green.perTime_timeIcc_of_forall_seq` without `Unit ×`).
* **Reuse and copies.** Imported, not copied: `s1_std_of_stFlow`, `s1_F3`-`s1_F8`, `s1_h55`, `s1_LI` (`conArg`, T2076), `s1_wl_det`, `s1xM*`, `gopbound`, `step1NetLift`,
  `forbidden_region`, `stepOneBootstrap`, `Prec.whp`, the net lemmas of `Gauss/Domination.lean`.  Copied: `s1Net`, `s1Net_mem`, `s1_exists_close` = `contTime`,
  `contTime_mem`, `cont_exists_close`, `private` in `ContinuityNet.lean` (lines 106, 110, 117), as RBM2D did.  Not used: `stNetLift_holds` (`Continuity.lean:777`; loop
  half only, per-section form; `step1NetLift` covers both halves in the per-time form), `stConArg_holds`, `StochDomAt.of_subset_whp`, `of_subset_compl`.
* **DECISIONS §29** (script above): `0 ≤ s` is used for `t - s ≤ 1` (`hlen`), for `0 ≤ u` at net points and in the `gopbound` event and the pins, and inside the imported
  F6, F8, `s1_h55`, `s1_LI`; `s < t` enters only as `(hst n).le` (line 526), and `STConStInd` (`(1-t)/(1-s) < 1` eventually) forces `s < t` for large `n` anyway; `t ≤
  lemT z` gives `u ≤ lemT z` for the pins and `t < 1`; instances at `s = 0`, `s = 1/32`, windows ending at `1/16 ≤ lemT z_n`; `∀ᶠ` facts are exactly the `filter_upwards`
  lines (F3-F8, `hR`, `N ≥ 2`), the pointwise ones are `∀ n`; no `ℓ`, no `L^d ≤ W^K`; the instances run over `(eq:WO)`: `lam = W^{-3/2+1/10}` (`sz1`, lower end), `lam =
  (2(n+1))^{-6}` (`sz0`, interior), `lam = 10 = 𝔡⁻¹` (`sz2`, upper end; `> L_n` for `n = 0, 1`).
* **Registry.** No new `Prop`-valued predicate; `RBM3D/Test/Axioms.lean` untouched; pre-check exit 0; `Step1TargetV3` now carries nothing (listed in "carry nothing yet"),
  its owed line can go once this merges.


## (c) Verified Mathlib names used (resolved by `resolve.lean` against the environment with the file's `open`s; the file compiles with them)
`Continuous.finset_sup'_apply`, `Filter.Eventually.of_forall`, `Filter.eventually_ge_atTop`, `Finset.univ_nonempty`, `Fintype.card_bool`,
`Fintype.card_fin`, `Fintype.card_fun`, `Fintype.card_prod`, `Nat.mul_le_mul`, `Nat.one_le_pow`,
`Nat.pow_le_pow_left`, `Nat.zero_le`, `Real.one_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`,
`Real.rpow_le_rpow`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_neg_one`, `Real.rpow_neg`,
`Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `ZMod.card`,
`abs_of_nonpos`, `continuousOn_const`, `continuous_const`, `le_min`, `le_of_eq`,
`le_or_gt`, `le_rfl`, `le_trans`, `lt_of_le_of_lt`, `lt_of_lt_of_le`,
`min_eq_left`, `min_eq_right`, `min_le_left`, `min_le_right`, `mul_comm`,
`mul_le_mul_of_nonneg_right`, `mul_nonneg`, `mul_pos`, `mul_pow`, `norm_nonneg`,
`norm_sub_rev`, `one_div_le_one_div_of_le`, `one_div`, `one_le_pow₀`, `one_pos`,
`pow_add`, `pow_le_pow_iff_left₀`, `pow_mul`, `sq_nonneg`, `two_mul`,
`two_ne_zero`, `zero_le_one`.
Tactic syntax used and compiled: `push Not at h` (the form this Mathlib has, as in RBM2D `Step1.lean:1209`); `nlinarith`, `linarith`, `positivity`, `norm_num`, `simp`, `filter_upwards`, `convert`.  Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
* **No new paper-delta candidate.**  The theorem proves the merged pin `STStep1` (paper `(lRB1)` `1_2:1321`, `(Gtmwc)` `1_2:1327`) under the two `lem_GbEXP` parts; the paper omits the proof of Step 1
  (`3_5:65`: "the same as that in [YY_25, Section 5.1] ... Hence, we omit the details"), so the proof route (RBM2D, from [YY_25]) is not paper text.  The statement differences with the paper are the
  signed T2015c, T2015d, T2015e, T2015g (DECISIONS §19) and the cited T2079a-e (`docs/reports/T2079-prove.md` (d)); this file adds none.
* **Observation 1 (registry, for the dispatcher).**  `STBootstrap` (`RBM3D/Test/Axioms.lean:101`) and `STForbidden` (`:103`) are registered owed with the comment "S1-36"; they are not targets of this ticket
  (ticket line 7 pins only `Step1TargetV3`) and are not proved here.  The private `s1_forb`, `s1_boot` have another shape (they take the two `lem_GbEXP` instances and `S1Std`, which carries `STConStInd`;
  `STBootstrap` has no `STConStInd` hypothesis, so `S1Std` is not available for it).  The only theorem that takes `STBootstrap` is `inst_bootstrap` (`Induction/Defs.lean:596`).
* **Observation 2.**  Ticket line 9 names `stNetLift_holds`; the proof uses `step1NetLift` (same file, T2062) because `stNetLift_holds` covers only the loop half (see narrative).  `s1Net`, `s1Net_mem`, `s1_exists_close`
  can go if a later ticket makes `contTime*` of `ContinuityNet.lean` public.
