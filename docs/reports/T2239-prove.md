Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 01:29:14 UTC 2026

Notation: `x_u = 1-u`, `λ = sz.lam n`, `B_u = sz.Bctl n u`, `T_u = STExpTarget`, `N = sz.size n`, `W = sz.W n`, `d = 3` in the instance.
Regime (i) = `STReg5I`: `λ²/L² ≤ 1-t ≤ 1-s ≤ λ²` (`Step5Pins.lean:44`). Targets 1-7 are those of `docs/tickets/T2239.md`.

### (i) Exponent table

| # | quantity | value / form | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | kernel ratio `ρ = (λ²+x_v)/(λ²+x_u)` (T1, `expIntI_ratio_le`) | `≤ 2` | `s≤v≤u<1`, `x_s ≤ g²` give `x_v ≤ x_s ≤ g² ≤ g²+x_u`, so `g²+x_v ≤ 2g² ≤ 2(g²+x_u)` | grid max `1.99997 < 2`; at `(7/8,15/16)`: `18/17 = 1.059` |
| 2 | NAL exponent `n_-1` (`STEKSumRes2NAL`, `n_=2`, `σ₁=σ₂`: `σ 0 = σ (finRotate 2 0)`) | `ρ^1 ≤ 2` | `Prec` bound has `ρ^(n_-1) X` (`Step34Pins.lean:637-650`) | `2 ≤ 4`, absorbed in `4X` |
| 3 | sum-zero exponent `n_` (`STEKSumRes2`, S6-09b input) | `ρ^2 ≤ 4` | `Step34Pins.lean:651-665` | `= 4` exactly; T3 states `4·X` for both cases |
| 4 | `u`-integral (T2, `expIntI_log_ratio`) | `∫_s^u x_v⁻¹ = log(x_s/x_u) ≤ 2 log L` | `x_s ≤ g²`, `x_u ≥ g²/L²`; route `expIntII_log_ratio` (`ExpIntII.lean:71`) at `d:=4`, `g:=gL`: `1-s ≤ (gL)²/L² = g²` (h1), `(gL)²/L⁴ = g²/L² ≤ 1-u` (h2), factor `(4-2) log L` | equality at `x_s/x_u = L²`; grid max of `log(x_s/x_u)/(2 log L)` = 1.0 |
| 5 | rates window | `x_v ≥ x_u ≥ λ²/L² ≥ λ²/L^d` | `expIntII_rates_le_target` needs `λ²/L^d ≤ 1-u`, `λ ≠ 0`, `u<1` (`ExpIntII.lean:159`) | factor `L^{d-2} ≥ 1`; `λ≠0` from `st6_lam_pos` (eventually) |
| 6 | rates constant | `B^{11/5}+B^{5/2} ≤ 3 T_v ≤ 3 T_u` | `B_v ≤ B_u` (`STBctl_mono`), `T` monotone in `B` | script: `W∈{4,10,100,1000}`, `u∈{7/8,9/10,15/16}` all hold, ratio `lhs/3T` between 0.33 and 0.43 |
| 7 | total `log` loss | `4 · 3 · 2 · log L (·2) = 48 log L` (ticket) `≤ N^{τ/2}` | `expIntII_log_eventually` (`ExpIntII.lean:279`, any `C`, `τ>0`, `L ≤ N`, `N→∞`) | eventual; at `szB` (`L=4`): `τ=1` from `n=1`, `τ=1/2` from `n≈100` (script); true constant is `24` |
| 8 | lower control `STEKLow`, `b` | `b = 3` | `X_v ≥ x_v⁻¹B_v^{11/5} ≥ B_v^{11/5} ≥ (c/N)^{11/5}`, `c = (1+λ²)⁻¹`, `B_v ≥ W^{-d}(λ²+1)⁻¹`, `W^d ≤ N`; need `N^{4/5} ≥ c^{-11/5}` | at `szB` (`c=1/2`): need `N ≥ 6.7`, holds for all `n` (`N ≥ 4096`) |
| 9 | window `STEKWin sz s u` | `0≤s`, `s≤u`, `u ≤ 1-λ²/L²`, `u<1`, eventually `W⁻¹ ≤ x_t/x_s ≤ x_u/x_s` | first three from `STReg5I` + `u ≤ t`; `u<1` from `st5_t_lt_one` (`t ≤ lemT z < 1`); last from `(con_st_ind)` + `st_window` (`d𝔠d < 1`, `ScaleFacts3.lean:423`) | `d𝔠d`: `1/100` (ticket) vs `<1`; `u ≤ 1-λ²/L²` is equality at `szB` (`t = 15/16`) |
| 10 | `(con_st_ind)` threshold | `B_t^{𝔠d} ≤ x_t/x_s` | `𝔠d>0`, eventual (limit `B_t → 0`) | at `szB`, `𝔠d = 1/300`: `n ≥ 1.34e30`; `𝔠d = 1/100`: `n ≥ 1.1e10`; `𝔠d = 1/4` (`d𝔠d = 3/4 < 1`): all `n ≥ 0`. The needed consequence `W⁻¹ ≤ 1/2` holds for all `n` (`W ≥ 4`). See finding F2. |
| 11 | bulk | `κ_k = √(2κ)/2`, `κ = 1/10` | `|E| ≤ 2-κ` (`st6_flowE_lt_two`), `st6_mE_im_ge` | `0.2236 ≤ Im m(E) = 0.968` at `|E| ≤ 1/2` |
| 12 | decay hypothesis `STEKDecay` | `STExpDriftDecayConcl` on `[s,t]`, restricted to `[s,u] ⊂ [s,t]` | deterministic `𝒜`: `Whp` of an eventually-sure event | none needed |
| 13 | clause-4 derivative bound of `STMollifierProps` | `‖∂_tϑ‖ ≤ C x_t⁻¹ ℓ_t^{-d m}` (`Step34Pins.lean:515`), no decay | `(deccA0)` of `(𝒫f)∂ϑ` is needed by `(sum_res_2)` (S6-09b) | FINDING T2239a, below |

Finding F2 (instance size). The ticket's `𝔠d = 1/300` makes the eventual clause `(con_st_ind)` hold only for `n ≳ 1.3e30`; it is the limit statement `conStInd_const` (`Step34Pins.lean:825`, any `𝔠d>0`) that discharges it. The window consequence used by the targets (`W⁻¹ ≤ 1/2`) is true from `n = 0`. A non-astronomical alternative at the same `szB` is `𝔠d = 1/4` (`3·(1/4) < 1`). No statement of T2239 constrains `𝔠d ≤ 1/100`.

Finding T2239a (the ticket's required item; mathematics). Verdict: **the route is blocked as stated; falsity of `STExpIntQConcl'` is NOT established.**
- Clause 4 of the merged `STMollifierProps` bounds `‖∂_tϑ_t‖` in sup norm only (`Step34Pins.lean:515`); the paper's `(eq:derv_Theta)` second estimate is also sup-norm only (`paper/tex/3_5_Loop_Hierarchy.tex:1215`); the paper's decaying example `rmk:choosechi` (`:1250`) has decaying `∂_tϑ` but is not what the definition requires. `STExpIntQConcl'` quantifies over every `ϑ` with `STMollifierProps` (check file, `STExpIntQConcl'`).
- `(sum_res_2)` (`3_5:1659`) needs `(deccA0)` of the whole `𝒬`-source; for the term `(𝒫f_v)∂_vϑ_v` of `STExpQsrc` (`Step6Pins.lean:236`) this is exactly decay of `∂_vϑ_v`. Paper line `6:132` ("Applying lem_+Q, … and using (sum_res_2)") does not state it. Without decay only `(sum_res_Ndecay)` is available, with `ρ_N = (1-v)/(1-u) ≤ L²` (`x_v ≤ λ²`, `x_u ≥ λ²/L²`), so `ρ_N^2 ≤ L⁴`, which is not `≺ 1` (`L^d ≤ W^K` only).
- Dispatcher sketch checked arithmetically only (script below, `m=1`): `ϑ' = ϑ₀ + δ sin(t/δ) g`, `g` sum-zero in `a₂`, `‖g‖_∞ = (C/2)L^{-d}`, supported at `|a₂-a₁| = L/2`, `δ = e^{-cdL/2}`, `ϑ₀` with constants `(C/2, c)`. Clause 1 (sum) holds; clause 2 holds since `ℓ_t ≤ L`, `dist ≤ dL/2`; clause 3 holds; clause 4 holds since `x_t⁻¹ ≥ 1`, `ℓ_t^{-d} ≥ L^{-d}`. At the support `|∂_tϑ'| = (C/2)L^{-d} ≥ W^{-D}` for `D = K+1` (`L^d ≤ W^K`), so `(deccA0)` fails once `W^ε ℓ ≤ L/2`. At the fixed `szB` (`L=4`, `W→∞`) this region is empty, so the instance is not affected. That `STExpIntQConcl'` itself is false is not shown (it needs the hypotheses `STExpDuhEqQ` for this `ϑ'`).
- Also: the commutator `[𝒬,Θ]f = Θ((𝒫f)ϑ) - (𝒫Θf)ϑ` needs decay of `Θ^{(2)}` applied to a `ϑ`-decaying tensor; no merged lemma states that `EKFastDecay` is preserved by `STthetaOp`/`ThetaN` (`comm -12 <(grep -rl EKFastDecay RBM3D|sort) <(grep -rl 'STthetaOp\|ThetaN' RBM3D|sort)` prints only `RBM3D/Induction/Step34Pins.lean`, the pin file). The `(𝒫Θf)ϑ` part decays by clause 2 as in `stQop_sub_fastDecay` (`QopNorm.lean:378`).
- Options for S6-09b: (a) integrate by parts in `v` for `∫𝒰_{v,u}(𝒫f_v)∂_vϑ_v dv` within the merged clauses; (b) a successor `STExpIntQConcl''` with a derivative-decay clause, met by `QopAlgebra_mollifier` (`QopAlgebra.lean:345`, explicit `exp(-u_tS)/z`, whose `∂_t` decays) through a strengthened `st6_mollifier_family`; (c) prove decay of `Θ^{(2)}`-images separately for the commutator. Definitions of target 6 are unaffected (fixed by §73 (3)). Dispatcher/REQ before S6-09b is released.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `λ = 1`, `N = (4W)³`), `zB = 1/2 + i/64`, flow `(κ,ε,𝔠,𝔡) = (1/10, 1/10, 1/6, 1/10)`, `s ≡ 7/8`, `t ≡ 15/16`, `𝔠d = 1/300`, kernel `n_ = 2`, `σ₁=σ₂`, `g = 1`. `lemT(zB) ≥ 31/32` (`lemT_zB`, `Step34Pins.lean:789`), `|E| ≤ 1/2`. Hypotheses checked: `0 ≤ s < t ≤ lemT z < 1`; `STReg5I`; `STEKWin sz s u` for `u ∈ [s,t]`; `STConStInd` (limit; F2); ratio `≤ 2`; log integral; rates; bulk; `STEKLow`; `d𝔠d < 1`; `L ≥ 3`. External hypotheses of the instance (`STExpDriftHiConcl`, `STExpDriftDecayConcl`, `LWtermEXP 3`, `STExpIntI' 3`) are other gates' pins and stay hypotheses; their limit computation: `B_t^{𝔠d} → 0` (above, F2), `W → ∞` (`szB_W_tendsto`), `λ²/L² = 1-t` boundary equality is the extreme of regime (i).

Command: `python3 .../scratchpad/T2239/inst.py` (excerpt of the verbatim output):
```
regime(i): lam^2/L^2 = 1/16 <= 1-t = 1/16 : True  1-s = 1/8 <= lam^2: True
lemT(zB) >= 31/32 = 0.96875 >= t = 0.9375 : True  d*cd = 1/100 <1: True
window u<=1-lam^2/L^2 = 15/16 >= t: True
T1 ratio 18/17 1.0588235294117647 <=2: True
T2 int =log(x_s/x_u)= 0.6931471805599453  <= 2 log L = 2.772588722239781 True
(1-t)/(1-s) = 1/2  >= 1/W for W>=4: True
B_t*W^3 = 1.1911764705882353
(con_st_ind) B_t^(1/300)<=1/2 holds for n >= 1343769981412883754782222712828 (2^100 ~ 1267650600228229401496703205376 ); eventual, via limit B_t->0 (conStInd_const)
st_window const (1+10^2)^(1/300)= 1.0155026738331319 <= 4^0.99 = 3.944930817973437
W 4 u 0.875 lhs 0.000141 3T 0.000340 True B<=2/(lam^2W^d): True
W 100 u 0.9375 lhs 9.426e-14 3T 2.686e-13 True B<=2/(lam^2W^d): True
W 1000 u 0.875 lhs 1.637e-20 3T 4.888e-20 True B<=2/(lam^2W^d): True
tau 1.0 n 0 N^(tau/2) 64.0 >=48 log L = 66.54 : False
tau 1.0 n 1 N^(tau/2) 89.44 >=48 log L = 66.54 : True
tau 0.5 n 100 N^(tau/2) 92.11 >=48 log L = 66.54 : True
grid max ratio 1.9999694828875296 <=2; max log(xs/xu)/(2 log L) 1.0 <=1
```
(The grid is `λ² ∈ {1e-4,1e-2,0.5,1,10,100}`, `L ∈ {4,16,256}`, `λ²/L² ≤ x_u ≤ x_v ≤ x_s ≤ λ²`, `x_s < 1`.) Further commands and outputs:
```
$ python3 cd.py        # (con_st_ind) at szB, (1-t)/(1-s) = 1/2
cd=0.25000  d*cd=0.7500  need W=n+4 >= 2.67115  => n >= 0
cd=0.01000  d*cd=0.0300  need W=n+4 >= 1.14725e+10  => n >= 1.14725e+10
cd=0.00333  d*cd=0.0100  need W=n+4 >= 1.34377e+30  => n >= 1.34377e+30
$ python3 t2239a.py    # sizes of the T2239a sketch (arithmetic only), d=3
L 64 W 8 L^d<=W^K: True delta 2.03e-42 c2 True c4 True |d_t theta'| at far support = 3.8147e-06 vs W^-D (D=7) = 4.768e-07 => (deccA0) fails: True
L 16 W 4 L^d<=W^K: True delta 3.78e-11 c2 True c4 True |d_t theta'| at far support = 2.4414e-04 vs W^-D (D=7) = 6.104e-05 => (deccA0) fails: True
L 512 W 8 L^d<=W^K: True delta 0.0 c2 True c4 True |d_t theta'| at far support = 7.4506e-09 vs W^-D (D=10) = 9.3132e-10 => (deccA0) fails: True
$ python3 -c "...sqrt(2*0.1)/2 ..."
kernel kappa chain: sqrt(2*0.1)/2 = 0.2236  <= Im m(E) at |E|<=1/2 >= 0.9682 ; |E|<=2-kappa=1.9
```
The `c2`/`c4` columns restate the construction (`δ` chosen so that clause 2 holds, `ℓ_t ≤ L`), they are not independent evidence; `δ = 0.0` in the third row is float underflow of `e^{-768}`.

### Verdicts (stage 1a)

- Target 1 `expIntI_ratio_le`: PASS (hypotheses `s ≤ v ≤ u < 1`, `1-s ≤ g²` force `g ≠ 0`; the bound `≤ 2` follows by hand, grid max `1.99997`).
- Target 2 `expIntI_log_ratio`: PASS (route `expIntII_log_ratio` at `d := 4`, `g := gL`; both hypotheses h1, h2 follow, constant `(4-2) = 2`).
- Target 3 `expIntI_kernel_unif`: PASS (window, decay restriction, `STEKLow` with `b=3`, bulk, NAL/sum-zero ratio `≤ 2`/`≤ 4`; one lift over `u`).
- Target 4 `expIntI_concl_of_kernel`: PASS (rates `3T_u`, `∫ ≤ 2 log L`, `48 log L ≤ N^{τ/2}` eventually).
- Target 5 `expIntI_same`: PASS.
- Target 6 (definitions, consumer `ST_step6_caseI_of_pins''`, `ST_step6I_of_LW_Int`): PASS for S6-09a; the two definitions are written as given in any case. T2239a does not affect them (it concerns `stExpIntI'_holds`, S6-09b).
- Target 7 (instances): PASS (nondegenerate: `szB`, `(7/8, 15/16)`, `L=4`, `d=3`; F2 on `𝔠d`).
- T2239a: blocker for S6-09b confirmed at the level of the route (no decay of `∂ϑ` in the merged clauses); falsity not established.
- Overall: PASS.

## (b) Script output — Tue Oct  6 02:04:59 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2239`, branch `t/T2239`, commit `3fcac0f` (base `e5b944a`; `main` is now `fd80185`). Files: `RBM3D/Induction/ExpIntI.lean` (new, 901 lines),
  `RBM3D/Test/Axioms.lean` (+4 -2). Scratch scripts (`extract.py`, `gen_check_eq.py`, `consumer_diff.sh`, `clash.sh`, `count_lists.py`, `where.lean`, `precheck.lean`, `axioms_check.lean`) are in
  `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2239/`.
### Build
```
$ lake build RBM3D.Induction.ExpIntI                  # committed tree, started Tue Oct  6 02:02:03 UTC 2026
Build completed successfully (3873 jobs).
$ grep -c "ExpIntI.lean" <that build log>             # warnings or errors of the new file
0
$ lake env lean RBM3D/Induction/ExpIntI.lean; echo exit=$?   # started Tue Oct  6 02:02:04 UTC 2026; no output lines
exit=0
$ lake build     # full library, temporary uncommitted `import RBM3D.Induction.ExpIntI` in RBM3D.lean (removed again), Tue Oct  6 02:02:23 UTC 2026 to Tue Oct  6 02:03:01 UTC 2026
RBM3D.lean:282:0: axiom audit: 6949 theorems, 2342 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 143 owed + 89 structural + 7 refuted; 113 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4042 jobs).
$ git diff -- RBM3D.lean | wc -l       # after removing the temporary import
0
```
### Axioms (17 public declarations of the file: 2 definitions, 7 theorems, 8 instances)
```
$ lake env lean axioms_check.lean | sed "s/.*depends on axioms: //" | sort | uniq -c        # started Tue Oct  6 02:02:09 UTC 2026
  17 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Induction/ExpIntI.lean ; echo rc=$?
rc=1
```
### Target statements, extracted from the file by script (`extract.py full|stmt`, whitespace collapsed; file lines 56, 71, 80, 90, 253, 356, 465, 573, 660)
```
def STExpIntQConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ), (∀ᶠ n in atTop, STMollifierProps (d := d)
  (sz.lam n) C c (ϑ n)) → STExpDuhEqQ sz E s t ϑ → ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) → Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖RBM.Ind.Ugen d
  (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p) → Prec sz (U := STIdx2P sz
  STSigMixed s t) (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))
def STExpIntI' (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl' sz E s t →
  STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)
theorem expIntI_ratio_le {g s v u : ℝ} (hsv : s ≤ v) (hvu : v ≤ u) (hu : u < 1) (hs : 1 - s ≤ g ^ 2) : (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|) ≤ 2
theorem expIntI_log_ratio {L : ℕ} {g s u : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hu : u < 1) (h1 : 1 - s ≤ g ^ 2) (h2 : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) : ∫ v in s..u, (1 - v)⁻¹ ≤ 2 * Real.log (L : ℝ)
theorem expIntI_kernel_unif {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (_hε : 0 < ε) (_h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow
  sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (σ : Fin 2 → Bool) (𝒜 : ∀ n : ℕ, ℝ
  → (Fin 2 → Zd d (sz.L n)) → ℂ) (X : ℕ → ℝ → ℝ) (hcase : σ 0 = σ 1 ∨ ∀ n v, EKSumZero (𝒜 n v)) (hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → EKFastDecay
  (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v)) (hX0 : ∀ n v, 0 ≤ X n v) (hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v) (hbd : ∀ τ : ℝ, 0
  < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v) (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
  ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ) (𝒜 n v)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * X n v) :=
theorem expIntI_concl_of_kernel {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) (hd : 3 ≤ d) {E s t : ℕ → ℝ} (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hduh :
  STExpDuhEq sz E s t) (P : (Fin 2 → Bool) → Prop) (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) → ∀ σ : Fin 2 → Bool, P σ → ‖RBM.Ind.Ugen d
  (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
  STExpIntConcl sz ∅ P E s t
theorem expIntI_same {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠
  𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hduh : STExpDuhEq sz (STflowE z) s t) (hdr
  : STExpDriftHiConcl sz (STflowE z) s t) (hdd : STExpDriftDecayConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigSame (STflowE z) s t
theorem ST_step6_caseI_of_pins'' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d)
  (hWd : STExpWardI' d) (hIni : STExpIniI' d) (hInt : STExpIntI' d) : STStep6I d
theorem ST_step6I_of_LW_Int (d : ℕ) (hLW : LWtermEXP d) (hInt : STExpIntI' d) : STStep6I d :=
```
### Compiled nonempty instances (namespace `RBM.Gauss.Step6Inst`; full text of the first four, statements of the last four; file lines 680, 687, 701, 707, 735, 838, 871, 884)
```
theorem inst_skeleton6I'' (hLW : LWtermEXP 3) (hInt : STExpIntI' 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) := inst_step6I
  (ST_step6I_of_LW_Int 3 hLW hInt)
theorem inst_expIntI_same (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) (hdd : STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
  STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) := expIntI_same (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num
  : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
  szB_reg5I (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) (st6_duhEq_of_pin szB (stExpDuhamelZ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
  (fun _ => by norm_num) (szB_flow_ht (by norm_num))) hdr hdd
theorem inst_expIntI_log_ratio : ∫ v in (7 / 8 : ℝ)..(15 / 16), (1 - v)⁻¹ ≤ 2 * Real.log (((szB.L 0 : ℕ) : ℝ)) := expIntI_log_ratio (L := szB.L 0) (g := szB.lam 0) (by simp [szB]) (by
  norm_num) (by norm_num) (by simp [szB]; norm_num) (by simp [szB]; norm_num)
theorem inst_expIntI_ratio_le : ((szB.lam 0) ^ 2 + |1 - (7 / 8 : ℝ)|) / ((szB.lam 0) ^ 2 + |1 - (15 / 16 : ℝ)|) ≤ 2 := expIntI_ratio_le (g := szB.lam 0) (s := 7 / 8) (v := 7 / 8) (u := 15 /
  16) le_rfl (by norm_num) (by norm_num) (by simp [szB]; norm_num)
theorem inst_expIntI_kernel_unif (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) → ‖RBM.Ind.Ugen 3
  (szB.L n) (szB.lam n) (STflowE zB n) (fun _ => true) v (u : ℝ) (fun a : Fin 2 → Zd 3 (szB.L n) => if a 0 = a 1 then (1 : ℂ) else 0)‖ ≤ ((szB.size n : ℕ) : ℝ) ^ τ * (4 * (fun (_ : ℕ) (_ :
  ℝ) => (1 : ℝ)) n v)
theorem inst_expIntI_kernel_unif_sumzero (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) →
  ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) ![true, false] v (u : ℝ) (fun a : Fin 2 → Zd 3 (szB.L n) => (if a 1 = a 0 then (1 : ℂ) else 0) - (if a 1 = a 0 + (Pi.single 0 1 : Zd 3
  (szB.L n)) then (1 : ℂ) else 0))‖ ≤ ((szB.size n : ℕ) : ℝ) ^ τ * (4 * (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) n v)
theorem inst_expIntI_tensors_ne_zero : (fun a : Fin 2 → Zd 3 (szB.L 0) => if a 0 = a 1 then (1 : ℂ) else 0) 0 ≠ 0 ∧ (fun a : Fin 2 → Zd 3 (szB.L 0) => (if a 1 = a 0 then (1 : ℂ) else 0) -
  (if a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L 0)) then (1 : ℂ) else 0)) 0 ≠ 0
theorem inst_expIntI_concl_of_kernel (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) → ∀ σ : Fin 2 →
  Bool, σ 0 = σ 1 → ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) σ v (u : ℝ) (fun b => szB.STExpDrift n (STflowE zB n) v σ b)‖ ≤ ((szB.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (szB.Bctl n
  v ^ (11 / 5 : ℝ) + szB.Bctl n v ^ (5 / 2 : ℝ)))) : STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
```
### Registry pre-check (DECISIONS §20 (2))
```
$ lake env lean precheck.lean    # import RBM3D; import RBM3D.Induction.ExpIntI; #assert_rbm_axioms (temporary root import in place); started Tue Oct  6 02:03:01 UTC 2026, after the full build
exit=0
axiom audit: 6949 theorems, 2342 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 143 owed + 89 structural + 7 refuted; 113 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ python3 count_lists.py    # entries of the four lists of Axioms.lean at the base e5b944a and at the branch
owedProps base 142 branch 143 added ["RBM.Gauss.Sizes.STExpIntI'"] removed []
structuralProps base 88 branch 89 added ["RBM.Gauss.Sizes.STExpIntQConcl'"] removed []
(borrowedProps 2 -> 2, refutedProps 7 -> 7)
```
### Check-file equality, consumer diff, name clash, diff
```
$ lake env lean check_eq.lean    # check imports + `import RBM3D.Induction.ExpIntI` + sections 1-2 + 7 `example : T2239Check.X := @X`, 2 `rfl` (`STExpIntI'`, `@STExpIntQConcl'`), 3 section-3 `example : <stmt> := @inst_*`; started Tue Oct  6 02:02:13 UTC 2026
examples: 12; 0 error lines; exit=0
$ consumer_diff.sh    # ExpIniI.lean `ST_step6_caseI_of_pins'` (82 lines) against ExpIntI.lean `ST_step6_caseI_of_pins''`
old: ExpIniI.lean:1127-1208; new: ExpIntI.lean:573-654
1,3c1,3
< theorem ST_step6_caseI_of_pins' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
<     (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
<     (hIni : STExpIniI' d) (hInt : STExpIntI d) : STStep6I d := by
---
> theorem ST_step6_caseI_of_pins'' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
>     (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI' d)
>     (hIni : STExpIniI' d) (hInt : STExpIntI' d) : STStep6I d := by
53c53
<   have hmainQ := hint.2 C c' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
---
>   have hmainQ := hint.2 C c' hC hc' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
55c55
<   have hw := (hward C c' ϑ hϑ).1
---
>   have hw := (hward C c' hC hc' ϑ hϑ).1
diff lines (changed hunks): 3
$ clash.sh    # grep -rnwF of the 27 new names (17 public, 10 private) over RBM3D/, RBM3D.lean, docs/tickets; started Tue Oct  6 02:03:48 UTC 2026
names checked: 27 (17 public, 10 private), hits outside ExpIntI.lean, Test/Axioms.lean, T2239 files: 0
hits in Test/Axioms.lean (this ticket's registry lines, listed by grep -n): 6
236 237 238 334 
$ git diff --stat main...t/T2239
 RBM3D/Induction/ExpIntI.lean | 901 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   6 +-
 2 files changed, 905 insertions(+), 2 deletions(-)
$ git diff main t/T2239 -- RBM3D/Induction/{Step6Pins,Step6Kit,ExpIniI,ExpWardI,ExpIntII}.lean RBM3D/Evolution/Prec.lean | wc -l
0
$ git merge-tree --write-tree main t/T2239; echo rc=$?
210a5bf25c807c81ca373e7862041d6c1a64e224
rc=0
```
Ports: none from RBM1D or RBM2D (no file of either was read, no `git diff --stat` to give). RBM3D-internal copies: `expIntI_window` (`ExpIniI.lean:513-521`), `expIntI_lift` (`ExpIntII.lean:357-387`),
  `expIntI_drift_pi` (`ExpIntII.lean:323-352`), `expIntI_drift_integral_le` / `expIntI_concl_of_kernel` (adapted from `ExpIntII.lean:202-268`, `:472-529`), the consumer (`ExpIniI.lean:1127-1208`), `inst_expIntI_diag_decay` (`ExpIniI.lean:1245-1259`).

**Narrative.**
1. Result: targets 1-6 are proved and the three instances of target 7 compile; instances for targets 1, 3 (NAL and sum-zero branch) and 4 are added, so every public theorem of the file has one (8 `inst_*` theorems in all).
   Each statement equals its check-file statement (12 examples, 0 errors, `rfl` for the two definitions). The only existing file touched is `Test/Axioms.lean` (diff stat above; the six merged files named in the ticket have 0
   diff lines); no hypothesis added or removed, no pin changed, no obstruction. `ExpIntI.lean` has 901 lines (ticket estimate 750 / 950 / 1200).
2. Kernel (target 3): for each time sequence `u ∈ [s,t]` the merged `stek_sumRes2NAL_holds` (`σ 0 = σ 1`, i.e. `σ 0 = σ (finRotate 2 0)`) or `stek_sumRes2_holds` (sum-zero family), `n_ = 2`,
   `m n = mE (STflowE z n)`, `κ' = √(2κ)/2`, window `STEKWin sz s u` (private `expIntI_window`, copy of `expIniI_window`), is applied to the deterministic `𝒜_v`: `STEKDecay` (restricted from `[s,t]`
   to `[s,u]`) and `STEKLow` by `HighProbAt.of_eventually_univ`, `Prec ‖𝒜‖ X` by `st6_prec_det_iff`. The output factor is `ρ^{n_-1} = ρ ≤ 2` (NAL) or `ρ^{n_} = ρ² ≤ 4` (sum-zero) with
   `ρ = (λ² + 1-v)/(λ² + 1-u) ≤ 2` (`expIntI_ratio_le`, `1 - s ≤ λ²` is `(hR n).2`); both are `≤ 4`. The lift over `u` is `expIntI_lift` (copy of `expIntII_lift`), deterministic on both sides.
3. Assembly (target 4): regime-(i) copy of `STExpIntConcl_of_kernel` with `A = ∅` (`st5_zeroModeSet_empty`): `∫_s^u (1-v)⁻¹ ≤ 2 log L` (target 2), rates `B^{11/5} + B^{5/2} ≤ 3 T_u` by
   `expIntII_rates_le_target` (its window `λ²/L^d ≤ 1-u` follows from `λ²/L² ≤ 1-t` and `L^d ≥ L²`), `λ ≠ 0` from `0 < 1-u ≤ 1-s ≤ λ²`, and `6 log L ≤ N^{τ/2}` eventually (`expIntII_log_eventually`, `C = 3·2`).
4. `expIntI_same`: control `X_v = |1-v|⁻¹ (B_v^{11/5} + B_v^{5/2})` (absolute value, so that `0 ≤ X n v` for every `v`, as target 3 requires); `‖D_v‖ ≤ N^τ X_v` from `STExpDriftHiConcl`
   (`expIntI_drift_pi`, copy of `expIntII_drift_pi`); decay of `D_v^σ` from `STExpDriftDecayConcl` through `HighProbAt.nonempty` (a `Whp` event that does not depend on `ω` is eventually nonempty);
   lower control `X ≥ N^{-3}` from `N⁻¹ ≤ B` (`expAvg_Bctl_ge`, merged, `ExpAvg.lean:604`, not in the check file's list); the factor `4` is absorbed by `4 ≤ N^{τ/2}` eventually.
   (a) row 7 counts `48 log L`; this route needs `6 log L ≤ N^{τ/2}` and, separately, `4 ≤ N^{τ/2}`, both implied by (a)'s inequality: no correction, so no (a′).
5. Consumer: `ST_step6_caseI_of_pins''` is `ST_step6_caseI_of_pins'` with three changed hunks (the name and the binder types `hWd : STExpWardI' d`, `hInt : STExpIntI' d`; `hint.2 C c' hC hc' …`;
   `(hward C c' hC hc' …).1`), the O2 check above; `hward := H₃ …` and `hint := H₅ …` are unchanged and typecheck against the primed premise. `ST_step6I_of_LW_Int` applies it to the proved pins.
6. Instances at `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `λ = 1`), `zB`, `(s,t) = (7/8, 15/16)`, `𝔠_d = 1/300` by `conStInd_const` (the limit statement, (a) F2). Open hypotheses: `LWtermEXP 3`, `STExpIntI' 3`
   (`inst_skeleton6I''`); `STExpDriftHiConcl`, `STExpDriftDecayConcl` (`inst_expIntI_same`); `hker` (`inst_expIntI_concl_of_kernel`). The kernel instances use the tensor `1_{a₁=a₂}` (`σ = (+,+)`)
   and the sum-zero dipole `1_{a₂=a₁} - 1_{a₂=a₁+e}` (`σ = (+,-)`, so the `(sum_res_2)` branch is the one used), both with `‖𝒜‖ ≤ 1`, value `1` at `a = 0` (`inst_expIntI_tensors_ne_zero`) and `X ≡ 1`;
   sum-zero, decay, control and bound are proved there.
   `hker` of `inst_expIntI_concl_of_kernel` is written with `σ 0 = σ 1` (defeq to `STSigSame σ`) because `scanPremises` collects every `Prop` constant occurring in a hypothesis type, so `STSigSame` would be reported unregistered.
7. Registry: `STExpIntI'` owed (142 → 143), `STExpIntQConcl'` structural (88 → 89), the comments of `STExpIntI`, `STExpIniI` rewritten as the ticket says; the pre-check forced no other line. The root import was
   temporary and is removed (`git diff -- RBM3D.lean` empty); the hub adds it at merge.
8. §29 / §45 O2: (1) `0 ≤ s ≤ v ≤ u ≤ t < 1` (`st5_t_lt_one`); (2) regime (i): window `u ≤ t ≤ 1 - λ²/L²` (`(hR n).1`), ratio from `(hR n).2`, rates `λ²/L^d ≤ λ²/L² ≤ 1-u`, log `x_s/x_u ≤ L²`; (3) `L^d ≤ W^K`
   is not used here (it is inside the merged pins); (4) hypotheses `∀ n`, conclusions eventual, `(con_st_ind)` enters only through the eventual clause of `STEKWin` (`st_window`, `d 𝔠_d < 1`); (5) one lift over `u`,
   deterministic both sides; (6) `λ_n ≠ 0` derived inside `expIntI_drift_integral_le`, `N → ∞` from `hflow.1.2.2.1`, `|E_n| < 2` from `st6_flowE_lt_two`; (7) scale `N = sz.size n`, `log L ≺ 1`.
   Mollifier constants occur only in the two definitions and the consumer.
9. T2239a, preflight verdict of (a) (not re-derived here): the route of S6-09b is blocked as stated (no decay of `∂ϑ` in the merged clauses); falsity of `STExpIntQConcl'` is not established. Nothing in this file depends on it; the
   definitions of target 6 are written as given.

## (c) Verified names used (all resolved by the compile; `where.lean` prints module and first line of the declaration's range; names shared with `ExpIntII.lean` are as in T2233 (c))
- Mathlib: `Real.one_le_rpow` Analysis.SpecialFunctions.Pow.Real:678, `Real.one_lt_rpow` :674, `Real.inv_rpow` :485, `Real.rpow_neg` :259, `Real.rpow_le_rpow_of_exponent_le` :616, `Real.rpow_le_rpow` :549,
  `Real.rpow_add` :208, `Real.rpow_nonneg` :163, `Real.rpow_pos_of_pos` :116, `Real.log_nonneg` Analysis.SpecialFunctions.Log.Basic:212, `tendsto_rpow_atTop` Analysis.SpecialFunctions.Pow.Asymptotics:37,
  `pow_le_pow_right₀` Algebra.Order.GroupWithZero.Basic:500, `one_le_inv₀` :896, `le_mul_of_one_le_left` :364, `le_mul_of_one_le_right` :370, `div_le_div_of_nonneg_left` :1270,
  `div_le_div_of_nonneg_right` :1193, `div_le_iff₀` :1132, `inv_nonneg` :846, `abs_of_pos` Algebra.Order.Group.Unbundled.Abs:91, `abs_pos` :227, `half_pos` Algebra.Order.Field.Basic:112,
  `Filter.eventually_all` Order.Filter.Finite:246, `Filter.not_eventually` Order.Filter.Basic:828, `Filter.Frequently.and_eventually` :793, `Filter.Frequently.exists` :802, `Filter.Eventually.of_forall` :663,
  `intervalIntegral.norm_integral_le_of_norm_le` MeasureTheory.Integral.IntervalIntegral.Basic:758, `intervalIntegral.integral_const_mul` :818, `ContinuousOn.intervalIntegrable` :504,
  `ContinuousOn.inv₀` Topology.Algebra.GroupWithZero:129, `ContinuousOn.mul` Topology.Algebra.Monoid.Defs:105, `Set.uIcc_of_le` Order.Interval.Set.UnorderedInterval:76, `norm_add_le`
  Analysis.Normed.Group.Basic:99, `norm_le_pi_norm` :346 and `pi_norm_le_iff_of_nonneg` :318 (Analysis.Normed.Group.Constructions), `Finset.sum_eq_single` Algebra.BigOperators.Group.Finset.Basic:354,
  `Finset.sum_sub_distrib` Algebra.BigOperators.Group.Finset.Defs:678, `Finset.mem_filter` Data.Finset.Filter:126, `Classical.choose_spec` Init.Classical:32, `eq_true` / `eq_false` Init.SimpLemmas:19 / :25.
- `MeasureTheory.IsProbabilityMeasure.measure_univ` MeasureTheory.Measure.Typeclasses.Probability:65, written `measure_univ` under `open MeasureTheory`.
- RBM3D (merged): `RBM.Gauss.HighProbAt.nonempty` Defs.StochDomAt:609, `HighProbAt.of_eventually_univ` :596, `Sizes.expAvg_Bctl_ge` Induction.ExpAvg:602 (docstring start; theorem line 604), `expIntII_log_ratio`
  Induction.ExpIntII:70, `expIntII_rates_le_target` :157, `expIntII_log_eventually` :278, `stek_sumRes2NAL_holds` Evolution.Prec:238, `stek_sumRes2_holds` :389, `st_window` Induction.ScaleFacts3:417,
  `scaleFacts3_W_tendsto` :408, `st6_prec_det_iff` Induction.Step6Kit:79, `st6_target_nonneg` :492, `st5_t_lt_one` Induction.Step5Kit:191, `st5_zeroModeSet_empty` :96, `STBctl_mono` Induction.ScaleFacts:73,
  `STBctl_pos` :63, `RBM.zdistD_neg` Defs.Lattice:103, `RBM.one_le_ellT` Defs.Params:39, `RBM.ellT_pos` :44.
- Verified absent: the root name `measure_univ` (unknown without `open MeasureTheory`). Deprecated (compile warning in a scratch file, not used in the file): `if_pos`, `if_neg`.

## (d) Open issues and paper-delta candidates
- `T2239a` (preflight finding (iv); the verdict of (a), not re-derived here): the route of S6-09b is blocked as stated, because the merged clause 4 of `STMollifierProps` (`Step34Pins.lean:515`) bounds `‖∂_tϑ‖` without decay while
  `(sum_res_2)` needs `(deccA0)` of `(𝒫f_v)∂_vϑ_v`; falsity of `STExpIntQConcl'` is not established. Nothing in this file depends on it. Options named in (a): integration by parts within the merged clauses,
  a successor `STExpIntQConcl''` with a derivative-decay clause, or other; dispatcher / REQ before S6-09b is released.
- `T2239b` (ticket candidate (a), `6:97`, `6:104`): regime (i), `σ₁ = σ₂`, made explicit: `(sum_res_2_NAL)` at `n = 2` with ratio `(λ² + 1-v)/(λ² + 1-u) ≤ 2` (`1 - s ≤ λ²`), `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u))
  ≤ 2 log L` (`1-u ≥ λ²/L²`), drift rates `B^{11/5} + B^{5/2} ≤ 3 T_u` (`1-u ≥ λ²/L^d`), kernel loss `4` absorbed by `4 ≤ N^{τ/2}`; the `(sum_res_2)` branch has ratio² `≤ 4`.
- No step needed a hypothesis that a statement lacks (no `T2239c…`). Open: none for this file.
- Merge note for the hub (§20 (3)): `git merge-tree --write-tree main t/T2239` is clean (rc 0, `main` at `fd80185`). `Axioms.lean` hunks on the branch: `:236-238` (comments of `STExpIntI`, `STExpIniI` and the new owed
  line `STExpIntI'`) and `:334` (structural `STExpIntQConcl'`, after `STExpWardIConcl'`, before `locBad1`); the base already contains the merges of T2234 and T2235. Root import: `import RBM3D.Induction.ExpIntI` after the last `import` line of `RBM3D.lean`.
- Follow-ups, not done (not targets): S6-09b proves `stExpIntI'_holds` (first conjunct `expIntI_same`; the `(sum_res_2)` branch of `expIntI_kernel_unif` is its input for the `𝒬` part) and then
  `stStep6I_of_LW d h := ST_step6I_of_LW_Int d h (stExpIntI'_holds d)`; `inst_skeleton6I''` then leaves only `LWtermEXP 3` open.
