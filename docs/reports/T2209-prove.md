Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:16:40 UTC 2026
Notation: `T_{u,D}(r)=α_u e^{-√r}+W^{-D}`, `α_u=(W^d(1-u))^{-2}`, `ρ_j=(1-u_j)/(1-u_k)`, `ℓ*=(log W)^{3/2}`, `N=(WL)^d`; regime (iii): `lam² ≤ 1-u`.
**Finding F2 (the level of `D`; truth of targets 1-7 unaffected, closure of S5-11 affected).** The ticket route (one level `D′` for all times: stop at `J♯_{D′}`, S5-09 at `D′`, targets 2/7 at `D′`, then `ρ²W^{-D′} ≤ W^{-D}`)
does not close the stopped loop. Floor of the LK×LK drift (`p_j = N^τ J² W^{-d}(1-u_j)^{-2}`): `Σ c_j p_j ρ_j² W^{-D′} = N^τ J² W^{-d}(1-t′)^{-2} W^{-D′}`, but the stopped ratio needs `≤ W^ε·W^{-D′}`.
At `1-t′ = lam² = W^{-d+2𝔡}` (WO boundary, allowed by regime (iii)) the excess is `W^{ε+d-4𝔡}`: closes iff `𝔡 ≥ (d+ε)/4` (script b). The output is a bound at level `D′-(2d+1)`, not at the stopping level.
Repair (algebra + script b): time-dependent level `D_u := D* + 2 log_W(1-u)`, `D* := max(D,D₀)+2d+1`. Then `W^{-D_u}=(1-u)^{-2}W^{-D*}`, `T_{u,D_u}=(1-u)^{-2}ψ(r)` with `ψ=W^{-2d}e^{-√r}+W^{-D*}`, `ρ_j² W^{-D_{u_j}} = (1-u_k)^{-2}W^{-D*}` exactly,
`T_{u_k,D_{u_j}} ≤ T_{u_k,D_{u_k}}` (floors `(1-u_j)^{-2} ≤ (1-u_k)^{-2}`). Stop on `J♯` at `(u,D_u)` (S5-09 `Jsharp` takes `D` per call); descend at the end by target 1 since `D_u ≥ D` (`1-u ≥ lam² ≥ W^{-d}`).
Needs: **target 2′** (below, replaces pin 2; pin 2 is `D_j ≡ D`), targets 4/7 at `D=D_{u_j}` per time, target 5 only at the fixed `D*`.

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 0 | `D₀` | `2/𝔠+12d` (48 at sz0) | `(L^dW^{6d})² ≤ W^{D₀}`: `L^d ≤ N ≤ W^{1/𝔠}` (Bandwidth), `W ≥ 1` | equality in `N ≤ W^{1/𝔠}` |
| 1 | level `D_u`, `D*` | `D*+2log_W(1-u)`, `D*=max(D,D₀)+2d+1` | `D_u ≥ max(D,D₀)+1+4𝔡` (WO: `1-u ≥ W^{-d+2𝔡}`), `D_u ≤ D*` | `1+4𝔡` |
| 2 | `ρ` | `≤ lam^{-2} ≤ W^{d-2𝔡}` | `ρ_j² W^{-D_{u_j}} = (1-u_k)^{-2}W^{-D*}` | exact identity |
| 3 | `ε` | `0<ε<min(1/2,𝔡/4)` | `W^ε ≤ W^{1/2}` (hJstW of goodDet); `2ε-𝔡/2<0`; `Admissible ⇒ 𝔡 ≤ d/2` (WO with `W→∞`) | `1/2-ε`, `𝔡/4-ε` |
| 4 | `τ` (target 6) | `𝔠ε/2` | `N^τ ≤ W^{τ/𝔠} = W^{ε/2}` (Bandwidth) | exact |
| 5 | `τ′` | `min(τ_loss/24, 1/(2D*))` | `D_uτ′ ≤ 1/2` (QW), `6τ′ ≤ τ_loss/4` (loss), `D_u ≤ D*` | 0 by definition |
| 6 | `(lam²W^d)^{-1/4}` | `≤ W^{-𝔡/2}` | WO: `lam²W^d ≥ W^{2𝔡} ≥ 1` | `W^{-(𝔡/2-2ε)}` on `W^{2ε}·` |
| 7 | closure | `W^{ε/2}C(2+log W) < W^ε` | `C(2+log W) < W^{ε/2}` eventually | thresholds in (ii)a |
| 8 | Riemann sums | constants `1`, `2`, `log` | left sums of increasing `(1-u)^{-2,-3/2,-1}`: `(b-a)(1-a)^{-2} ≤ (1-b)^{-1}-(1-a)^{-1}`, `(b-a)(1-a)^{-3/2} ≤ 2((1-b)^{-1/2}-(1-a)^{-1/2})`, `1-1/x ≤ log x` | telescopes exactly |
| 9 | `C` of target 2 | `(3e^{(4d+1)/4})² = 5986.27` at `d=3` (merged `stTailtoTail_holds`) | uniform in `s,t,L,W,g,D` | — |
| 10 | weight `c` (target 7) | `1/(4d+1)`; `C₇=18e^{8d+2}=3.5e12` at `d=3` | `d(e^c-1) ≤ 1/4` (0.2399 at `d=3`); `2√r ≤ c r+1/c`; `Σ|K|e^{2√|a-b|} ≤ 3e^{4d+1}ρ` | — |
| 11 | far range | `ℓ*/2-1 ≥ ℓ*/8` | `ℓ* ≥ 8` from `log W ≥ 4` | `3ℓ*/8-1 ≥ 2` |
| 12 | `Y`, `D₂` | `Y` crude bound of `STeeM` (`m N (16N)^{2m+2}`, `m=2`, from `η_u ≥ 1/(16N)`, `difRep2_norm_STeeM_le_N`); `D₂` free | far term `4YL^dρ³W^{-D₂}`: S5-11 chooses `D₂` with `YL^dρ³W^{-D₂} ≤ W^{-2D*}` | with ONE exponent `D` (ticket) `D ≥ (C_Y+C)/𝔠` is not implied by `D₀=2/𝔠+12d` |

### Premises of `lemDecCalEPrec_goodDet` at `Jst≡W^ε`, level `D_u`, `τ′` (row 0 of the ticket; all read from the signature)
`1 ≤ W^ε`; `W^ε ≤ W^{1/2}`; `hQW`: `lemDecCalEPrec_QW` with `D:=D_u`, `D_uτ′ ≤ D*τ′ ≤ 1/2`; `hfl`: row 0 and `D_u ≥ D₀`; `|E|<2`, `0 ≤ u<1`; `hlam, hlamu, hA, hlog`: WO and `W → ∞`; `hkell`: `lemDecCalEPrec_kell` takes any exponent, use `D_u`;
`hloss`: `lemDecCalEPrec_lossWG_eventually` with `6τ′ ≤ τ/4`. Premise 1 of the good event from the stopping condition (target 4); premises 2-7 from target 5 at `D*` (events 2-7 do not contain `D`). No failed line.

### (ii) One nondegenerate instance (numbers) and the scripts
Data: `d=3`, `sz0` at `n=0`: `L=4, W=32, lam=1/64, N=2097152`, `𝔠=1/6`, `𝔡=1/10` (also `𝔡=3/10`: WO holds with equality), `ε=1/50`, `D=1` ⇒ `D₀=48`, `D*=55`, `τ=1/600`, `s=0`, `t=1/16` (`lam²=1/4096 ≤ 1-t=15/16`).
(a) `cd <scratchpad>/T2209 && python3 inst_a.py | grep -v "^closure: d=0.1, eps=0.02, tau=0.00167, C=6000"`
```
n=0: L,W,lam,N = 4 32 0.015625 2097152
Admissible(c=1/6,d=1/10), lam^2<=15/16, 1<=lam^2 W^d for m<=1e6: violations = 0
D0 = 48.0  D' = 48.0  D*=max(D,D0)+2d+1 = 55.0
floor (L^d W^{6d})^2 <= W^{D0} for m<=1e6: violations = 0
n=0: rho_max=lam^-2 = 4096.0  <= W^d = 32768 : True
n=0: log_W(rho^2 W^-D') = -43.2  <= -D = -1
T1: T_{1/16,48}(3) = 1.8747245610318103e-10  <= T_{1/16,1}(3) = 0.031250000187472454 : True
eps = 0.02  tau6 = 0.0016666666666666666  tau' = 6.944444444444444e-05
N^tau' = 1.0010113507088927  <= W^(1/2) = 5.656854249492381 : True ; W^eps = 1.0717734625362931
closure: d=0.1, eps=0.02, tau=0.00167, C=1.0: holds for log(2m) >= 87.8  (W >= e^439)
closure: d=0.3, eps=0.07, tau=0.00583, C=1.0: holds for log(2m) >= 18.7  (W >= e^94)
closure: d=0.3, eps=0.07, tau=0.00583, C=6000.0: holds for log(2m) >= 59.1  (W >= e^296)
T3 max over 300 grids of LHS/RHS (each must be <=1):  [0.9811830413058944, 0.8954336351632063, 0.9999659982985881]
T3 instance u= [0.5, 0.75, 0.875, 0.9375] :  7.0  <=  16.0
```
(`d=` in the closure lines is `𝔡`; `m=n+1`, `W=(2m)^5`.) Limit computation for the external hypotheses at `sz0` (`W=(2m)^5, L=4m, lam=(2m)^{-6}`): WO `W^{-3/2+𝔡}=(2m)^{-7.5+5𝔡} ≤ (2m)^{-6}` iff `𝔡 ≤ 0.3`; Bandwidth `N^{1/6}=(WL)^{1/2} ≤ W` iff `L ≤ W`;
`N ~ m^{18} → ∞`; `lam²W³=(2m)³ ≥ 8`. Target 6: its hypotheses hold at every `n`; the conclusion is a `∀ᶠ` whose thresholds are the `W ≥ e^{94}` … `e^{439}` above (`log W` against `W^{ε/2}`: intrinsic, not a failed hypothesis). Target 3 instance above is the first inequality at `k=3`. Stochastic premises of target 5 (`STLKU, STLocalEntryU, STAvgU, STLmaxU, GijGEXPTSwap`) are other gates' pins and stay hypotheses of its instance.
(b) `python3 inst_b.py | grep -E "sigma=\(1, 0\) E=0.0|^T2'|W\^-D_j|frakd=(0.1|0.75|1.0):"` (target 2 at `d=3, L=4, g=1/64, W=32, D=1`, `u=(0,1/48,1/24,1/16)`, `c_j=1/48`, `p=(1,2,1/2)`, random-phase `ℰ_j` with `|ℰ_j(b)|=p_jT`; dense `uKer=(1-vμS)(1-wμS)^{-1}`)
```
T2 sigma=(1, 0) E=0.0: max |LHS|/RHS(C=(3e^(13/4))^2) = 1.833e-04;  max |LHS|/RHS(C=1) = 0.523
T2' (per-j level D_j): max over r of [sum c_j p_j (C T_{u_k,D_j}+rho_j^2 W^-D_j)] / [(C+1) sum c_j p_j That_{u_k}] = 0.9998329791014207  (must be <=1)
   W^-D_j (1-u_j)^2 = W^-D*  -> [1.0, 0.9999999999999896, 0.9999999999999936]
uniform D': d=3, frakd=0.1: exponent of W in Extra/(W^eps*floor) = +2.620  (closes iff <=0, i.e. frakd >= (d+eps)/4 = 0.755)
uniform D': d=3, frakd=0.75: exponent of W in Extra/(W^eps*floor) = +0.020  (closes iff <=0, i.e. frakd >= (d+eps)/4 = 0.755)
uniform D': d=3, frakd=1.0: exponent of W in Extra/(W^eps*floor) = -0.980  (closes iff <=0, i.e. frakd >= (d+eps)/4 = 0.755)
```
(c) `python3 inst_c.py | grep -E "^(hyp|ell|H3|max)|\|a1-a2\|=(0|10):" | grep -v "mu=(-0"` (target 7 at `d=3, L=20, W=64, g=1/64, E=0, v=1/32, w=1/16, D=8`; `X` = worst nonnegative tensor `pT_v²·1(near)+Y·1(far)`, `p=Y=1`; kernels by FFT; `|K|` for `σ=(+,-)`)
```
hyp: 0<=v<=w<1: True; g^2=2.441e-04 <= 1-w=0.9375: True; |E|<=2: True; log W=4.1589 >= 4: True
ell*=(log W)^(3/2)=8.4814; ell*/8=1.0602; L=20: max zdist=10; far pairs (|b_i-b'_i|>ell*) exist: True
H3: max_{|x|>=ell*/8} Theta_w(x) = 2.817e-10 ; W^-D2 >= that for D2 = 5 (W^-D2=9.313e-10); Theta_w(0)=1.0666
  mu=(1.00,1.00) |a1-a2|=0: near/[C p (T_w^2+rho^4 W^-2D)] = 2.838e-13;  near/[p T_w(r)^2 (C=1)] = 1.000;  far-weight*Y/[4 Y L^d rho^3 W^-D2] = 4.389e-10
  mu=(1.00,1.00) |a1-a2|=10: near/[C p (T_w^2+rho^4 W^-2D)] = 2.840e-13;  near/[p T_w(r)^2 (C=1)] = 1.001;  far-weight*Y/[4 Y L^d rho^3 W^-D2] = 4.322e-10
max ratios (must be <=1): 2.8402776664652017e-13 4.861847094901116e-10
```
The ratio `1.001` (not `<1`) at `C=1` is the amplitude identity `ρ⁴α_v²=α_w²`: a constant `C ≥ 1.001` is needed, `C₇` is ample.

### Target 2′ and target 7 (mathematics; names are the merged objects)
**2′** (pin 2 with `D:ℕ→ℝ`): same hypotheses with `‖ℰ_j(b)‖ ≤ p_j T_{u_j,D_j}(|b₁-b₂|)` (`j<k`); conclusion `‖Σ_j c_j (𝒰_{u_j,u_k,σ}∘ℰ_j)_a‖ ≤ Σ_j c_j p_j (C T_{u_k,D_j}(|a₁-a₂|) + ρ_j² W^{-D_j})`. Termwise `stTailtoTail_holds` at `D_j` (scaling by `p_j`, `p_j=0 ⇒ ℰ_j=0`, `EKsgn m σ = fun i => mSigma E (σ i)` by `rfl`-same body, `‖mE E‖=1`); pin 2 is `D_j≡D`.
**4′** (optional): hypothesis `ω ∈ good(E, D₁, J₀, τ′, n, u)` with `D₁` independent of the conclusion level `D` (events 2-7 contain neither); the pinned target 4 is `D₁=D`. With pin 4 alone S5-11 needs a 10-line transfer of event 1 from `D*` to `D_u` by target 1.
**7** `pfStep5Alg_qvKernel` (≤15 lines): for `d ≥ 3`, `L ≥ 3`, `g,W>0`, `D,D₂∈ℝ`, `|E|≤2`, `σ∈{±}²`, `0≤v≤w<1`, `g² ≤ 1-w`, `4 ≤ log W`, `p,Y ≥ 0`, `X=STeeM σ · ·` and hypotheses
(H1) `‖X(b,b′)‖ ≤ p T_{v,D}(|b₁-b₂|)²` if `max_i|b_i-b′_i| ≤ ℓ*`; (H2) `‖X(b,b′)‖ ≤ Y` for all `b,b′`; (H3) `‖Θ_w(x,y)‖ ≤ W^{-D₂}` if `|x-y| ≥ ℓ*/8` (`Θ_w` = `Theta d L g w`);
conclusion, `∀a`: `‖STeeUM(v,w,σ,a)‖ ≤ C₇ p (T_{w,D}(|a₁-a₂|)² + ρ⁴W^{-2D}) + 4 Y L^d ρ³ W^{-D₂}`, `ρ=(1-v)/(1-w)`, `C₇=18e^{8d+2}`; here `STeeUM = Σ_{b,b′} Π_i uKer(cycProd(mSigma E σ)_i; v,w)(a_i,b_i) Π_i uKer(cycProd(mSigma E ¬σ)_i; v,w)(a_i,b′_i) X(b,b′)`.
Differs from the ticket: `D₂` separate from `D` and the far term has no `N^C` (row 12). Proof: near pairs: extend to all pairs; `b′` rows `≤ρ²`; `T_v² ≤ 2α_v²e^{-2√·}+2W^{-2D}`, weighted rows (row 10), triangle for `2√`, `ρ⁴α_v²=α_w²`. Far pairs: some `|b_i-b′_i|>ℓ*` ⇒ one kernel has distance `>ℓ*/2`; its entry is `(w-v)μ(SΘ_{wμ})(a,b)` (`uKer_eq_one_add`), `≤ W^{-D₂}` by (H3) and property 4; 4 choices, other rows `≤ρ`, far sum `≤ L^dW^{-D₂}`.
Convention check: `STGridRepNAt` conjunct 4 uses `STeeUM … (u_j) (u_k) (pathH … j ω) i.1 i.2` with `UN … (mSigma E (i.1 i′))` = `Ugen`: same argument order, `σ`-kernel on `b`, `¬σ`-kernel on `b′`, no conjugation mismatch; conjunct 3 of `Bounds` bounds the first index of `STee` = `b`, as (H1).

### (3) Consumer chain (S5-11), per Fable §4(3) term, all at `T̂_u := T_{u,D_u}`, `J♯(u_j,D_{u_j}) ≤ W^ε` for `j<k`
- initial: `STDecayStrong` at `s`, exponent `D*`, `Bctl ≤ 2(W^d(1-s))^{-1}` ⇒ `|A₀| ≤ 4N^{τ₁}T_{s,D_s}`; target 2′ (`k=1`) ⇒ `≤ 4N^{τ₁}(C+1)T̂_{t′}` [bracket `1`].
- LK×LK: `p_j=N^τW^{2ε}W^{-d}(1-u_j)^{-2}`; 2′ + target 3(i) ⇒ `N^τ(C+1)W^{2ε}(W^d(1-t′))^{-1}T̂ ≤ N^τ(C+1)W^{2ε}(lam²W^d)^{-1/4}T̂` [bracket `W^{2ε}(·)^{-1/4}`].
- G̃: indicator `≤ 1`, `p_j=N^τ(1-u_j)^{-1}[1+W^{3ε/2}(W^d(1-u_j))^{-1/2}]`; 2′ + target 3(iii) `log ρ_{0k} ≤ d log W`, 3(ii) `2W^{3ε/2}(W^d(1-t′))^{-1/2} ≤ 2W^{2ε}(lam²W^d)^{-1/4}` [`log W`, `W^{2ε}(·)^{-1/4}`].
- martingale: target 7 per `j` at `D_{u_j}` with `p_j=N^τ(1-u_j)^{-1}[1+W^{3ε}(W^d(1-u_j))^{-1/2}]`, `T_{w,D_j}²+ρ_j⁴W^{-2D_j} ≤ 2T̂_w²`; 3(iii)+3(ii) ⇒ `Σ Δ p_j ≤ N^τ[d log W+2W^{3ε}(W^d(1-t′))^{-1/2}]`; Azuma (`N^{-D} ≤ W^{-2D*}`) ⇒ `|Mart| ≤ N^{ε′+τ/2}√(2C₇)(√(d log W)+√2 W^{3ε/2}(·)^{-1/4}+1)T̂` [same bracket]. Rem: `K ≥ N^{C_K}` makes `N^{C₀}Δ^{1/2} ≤ W^{-D*}`.
- sum `≤ N^{τ_tot}C_tot(1+log W+W^{2ε}(lam²W^d)^{-1/4})T̂`: target 6 (`C:=C_tot`, then `τ`; each loss `≤ τ/(#terms)`) `< W^ε`. Final: `LK2 ≤ W^εT_{u,D_u} ≤ W^εT_{u,D}` (target 1). No random right side is lifted (§64 (4)): targets 1-7 are per `(n,u_j,ω)`; S5-11's only lift is `STLK2 ≤ N^τ T_{u,D}` (deterministic right side).
Structure of target 7 (no size estimate here): needs private copies of the Weight, Theta, Kernel, Sqrt sections of `TailtoTail.lean` (private there) with weight `c=1/(4d+1)` and `e^{2√}`, plus a new near/far Main; the ticket's stop rule on its size is for the dispatcher.

### Verdicts
- Target 1 PASS. Target 3 PASS (script a, exact telescoping). Target 4 PASS (4′ optional). Target 5 PASS (any real `D`: `Bctl² ≤ W^D T_{u,D}` as `T ≥ W^{-D}`, `Bctl ≤ 1`). Target 6 PASS (`τ=𝔠ε/2`; closure threshold large but the statement is `∀ᶠ`).
- Target 2 FAIL as the sufficient pin: true as stated, but its single `D` does not close S5-11 (F2); amend to 2′ (same proof, one extra binder). Target 7 PASS with the statement above (replaces the ticket's single-`D` form).
- Ticket verdict: FAIL (stop and report to the dispatcher: amend pin 2 to 2′, restate target 7, optionally 4′; the rest of the chain closes).

## (a′) Preflight corrections — Mon Oct  5 21:16:36 UTC 2026
None. Targets 1, 3, 4, 5, 6 are proved with the statements of the check file (script diff in (b)); targets 2′ and 4′ with the statements of (a) as adopted by Amend 1. Target 7 is not in this ticket (Amend 1).

## (b) Script output — Mon Oct  5 21:16:36 UTC 2026
Branch `t/T2209`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2209`; the only file changed is `RBM3D/Induction/PfStep5Alg.lean` (new); `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are untouched. Scratch files: `<scratchpad>/T2209/`.
### Build, hygiene, axioms, registry pre-check (cwd = the worktree)
```
$ date -u
Mon Oct  5 21:15:46 UTC 2026
$ git log --oneline -6; git diff --stat main...t/T2209; echo "uncommitted entries: $(git status --short | wc -l)"
4bdfc12 T2209: PfStep5Alg: compiled distance check for the instance point of target 1
07f8cf8 T2209: PfStep5Alg: joint satisfiability of the hypotheses of targets 4', 4 at sz0 (from target 5 and the five stochastic pins)
3855d74 T2209: reflow two module-docstring lines of PfStep5Alg (longLine linter)
bbb8a29 T2209: name the instances of PfStep5Alg (theorems with printable axioms), tie targets 4/4' instances to the flow energy
96f0ab4 T2209: Induction/PfStep5Alg (S5-10): targets 1, 2', 2, 3, 4', 4, 5, 6 of lem:pf_step5 part 1
ed9c0f1 T2203: merge LW-10c3 Graph/LocalRegular6c
 RBM3D/Induction/PfStep5Alg.lean | 785 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 785 insertions(+)
uncommitted entries:        0
$ lake build RBM3D.Induction.PfStep5Alg 2>&1 | grep -E "PfStep5Alg|Build completed"
Build completed successfully (3846 jobs).
$ lake build RBM3D.Induction.PfStep5Alg >/dev/null 2>&1; echo "exit $?"
exit 0
$ lake env lean RBM3D/Induction/PfStep5Alg.lean 2>&1 | wc -l
       0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/PfStep5Alg.lean
0
$ grep -c "^#print axioms" final_axioms.lean   # final_axioms.lean: `import RBM3D.Induction.PfStep5Alg`, `open RBM.Gauss.Sizes`, one `#print axioms` per `^theorem (pfStep5Alg_[\w']+)` of the file
23
$ lake env lean final_axioms.lean | sed -E "s/^.(.*). depends on axioms: (.*)$/\2/" | sort | uniq -c
  23 [propext, Classical.choice, Quot.sound]
$ lake build > final_full4.log 2>&1; tail -1 final_full4.log; echo "exit $?"   # whole library; RBM3D.lean does not import the new module yet
Build completed successfully (4016 jobs).
exit 0
$ date -u; lake env lean registry_precheck.lean > out 2>&1; echo "exit $?"; sed -n 1p out; grep "premises found by scanning" out; grep -c 'PfStep5Alg\|pfStep5Alg' out   # registry_precheck.lean: `import RBM3D`, `import RBM3D.Induction.PfStep5Alg`, `#assert_rbm_axioms`
Mon Oct  5 21:16:02 UTC 2026
exit 0
axiom audit: 6348 theorems, 2206 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 96, structural 25, refuted 4).
0
$ (cd /Users/junyin/Lean_proof/RBM3D && grep -rn "PfStep5Alg\|pfStep5Alg" RBM3D | wc -l); grep -rn "PfStep5Alg\|pfStep5Alg" RBM3D --include='*.lean' | grep -v "^RBM3D/Induction/PfStep5Alg.lean" | wc -l   # main worktree; then this worktree without the new file
       0
       0
$ git diff --name-only main...t/T2209
RBM3D/Induction/PfStep5Alg.lean
```
### Statements, extracted by script (`stmts.py`: regex over the Lean file and over `docs/tickets/checks/T2209-check.lean`)
```
== pins 1-6: body of the Lean file's def == body of the check file's def (binder line included)
PfStep5Alg_closure_pin: body True, binder line True
PfStep5Alg_goodProb_pin: body True, binder line True
PfStep5Alg_goodStop_pin: body True, binder line True
PfStep5Alg_riemann_pin: body True, binder line True
PfStep5Alg_tailAnti_pin: body True, binder line True
PfStep5Alg_ugenSum_pin: body True, binder line True
== theorem headers
theorem pfStep5Alg_tailAnti {d : ℕ} (sz : Sizes d) : PfStep5Alg_tailAnti_pin sz := by
theorem pfStep5Alg_ugenSum' (d : ℕ) : PfStep5Alg_ugenSum'_pin d := by
theorem pfStep5Alg_ugenSum (d : ℕ) : PfStep5Alg_ugenSum_pin d := by
theorem pfStep5Alg_riemann : PfStep5Alg_riemann_pin := by
theorem pfStep5Alg_goodStop' {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop'_pin sz := by
theorem pfStep5Alg_goodStop {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop_pin sz := by
theorem pfStep5Alg_goodProb {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodProb_pin sz := by
theorem pfStep5Alg_closure {d : ℕ} (sz : Sizes d) : PfStep5Alg_closure_pin sz := by
== PfStep5Alg_ugenSum'_pin  (binder line: def PfStep5Alg_ugenSum'_pin (d : ℕ) : Prop :=)
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W E : ℝ) (D : ℕ → ℝ), 0 < g → 0 < W → |E| ≤ 2 →
      ∀ (σ : Fin 2 → Bool) (k : ℕ) (u c p : ℕ → ℝ) (ℰ : ℕ → (Fin 2 → Zd d L) → ℂ),
        0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 → g ^ 2 ≤ 1 - u k → (∀ j, 0 ≤ c j) →
        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) (D j) (zdistInf d L (b 0 - b 1) : ℝ)) →
        ∀ a, ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ ≤
          ∑ j ∈ Finset.range k, c j * p j *
            (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j)))
== PfStep5Alg_goodStop'_pin  (binder line: def PfStep5Alg_goodStop'_pin {d : ℕ} (sz : Sizes d) : Prop :=)
  ∀ (E : ℕ → ℝ) (D D₁ ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
    1 ≤ ((sz.size n : ℕ) : ℝ) →
    LemDecCalELip_Jsharp sz E D n u ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ω ∈ lemDecCalEPrec_good sz E D₁ J₀ τ' n u →
    ω ∈ lemDecCalEPrec_good sz E D (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε) τ' n u
== diff PfStep5Alg_ugenSum_pin -> PfStep5Alg_ugenSum'_pin (check-file pin -> new pin)
-    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E : ℝ), 0 < g → 0 < W → |E| ≤ 2 →
+    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W E : ℝ) (D : ℕ → ℝ), 0 < g → 0 < W → |E| ≤ 2 →
-        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) D (zdistInf d L (b 0 - b 1) : ℝ)) →
+        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) (D j) (zdistInf d L (b 0 - b 1) : ℝ)) →
-            (C * tailTD d W (u k) D (zdistInf d L (a 0 - a 1) : ℝ) +
-              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-D))
+            (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
+              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j)))
== diff PfStep5Alg_goodStop_pin -> PfStep5Alg_goodStop'_pin (check-file pin -> new pin)
-  ∀ (E : ℕ → ℝ) (D ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
+  ∀ (E : ℕ → ℝ) (D D₁ ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
-    ω ∈ lemDecCalEPrec_good sz E D J₀ τ' n u →
+    ω ∈ lemDecCalEPrec_good sz E D₁ J₀ τ' n u →
```
### Instances (file lines 529-783; named theorems so that `#print axioms` applies); excerpt `sed -n '541,542p;570,573p;630p;649,650p;669,671p;758p;770p;780,781p'`
```
theorem pfStep5Alg_inst_tailAnti : STtailTD sz0 0 (1 / 16) 48 pfStep5Alg_instA ≤ STtailTD sz0 0 (1 / 16) 1 pfStep5Alg_instA :=
  pfStep5Alg_tailAnti sz0 0 (1 / 16) 1 48 pfStep5Alg_instA (by norm_num)
  obtain ⟨C, hC, H⟩ := pfStep5Alg_ugenSum' 3 (le_refl 3)
  refine ⟨C, hC, fun a => ?_⟩
  exact H 4 (by norm_num) (1 / 64) 32 0 (fun j => (j : ℝ) + 1) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] 3 pfStep5Alg_instU (fun _ => 1 / 48) (fun j => (j : ℝ) + 1) (fun _ _ => (0 : ℂ))
  pfStep5Alg_riemann 3 (fun j => 1 - (1 / 2 : ℝ) ^ (j + 1)) (by norm_num)
  pfStep5Alg_goodStop' sz0 (STflowE z0) 1 55 (1 / 4) (1 / 100) J₀ 0 (1 / 16) ω (by norm_num)
    (by rw [sz0_values.2.2.1]; norm_num) hstop hgood
  pfStep5Alg_goodProb sz0 (STflowE z0) sInst tInst 1 sz0_tendsto
    ((st5_Bctl_le_one sz0 (by norm_num) (by norm_num) flow_z0 sz0_ht).mono fun n hn u => hn (u : ℝ) u.2.2)
    hLK hLoc hAvg hLmax hGij (1 / 100) 1 (by norm_num) (by norm_num)
  pfStep5Alg_inst_goodStop'_nonvac 1 1 le_rfl (by norm_num) hLK hLoc hAvg hLmax hGij
  pfStep5Alg_inst_goodStop'_nonvac 1 55 (by norm_num) (by norm_num) hLK hLoc hAvg hLmax hGij
  pfStep5Alg_closure sz0 (1 / 6) (1 / 10) sz0_admissible (1 / 50) 6000 (by norm_num) (by norm_num)
    (by norm_num)
```
### Narrative
- Delivered (Amend 1 scope): targets 1, 2′ with its corollary 2, 3, 4′ with its corollary 4, 5, 6, in `RBM3D/Induction/PfStep5Alg.lean` (785 lines; imports `RBM3D.Induction.LemDecCalEPrec`, `RBM3D.Induction.TailtoTail`). Target 7 is not proved here (split to S5-10a by Amend 1).
- Statements: pins 1-6 equal the check-file pins (script above); pins 2′, 4′ differ from pins 2, 4 only by the diff lines above; pin 2 is proved from 2′ with `D := fun _ => D`, pin 4 from 4′ with `D₁ = D`. No hypothesis added or weakened, no frozen signature touched (new file only).
- Routes. 1: `W ≥ 1` and monotonicity of `x ↦ W^x`. 2′: `stTailtoTail_holds d` termwise at level `D_j` (its constant `C` taken abstractly), scaling by `p_j` (`p_j ≥ 0` from the hypothesis at the zero index since `T > 0`; `p_j = 0` gives `ℰ_j = 0`), `norm_mE`, `EKsgn (mE E) σ` accepted for `fun i => mSigma E (σ i)` by `exact`, then the triangle inequality. 3: each term against its telescoping term (`(b-a)(1-a)⁻²`: difference `(b-a)²/((1-a)²(1-b))`; exponent `3/2`: `r = (1-a)^{-1/2}`, `R = (1-b)^{-1/2}`, difference `(R-r)²(2R+r)/R²`; `log`: `Real.log_le_sub_one_of_pos`), sums collapsed by `Finset.sum_range_sub(')`; no integrals. 4′: conjunct 1 of `lemDecCalEPrec_good` from `LemDecCalELip_Jsharp_basic`, `LemDecCalELip_tail_pos`, `N^{τ'} ≥ 1`; conjuncts 2-7 carried over from the hypothesis. 5: `st5_prec_mono` (`c = 1`) turns `STLKU` at `k = 2` into `STLK2 ≺ W^D T` (`Bctl² ≤ 1 ≤ W^D W^{-D} ≤ W^D T`, `lemDecCalEPrec_tail_ge`), then `lemDecCalEPrec_prob`. 6: `τ = 𝔠ε/2` (independent of `C`); `N^τ ≤ W^{ε/2}` from `Bandwidth`; `(lam²W^d)^{-1/4} ≤ W^{-𝔡/2}` from `lam_sq_mul_pow_ge`; `W^{2ε-𝔡/2} ≤ 1`; `log W ≤ (4/ε)W^{ε/4}` (`Real.log_le_rpow_div`); `W^{ε/4} ≥ 4C/ε + 2C + 1` eventually.
- Instances (`d = 3`, `sz0`, `L = 4`, `W = 32`): 1 at `n = 0`, `u = 1/16`, `D = 1 < 48 = D'`, `a = ((0,0,0),(1,1,1))` with `zdistInf = 1` (`pfStep5Alg_instA_dist`) (`≤` and strict); 2′ at `k = 3`, `u_j = j/48`, `g = 1/64`, `c_j = 1/48`, `p_j = D_j = j + 1`, tensors `ℰ ≡ 0` and the extremal `ℰ_j(b) = p_j T_{u_j,D_j}`; 2 at `D ≡ 1`, `ℰ ≡ 0`; 3 at `u_j = 1 - 2^{-(j+1)}`, `k = 3` (first sum `= 7`, `pfStep5Alg_inst_riemann_sum`); 4′, 4 at `n = 0`, `u = 1/16`, `ε = 1/4`; 5 at `E = STflowE z0`, `[0, 1/16]`, `D = 1`; 6 at the merged `Admissible (1/6) (1/10)`, `ε = 1/50`, `C = 6000`.
- Hypotheses left in the instances: the sample events (stopping condition, good event) of 4′, 4, and the five stochastic pins `STLKU, STLocalEntryU, STAvgU, STLmaxU, GijGEXPTSwap` of 5 (other gates). `pfStep5Alg_inst_goodStop'_nonvac` (cases `pfStep5Alg_inst_goodStop_nonvac_one`, `pfStep5Alg_inst_goodStop'_nonvac_55`) shows that, given those five pins, the events of 4′/4 are jointly satisfiable at `sz0` for `D ≤ D₁`, `0 ≤ D₁`: target 5 bounds the complement of the good event at `Jst = W^{D₁}` by `N⁻¹ < 1`, so the event contains a sample, and on it `J♯(D) ≤ W^{D₁ + 6/100}` (target 1, `LemDecCalELip_Jsharp_basic`). The witness uses the large `ε = D₁ + 6/100`, not the small `ε` of S5-11.
- Nothing ported: no declaration or proof text of RBM1D/RBM2D was used (no command of this stage touched `../RBM1D` or `../RBM2D`), no private proof was copied; helpers are `private` with the prefix `pfStep5Alg_`. Registry: the new `def … _pin : Prop` occur only as theorem conclusions; the pre-check exits 0 and mentions no new name, so `Test/Axioms.lean` needs no line.
- For the hub: `RBM3D.lean` does not import the new module on this branch; the merge must add `import RBM3D.Induction.PfStep5Alg` after the last `import` and re-run the whole build.

## (c) Verified Mathlib names (`c_names_final.lean`: 30 `#check`s = the 21 names below + the 9 project names after them; 0 errors, 0 deprecation messages)
```
Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_lt_rpow_of_exponent_lt : 1 < x → y < z → x ^ y < x ^ z
Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos : 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.rpow_le_rpow : 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_add : 0 < x → ∀ y z, x ^ (y + z) = x ^ y * x ^ z
Real.rpow_mul : 0 ≤ x → ∀ y z, x ^ (y * z) = (x ^ y) ^ z
Real.one_le_rpow : 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.log_le_rpow_div : 0 ≤ x → 0 < ε → Real.log x ≤ x ^ ε / ε
Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1
Real.log_div : x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y
Real.sqrt_eq_rpow : √x = x ^ (1 / 2)      Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x
Finset.sum_range_sub : ∑ i ∈ range n, (f (i+1) - f i) = f n - f 0
Finset.sum_range_sub' : ∑ i ∈ range n, (f i - f (i+1)) = f 0 - f n
monotone_nat_of_le_succ : (∀ n, f n ≤ f (n+1)) → Monotone f
Filter.tendsto_atTop_mono' : f₁ ≤ᶠ[l] f₂ → Tendsto f₁ l atTop → Tendsto f₂ l atTop
tendsto_rpow_atTop : 0 < y → Tendsto (fun x => x ^ y) atTop atTop
pow_le_pow_of_le_one : 0 ≤ a → a ≤ 1 → m ≤ n → a ^ n ≤ a ^ m
le_mul_of_one_le_left : 0 ≤ b → 1 ≤ a → b ≤ a * b
one_le_mul_of_one_le_of_one_le : 1 ≤ a → 1 ≤ b → 1 ≤ a * b
```
Verified absent (grep in Mathlib, 0 hits): `Real.rpow_le_rpow_of_exponent_nonpos`, `Real.rpow_le_rpow_of_neg`. The 9 project names (all merged): `stTailtoTail_holds`, `norm_mE`, `lam_sq_mul_pow_ge`, `st5_prec_mono`, `st5_Bctl_le_one`, `lemDecCalEPrec_prob`, `lemDecCalEPrec_tail_ge`, `LemDecCalELip_Jsharp_basic`, `LemDecCalELip_tail_pos`.

## (d) Open issues and paper-delta candidates
1. Target 7 (`pfStep5Alg_qvKernel`) is S5-10a's (Amend 1); S5-11's martingale term depends on it.
2. The instances of 4′, 4 keep the sample events as hypotheses; joint satisfiability is shown only given the five stochastic pins of target 5 and at the large `ε = D₁ + 6/100`.
3. Target 6 is `∀ᶠ n` with a large threshold (preflight (a), script a: `𝔡 = 1/10, ε = 1/50, C = 1`: `log(2m) ≥ 87.8`); a consumer must not instantiate it at a finite `n`.
4. `RBM3D.lean` does not yet import the new module (hub, at merge).

Paper-delta candidates (dispatcher numbers them):
- T2209a: `lem_dec_calE` is applied to the stopped process per time at the realized control `J♯ ≤ W^ε` (S5-09's per-time layer), not as the `Prec` lemma with a deterministic `J*` (`3_5:2367-2369`): targets 4′, 4 are the stopping-condition step.
- T2209b: the time integrals of `(int_K-L_ST)` are left Riemann sums on the grid of §7 (constants 1, 2 and `log`, target 3), without a range argument.
- T2209c: not here; the squared-profile `TailtoTail` (target 7) moved to S5-10a by Amend 1.
- T2209d: `lem:pf_step5` is proved at the time-dependent level `D_u = D* + 2 log_W(1-u)`, `D* = max(D, D₀) + 2d + 1`, and descends by target 1 (Amend 1, DECISIONS §70): target 2′ takes the level as a sequence `D : ℕ → ℝ`, target 4′ a good-event level `D₁` separate from the conclusion level (continues T2193a).
- T2209e (new): the closure of `lem:pf_step5` is explicit: `ε < 𝔡/4`, `τ = 𝔠ε/2`, bracket `1 + log W + W^{2ε}(ilambda²W^d)^{-1/4}` (target 6); the paper says "analogous to, and in fact much simpler than, the proof of equation (2.76) in [YY_25, Section 5.3] ... we omit the details" (`3_5:2380`).
- T2209f (new): the good event of S5-09 is used at the crude control `Jst n u D = W^D` whose hypothesis follows from `STLKU` at `k = 2` and `Bctl ≤ 1`, every real `D` (target 5): no circularity with the conclusion.
