Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 22:49:22 UTC 2026

Notation. `lw = log W`, `ℓ = ℓ_s = ellT L g s ≥ 1`, window `w = lw³ℓ` (`STCltIsoConcl`, `Step5Pins.lean:418-419`), far cutoff `ρ = lw⁴ℓ = lw·w` (`STfFar`, `Step5Pins.lean:364-365`), pairing radius `R = 10w`; `|·|` is `zdistInf`, `δ(i,k) = |b_i0 − b_k0|` (first labels), `n = 2p`.

### (i) Exponent table
| Row | Value | Constraint | Slack |
|---|---|---|---|
| Cluster construction (T1) | maximal `2R`-separated `S ⊂ Fin n` for `δ`; `φ(k)` = nearest point of `S` (min-index ties); `φ∘φ=φ`; `φ k = k` for `k ∈ S` | RBM2D `cltm_exists_cluster` (`CltMoments.lean:75`, c9a24cf) uses `3R`; separation `2R` suffices: a partner `k₀` of `i ∈ S` has `δ(i,k₀)<R`, so `k₀ ∉ S` and any `s ≠ i` in `S` has `δ(k₀,s) ≥ 2R−R > δ(k₀,i)`; non-members have some `s ∈ S` with `δ<2R` | member radius `2R = 20w ≤ 2pR` (ticket) for all `p ≥ 1`; brute-force check below, 0 violations |
| `r`, structures (T1) | `r = |S| ≤ p`; `#φ ≤ n^n = (2p)^{2p}` | each fixed point carries ≥1 other index so `2r ≤ n` (`cltm_two_mul_free_le :370`); `cltm_card_cluster_le :380` | `p=1`: `r=1`, `#φ ≤ 4` |
| Pairing vs isolation (T1) | `Paired_R(b) := ∀i ∃k≠i, δ(i,k) < R` (strict) | `¬Paired_R ⇔ ∃i ∀j≠i, R ≤ δ(i,j)` (push_neg) is the hypothesis of `STCltIsoConcl` (`Step5Pins.lean:420-421`: `10 * log W ^ 3 * ellT … ≤ zdistInf …`, first labels) with `R = 10*lw^3*ℓ` literally | paper `(eq:pairingcond)` uses `≤`, `(eq:bound_isolated)` uses `≥`: both hold at `δ = R` (overlap); strict pairing is the exact complement, `≤`-pairing gives only `¬Paired_≤ ⇒ isolated`. Candidate `T2165a`. `STCltIsoConcl` also needs `\|b_k0−b_k1\| ≤ w` for all `k`: the window of region `(eq:sumregionsforb)` |
| Premise on `lw` | `lw ≥ max(40, 2d)` (`(40,6)` at `d=3`) | BD1 half-ball: `\|r\|₁ ≤ d w ≤ ½\|a\|₁` follows from `2dw ≤ ρ < \|a\|_∞ ≤ \|a\|₁` ⇔ `lw ≥ 2d` (D368 form); comparability: `2R = 20w ≤ ρ/2` ⇔ `lw ≥ 40` | no `p`-dependence (ticket's `40p` is for the `2pR` component radius). At `szCL`, `n=34`: `lw−40 = 0.2025`; `n=33` fails (script A) |
| Weight at `a₁` (T2a) | `\|g²Θ_t(a₁,b₁)\| ≤ C_T/(\|x\|^{d−2}+1)`, `x = b₁−a₁`, `C_T = 2C₅(1+2^{d−1})` | route: `prop5Decay_holds` (`Prop5Hold.lean:784`, `C₅=C₅(d,Λ)`, any `m` with `‖m‖=1`) ⇒ `meanFar_T1` (`MeanFar.lean:762`, public): `\|Θ(0,x)\| ≤ C₅(1+2^{d−1}) g⁻² (\|x\|+1)^{−(d−2)}`; regime `g²/L² ≤ 1−t` (STReg5I) is used only for the zero-mode term `(L^d\|1−t\|)⁻¹ ≤ 2^{d−1}(g²+\|1−t\|)⁻¹(\|x\|+1)^{−(d−2)}` (`zeroMode_le_of_ge`, `Defs/Tail.lean:119`, needs `\|x\| ≤ L`); `Θ_{xy} = Θ_{0,y−x}` (`Theta_apply_add_right_of_three_le`, `Props4.lean:100`; `meanFar_Theta_shift` is private); `(x+1)^{−m} ≤ 2/(x^m+1)`; `STmsig E σ = PropSpin (mE E) σ`, `‖mE E‖ = 1` for `\|E\| ≤ 2` (`norm_mE`), as `MeanFar.lean:2063` | regime equality allowed (`szCL`: `1−t = 1/L²`) |
| Weight at `a₂` (T2b) | `\|g²(Θ_t(b₂,a₂)−Θ_t(b₁,a₂))\| ≤ C_B w/(\|a₂−b₁\|^{d−1}+1)`, `C_B = 2d·C₆` | `prop6Diff1_holds` (`Prop6Hold.lean:353`, `C₆ = C₆(d,Λ,κ,c=½)`, premises `0<κ ≤ Im m`, `\|r\|₁ ≤ c\|a\|₁`; proof constant `2^{d−1}C₁`, line 357); `a = a₂−b₁`, `r = b₁−b₂`, `a+r = a₂−b₂`; `g²(g²+\|1−t\|)⁻¹ ≤ 1` (BD1 has no zero-mode term, no regime needed); `\|r\|₁ ≤ d\|r\|_∞ ≤ dw` (`zdistD_le_mul_zdistInf`, `Defs/Sizes.lean:122`); `(\|a\|₁+1)^{−(d−1)} ≤ (\|a\|_∞+1)^{−(d−1)} ≤ 2/(\|a\|_∞^{d−1}+1)`; `κ' = min(κ,½) ≤ Im mE` as `MeanFar.lean:1992, 2046` | `\|a\|_∞ > ρ ≥ 2dw`: slack `ρ/(2dw) = lw/(2d) ≥ 1` |
| Comparability (T3) | `\|b₁−b₁'\| ≤ 2R`, `\|x\| > ρ` ⇒ `\|x'\|+1 ≥ (\|x\|+1)/2`; profile ratio `≤ 2^{d−2}` (exp `d−2`), `≤ 2^{d−1}` (exp `d−1`), each `≤ 2^d`; both weights `≤ 2^{2d−3}` | `\|x'\| ≥ \|x\|−20w > \|x\|/2` since `20w ≤ ρ/2 < \|x\|/2`; `(x'^m+1) ≥ 2^{−m}(x^m+1)`; premise `lw ≥ 40` (exact, no `p`) | `szCL n=34`: `ρ/(40w) = 1.0051` |
| Per-cluster sum (T4) | `Σ_{b₁^{(k)}∈Ball(2R), k∈A∖rep} Σ_{b₂^{(k)}: \|b₁−b₂\|≤w} Σ_{b₂^{rep}} ∏ (\|b₁−b₂\|^{d−2}+1)⁻¹ ≤ C₄ w^{(d+2)(\|A\|−1)+2}`, `C₄ = (41^d)^{\|A\|−1}(2^{d−1}cs_d)^{\|A\|}`, `cs_d = d2^d` | `Σ_{\|x\|≤w}(\|x\|^{d−2}+1)⁻¹ ≤ 2^{d−3}cs_d(w+1)² ≤ 2^{d−1}cs_d w²` (`w ≥ 1`; shell count `≤ cs_d(k+1)^{d−1}` as `meanFar_card_shell_real`/`meanFar_sum_ball`, both private: re-port as `cltMom1_*`; `Defs/Shells`/`RadialSum` are `ℓ¹` (`zdistD`) and cannot serve an `ℓ^∞` profile); ball count `(2·2R+1)^d ≤ (41w)^d`; `sum_compat` (RBM2D `:168`) generalised to labels `Fin 2 → Zd d L`, compat on the first label | `d=3`: `C₄ = 6.352e8` (`\|A\|=2`), `4.203e15` (`\|A\|=3`) |
| Tail sum (T5) | `Σ_{\|x\|>ρ}(\|x\|+1)^{−(d−1)k} ≤ cs_d ρ^{−((d−1)k−d)}` | shells give `cs_d Σ_{r>ρ}(r+1)^{−e}`, `e = (d−1)(k−1) ≥ 2`; `Σ_{r≥m}(r+1)^{−2} ≤ 1/m`, `m = ⌊ρ⌋+1 > ρ` (telescoping, `1/(r(r+1))`) | exponent `(d−1)k−d = d−2 ≥ 1` at `k=2`; `d=3,k=2`: `1` |
| `(eq:simplecalculus)` (T5) | `Σ_{b: \|b−a₁\|∧\|b−a₂\|>ρ} (\|a₁−b\|^{d−2}+1)^{−k}(λ/(\|a₂−b\|^{d−1}+1))^k ≤ C₅(d,k) (D^{d−2}+1)^{−k} λ^k ρ^{d−(d−1)k}`, `D = \|a₁−a₂\|`, `C₅(d,k) = 2(3·2^{2d−4})^k d2^d` (`6912` at `d=3,k=2`) | case `\|b−a₁\| ≥ \|b−a₂\|`: `\|a₁−b\| ≥ D/2`, factor `2^{(d−2)k}`, then tail sum over `\|b−a₂\|>ρ`; case `\|b−a₁\| < \|b−a₂\|`: `\|a₂−b\| ≥ D/2`, `y^{d−1}+1 ≥ (y^{d−2}+1)(y+1)/3`, `\|a₂−b\| ≥ \|a₁−b\|`, tail sum over `\|b−a₁\|>ρ`. `(d−1)k > d` is used exactly in the tail (`e ≥ 2`); fails at `k=1` (`e=0`: `Σ_{r>ρ} 1` grows like `L`) | ticket-literal form `λ = ℓ`: `ℓ^kρ^{d−(d−1)k} = ℓ^{d−(d−2)k} lw^{4(d−(d−1)k)} ≤ ℓ^{d−(d−2)k}` (`lw ≥ 1`, negative exponent), needs `ℓ ≤ ρ`. But BD1's numerator is `C_B w = C_B lw³ℓ`, not `ℓ`: S5-24 needs `λ = C_B w`. Candidate `T2165b` |
| Exponent count (T6) | per cluster `k = \|A\|`: `d−(d−2)k+(d+2)(k−1)+2 = 4k`; `∏_i w^{(d+3)k_i−d} ρ^{d−(d−1)k_i} = ℓ^{8p} lw^{dr+(13−d)·2p}` (`r` clusters, `Σk_i = 2p`) | `(d+3)k−d + d−(d−1)k = 4k`; `lw`-power `3((d+3)k−d)+4(d−(d−1)k) = d+(13−d)k`; `dr+(13−d)2p ≤ 26p` (`r ≤ p`, `d≥3`); `ℓ^{8p}/(D^{d−2}+1)^{2p} = (ℓ⁴/(D^{d−2}+1))^{2p}` | `d=3,p=1,r=1`: `lw^{23}`; the paper's `≺` hides `lw^{dr+(13−d)2p}`. Candidate `T2165c` |
| `d=2` tokens replaced | `Z2 L → Fin 2 → Zd d L`, `zdist2 → zdistInf` of first-label difference, `KLoop.card_ball_le`(`(2R+1)²`) `→ (2R+1)^d`, `cltFw`/`5+4 log L` (`cltm_sum_f_sq`, `cltm_double_sum`, `cltm_T2`: `d=2` log sums) `→` tail sum above | grep counts in `CltMoments.lean:45-700` @c9a24cf: `Z2` 52, `zdist2` 47, `cltFw` 34, `KLoop.card_ball_le` 3 | — |

### (ii) One concrete nondegenerate instance
Scripts in `$SP/T2165/` (`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad`). All hypotheses are deterministic; there is no external hypothesis (the only limit is `log W_n → ∞`, computed in script A at the merged data `szCL`, `Step5Pins.lean:640-715`).

Command: `cd $SP/T2165 && python3 t2.py`
```
== (A) merged data szCL (Step5Pins:640-715), n=34: L=2(n+24)^5, W=2^(n+24), lam=1, s=0, t=1-1/L^2, E=0 (m=i, Im m=1)
L=1312713536  log W=40.2025  ell_s=1.0  w=lw^3 ell=64977.1  rho=lw^4 ell=2612244.5  R=10w=649771.1  2R=1299542.1
  lw>=max(40,2d), 2dw<=rho, 40w<=rho, rho<L/2, w<L/2, 1<=ell_s<=rho: [True, True, True, True, True, True]
  regime (i): lam^2/L^2=1-t (equality); 1-s=1<=lam^2=1; kappa=1/2<=Im m=1.  slack: lw-40=0.2025 (n=33: 39.5094<40, so n>=34); rho/(40w)=1.0051; (L/2)/rho=251.3
== (B) small instance for the compiled examples: d=3, L=83, p=1 (n=2p=2), abstract scales w=1, rho=40 w=40, R=10 w=10, cluster radius 2R=20
 b0=((41, 41, 41), (41, 41, 42)): window 1<=w:True; far |b1-a1|=41>40:True, |b1-a2|=41>40:True
 b1=((36, 41, 41), (36, 41, 40)): window 1<=w:True; far |b1-a1|=41>40:True, |b1-a2|=41>40:True
 delta(0,1)=5: paired (<R=10): True; isolated in STCltIsoConcl sense (R<=delta): False; S=[0], phi=[0,0], member within 2R: True, r=1<=p=1, #structures<=(2p)^(2p)=4
 BD1 data: a=a2-b1=(42, 42, 43) |a|_inf=41>40, |a|_1=122; r=b1-b2=(0, 0, 82) |r|_1=1<=d*w=3 and <=|a|_1/2:True
 Theta data: g=1/2<=Lam=1, t=9/10, g^2/L^2=1/27556 = 3.629e-05 <= 1-t=1/10; m=i, ||m||=1, kappa=1/2<=1
 target 5 data: k=2, lambda=w=1, rho=40>=ell=1; (d-1)k=4>d=3: True; shell tail exponent (d-1)k-d=1
```
(`a₁ = 0`, `a₂ = (0,0,1)`.) The Lean statements take `(w, ρ)` as real parameters with hypotheses `2dw ≤ ρ`, `40w ≤ ρ`, `1 ≤ w`; the `lw`-form (`w = lw³ℓ`, `ρ = lw⁴ℓ`, `lw ≥ max(40,2d)`) is a corollary whose real-number instance is (A) (a far point exists only at `L > 2ρ ≈ 5.2e6`, so the compiled examples use (B), with merged `Theta` at `g=1/2, t=9/10, m=i`).

Command: `cd $SP/T2165 && python3 t1.py` (random `b` in `Z_L^3`, `n ∈ {2,4,6}`, `R ∈ {1,2,3}`; greedy maximal `2R`-separated `S`; checks `φ∘φ=φ`, partner of each fixed point, `δ(φ k,k) ≤ 2R`, `2r ≤ n`, and `Paired ⇔ ¬isolated`)
```
trials 200000: paired 5611 unpaired(=isolated) 194389 configs with a distance exactly R: 80554 violations 0
```
Command: `cd $SP/T2165 && python3 t45.py` (target 5 on `Z_L^3`, `a₁=0`, `s` is a stand-in for `lw`, used only for `ρ = s⁴ℓ`, `w = s³ℓ`; `L=63` uses 75 structured `a₂`, `L=31` all 816 up to symmetry)
```
target5 d=3, a1=0, worst over a2: tail-ratio=LHS/((D12^(d-2)+1)^-k lam^k rho^(d-(d-1)k)) (lam=s^3 l); paper-ratio=LHS/((D12^(d-2)+1)^-k l^d/l^((d-2)k)) (lam=l); rho=s^4 l; C5(k)=2(3*2^(2d-4))^k d 2^d
L=31 l_s=2 s=1.0 (#a2=816): k=2: tail 23.7 paper 23.7 (<=C5=6912: True); k=3: tail 5.156 paper 5.156 (<=C5=82944: True)
L=31 l_s=2 s=1.5 (#a2=816): k=2: tail 7.598 paper 1.501 (<=C5=6912: True); k=3: tail 6.039 paper 0.04655 (<=C5=82944: True)
L=31 l_s=4 s=1.0 (#a2=816): k=2: tail 27.99 paper 27.99 (<=C5=6912: True); k=3: tail 12.9 paper 12.9 (<=C5=82944: True)
L=31 l_s=4 s=1.5 (#a2=816): k=2: far region empty; k=3: far region empty
L=63 l_s=2 s=1.0 (#a2=75): k=2: tail 21.52 paper 21.52 (<=C5=6912: True); k=3: tail 4.992 paper 4.992 (<=C5=82944: True)
L=63 l_s=2 s=1.5 (#a2=75): k=2: tail 30.27 paper 5.979 (<=C5=6912: True); k=3: tail 19.7 paper 0.1518 (<=C5=82944: True)
L=63 l_s=4 s=1.0 (#a2=75): k=2: tail 27.71 paper 27.71 (<=C5=6912: True); k=3: tail 9.152 paper 9.152 (<=C5=82944: True)
L=63 l_s=4 s=1.5 (#a2=75): k=2: tail 8.739 paper 1.726 (<=C5=6912: True); k=3: tail 7.29 paper 0.05619 (<=C5=82944: True)
k=1 (fails): paper ratio LHS/(ell^2/(D12+1)) at a2=(L//4,0,0), l_s=2, s=1
L=31: ratio 121.6  (nonempty 1)
L=63: ratio 298.4  (nonempty 1)
L=127: ratio 649.3  (nonempty 1)
```
Command: `cd $SP/T2165 && python3 t4.py` (target 4: the sum factorises as `(|Ball|·Y_w)^{|A|−1}·Y_w`; with `2R = 20w ≥ 40 > L/2` the ball is the whole torus at these sizes, so the check is of the saturated case; `(p,|A|) ∈ {(1,2),(2,2),(2,3)}` all enter through `|A|` only)
```
target4 d=3: LHS=(|Ball_inf(2R)|*Y_w)^(|A|-1)*Y_w, Y_w=sum_{|x|<=w}1/(|x|^(d-2)+1), 2R=20w, w=l_s (s=1); bound w^((d+2)(|A|-1)+2); C4=(41^d)^(|A|-1)(2^(d-1)cs)^|A|
L=31 l_s=2 |Ball|=29791/29791 Y=46.67: |A|=2: 5.069e+05 <= 6.352e+08: True; |A|=3: 2.202e+10 <= 4.203e+15: True
L=31 l_s=4 |Ball|=29791/29791 Y=178.37: |A|=2: 5.785e+04 <= 6.352e+08: True; |A|=3: 3.002e+08 <= 4.203e+15: True
L=63 l_s=2 |Ball|=250047/250047 Y=46.67: |A|=2: 4.254e+06 <= 6.352e+08: True; |A|=3: 1.551e+12 <= 4.203e+15: True
L=63 l_s=4 |Ball|=250047/250047 Y=178.37: |A|=2: 4.855e+05 <= 6.352e+08: True; |A|=3: 2.115e+10 <= 4.203e+15: True
target 6: exponent identity d-(d-2)k+(d+2)(k-1)+2=4k (exact), and l_s / log W exponents of w^((d+3)k-d) rho^(d-(d-1)k), w=lw^3 l, rho=lw^4 l
identities hold (asserted) for d=3,4,5, k=2..8
all partitions of 2p into parts>=2, p=1,2,3: r<=p, sum of l_s exponents 4k_i = 8p: True ; log W exponent per cluster d+(13-d)k: k=2 -> 23 , total <= 13*2p
```

### Verdict
- Target 1 (clusters; `¬Paired ⇔` isolation): PASS (strict pairing; construction `2R`, not RBM2D's `3R`).
- Target 2 (weights): PASS (premises `3 ≤ d`, `3 ≤ L`, `0<g≤Λ`, regime `g²/L² ≤ 1−t`, `κ ≤ Im m`, `‖m‖=1`, `lw ≥ 2d`; BD1 premise `|r| ≤ ½|a|` holds).
- Target 3 (comparability): PASS (exact premise `40w ≤ ρ`, i.e. `lw ≥ 40`, independent of `p`).
- Target 4 (per-cluster sum): PASS.
- Target 5 (`(eq:simplecalculus)`): PASS in the general form `λ^kρ^{d−(d−1)k}`; the ticket-literal numerator `ℓ_s` follows only as the special case `λ = ℓ`, and S5-24 needs `λ = C_B lw³ℓ`.
- Target 6 (exponent count): PASS (explicit `lw^{dr+(13−d)2p}`).

## (b) Script output — Sun Oct  4 23:30:24 UTC 2026
Branch `t/T2165` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2165`), `git log --oneline -3`: `7587804` (docstring corrections), `d569a3b` (the module), `69b1099` (main). The only file changed is `RBM3D/Evolution/CltMoments1.lean` (`RBM3D/Test/Axioms.lean` and `RBM3D.lean` untouched):
```
$ git diff --stat main...t/T2165
 RBM3D/Evolution/CltMoments1.lean | 2128 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 2128 insertions(+)
$ lake build RBM3D.Evolution.CltMoments1 > build_mod.log; tail -2 build_mod.log; grep -c error build_mod.log; grep -c sorry build_mod.log
Build completed successfully (3815 jobs).
exit=0
0
0
$ (temporary `import RBM3D.Evolution.CltMoments1` in RBM3D.lean, reverted: `git status` clean) lake build > full_build.log
info: RBM3D.lean:212:0: axiom audit: 4909 theorems, 1725 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 0, owed 63, structural 19).
Build completed successfully (3937 jobs).
```
Axioms of 25 declarations (`#print axioms`); over all 59 public declarations: 55 with `[propext, Classical.choice, Quot.sound]`, 2 with `[propext, Quot.sound]`, 1 with `[propext]`, 1 (`CltMom1.Cluster`) with none:
```
[propext, Classical.choice, Quot.sound]: cltMom1_clusters, cltMom1_not_paired_iff, cltMom1_iso_hyp_iff, cltMom1_weight_a1, cltMom1_weight_a2, cltMom1_comparable, cltMom1_comparable_weights, cltMom1_cluster_sum, cltMom1_cluster_sum_C4, cltMom1_term_le, cltMom1_simplecalculus, cltMom1_simplecalculus_ell, cltMom1_exponent_count, cltMom1_exponent_count_eq, cltMom1_prod_exponent_exact, cltMom1_cluster_term_le, cltMom1_clusterSum_le, cltMom1_paired_moment_le, cltMom1_paired_sum_le, cltMom1_exists_cluster, cltMom1_card_cluster_le, cltMom1_b_paired
[propext, Quot.sound]: cltMom1_exponent_identity, cltMom1_exponent_nat
[propext]: cltMom1_cluster_inst
```
Target statements, extracted by script (`extract.py`: from the `theorem` line to the first line containing `:=`):
```
-- CltMoments1.lean:855
theorem cltMom1_clusters {p : ℕ} (hp : 1 ≤ p) {R : ℝ} (hR : 0 ≤ R)
    (b : Fin (2 * p) → (Fin 2 → Zd d L)) (hb : CltMom1.Paired R b) :
    ∃ φ : Fin (2 * p) → Fin (2 * p), CltMom1.Cluster φ ∧
      (∀ s, φ s = s → 2 ≤ (Finset.univ.filter fun k => φ k = s).card) ∧
      (CltMom1.free φ).card ≤ p ∧
      (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * R) ∧
      (∀ k, ((zdistInf d L ((b (φ k)) 0 - (b k) 0) : ℕ) : ℝ) ≤ 2 * (p : ℝ) * R) ∧
      ((((Finset.univ : Finset (Fin (2 * p) → Fin (2 * p))).filter
          (fun φ => CltMom1.Cluster φ)).card : ℝ) ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p)) := by
-- CltMoments1.lean:894
theorem cltMom1_iso_hyp_iff (sz : Sizes d) (n p : ℕ) (s : ℝ)
    (b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n))) :
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) ↔
      ¬ CltMom1.Paired (10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) b :=
-- CltMoments1.lean:938
theorem cltMom1_weight_a1 (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) a b‖ ≤
          C * (1 + 2 ^ (d - 1)) / (((zdistInf d L (a - b) : ℕ) : ℝ) ^ (d - 2) + 1) := by
-- CltMoments1.lean:973
theorem cltMom1_weight_a2 (d : ℕ) (Λ κ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
      ∀ a₂ b₁ b₂ : Zd d L, ∀ w ρ : ℝ, 2 * d * w ≤ ρ → ρ < ((zdistInf d L (a₂ - b₁) : ℕ) : ℝ) →
        ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ w →
        g ^ 2 * ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₂ a₂ -
            Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) b₁ a₂‖ ≤
          C * d * w / (((zdistInf d L (a₂ - b₁) : ℕ) : ℝ) ^ (d - 1) + 1) := by
-- CltMoments1.lean:1096
theorem cltMom1_comparable_weights {r ρ lam : ℝ} (hρ : 2 * r ≤ ρ) (hr0 : 0 ≤ r) (hlam : 0 ≤ lam)
    (a₁ a₂ b b' : Zd d L) (hb₁ : ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ))
    (hb₂ : ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)) (hbb' : ((zdistInf d L (b - b') : ℕ) : ℝ) ≤ r)
    (hd : 2 ≤ d) :
    (1 / (((zdistInf d L (a₁ - b') : ℕ) : ℝ) ^ (d - 2) + 1) ≤
        2 ^ d * (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ∧
      1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1) ≤
        2 ^ d * (1 / (((zdistInf d L (a₁ - b') : ℕ) : ℝ) ^ (d - 2) + 1))) ∧
    (lam / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1) ≤
        2 ^ d * (lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ∧
      lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1) ≤
        2 ^ d * (lam / (((zdistInf d L (a₂ - b') : ℕ) : ℝ) ^ (d - 1) + 1))) := by
-- CltMoments1.lean:1342
theorem cltMom1_cluster_sum_C4 (hd : 3 ≤ d) {w : ℝ} (hw : 1 ≤ w) (m : ℕ) (x : Zd d L) :
    ∑ b₂ : Zd d L, ∑ β : Fin m → (Fin 2 → Zd d L),
      CltMom1.G d L w (x - b₂) * ∏ k : Fin m,
        (if ((zdistInf d L ((β k) 0 - x) : ℕ) : ℝ) ≤ 20 * w then
          CltMom1.G d L w ((β k) 0 - (β k) 1) else 0) ≤
      (41 ^ d) ^ m * ((d : ℝ) * 4 ^ d) ^ (m + 1) * w ^ ((d + 2) * m + 2) :=
-- CltMoments1.lean:1536
theorem cltMom1_simplecalculus (hd : 3 ≤ d) {q : ℕ} (hq : 2 ≤ q) {ρ lam : ℝ} (hρ : 0 < ρ)
    (hlam : 0 ≤ lam) (a₁ a₂ : Zd d L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q *
        (lam / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q ≤
      (2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ q) *
        (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q * (lam ^ q / ρ ^ ((d - 1) * q - d)) := by
-- CltMoments1.lean:1622
theorem cltMom1_simplecalculus_ell (hd : 3 ≤ d) {q : ℕ} (hq : 2 ≤ q) {ρ ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (hℓρ : ℓ ≤ ρ) (a₁ a₂ : Zd d L) :
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L =>
        ρ < ((zdistInf d L (a₁ - b) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - b) : ℕ) : ℝ)),
      (1 / (((zdistInf d L (a₁ - b) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q *
        (ℓ / (((zdistInf d L (a₂ - b) : ℕ) : ℝ) ^ (d - 1) + 1)) ^ q ≤
      (2 * CltMom1.cs d * (3 * 2 ^ (2 * d - 3)) ^ q) *
        (1 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ q * (ℓ ^ d / (ℓ ^ (d - 2)) ^ q) := by
-- CltMoments1.lean:1664
theorem cltMom1_exponent_identity (d k : ℕ) :
    (d : ℤ) - ((d : ℤ) - 2) * k + ((d : ℤ) + 2) * ((k : ℤ) - 1) + 2 = 4 * k := by ring
-- CltMoments1.lean:1689
theorem cltMom1_exponent_count {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) {lw ℓ : ℝ} (hlw : 1 ≤ lw) (hℓ : 0 < ℓ) :
    (lw ^ 3 * ℓ) ^ ((m + 1) + ((d + 2) * m + 2)) / (lw ^ 4 * ℓ) ^ ((d - 1) * (m + 1) - d) ≤
      ℓ ^ (4 * (m + 1)) * lw ^ (12 * (m + 1)) := by
-- CltMoments1.lean:1879
theorem cltMom1_clusterSum_le (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz : ℝ} (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ)
    (hMz : 0 ≤ Mz) (a₁ a₂ : Zd d L) {z : (Fin 2 → Zd d L) → ℝ} (hz0 : ∀ β, 0 ≤ z β)
    (hzu : ∀ β β' : Fin 2 → Zd d L, 0 < z β →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      z β' ≤ CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) *
        CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1)) :
    CltMom1.clusterSum (2 * p) z (20 * (lw ^ 3 * ℓ)) ≤
      ((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
        ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
          (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p)) := by
```
Compiled nonempty instances (section 9; `d = 3`, `L = 83`, `p = 1`, `w = 1`, `ρ = 40`, `R = 10`, `a₁ = 0`, `a₂ = (0,0,1)`; `cltMom1_b` = `((41,41,41),(41,41,42))`, `((36,41,41),(36,41,40))`; `cltMom1_b_paired : Paired 10 cltMom1_b`); first line of each `example` (script `grep ^example`), all compiled in the build above:
```
-- :1980  example := cltMom1_clusters (d := 3) (L := 83) (p := 1) le_rfl (R := 10) (by norm_num) cltMom1_b cltMom1_b_paired
-- :1984  example : ¬ CltMom1.Paired (10 : ℝ)
-- :2001  example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom1_xi (0 : Zd 3 83) ![41, 41, 41]‖ ≤
-- :2008  example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom1_xi (![36, 41, 40] : Zd 3 83) cltMom1_a₂ -
-- :2023  example := cltMom1_comparable_weights (d := 3) (L := 83) (r := 20) (ρ := 40) (lam := 1) (by norm_num) (by norm_num)
-- :2037  example := cltMom1_cluster_sum_C4 (d := 3) (L := 83) (by norm_num) (w := 1) le_rfl 1 (0 : Zd 3 83)
-- :2040  example := cltMom1_simplecalculus (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (lam := 1)
-- [repair 1dde590] :2044  example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (ℓ := 1)
-- :2044  example : (Finset.univ.filter (fun b : Zd 3 83 =>
-- :2058  example := cltMom1_exponent_identity 3 2
-- :2060  example := cltMom1_exponent_nat (d := 3) (m := 1) (by norm_num) le_rfl
-- :2062  example := cltMom1_exponent_count (d := 3) (m := 1) (by norm_num) le_rfl (lw := 41) (ℓ := 1) (by norm_num) one_pos
-- :2065  example := cltMom1_exponent_count_eq (d := 3) (m := 1) (by norm_num) le_rfl (lw := 41) (ℓ := 1) (by norm_num) one_pos
-- :2067  example := cltMom1_prod_exponent_exact cltMom1_cluster_inst 3 (lw := 41) (ℓ := 1) (by norm_num)
-- :2069  example := cltMom1_scale_comparable (lw := 41) (ℓ := 1) (p := 1) (by norm_num) zero_le_one
-- :2071  example := cltMom1_scale_bd1 (d := 3) (lw := 41) (ℓ := 1) (by norm_num) zero_le_one
-- :2119  example := cltMom1_clusterSum_le (d := 3) (L := 83) (by norm_num) 1 (lw := 1) (ℓ := 1) (Mz := 1) le_rfl le_rfl
-- :2123  example := cltMom1_paired_moment_le (d := 3) (L := 83) (by norm_num) 1 (lw := 1) (ℓ := 1) (Mz := 1) le_rfl le_rfl
```
Name-clash grep (script: for each of the 59 new public names, `grep -rnw <name> RBM3D --include=*.lean --exclude=CltMoments1.lean`): `clashes: []`.
Ports (RBM2D, read-only): `git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/CltMoments.lean`:
```
 RBM2D/Evolution/CltMoments.lean | 240 ++++------------------------------------
 1 file changed, 24 insertions(+), 216 deletions(-)
```
Source used: `git show c9a24cf:RBM2D/Evolution/CltMoments.lean`, lines 72-73, 75-148, 150-166, 168-328, 333-388, 391-410, 690-694 (338 of the 656 lines of `section Combinatorics` `:45-700`), adapted (`Z2 L ↦ Fin 2 → Zd d L`, `zdist2 ↦ zdistInf` of first labels, `3R ↦ 2R`); remaining `Z2`/`zdist2` tokens in the file: 4, all in comments. RBM1D: nothing ported.

Narrative (facts as in the tool log above):
- Clusters (target 1): RBM2D's maximal separated set with nearest-point assignment (`cltMom1_exists_cluster`, `CltMoments1.lean:513`), separation `2R` instead of RBM2D's `3R`; not the paper's components of `|b₁^{(k)}-b₁^{(l)}| ≤ R`. Members lie within `2R ≤ 2pR`; `r ≤ p` from `cltMom1_two_mul_free_le`; `≤ (2p)^{2p}` structures from `cltMom1_card_cluster_le`.
- Not paired ⇔ isolated: `CltMom1.Paired R b` is strict (`< R`); `cltMom1_iso_hyp_iff` has on its left the hypothesis text of `STCltIsoConcl` (`Step5Pins.lean:420-421`) and is `(cltMom1_not_paired_iff _ _).symm`; so S5-24 splits the sum without a translation lemma. `cltMom1_paired_sum_le`: paired sum `≤ clusterSum n z (2R)`.
- Weights (target 2): `cltMom1_weight_a1` applies the public `meanFar_T1` (`MeanFar.lean:762`) to `T = Θ_t(0,·)` with `prop5Decay_holds` (`Prop5Hold.lean:784`); the zero-mode term `(L^d(1-t))⁻¹` is absorbed inside `meanFar_T1` by `g²/L² ≤ 1-t` (`zeroMode_le_of_ge`, `Defs/Tail.lean:119`), factor `1+2^{d-1}`; the shift `Θ_{ab} = Θ_{0,b-a}` is `Theta_apply_add_right_of_three_le` (`Props4.lean:100`).
- `cltMom1_weight_a2` applies `prop6Diff1_holds` (`Prop6Hold.lean:353`, `c = 1/2`) at `a = a₂-b₁`, `r = b₁-b₂`; its premise `|r|₁ ≤ ½|a|₁` follows from `|r|₁ ≤ d|r|_∞ ≤ dw` and `2dw ≤ ρ < |a|_∞ ≤ |a|₁`; `(prop:BD1)` has no zero-mode term and `g²(g²+|1-t|)⁻¹ ≤ 1`. `meanFar_core`, `meanFar_T2` are not used (mean part, `(prop:BD2)`).
- Comparability (target 3): factor `2^m ≤ 2^d` in both directions under `2r ≤ ρ < |a-b|`; `cltMom1_scale_comparable`: `2·(2pR) = 40 p w ≤ ρ` holds when `log W ≥ 40 p`, and for the cluster radius `2R` (`p = 1`) when `log W ≥ 40`; `cltMom1_scale_bd1`: `2dw ≤ ρ` holds when `log W ≥ 2d` (the converses are division by `w`, not formalized).
- Per-cluster sum (target 4): the sum over `m = |A|-1` further indices and the representative's second label is the explicit multi-sum of `cltMom1_cluster_sum`, bounded by `Y_w ((2R_b+1)^d Y_w)^m`, and by `(41^d)^m (d 4^d)^{m+1} w^{(d+2)m+2}` at `R_b = 20 w` (`cltMom1_cluster_sum_C4`). The shell count is re-proved from the private `meanFar_card_shell`, `meanFar_sum_shell` (`MeanFar.lean:89-187`) as `cltMom1_*`, because `Defs/Shells` counts `ℓ¹` spheres; of the imported modules only the one-dimensional counts `card_zdist_eq_le`, `card_zdist_le_le` of `Defs/Shells` are used, `Defs/RadialSum` is not.
- `(eq:simplecalculus)` (target 5): both cases `|a₁-b| ≷ |a₂-b|` are in `cltMom1_calc_point`; `(d-1)q > d` enters only in `cltMom1_tail_sum` (`E = (d-1)q-d ≥ 1` from `2 ≤ q`, `3 ≤ d`); the failure at `q = 1` is the preflight script output in (a) (ratios `121.6, 298.4, 649.3`), not re-derived. Constant `C = 2 cs (3·2^{2d-3})^q`, `cs = 2d·2^{d-1}`; general numerator `λ`, power `ρ^{-((d-1)q-d)}`; the ticket-literal `ℓ^d/(ℓ^{d-2})^q` form needs `ℓ ≤ ρ` (`cltMom1_simplecalculus_ell`).
- Exponent count (target 6): `cltMom1_exponent_identity` (`ring`); `cltMom1_exponent_count_eq`: cluster factor `= ℓ^{4|A|} lw^{d+(13-d)|A|}`; `cltMom1_exponent_count`: `≤ ℓ^{4|A|} lw^{12|A|}`; `cltMom1_prod_exponent_exact`: product over clusters `= ℓ^{8p} lw^{dr+(13-d)2p}`; total log factor `lw^{24p}` in `cltMom1_clusterSum_le` ((a) states `≤ lw^{26p}`; the Lean bound is sharper).
- Assembly: `cltMom1_clusterSum_le` / `cltMom1_paired_moment_le` reduce S5-24's paired part to the hypothesis `hzu` (`z β' ≤ u(β₁) G_w(β₁'-β₂')` for `z β > 0`, `|β₁-β₁'| ≤ 20 w`), which S5-24 derives from targets 2, 3 and `(eq:propcalB)`; the instance has `z` = point mass of value `c > 0` (`cltMom1_c_pos`).
- Registry: `RBM3D/Test/Axioms.lean` unchanged. `CltMom1.Cluster` is a `Prop` def assumed by theorems; a scratch `#assert_rbm_axioms` on the module closure listed it among the unregistered premises before the witness theorem `cltMom1_cluster_inst` was added and not after; `Paired` is witnessed by `cltMom1_b_paired`. The full build with the temporary import passes the audit (above).
- §29: (5) everything is deterministic (no `Prec`); (6) premises written in the statements: `3 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `g²/L² ≤ 1-t`, `1 ≤ lw`, `1 ≤ ℓ`, `2dw ≤ ρ`, `2r ≤ ρ`; of `1 ≤ ℓ_s ≤ ℓ_t` only `1 ≤ ℓ_s` is used; (7) all distances are `zdistInf`; the weights are written with `a - b`, `STfFar` with `b - a` (`cltMom1_zdistInf_sub_comm`).
- Section (a) is not edited and needs no (a′): its constants are estimates; the Lean constants are `C_T = C₅(1+2^{d-1})`, `C₄ = (41^d)^m (d 4^d)^{m+1}`, `C(d,q) = 2 cs (3·2^{2d-3})^q`. File size 2128 lines (portmap estimate 1300).

## (c) Verified Mathlib names (`#check`, script `names_check.lean`; all used in the file)
- `pow_add_pow_le : 0 ≤ x → 0 ≤ y → n ≠ 0 → x ^ n + y ^ n ≤ (x + y) ^ n` (profile `r^m + 1 ≤ (r+1)^m`)
- `piFinTwoEquiv`, `Fintype.sum_equiv`, `Fintype.sum_prod_type` (two-label sums `Fin 2 → Zd d L ≃ Zd d L × Zd d L`)
- `Finset.prod_univ_sum`, `Fintype.piFinset_univ`, `Finset.prod_pow_eq_pow_sum` (product of sums, cluster product)
- `Finset.exists_max_image`, `Finset.exists_min_image`, `Finset.card_insert_of_notMem`, `Finset.card_pair` (cluster construction)
- `Finset.card_eq_sum_card_fiberwise`, `Finset.sum_fiberwise_of_maps_to`, `Finset.prod_fiberwise_of_maps_to`, `Finset.single_le_sum`
- `Nat.floor_lt`, `Nat.lt_floor_add_one`, `Nat.le_floor`, `Nat.floor_le` (tail sum, ball counts)
- `one_div_pow`, `one_div_le_one_div_of_le`, `div_le_div_of_nonneg_left`, `div_le_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`
- `pow_le_pow_left₀`, `pow_le_pow_right₀`, `pow_le_one₀`, `one_le_pow₀`
- `zpow_sub₀`, `zpow_add₀`, `zpow_natCast` (exact exponents of target 6); `sub_add_sub_cancel`, `Equiv.subLeft`, `Equiv.subRight`
- Verified absent: `Equiv.piFinTwo` (use `piFinTwoEquiv`), `zpow_sum` (proved by induction in `cltMom1_prod_exponent_exact`), `Finset.sum_Ico_inv_sq_le` (the telescoping tail `cltMom1_tail_inv_sq` is proved by induction).

## (d) Open issues and paper-delta candidates
- `T2165a`: `(eq:pairingcond)` is `≤` in the paper, strict `<` here (the exact complement of `(eq:bound_isolated)`'s `≥`, which overlap at equality); the clusters are a `2R`-separated cover with nearest-point assignment (members within `2R`), not components.
- `T2165b`: the numerator of the weight at `a₂` is `C₆ d (log W)³ ℓ_s` (the window), not `ℓ_s`; `(eq:simplecalculus)` holds with `λ^q ρ^{-((d-1)q-d)}`, and with `ℓ^d/(ℓ^{d-2})^q` when `ℓ ≤ ρ` (`log W ≥ 1`).
- `T2165c`: the `≺` of `(eq:2p_product_pair)` hides `lw^{d+(13-d)|A|} ≤ lw^{12|A|}` per cluster, `lw^{24p}` in total (explicit in `cltMom1_clusterSum_le`).
- `T2165d`: scale premises: comparability is guaranteed by `log W ≥ 40` for radius `2R` (`≥ 40 p` for `2pR`), `(prop:BD1)` by `log W ≥ 2d` (D368 form); the Lean statements carry them as `2r ≤ ρ`, `2dw ≤ ρ`.
- For S5-24: supply `hzu` of `cltMom1_clusterSum_le` (weights `cltMom1_weight_a1/a2` with `λ = w`, comparability `cltMom1_comparable_weights` at the representative, which must be far), the constant `M`, and the isolated part from `stCltIso_holds`; the factor `lw^{24p}` is absorbed by `N^τ`.
- Not claimed: the failure of target 5 at `q = 1` is a remark (evidence: (a)), not a Lean statement; no claim of this ticket was found false.
- Merge: the hub adds `import RBM3D.Evolution.CltMoments1` to `RBM3D.lean` (not done here).

## Repair — Sun Oct  4 23:36:02 UTC 2026
Repairer model: claude-opus-5-5
Audit round 1 (`docs/reports/T2165-audit.md`) RETURN item 1: the ticket-literal endpoint `cltMom1_simplecalculus_ell` had no compiled instance. Added one `example` in section 9 (commit `1dde590` on `t/T2165`); nothing else in the file changed. The line marked `[repair 1dde590]` in the (b) instance list is that example; the other line numbers in (b) refer to `7587804` (from `:2044` on they are now `+4`, listing below).
```
$ git diff --stat 7587804 1dde590
 RBM3D/Evolution/CltMoments1.lean | 4 ++++
 1 file changed, 4 insertions(+)
$ git diff 7587804 1dde590 | grep "^[+-][^+-]"
+/-- **Instance of target 5, ticket-literal form** (`q = k = 2`, `ρ = 40`, `ℓ = 1`, `a₁ = 0`, `a₂ = (0,0,1)`). -/
+example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q := 2) le_rfl (ρ := 40) (ℓ := 1)
+  le_rfl (by norm_num) (0 : Zd 3 83) cltMom1_a₂
$ lake build RBM3D.Evolution.CltMoments1 ; echo exit=$?   (tail; error count)
Build completed successfully (3815 jobs).
exit=0
errors: 0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Evolution/CltMoments1.lean | wc -l
0
$ grep -n "^example" RBM3D/Evolution/CltMoments1.lean   (at 1dde590)
1980:example := cltMom1_clusters (d := 3) (L := 83) (p := 1) le_rfl (R := 10) (b
1984:example : ¬ CltMom1.Paired (10 : ℝ)
2001:example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom
2008:example : ∃ C : ℝ, 0 < C ∧ (1 / 2 : ℝ) ^ 2 * ‖Theta 3 83 (1 / 2 : ℝ) cltMom
2023:example := cltMom1_comparable_weights (d := 3) (L := 83) (r := 20) (ρ := 40
2037:example := cltMom1_cluster_sum_C4 (d := 3) (L := 83) (by norm_num) (w := 1)
2040:example := cltMom1_simplecalculus (d := 3) (L := 83) (by norm_num) (q := 2)
2044:example := cltMom1_simplecalculus_ell (d := 3) (L := 83) (by norm_num) (q :
2048:example : (Finset.univ.filter (fun b : Zd 3 83 =>
2062:example := cltMom1_exponent_identity 3 2
2064:example := cltMom1_exponent_nat (d := 3) (m := 1) (by norm_num) le_rfl
2066:example := cltMom1_exponent_count (d := 3) (m := 1) (by norm_num) le_rfl (l
2069:example := cltMom1_exponent_count_eq (d := 3) (m := 1) (by norm_num) le_rfl
2071:example := cltMom1_prod_exponent_exact cltMom1_cluster_inst 3 (lw := 41) (ℓ
2073:example := cltMom1_scale_comparable (lw := 41) (ℓ := 1) (p := 1) (by norm_n
2075:example := cltMom1_scale_bd1 (d := 3) (lw := 41) (ℓ := 1) (by norm_num) zer
2123:example := cltMom1_clusterSum_le (d := 3) (L := 83) (by norm_num) 1 (lw := 
2127:example := cltMom1_paired_moment_le (d := 3) (L := 83) (by norm_num) 1 (lw 
```

