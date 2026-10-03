Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 14:20:21 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `g = sz.lam n`, `Λ = 𝔡⁻¹`, `K = 1/𝔠`, `ε<1`. Pins: `EKSumDecay1/NAL/2/Nonzero` (`RBM3D/Evolution/Pins.lean:76-137`); all four carry `0 ≤ s` (resp. `0 ≤ t`) in the window and the PT antecedents need `0 ≤ t < 1` (`RBM3D/Propagator/Pins.lean:35-95`).

### (i) Exponent table

| # | quantity | value / choice | constraint | slack |
|---|---|---|---|---|
| 1 | `C` (pin 1/NAL/2) | from pin, depends on `(d,n_,Λ[,κ,K])` only, before `ε,D` | `C>0` | — |
| 2 | `ε` | `min(1/2, τd/(4C))` | `0<ε<1`; `Cε/d ≤ τ/4` | `ε ≤ 1/2 <1`; equality in 2nd constraint when `τd/(4C)<1/2` |
| 3 | `W^{Cε} ≤ N^{τ/4}` | via `W ≤ N^{1/d}` (`W^x ≤ N^{x/d}`) | `Cε/d ≤ τ/4` | 0 (tight, by choice of ε) |
| 4 | `D₀` (the pin's `D`) | `C+1+D/𝔠` | `D₀>1` | `C + D/𝔠 > 0` |
| 5 | `W^{-D₀+C}=W^{-(1+D/𝔠)} ≤ N^{-D}` | via `W ≥ N^𝔠`, exponent `-𝔠(1+D/𝔠) = -𝔠-D` | `-𝔠-D ≤ -D` | `𝔠>0` |
| 6 | `N^{τ/4}·N^{τ/4} ≤ N^τ` | `N ≥ 1` | `τ/2 ≤ τ` | `τ/2` |
| 7 | `4 ≤ W^ε` | `W^ε ≥ N^{𝔠ε}`, `N→∞` | `N ≥ 4^{1/(𝔠ε)}` | eventual (numbers in (ii)) |
| 8 | `1<W` | from row 7 (`W^ε ≥ 4`, `ε>0`) | — | `W^ε ≥ 4` |
| 9 | `L^d ≤ W^K`, `K=1/𝔠` | `L^d ≤ N` (`W≥1`), `N ≤ W^{1/𝔠}` (`N^𝔠 ≤ W`) | `Admissible 𝔠 𝔡` (Bandwidth) | `W^K/L^d ≥ W^K/N ≥ 1`; at sz0 `(2m)^30/(4m)^3` |
| 10 | `log L ≤ W^ε` (Res2 only) | `log L = (1/d) log L^d ≤ (K/d) log W ≤ (2K/(dε)) W^{ε/2}` (`log y ≤ y^a/a`) | suffices `W^{ε/2} ≥ 2K/(dε)` (`=4/ε` at `K=6,d=3`) | eventual, `W ≥ N^𝔠 → ∞`; sufficient bound is much larger than the true threshold (see (ii)) |
| 11 | `0<g ≤ Λ` | `WO`: `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` eventually, `W^{-d/2+𝔡}>0` | eventual | — |
| 12 | `W⁻¹ ≤ (1-t)/(1-v)`, `v ∈ [s,t]` | `STEKWin` gives `W⁻¹ ≤ (1-t)/(1-s) ≤ (1-t)/(1-v)` | `1-v ≤ 1-s`, `1-t>0` | factor `(1-s)/(1-v) ≥ 1` |
| 13 | `0 ≤ v`, `v ≤ t ≤ 1-g²/L²` | `STEKWin`: `0 ≤ s ≤ v ≤ t` | — | `1-g²/L²-t ≥ 0` |
| 14 | `ratio ≥ 1` (Res1/NAL/Res2) | `(g²+|1-v|)/(g²+|1-t|) ≥ 1` since `|1-t| ≤ |1-v|`; Res1 also `ellT_t ≥ ellT_v` (`ellT = min(max(g/√|1-·|,1),L)`, `|1-t|≤|1-v|`), so `ellT_t²/ellT_v² ≥ 1` | `X ≥ N^{-b}` absorbs `W^{-D₀+C}` (`of_highProbAt_add_rpow_neg`) | — |
| 15 | Nonzero: `C‖𝒜‖ ≺ X` | `C ≤ N^{τ/2}` eventually, `‖𝒜‖ ≤ N^{τ/2}X` w.h.p. | `N → ∞` | `τ/2` |
| 16 | **Nonzero: `0 ≤ s`** | pin `EKSumDecayNonzero` needs `0 ≤ s`; Props 5s, 8 need `0 ≤ t < 1` | **not a hypothesis of `STEKNonzero`**; implied only if `g ≤ L` (`1-g²/L² ≥ 0`) | `Admissible` gives only `g ≤ 𝔡⁻¹` eventually and `L ≥ 3` (not `g ≤ L`): **slack negative** |

Rows 1-14 close for `STEKSumNdecay` (rows 11 only for `g>0`), `STEKSumRes1`, `STEKSumRes2NAL`, `STEKSumRes2`. Row 16 does not close for `STEKNonzero`.

### (ii) Concrete instance, and the instance-data check

Eventual thresholds `n_0` (smallest `n` from which the hypothesis holds for all larger `n`, bisection on the log scale, checked to `n = 10^70`) at `sz0` (`L=4(n+1), W=(2(n+1))^5, g=(2(n+1))^{-6}`, `d=3, 𝔠=1/6, 𝔡=1/10`, `(s,t)=(0,1/16)`) and `szB` (`L=4, W=n+4, g=1`, same `𝔠,𝔡`, `(s,t)=(7/8,15/16)`), `K=6`, `Λ=10`:
```
$ python3 scratchpad/T2053/thr.py   (sz0, szB; eps in {1/10, 1/100})
sz0 eps=0.1  n0: 4<=W^eps:7  logL<=W^eps:3  L^d<=W^K:0  1/W<=(1-t)/(1-s):0  t<=1-g^2/L^2:0  0<g<=1/dd:0  W>=N^c:0
sz0 eps=0.01 n0: 4<=W^eps:549755813887  logL<=W^eps:7.39e38  L^d<=W^K:0  [rest 0]
szB eps=0.1  n0: 4<=W^eps:1048572  logL<=W^eps:23  [rest 0]
szB eps=0.01 n0: 4<=W^eps:1.6069e60 (=2^200-4)  logL<=W^eps:1.53e14  [rest 0]
```
(`4 ≤ W^ε` at sz0 is exactly `2(n+1) ≥ 4^{1/(5ε)}`: `n_0 = 7 (=4^2/2-1)`, `2^39-1 = 549755813887`.) The thresholds are eventual, so the theorems do not need them; the instances of stage 1b keep every deterministic hypothesis (`Admissible`, `STEKWin` incl. its `∀ᶠ`, `κ ≤ Im m`, `EKSumZero`) discharged at all `n`.

Window check of the ticket's instance data (exact fractions):
```
$ python3 scratchpad/T2053/win.py
sz0@n=0  (s,t)=(0,1/16):      STEKWin=True   STEKNonzero-window(1-g^2/L^2<=s)=False  (1-g^2/L^2=65535/65536)
szB      (s,t)=(7/8,15/16):   STEKWin=True   STEKNonzero-window=False
szB      (s,t)=(15/16,31/32): STEKWin=False  STEKNonzero-window=True   (1-g^2/L^2=15/16)
szB window ratio (1-t)/(1-s) at (7/8,15/16): 1/2 >= 1/W for every W>=2
```
So the ticket's "each theorem at `(sz0,sInst,tInst)` and `(szB,15/16,31/32)`" cannot hold uniformly: `STEKSumRes1/NAL/Res2` need case (i): use `(sz0,0,1/16)` and `(szB,7/8,15/16)` (`t = 1-g²/L²` boundary, `STEKWin` holds); `STEKSumNdecay` has no window and works at both; `STEKNonzero` needs case (ii): only `(szB,15/16,31/32)` (`s = 1-g²/L²`), not `sz0` with `s≡0`.

Counterexample to `STEKNonzero` as stated (row 16). Data: `d=3, n_=2, κ=1/2`, `L≡4`, `W_n=n+4`, `g≡50`, `𝔠=1/6`, `𝔡=1/100` (`Admissible`: `W ≥ N^{1/6}` since `N^{1/6}=(4(n+4))^{1/2} ≤ n+4`; `W^{-3/2+1/100} ≤ 50 ≤ 100`), `m=i`, `σ=(+,-)` (`cycProd = m·m̄ = 1` at both indices), `A=univ`. Here `1-g²/L² = -155.25`, so `s_n = -3/2` satisfies `1-g²/L² ≤ s_n`, `s_n ≤ t_n < 1` with `t_n = (1-δ_n)/λ`, `λ = (1-6g²)/(1+6g²)` (exact least eigenvalue of `S^(B)(g)`, eigenvector the checkerboard `f=(-1)^{x₁+x₂+x₃}`, `f ⟂ 1`), `δ_n = e^{-N_n}`. `𝒜 = f⊗f`, `X ≡ 1` (so `‖𝒜‖ ≺ X` by `prec_of_le`); `Q^{(A)}f⊗f = f⊗f`, `U_{v,t}(f⊗f) = ((1-vλ)/(1-tλ))² f⊗f` and at `v=s_n`: `1-tλ = δ_n`, so `‖Q U 𝒜‖ ≈ (0.5/δ_n)² ≫ N^τ` for every `τ`; `seqP` is a probability measure, so the bad set has probability `1`.
```
$ python3 scratchpad/T2053/cex.py
row sums ok: True  symmetric: True
lam_min = -0.9998666755549632  closed form -0.999866675554963
f orthogonal to constants: True
1-g^2/L^2 = -155.25
delta=0.001 t=-0.99913321 (s<=t<1: True, s>=1-g^2/L^2: True) per index=4.998e+02, two indices=2.498e+05
delta=1e-06 t=-1.00013234 (s<=t<1: True, s>=1-g^2/L^2: True) per index=4.998e+05, two indices=2.498e+11
delta=1e-09 t=-1.00013334 (s<=t<1: True, s>=1-g^2/L^2: True) per index=4.998e+08, two indices=2.498e+17
```
(`t_n<0`: the pins' `0 ≤ s` is exactly what excludes this.) The nonvacuous hypothesis set above satisfies every hypothesis of `STEKNonzero`, so the conclusion is false: the statement needs `(∀ n, 0 ≤ s n)` (as `STEKSumNdecay` and `STEKWin` have). With `0 ≤ s` added, rows 11-15 close and the derivation is `ekSumDecayNonzero_holds` + `StochDomAt.mul` with the constant `C`.

### Verdicts
- `stek_sumNdecay_holds`: PASS (probe `3c58211` compiled; window-free; instance at `(sz0,0,1/16)` and `(szB,15/16,31/32)`).
- `stek_sumRes1_holds`, `stek_sumRes2NAL_holds`, `stek_sumRes2_holds`: PASS (rows 1-14 close), instance data to be `(sz0,0,1/16)` and `(szB,7/8,15/16)`, not `(szB,15/16,31/32)` (`STEKWin` fails there: `t=31/32 > 1-g²/L²=15/16`).
- `stek_nonzero_holds`: **FAIL** — `STEKNonzero d` is false as stated (no `0 ≤ s n`; counterexample above). Per the ticket ("if one is false or unprovable as stated, stop and report"): dispatcher must amend `Step34Pins.lean` (add `(∀ n, 0 ≤ s n) →`) or the ticket. Instance would then be `(szB,15/16,31/32)` only.

Overall verdict: FAIL.

## (a, round 2) Math preflight under Amend 1 — Sat Oct  3 18:53:50 UTC 2026

Amended pin: `STEKNonzero` window `(∀ n, 1-g²/L² ≤ s n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1)` (Amend 1, DECISIONS §27). Rows 1-15 above are unchanged (the round-1 text stays). Merged uses of the pin: `grep -rn STEKNonzero RBM3D` finds only its definition (`Step34Pins.lean:665`), so no merged instance or theorem in that file is broken by the edit.

### (i) Row 16, redone

| # | quantity | value / choice | constraint | slack |
|---|---|---|---|---|
| 16 | Nonzero: `0 ≤ s` | now a hypothesis `(∀ n, 0 ≤ s n)` | `EKSumDecayNonzero` needs `0 ≤ s` (`Evolution/Pins.lean:131`); `prop5Short_holds`, `prop8ZeroMode_holds` need `0 ≤ t < 1` at the time argument | closes: for `v ∈ [s n, t n]`, `0 ≤ s n ≤ v`, `1-g²/L² ≤ s n ≤ v`, `v ≤ t n < 1`, so `(v, t n)` satisfies the pin's window `0 ≤ s'`, `1-g²/L² ≤ s' ≤ t' < 1` |
| 16a | `0<g≤Λ=𝔡⁻¹` (pin) | `Admissible` gives `WO`: eventual | eventual (finite many `n` need no bound: `Prec` is eventual) | — |
| 16b | `C` (pin Nonzero) | `C` depends on `(d,n_,Λ,κ)` only | `C ≤ N^{τ/2}` once `N` large | row 15 unchanged |

Four-point check (DECISIONS §29) for the amended pin: (1) `0 ≤ s`, `t<1` are hypotheses; (2) window boundary `1-g²/L²` may be negative (`g>L`), then the window is `[0,t]`, nonempty (script below: `s=0,t=1/2` at `L=4,g=50`); (3) the pin does not use `L^d ≤ W^K`; (4) `∀ n` window conditions are all in the hypotheses, the size conditions `0<g≤Λ` are eventual. No further defect found.

### (ii) Amended instance list, checked
```
$ python3 scratchpad/T2053/amend.py
Nonzero amended-window at the amended instance: True
Nonzero amended-window at old cex s=-3/2, t=-1+: False
cex window nonempty with 0<=s (s=0,t=1/2): True  1-g^2/L^2 = -621/4
STEKWin sz0@n=0 (0,1/16): True; (1-t)/(1-s)=15/16 >= 1/W for all W>= 16/15
STEKWin szB (7/8,15/16): True; (1-t)/(1-s)=1/2 >= 1/W for all W>= 2
Ndecay window 0<=s<=t<1 at sz0@n=0 (0,1/16): True
Ndecay window 0<=s<=t<1 at szB (7/8,15/16): True
Ndecay window 0<=s<=t<1 at szB (15/16,31/32): True
szB g=1 in (0,10]: True ; sz0 g_n=(2(n+1))^-6 in (0,1/64] <=10: True
```
(`sz0@n=0` is the smallest `L`, largest `g` of `sz0`, so the window checks hold for all `n`; `szB` has constant `L=4, g=1`.) Round-1 `win.py` output above gives the same `STEKWin`/Nonzero-window values. The Amend-1 instances: Res1/NAL/Res2 and Ndecay at `(sz0,0,1/16)`, `(szB,7/8,15/16)`; Nonzero at `(szB,15/16,31/32)` (`1-g²/L²=15/16 ≤ s`, `0 ≤ s`); Ndecay also at `(szB,15/16,31/32)`. Eventual thresholds `n_0` of round 1 (ε ∈ {1/10, 1/100}) are unchanged. The round-1 counterexample (`s=-3/2`) violates the new hypothesis `0 ≤ s` (row 2 of the output); with `0 ≤ s` the pin follows from `ekSumDecayNonzero_holds` (rows 11-15).

### Verdicts (amended ticket)
- `stek_sumNdecay_holds`, `stek_sumRes1_holds`, `stek_sumRes2NAL_holds`, `stek_sumRes2_holds`: PASS (unchanged).
- `stek_nonzero_holds`: PASS (row 16 closes under Amend 1).

Overall verdict: PASS.

## (b) Script output and narrative — stage 1b, Sat Oct  3 19:08:45 UTC 2026
```
$ git log -1 --format="%h %an: %s" t/T2053 ; git merge-base t/T2053 main ; git diff --name-only main...t/T2053
6270281 Jun Yin: T2053: EK-6 evolution-kernel lemmas at scale N (Evolution/Prec) and STEKNonzero 0 <= s (Amend 1)
6ef5d4921fdf
RBM3D/Evolution/Prec.lean
RBM3D/Induction/Step34Pins.lean
$ lake build RBM3D.Evolution.Prec 2>&1 | tail -2 ; grep -c "Prec.lean" (same log)
exit 0
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3706 jobs).
0
$ lake build 2>&1 | tail -2 ; echo exit   (full, worktree, run before the commit; Prec has no root import until the hub merges, see the pre-check)
Build completed successfully (3770 jobs).
exit 0
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Evolution.Prec; #assert_rbm_axioms)
exit 0
axiom audit: 1772 theorems, 810 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 5 borrowed + 43 owed + 25 structural; 22 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ lake env lean axioms.lean   (#print axioms of the five targets; #check)
'RBM.Gauss.Sizes.stek_sumNdecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes2NAL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_nonzero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
stek_sumNdecay_holds : ∀ (d : ℕ), STEKSumNdecay d
stek_sumRes1_holds : ∀ (d : ℕ), STEKSumRes1 d
stek_sumRes2NAL_holds : ∀ (d : ℕ), STEKSumRes2NAL d
stek_sumRes2_holds : ∀ (d : ℕ), STEKSumRes2 d
stek_nonzero_holds : ∀ (d : ℕ), STEKNonzero d
$ grep -n "^theorem stek_" RBM3D/Evolution/Prec.lean
215:theorem stek_sumNdecay_holds (d : ℕ) : STEKSumNdecay d := by
242:theorem stek_sumRes2NAL_holds (d : ℕ) : STEKSumRes2NAL d := by
358:theorem stek_sumRes1_holds (d : ℕ) : STEKSumRes1 d := by
391:theorem stek_sumRes2_holds (d : ℕ) : STEKSumRes2 d := by
422:theorem stek_nonzero_holds (d : ℕ) : STEKNonzero d := by
$ diff <(git show 3c58211:RBM3D/Probe/T2041Pins.lean | sed -n 691,830p | sed "s/stek_sumNdecay (d/stek_sumNdecay_holds (d/; s/stek_sumRes2NAL (d/stek_sumRes2NAL_holds (d/") <(sed -n 215,354p RBM3D/Evolution/Prec.lean); echo "diff exit $?"
diff exit 0
$ git diff main...t/T2053 -- RBM3D/Induction/Step34Pins.lean | grep "^[+-]" | cut -c1-175
-bulk `κ ≤ Im m` (both charges): `‖Q^{(A)}∘U_{v,t,σ}∘𝒜_v‖_∞ ≺ X` from `‖𝒜_v‖_∞ ≺ X` (no decay hypothesis). -/
+bulk `κ ≤ Im m` (both charges): `‖Q^{(A)}∘U_{v,t,σ}∘𝒜_v‖_∞ ≺ X` from `‖𝒜_v‖_∞ ≺ X` (no decay hypothesis).
+The window carries `0 ≤ s` (DECISIONS §27, T2053 Amend 1): without it `ilambda > L` lets `[s,t]` reach negative times. -/
-    ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
+    ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
$ grep -rn "STEKNonzero\|STEKSum" RBM3D --include=*.lean | grep -v "Step34Pins.lean\|Evolution/Prec.lean"  (in worktree, then in main)
(no output)
$ name clash: grep -rnE "stek_(sumNdecay|sumRes1|sumRes2NAL|sumRes2|nonzero)_holds|prec_core|prec_lam_bounds|prec_W_rpow_ge|prec_one_lt_W|prec_L_pow_le|prec_log_le|prec_window|prec_ratio_ge_one|PrecInst" RBM3D RBM3D.lean --include=*.lean | grep -v "^RBM3D/Evolution/Prec.lean"  (worktree, then main)
(no output)
$ no RBM1D/RBM2D port: the sources are the T2041 probe (3c58211) lines 684-832; no ../RBM1D or ../RBM2D file was read
```

Compiled nonempty instances (`sed -n 588,656p RBM3D/Evolution/Prec.lean`, blank lines and section comments dropped; `win_*`, `decay_*`, `low_one`, `prec_*`, `Az*` are private theorems of section 4 of the same file):
```
example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible sInst tInst
  (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num) (fun n => by simp only [tInst]; norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 sz0 sInst tInst)
example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) (fun n => by norm_num) (fun n => by norm_num) (fun n => by norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB (fun _ => 7 / 8) (fun _ => 15 / 16))
example := stek_sumNdecay_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num) (fun n => by norm_num) (fun n => by norm_num)
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB (fun _ => 15 / 16) (fun _ => 31 / 32))
example := stek_sumRes1_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible sInst tInst win_sz0
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (decay_delta0 sz0 sInst tInst)
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_delta0 sz0 sInst tInst)
example := stek_sumRes1_holds 3 le_rfl 2 le_rfl (1 / 6) (1 / 10) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I
  (fun _ => Complex.I) (fun _ => Complex.norm_I) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (decay_delta0 szB _ _)
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_delta0 szB _ _)
example := stek_sumRes2NAL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  sInst tInst win_sz0 (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, true] ⟨0, by decide⟩
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (decay_delta0 sz0 sInst tInst)
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_delta0 sz0 sInst tInst)
example := stek_sumRes2NAL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, true] ⟨0, by decide⟩
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (decay_delta0 szB _ _)
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_delta0 szB _ _)
example := stek_sumRes2_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  sInst tInst win_sz0 (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im) ![true, false]
  (fun n _ _ => Az (sz0.L n)) (decay_Az sz0 (by norm_num) sz0_tendsto sz0_bandwidth sInst tInst)
  (fun n _ _ => Az_sumZero (sz0.L n))
  (fun _ _ _ => (1 : ℝ)) (low_one sz0 sInst tInst) (prec_Az sz0 sInst tInst)
example := stek_sumRes2_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 7 / 8) (fun _ => 15 / 16) win_szB_I (fun _ => Complex.I) (fun _ => Complex.norm_I) (fun _ => I_im)
  ![true, false]
  (fun n _ _ => Az (szB.L n)) (decay_Az szB (by norm_num) szB_tendsto szB_bandwidth _ _)
  (fun n _ _ => Az_sumZero (szB.L n))
  (fun _ _ _ => (1 : ℝ)) (low_one szB _ _) (prec_Az szB _ _)
example := stek_nonzero_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) szB szB_admissible
  (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num [szB]) (fun n => by norm_num)
  (fun n => by norm_num) (fun n => by norm_num) (fun _ => Complex.I) (fun _ => Complex.norm_I)
  (fun _ => I_im) ![true, false] Finset.univ (fun i _ => Finset.mem_univ i)
  (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (prec_delta0 szB _ _)
```

Narrative (facts as in the script output above):
1. `RBM3D/Evolution/Prec.lean` (657 lines, namespace `RBM.Gauss.Sizes`) proves the five targets; each type is exactly `(d : ℕ) : STEK… d` (`#check` above). Imports: `Step34Pins`, `Evolution.{SumDecay,SumDecayZero,Nonzero}`, `Propagator.Prop6Hold`.
2. `stek_sumNdecay_holds` and `stek_sumRes2NAL_holds` are the probe's `stek_sumNdecay`, `stek_sumRes2NAL` (lines 691-830): the script diff shows no difference after the two renames.
3. `prec_core` (private) is the NAL absorption step, abstracted: from the pin shape `f ≤ W^{Cε} ρ ‖𝒜‖ + W^{-D₀+C}` (eventually, each `ε ∈ (0,1)`, `D₀ > 1`) and `ρ ≥ 1` eventually it gives `f ≺ ρ X`, with `ε = min(1/2, τd/(4C))`, `D₀ = C+1+D/𝔠` ((a) rows 2-6, 14). Used by Res1 and Res2.
4. Res1: `ρ = (ℓ_t²/ℓ_v²)·ratio^n_`; `ρ ≥ 1` from `ellT_mono` (needs `0 ≤ lam n`, eventual from `(eq:WO)`) and `ratio ≥ 1`; `4 ≤ W^ε` by `prec_W_rpow_ge`; the window passes from `STEKWin` to every `v` by `prec_window`.
5. Res2: `K = 1/𝔠`; `L^d ≤ N ≤ W^{1/𝔠}` (`prec_L_pow_le`); `log L ≤ W^ε` (`prec_log_le`: `log y ≤ y^a/a`, `a = εd/(2K)`) once `W^{ε/2} ≥ 2K/(εd)`, the threshold of (a) row 10; `EKSumZero` is the hypothesis.
6. Nonzero: `ekSumDecayNonzero_holds` with `prop5Short_holds`, `prop8ZeroMode_holds`; for `v ∈ [s n, t n]` the pair `(v, t n)` meets the pin's window `0 ≤ v`, `1-g²/L² ≤ v ≤ t n < 1` (this uses the Amend-1 hypothesis `0 ≤ s`); `C` is absorbed by `StochDomAt.const_mul_left`; only `0 < g ≤ 𝔡⁻¹` is eventual.
7. Amend 1: `(∀ n, 0 ≤ s n) →` inserted in `def STEKNonzero` plus one docstring sentence (diff above). `STEKNonzero`/`STEKSum*` occur in no file other than `Step34Pins.lean` and `Prec.lean`, in the worktree and in main (grep above) and the full `lake build` (3770 jobs, exit 0) passes, so no merged instance or theorem in `Step34Pins.lean` is broken.
8. Instances (10 `example`s, `d = 3`, `n_ = 2`, `m ≡ i` with `Im m = 1 ≥ κ = 1/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `X ≡ 1`): Ndecay at `(sz0, 0, 1/16)`, `(szB, 7/8, 15/16)`, `(szB, 15/16, 31/32)`; Res1, NAL (`σ = (+,+)`), Res2 at the first two; Nonzero at `(szB, 15/16, 31/32)` with `A = univ`. The tensor family is deterministic: `δ₀` (norm `≤ 1`; `(deccA0)` holds for all `n` since `W^ε ℓ_v > 0 = |a_i - a_j|`) and, for Res2, the sum-zero `Az = δ₀ ⊗ (δ₀ - δ_e)` (`Az L (0,0) = 1`, `EKSumZero` proved, `(deccA0)` from the `n` with `W^ε ≥ 4`, since the support has diameter 1 and `ℓ_v ≥ 1`). So `STEKDecay`, `STEKLow` (`b = 0`), `‖𝒜‖ ≺ 1` (`prec_of_le`) and the windows (`win_sz0`, `win_szB_I`, and the case-(ii) inequalities `1 - 1/16 ≤ 15/16`) are proved, not assumed.
9. Registry: no new `Prop` is defined and `RBM3D/Test/Axioms.lean` is unchanged; the pre-check imports `RBM3D` and `RBM3D.Evolution.Prec` and exits 0.
10. The worktree base is `6ef5d49`; `git diff --name-only main...t/T2053` lists only the two writable files. No correction to (a) was needed, so there is no (a′).

## (c) Verified Mathlib / Lean names used (`#where` script: module:line of the declaration; all resolve, none invented)
```
Real.log_le_rpow_div — Mathlib.Analysis.SpecialFunctions.Pow.Real:884
tendsto_rpow_atTop — Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics:37
Real.rpow_mul — Mathlib.Analysis.SpecialFunctions.Pow.Real:415
Real.rpow_le_rpow — Mathlib.Analysis.SpecialFunctions.Pow.Real:549
Real.rpow_nonneg — Mathlib.Analysis.SpecialFunctions.Pow.Real:163
Real.rpow_le_one — Mathlib.Analysis.SpecialFunctions.Pow.Real:662
Real.rpow_natCast — Mathlib.Analysis.SpecialFunctions.Pow.Real:61
Real.rpow_add — Mathlib.Analysis.SpecialFunctions.Pow.Real:208
Real.rpow_one — Mathlib.Analysis.SpecialFunctions.Pow.Real:148
Real.rpow_pos_of_pos — Mathlib.Analysis.SpecialFunctions.Pow.Real:116
Real.rpow_le_rpow_of_exponent_le — Mathlib.Analysis.SpecialFunctions.Pow.Real:616
Real.rpow_le_rpow_of_nonpos — Mathlib.Analysis.SpecialFunctions.Pow.Real:565
one_div_pos — Mathlib.Algebra.Order.GroupWithZero.Basic:850
one_le_div — Mathlib.Algebra.Order.Field.Basic:41
one_le_pow₀ — Mathlib.Algebra.Order.GroupWithZero.Basic:484
pow_le_pow_left₀ — Mathlib.Algebra.Order.GroupWithZero.Basic:513
one_le_mul_of_one_le_of_one_le — Mathlib.Algebra.Order.GroupWithZero.Basic:441
inv_anti₀ — Mathlib.Algebra.Order.GroupWithZero.Basic:1220
div_le_div_of_nonneg_left — Mathlib.Algebra.Order.GroupWithZero.Basic:1270
div_le_div_of_nonneg_right — Mathlib.Algebra.Order.GroupWithZero.Basic:1193
pi_norm_le_iff_of_nonneg — Mathlib.Analysis.Normed.Group.Constructions:318
Finset.sum_filter — Mathlib.Algebra.BigOperators.Group.Finset.Basic:332
Finset.sum_ite_eq' — Mathlib.Algebra.BigOperators.Group.Finset.Piecewise:149
Finset.sum_sub_distrib — Mathlib.Algebra.BigOperators.Group.Finset.Defs:678
Fin.forall_fin_two — Init.Data.Fin.Lemmas:983
Nat.pow_le_pow_left — Init.Data.Nat.Basic:804
Nat.le_mul_of_pos_left — Init.Data.Nat.Lemmas:605
mul_neg_of_pos_of_neg — Mathlib.Algebra.Order.GroupWithZero.Basic:45
div_le_iff₀ — Mathlib.Algebra.Order.GroupWithZero.Basic:1132
Complex.I_im — Mathlib.Basic.Complex.Basic:247
Complex.norm_I — Mathlib.Analysis.Complex.Norm:100
Fin.ext — Init.Data.Fin.Lemmas:52
```
Names verified absent from Mathlib: none recorded (every name above resolves under `#check`, `names_check.lean`, in this worktree). Project names used (read from the files): `tendsto_size`, `Sizes.W_rpow_le`, `Sizes.size_rpow_le_W_rpow`, `Sizes.prec_of_le`, `Prec.whp`, `ellT_mono`, `ellT_pos`, `one_le_ellT`, `StochDomAt.{mul,of_subset,const_mul_left,of_highProbAt_add_rpow_neg}`, `HighProbAt.{mono,inter,of_eventually_univ}`, `zdistD_single`, `zdist_one`, `zdistD_neg`, `ek_sum_fin_two`, `ekDelta0`, `ek*_holds`, `prop*_holds`.

## (d) Open issues and paper-delta candidates

- No new paper-delta candidate: the statement differences used here are T2016a, T2016b, T2016f, T2042a, T2041c (signed, not re-proposed); the `0 ≤ s` of `STEKNonzero` is DECISIONS §27 (no delta there).
- All hypotheses of the ten instances are discharged (none is another gate's unproved pin); the pins `EK*`/`prop*` used are merged theorems, so nothing new enters the registry.
- The full `lake build` above ran in the worktree (base `6ef5d49`, before the commit); the hub's merge-time full build adds the root import of `RBM3D.Evolution.Prec`, which the registry pre-check already exercised.
