Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 09:45:50 UTC 2026

### (i) Exponent table

Sources read: `Propagator/Pins.lean:30-118` (pins 5-8), `Loop/KLTree.lean:269-327` (`KLDecay` ... `KLPT`), `Loop/KLInduct.lean:92-105`, `Loop/KLWardIneq.lean:91-101`, `Loop/KBound.lean:74`, `Induction/Defs.lean:64,174`, `Induction/Step34Pins.lean:111,224`, `Defs/Sizes.lean:138-250`, `Defs/Semicircle.lean:190,309`.

| # | Quantity | Value / map | Constraint | Slack |
|---|---|---|---|---|
| 1 | `Λ` of `Prop5Decay`, `Prop6/7/8` | `Λ := gmax` | `0 < Λ` (`hg`), `g ≤ gmax` is the same range as in `KLDecay` etc. | none needed |
| 2 | `κ'` of `Prop5Short` | `κ' := min(κ,1)/2` | for `|E| ≤ 2-κ`: `κ' ≤ Im m(E) = sqrt(4-E²)/2`; `4-E² ≥ κ(4-κ)`, so `Im m ≥ sqrt(κ(4-κ))/2 ≥ κ/2` when `κ ≤ 2`; for `κ > 2` the set `|E| ≤ 2-κ` is empty | `κ=0.1`: `Im m ≥ 0.31225` vs `κ'=0.05`; `κ=0.5`: `0.66144` vs `0.25` (script A) |
| 3 | `m` for `KLDecay`/`KLDiffOne/Two`/`KLZero` | `m := I` (`‖I‖=1`, `Im I = 1`); `κ'' := 1` in pins 6,7,8 | `ξ = t·(m·m̄) = t·‖m‖² = t` at `(σ₁,σ₂)=(+,−)`: `PropSpin I true * PropSpin I false = I * conj I = 1` | `κ'' = 1 ≤ Im I = 1`, equality (allowed: `κ ≤ m.im`) |
| 4 | `m` for `KLShort` | `m := mE E`, `‖mE E‖=1` (`norm_mE`, `|E| ≤ 2`); `PropSpin (mE E) = mSigma E` (same `if σ then m else conj m`) | `κ' ≤ (mE E).im` from row 2 | as row 2 |
| 5 | `c` of `KLDiffOne/Two` | any `c ∈ (0,1)` (the pin is `∀ c ∈ (0,1)`); `Prop6Diff1 d gmax 1 c` | `0 < c < 1`: matches the pins' range (the old `ThetaDiffOne/Two`, false for `c ≥ 1` (Pins.lean:110-118), are not used) | none: `c` is passed through |
| 6 | loss `L^τ`, `τ>0` of `KLDiffOne/Two/Zero` | `C_KL := C_pin` (pin has no loss) | `1 ≤ L^τ` since `L ≥ 3`, `τ > 0`; the other factors are `≥ 0` | `L^τ ≥ 3^τ > 1` |
| 7 | constants of `KLPT` | `Cd,cd` from pin 5 at `(d,gmax)`; `Cκ,cκ` from pin 5s at `(d,gmax,κ')`; `C(c,τ)` from pins 6,7 at `(d,gmax,1,c)`, pin 8 at `(d,gmax,1)` | depend only on `d, gmax, κ, c, τ`; never on `L, g, t, E, W` (they are chosen before `∀ L`) | none needed |
| 8 | `KLbound_holds`, `KLwardIneq_holds` | `KLboundPin_holds d n κ gmax hd hn hκ hg (KLPT_holds hd hκ hg)`; same for ward (`2 ≤ n`) | `3 ≤ d`, `1 ≤ n` (`2 ≤ n`), `0<κ`, `0<gmax` | `n`-range exact |
| 9 | `KLoopBound d L W g (fun t => KLK d L g W E t)` (fixed `L W g`) | `gmax := g`, `κ := 2-|E|`, `p := ⟨L,W,_,_,g,_,_,E,_,t,_,_⟩`, lists to `Fin n` by `List.ofFn_get` | `3 ≤ d`, `3 ≤ L` (KLPar.hL), `1 ≤ W` (else `(W^d)⁻¹ = 0`), `0 < g`, `|E| < 2`; constant may depend on `E, g, L` (binds before `C`) | `KLinstPar`: `|E|=0 ≤ 2-1` |
| 10 | `L^τ ≤ N^{τ/d}` (new `L`-version of `Sizes.W_rpow_le`) | `N = (W L)^d`, `L^d ≤ (WL)^d` as `W ≥ 1` (`W_pos`) | `0 ≤ τ`, `0 < d`; uses only `W ≥ 1`, no `Bandwidth`, no `L^d ≤ W^K` (§29 (3)) | `sz0, n=0..3, τ=1.5`: flag `L^1.5 ≤ N^0.5` True (script B) |
| 11 | KL loss for `Prec` exponent `τ'>0` | `σ := d τ'/2`, KL constant `C=C(k,σ)`; `C L^σ ≤ C N^{τ'/2} ≤ N^{τ'}` for `N ≥ C^{2/τ'}` | needs `SizeTendsto` (`N → ∞`), eventual in `n`; `ζ ≥ 0` (`Bparam ≥ 0` for `0 ≤ τ n < 1`, `lam n > 0`) | threshold `n₀(C,τ')` |
| 12 | `STKbound` hypotheses (conditional form) | `SizeTendsto`; `∀ᶠ n, |E n| ≤ 2-κ`; `∀ᶠ n, 0 < lam n ∧ lam n ≤ gmax`; `3 ≤ d` | `3 ≤ L n`, `1 ≤ W n` are fields of `Sizes`. Flow form: `STFlow sz κ ε 𝔠 𝔡 z`, `E = STflowE z`, `gmax = 𝔡⁻¹`: `|lemE z_n| ≤ |Re z_n| ≤ 2-κ` (`abs_lemE_le`, `Semicircle.lean:309`, needs `0 < Im z_n`, given by `N^{-1+ε} ≤ Im z_n`); `lam n ≤ 𝔡⁻¹` and `lam n ≥ W^{-d/2+𝔡} > 0` eventually from `WO`; `SizeTendsto` from `Admissible` | `sz0,z0,n=0..3`: `lemE=0.5 ≤ 1.9`; WO flag True, so `0 < lam ≤ 10` (script B) |
| 13 | `STKward` | same hypotheses; `ζ = (W^d η_τ)⁻¹ Bctl^{k-2}` equals the RHS of `KLwardIneqAt` (`etaT E τ = (1-τ)·Im m(E) ≥ 0`); `STKI = KLK`; LHS `∑_x ‖KLK ⟨σ, ofFn a ++ [x]⟩‖` identical | `k ≥ 2`, `τ n ∈ [0,1)` | numeric check at `k=3` in script A |

Statement matching (field by field), all by reading:
* `KLDecay`: `∃ Cd cd, ∀ L hL g (0<g≤gmax), ∀ t ∈ [0,1), a`: bound for `Theta d L g (t:ℂ) 0 a`; pin 5 has `∃ C c, ∀ L hL g, ∀ t, ∀ m (‖m‖=1), ∀ σ₁ σ₂, a` at `(t:ℂ)*(PropSpin m σ₁ * PropSpin m σ₂)`; the `(+,−)` pair at `m=I` gives `t`. Quantifier order matches (constants before `L`).
* `KLShort`: bulk `∀ E, |E| ≤ 2-κ`, `s`, `t`: pin 5s with `m = mE E`, `κ' ≤ Im m`.
* `KLDiffOne/Two`: `∀ c ∈ (0,1), ∀ τ > 0, ∃ C`: pin 6/7 at `(κ''=1, m=I)` times `1 ≤ L^τ`.
* `KLZero`: `∀ τ > 0, ∃ C`: pin 8, `Theta0`, times `1 ≤ L^τ`.

Hypotheses of the owed pins as pinned (no condition on `E`, `lam`, size): `STKbound sz E` and `STKward sz E` are not provable unconditionally. Data (script A, E=1.9=2-κ, `κ=1/10`): constant sequence `L=5, W=2, lam=1/2, τ n = 1/2`, `k=3`: `max_{σ,a}|𝒦^{(3)}|/(W^{-d}B_{τ,0})² = 1.0645 > 1` at `N = (WL)^d = 1000` for all `n`; `Prec` needs `ξ ≤ N^{τ'} ζ` (the bad set is then all of the space, and `seqP` is documented as a probability measure, `StochDomAt.lean:724`), false for `τ' < ln(1.0645)/ln(1000) = 0.00905` while `N` does not tend to infinity. So `SizeTendsto` cannot be dropped even with `|E|`, `lam` bounded. Also `|E| > 2` (`E = 5`): `‖𝒦^{(1)}‖ = ‖mE 5‖ = 2.5` (Lean `sqrt(4-25)=0`) against `ζ = 1`, at `N=27` (script B). Hence target 3 and 4 are stated in the conditional form of row 12 (no edit of the pins); the pinned consumer `STStep3R` (`Step34Pins.lean`) carries `STFlow sz κ ε 𝔠 𝔡 z` and applies `STKbound sz (STflowE z)`, `STKward sz (STflowE z)`, which gives the three hypotheses (row 12). `STFlow` is not checked for the other consumers (`s1_Kbound_seq` takes `S1Std`).

DECISIONS §29 per statement: (1) time domain: every bound is `t, τ n ∈ [0,1)`, `0 ≤ τ n < 1` is in the pin; `η_τ > 0` is not needed, only `≥ 0`. (2) case (ii) boundary `1-ilambda²/L²`: not used, bounds are uniform in `t ∈ [0,1)`. (3) `L^d ≤ W^K`: not used (row 10 uses `W ≥ 1` only). (4) `∀ n` vs `∀ᶠ n`: hypotheses of rows 11-12 are `∀ᶠ n`; `Prec` is eventual; no condition at finitely many `n` is imposed beyond what `Sizes` gives. Constants depend only on `d, k, κ, gmax, τ'` (and `𝔡` via `gmax = 𝔡⁻¹`), not on `L, W, g, t, E`.

### (ii) One concrete nondegenerate instance

Command (python3, numpy; scratch `scratchpad/T2125/pre.py`, `flow2.py`; no Lean):

Script A (`python3 pre.py`), `d=3, L=5, W=2, g=1/2`, circulant `S^{(B)}`, `Θ = (1-ξ S^{(B)})⁻¹`, `K^{(3)}` from `KLK_three` (`KLTree.lean:218`), `E ∈ {0, 1.9}`, `t ∈ {0.5, 0.99}`, all 8 sign vectors, all labels (translation invariance fixes one label):
```
kappa=0.1: kappa'=0.05, min Im m on |E|<=2-kappa = 0.312250, ok=True, sqrt(k(4-k))/2=0.312250
kappa=0.5: kappa'=0.25, min Im m on |E|<=2-kappa = 0.661438, ok=True, sqrt(k(4-k))/2=0.661438
row sums SB: 0.9999999999999999 1.0000000000000002
E=0.0 t=0.5: max|K3|/ctl^2=0.7585  max_sigma,a2 sum_x|K3|/((W^d eta)^-1 ctl)=0.7868  ctl=0.16867 Bp0=1.3493
E=0.0 t=0.99: max|K3|/ctl^2=0.2581  max_sigma,a2 sum_x|K3|/((W^d eta)^-1 ctl)=0.3853  ctl=0.58077 Bp0=4.6462
E=1.9 t=0.5: max|K3|/ctl^2=1.0645  max_sigma,a2 sum_x|K3|/((W^d eta)^-1 ctl)=0.3554  ctl=0.16867 Bp0=1.3493
E=1.9 t=0.99: max|K3|/ctl^2=0.5058  max_sigma,a2 sum_x|K3|/((W^d eta)^-1 ctl)=0.2663  ctl=0.58077 Bp0=4.6462
```
(`ctl = W^{-d}B_{t,0}`; the ticket's `τ ∈ {0.5, 0.99}` are the `t` column.  Ratios are `O(1)`, the `L^τ` loss absorbs the constant when `N → ∞`; the value `1.0645 > 1` is the data of the unconditionality remark above.)

Script B (`python3 flow2.py`), the merged `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`), `z0 n = 1/2 + i N_n^{-4/5}` (`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `Induction/Defs.lean:435`); flags: `|lemE| <= |Re z|`, `WO` (`W^{-d/2+1/10} <= lam <= 10`), `Bandwidth` (`N^{1/6} <= W`), `locDomain` (`Im z >= N^{-9/10}`), `L^{1.5} <= N^{1.5/3}`:
```
n=0 L=4 W=32 N=2097152 lam=1.562e-02 lemE=0.500000 flags(|lemE|<=|Re z|, WO, Bandwidth, locDomain, L^1.5<=N^0.5)=(True, True, True, True, True)
n=1 L=8 W=1024 N=549755813888 lam=2.441e-04 lemE=0.500000 flags(|lemE|<=|Re z|, WO, Bandwidth, locDomain, L^1.5<=N^0.5)=(True, True, True, True, True)
n=2 L=12 W=7776 N=812479653347328 lam=2.143e-05 lemE=0.500000 flags(|lemE|<=|Re z|, WO, Bandwidth, locDomain, L^1.5<=N^0.5)=(True, True, True, True, True)
n=3 L=16 W=32768 N=144115188075855872 lam=3.815e-06 lemE=0.500000 flags(|lemE|<=|Re z|, WO, Bandwidth, locDomain, L^1.5<=N^0.5)=(True, True, True, True, True)
E=5 (Lean sqrt(4-25)=0): |K^(1)|= 2.5  N=(1*3)^3=27
```

Instance data for the three endpoint theorems, every hypothesis at once:
* `KLPT_holds`: `d=3`, `κ=1/10`, `gmax=1`; `κ' = min(1/10,1)/2 = 1/20 ≤ Im m(E)` on `|E| ≤ 1.9` (script A, `0.312250`); `m = I`; `c ∈ (0,1)` arbitrary, `τ>0` arbitrary, `L ≥ 3`, `0<g≤1`: nothing degenerate (no `N=0`, no empty index).
* `KLbound_holds` at `n=4`, the probe data `KLinstPar : KLPar 1 1` (`KLTree.lean:857`: `L=5, W=2, g=1/2, E=0, t=9/10`), `κ=1, gmax=1` (`|E|=0 ≤ 1`, `g ≤ 1`, `0 ≤ t<1`), `d=3`, `1 ≤ 4`: no hypothesis left.
* `stKbound_holds` / `stKward_holds` at `sz0`, `E = STflowE z0`: `SizeTendsto` (`sz0_tendsto`, `Sizes.lean:300`; `N_n` above `→ ∞`), `|E n| = 0.5 ≤ 2-1/10` (`κ=1/10`), `0 < lam n ≤ 𝔡⁻¹ = 10` (`gmax = 10`; `lam n ≤ 1/64`), `3 ≤ L n`, `1 ≤ W n` (fields). External-hypothesis limit check (TEAM §8 lesson 14): the only non-pinned hypotheses are `SizeTendsto` and the eventual bounds on `E`, `lam`; `N_n = (W_n L_n)^3 = (4(n+1)(2(n+1))^5)^3 ≥ n+1` (`sz0_tendsto` is merged), `lemE(z0 n) = 0.500000` for `n=0..3` (script B, `|lemE| ≤ |Re z| = 1/2` by `abs_lemE_le`), `lam_n → 0` stays in `(0, 10]`.
* Conversion `C L^σ ≤ N^{τ'}`: `σ = d τ'/2`; with `τ' = 1`, `σ = 1.5`: `L^σ ≤ N^{σ/d} = N^{1/2}` holds at `n=0..3` (flag in script B); `C ≤ N^{1/2}` then holds from some `n₀` on since `N → ∞`.

### Verdicts

* Target 1 `KLPT_holds hd hκ hg`: PASS (rows 1-7; each of the five fields follows from the matching pin, with `κ' = min(κ,1)/2`, `m = mE E` for `KLShort`, `m = I`, `κ''=1` otherwise).
* Target 2 `KLbound_holds`, `KLwardIneq_holds`: PASS (rows 8; direct composition). `KLoopBound` for `K = KLK … E`: PASS with hypotheses `3 ≤ d`, `3 ≤ L`, `1 ≤ W`, `0 < g`, `|E| < 2` (row 9); these are necessary to meet `KLPar`; the ticket's "no hypothesis beyond parameter ranges" holds.
* Target 3 `stKbound_holds`: PASS in the conditional form of row 12 (the pin as stated, no condition on `E`, `lam`, size, is not provable: data above; do not edit the pin). Proof needs the new `L^τ ≤ N^{τ/d}` (row 10) and `N → ∞`.
* Target 4 `stKward_holds`: PASS, same form.
* Registry: removal of the three owed lines (`STKbound`, `STKward`, `KLoopBound`) from `RBM3D/Test/Axioms.lean` is allowed only if no merged declaration still takes them as a hypothesis; `STKbound`/`STKward` occur as hypotheses in `Induction/Step1.lean`, `Step1Setup.lean`, `GridDriftN.lean`, `Step34Pins.lean` (grep), so those lines can be removed only if the registry scan accepts a proved conditional theorem; this is for stage 1b's pre-check, not a mathematical obstruction.
* Paper-delta candidates: `T2125a` (the unconditional `ML:Kbound`, `lem_wardineq_K` at sequence level require `N → ∞`, `|E_n| ≤ 2-κ`, `0 < lam_n ≤ gmax`: the paper has these from `(eq:WO)`, `𝐃_{κ,ε}`; Lean states them as hypotheses of the conditional form), `T2125b` (`κ' = min(κ,1)/2` in the bridge `Prop5Short ↦ KLShort`).

Overall verdict: PASS.

## (b) Script output — Sun Oct  4 10:04:03 UTC 2026

Stage 1b (`prover-hard`), branch `t/T2125`: code commit 825674b, docstring-only commit c4b40f5. Ports from RBM1D/RBM2D: none (no `diff --stat`). RBM3D templates rewritten here: `Sizes.W_rpow_le` (`Defs/Sizes.lean`) for `L_rpow_le`; `KL_rpow_le`, `KLBoundAt_prec` of the probe `64b58eb:RBM3D/Probe/T2004Pins.lean` for the absorption step of `KLFinal_prec_of_loss`.

```
$ date -u
Sun Oct  4 10:04:47 UTC 2026
$ git log --oneline -2; git diff --stat main...t/T2125
c4b40f5 T2125: KLFinal docstring: flow energy bound, not equality
825674b T2125: KL14a Loop/KLFinal (KLPT_holds, KLbound_holds, KLwardIneq_holds, KLoopBound_KLK, stKbound/stKward)
 RBM3D/Loop/KLFinal.lean | 541 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   8 +-
 2 files changed, 545 insertions(+), 4 deletions(-)

$ lake build RBM3D.Loop.KLFinal 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3713 jobs).

$ lake env lean ax.lean   # one `#print axioms` per new public declaration (12 lines)
'RBM.Loop.KLPT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLwardIneq_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLoopBound_KLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.L_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKward_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKbound_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKward_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.KLFinal_szConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.KLFinal_szConst_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.KLFinal_not_stKbound' depends on axioms: [propext, Classical.choice, Quot.sound]

$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Loop/KLFinal.lean; echo exit=$?
exit=1

$ python3 extract.py <names>   # target statements, lines of RBM3D/Loop/KLFinal.lean
143: theorem KLPT_holds {d : ℕ} {κ gmax : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
144:     KLPT d κ gmax :=

154: theorem KLbound_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax →
155:     KLBoundAt d n κ gmax :=

160: theorem KLwardIneq_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax →
161:     KLwardIneqAt d n κ gmax :=

168: theorem KLoopBound_KLK {d L W : ℕ} [NeZero L] {g E : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W)
169:     (hg : 0 < g) (hE : |E| < 2) : KLoopBound d L W g (fun t => KLK d L g W E t) := by

194: theorem L_rpow_le (hd : 0 < d) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
195:     ((sz.L n : ℕ) : ℝ) ^ τ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / d) := by

243: theorem stKbound_holds (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
244:     (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
245:     (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) : STKbound sz E := by

260: theorem stKward_holds (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
261:     (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
262:     (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) : STKward sz E := by

302: theorem stKbound_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
303:     (hz : STFlow sz κ ε 𝔠 𝔡 z) : STKbound sz (STflowE z) :=

308: theorem stKward_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
309:     (hz : STFlow sz κ ε 𝔠 𝔡 z) : STKward sz (STflowE z) :=

341: theorem KLFinal_not_stKbound : ¬ STKbound KLFinal_szConst (fun _ => 0) := by

```

Instances (compiled `example`s; line numbers are those of the file):
```
$ sed -n 399p RBM3D/Loop/KLFinal.lean   # KLPT_holds at d=3, kappa=1/10, gmax=1 (lines 405-449: the five fields applied at L=5, g=1/2, t=9/10, E=0)
example : KLPT 3 (1 / 10) 1 := KLPT_holds (by norm_num) (by norm_num) one_pos
$ sed -n 453,459p RBM3D/Loop/KLFinal.lean   # KLbound_holds, n=4, every tau>0, probe point KLinstPar (lines 462-471: KLwardIneq_holds, n=4)
example (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLInduct_instσ KLInduct_insta)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ τ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := KLbound_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos τ hτ
  exact ⟨C, hC, H KLinstPar KLInduct_instσ KLInduct_insta⟩
$ sed -n 475,477p RBM3D/Loop/KLFinal.lean   # KLoopBound_KLK at (d,L,W,g,E) = (3,5,2,1/2,0) (lines 479-487: applied at n=4)
example :
    KLoopBound 3 5 2 (1 / 2) (fun t => KLK 3 5 (1 / 2) 2 0 t) :=
  KLoopBound_KLK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
$ sed -n 505,513p RBM3D/Loop/KLFinal.lean   # stKbound_holds at sz0, E = STflowE z0; every hypothesis discharged (stKward_holds: 516-524)
example : STKbound sz0 (STflowE z0) := by
  refine stKbound_holds sz0 (by norm_num) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos
    sz0_tendsto (Eventually.of_forall fun n => (abs_lemE_le (z0_im_pos n)).trans
      (z0_locDomain n).1) (Eventually.of_forall fun n => ?_)
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hlam]
  exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hx1)⟩
$ sed -n 528,540p RBM3D/Loop/KLFinal.lean   # flow forms at flow_z0; STKbound read at k=3, tau=1/2
example : STKbound sz0 (STflowE z0) ∧ STKward sz0 (STflowE z0) :=
  ⟨stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0,
    stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0⟩

/-- `STKbound` read at the time sequence `τ_n ≡ 1/2` and `k = 3`: `max |𝒦^{(3)}| ≺ (W^{-d}B_{τ,0})²`
at the scale `N_n`, the statement of the pin at concrete nondegenerate data. -/
example :
    Prec sz0 (U := fun n => (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖STKloop sz0 n (STflowE z0 n) (1 / 2) p.1 p.2‖)
      (fun n _ _ => (sz0.Bctl n (1 / 2)) ^ (3 - 1)) :=
  stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) 3 (by norm_num)

```

```
$ for n in KLPT_holds KLbound_holds KLwardIneq_holds KLoopBound_KLK L_rpow_le stKbound_holds stKward_holds stKbound_of_flow stKward_of_flow KLFinal_szConst KLFinal_szConst_size KLFinal_not_stKbound; do grep -rnw "$n" RBM3D RBM3D.lean --include="*.lean" | grep -v "RBM3D/Loop/KLFinal.lean"; done   # main worktree, exact names
(no output)
$ same loop over /Users/junyin/Lean_proof/RBM3D-wt/*/RBM3D, excluding /T2125/
(no output)
```

Registry pre-check and full build:
```
$ git diff -U0 main...t/T2125 -- RBM3D/Test/Axioms.lean   # the registry edit (only change outside KLFinal.lean)
@@ -83 +83 @@ def borrowedProps : List Name :=
-`KLoopBound` is here rather than in `borrowedProps` because the paper does prove it:
+`KLoopBound` was here rather than in `borrowedProps` because the paper does prove it:
@@ -86,2 +86,2 @@ additional modifications to handle the higher-dimensional setting `d ≥ 3`.  Fo
-reader's convenience, we provide the proof below", and then gives it in full.  Assuming it
-here is a debt of this formalization (the molecule layer is missing), not a borrowing. -/
+reader's convenience, we provide the proof below", and then gives it in full.  T2125 left
+it: no theorem assumes it, and `KLoopBound_KLK` (`Loop/KLFinal.lean`) proves it for `K = KLK`. -/
@@ -89 +89 @@ def owedProps : List Name :=
-  [`RBM.Loop.TwoLoopBounded, `RBM.Loop.KLoopBound,
+  [`RBM.Loop.TwoLoopBounded,
$ git diff --stat 825674b c4b40f5   # c4b40f5 follows the full build below
 RBM3D/Loop/KLFinal.lean | 4 ++--
 1 file changed, 2 insertions(+), 2 deletions(-)
# full build: worktree RBM3D.lean temporarily + `import RBM3D.Loop.KLFinal` after the last import (not committed), tree at 825674b
$ lake build > full3.log 2>&1; grep -c "error" full3.log; tail -2 full3.log
0
Build completed successfully (3873 jobs).
exit=0
$ grep "axiom audit\|STKbound:\|KLPT:\|premises found\|^registry:" full3.log | cut -c1-120
info: RBM3D.lean:172:0: axiom audit: 3852 theorems, 1346 definitions, 0 axioms in `RBM` (compiler-generated declarations
  RBM.Loop.KLPT: 20 [no certificate]
  RBM.Gauss.Sizes.STKbound: 9 [no certificate]
premises found by scanning: 77 (borrowed 1, owed 61, structural 15).
registry: 5 borrowed + 100 owed + 39 structural; 67 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ grep -c KLoopBound full3.log
0
$ grep -rn KLoopBound RBM3D | grep -v "Test/Axioms.lean\|KLFinal.lean"   # nothing but the definition and two comments
RBM3D/Loop/KBound.lean:44:* `RBM.Loop.KLoopBound` : `ML:Kbound` stated verbatim, as a `Prop` (`docs/QUEUE.md`, Q24).
RBM3D/Loop/KBound.lean:74:def KLoopBound (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
RBM3D/Loop/KLUnique.lean:25:  (`64b58eb:RBM3D/Probe/T2004Pins.lean:915-971`, compiled there).  `KLretire_KLoopBound` of that
$ grep -n "STKward\|STKbound" RBM3D/Test/Axioms.lean | cut -c1-90   # STKward is not registered; STKbound line kept
91:   `RBM.Gauss.Sizes.STKbound,       -- `ML:Kbound` (`1_2:1056`), hypothesis of `STStep1
$ grep -rlE "STKbound|STKward" RBM3D --include="*.lean" | grep -v "KLFinal\|Test/"   # files still taking them as hypotheses
RBM3D/Induction/Step1Setup.lean
RBM3D/Induction/Step1.lean
RBM3D/Induction/IterationsA.lean
RBM3D/Induction/Defs.lean
RBM3D/Induction/GridDriftN.lean
RBM3D/Induction/Step34Pins.lean
```

Narrative.
1. `KLPT_holds` (`KLFinal_decay/short/diffOne/diffTwo/zero`, private): pins 5, 6, 7, 8 at `m = I`, `(σ₁,σ₂) = (+,−)` (`KLFinal_PropSpin_I`: `PropSpin I true * PropSpin I false = 1`), `κ'' = 1 ≤ Im I`; the loss `L^τ` of `KLDiffOne/Two/KLZero` is absorbed by `1 ≤ L^τ` with the same constant. `KLShort` is pin 5s at `m = mE E`, `κ' = min κ 1 / 2` (`KLFinal_mE_im_ge`: `Im mE E = √(4-E²)/2`, `E² ≤ (2-κ)²`; `norm_mE` for `‖m‖ = 1`). All constants come from the pins, chosen before `L`.
2. D12 / D174: the range `c ∈ (0,1)` of `KLDiffOne/Two` is passed unchanged to `prop6Diff1_holds`/`prop7Diff2_holds`; no `c ≥ 1` occurs. A separate lemma `KLPT_of_Prop5to8` is not added: `Prop5to8 d Λ κ c` is at one `c`, `KLDiffOne/Two` quantify over all `c`; the five `*_holds` pins are used directly.
3. `KLbound_holds`, `KLwardIneq_holds` are the K-loop pins applied to `KLPT_holds`. `KLoopBound_KLK` is stated for the one family `K = KLK`, hypotheses `3 ≤ d`, `3 ≤ L`, `1 ≤ W`, `0 < g`, `|E| < 2` (the `KLPar` ranges at `κ = 2 - |E|`, `gmax = g`); lists to `Fin n` by `List.ofFn_get`.
4. `stKbound_holds`, `stKward_holds`: private `KLFinal_prec_of_loss` turns "`ξ ≤ C L^s ζ` eventually, every `s > 0`" into `Prec` via `StochDomAt.of_eventually_empty`, with `s = dτ'/2`, `L^s ≤ N^{τ'/2}` (new `Sizes.L_rpow_le`, uses `W ≥ 1` only) and `C ≤ N^{τ'/2}` eventually from `SizeTendsto`. The `KLPar` point is `(L n, W n, lam n, E n, τ n)`; `0 ≤ τ n < 1` for all `n` as in the pin; `E`, `lam` conditions are `∀ᶠ n` (DECISIONS §29 (4)); no `L^d ≤ W^K`, no `Bandwidth`.
5. Conditional form. `KLFinal_not_stKbound` (compiled, three standard axioms) shows `¬ STKbound KLFinal_szConst (fun _ => 0)`: `L ≡ 3`, `W ≡ 1`, `lam ≡ 1/2`, `E ≡ 0` (bulk, `0 < lam ≤ 1`), `k = 2`, `τ ≡ 0`, `N ≡ 27`. So `SizeTendsto` cannot be dropped; the pin is not edited. The consumers carry `STFlow sz κ ε 𝔠 𝔡 z` (`Step34Pins.lean:255` etc.), which gives all three conditions: `stKbound_of_flow`, `stKward_of_flow` (`0 < κ`, `gmax = 𝔡⁻¹`, `|lemE z_n| ≤ |Re z_n| ≤ 2 - κ` by `abs_lemE_le`, `lam > 0` from `(eq:WO)`). No negative is compiled for `STKward`; no claim that the bulk and `lam` conditions are necessary.
6. Registry. `KLoopBound` carried by no theorem, removed (diff above). `STKward` is not in `Test/Axioms.lean` (grep above). The `STKbound` line stays: six files mention `STKbound`/`STKward` (list above), with binders at `Step1Setup.lean:671,693` (theorems) and `Step34Pins.lean:255,266,451,484` (pins); the ledger counts 9 theorems mentioning `STKbound`, 3 of them in `KLFinal.lean` (`stKbound_holds`, `stKbound_of_flow`, `KLFinal_not_stKbound`). The `KLPT` line (borrowed) stays: the ticket authorizes only the three owed lines.

## (c) Verified names (all by `#check`, scratchpad `names.lean`, no error)
- `Real.one_le_rpow`, `Real.rpow_le_rpow`, `Real.rpow_lt_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add'`, `Real.rpow_pos_of_pos`: as used in `L_rpow_le`, `KLFinal_prec_of_loss`, the negative.
- `Real.abs_le_sqrt`: `KLFinal_mE_im_ge`.
- `tendsto_rpow_atTop`, `Filter.Tendsto.eventually_ge_atTop`: eventual absorption `C ≤ N^{τ/2}`; `Filter.Eventually.exists` (as `.exists`): the negative.
- `pow_le_pow_left₀`, `sq_abs`, `le_mul_of_one_le_right`, `inv_le_one_of_one_le₀`, `one_le_pow₀`: scalar steps.
- `ENNReal.ofReal_lt_one`, `MeasureTheory.measure_univ`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `List.ofFn_get`, `List.ext_getElem`.
- Merged names used (in the file, by grep): `RBM.StochDomAt.of_eventually_empty`, `RBM.mE_im`, `RBM.norm_mE`, `RBM.abs_lemE_le`, `RBM.Loop.KLK_two`, `RBM.Loop.KLIndStepA_Bparam_nonneg`, `RBM.prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`, `prop8ZeroMode_holds`.
- Verified absent (grep above): `Sizes.L_rpow_le` and the nine new public names in main and in the other worktrees; `STKward` in the registry.

## (d) Open issues and paper-delta candidates
- T2125a: `STKbound sz E` as pinned (any `sz`, any `E`) is not provable: `KLFinal_not_stKbound` (`STKward` has the same shape; no negative compiled). Lean proves the conditional forms with `SizeTendsto`, eventual bulk `|E n| ≤ 2 - κ` and `0 < lam n ≤ gmax`; `STFlow` supplies them (`SizeTendsto` from `Admissible`, the bulk from `locDomain`, the `lam` range from `(eq:WO)`). The pins stay unedited (ticket).
- T2125b: bridge `Prop5Short ↦ KLShort` at `κ' = min κ 1 / 2`; `Prop6/7/8 ↦ KLDiffOne/Two/KLZero` at `m = I`, `κ'' = 1`; `m(+) m(−) = 1`.
- Open: consumers that take `STKbound`/`STKward` as hypotheses (e.g. `Step1Setup.lean:671,693`, `Step34Pins.lean:255`) are unchanged (not in this ticket's files); re-plumb them to `stKbound_of_flow`/`stKward_of_flow` under `STFlow` (KL14b or the consumer tickets), then drop the `STKbound` registry line. `KLoopBound` and the old pins stay for KL14b.
- Build output of `lake build RBM3D.Loop.KLFinal` has 9 `linter.style.longLine` warnings (no other warning from this file).
