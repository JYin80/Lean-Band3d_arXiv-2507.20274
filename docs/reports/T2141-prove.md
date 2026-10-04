Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:28:27 UTC 2026

Notation: `N = (WL)^d = sz.size`, `W ≥ N^𝔠` (Bandwidth), `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (WO), `1-t ≥ N^{-1+ε/2}` (RangeCond; `Green/Pins.lean:1049`, `v3_premises_of_stFlow`), `r = zdistInf(a'-b')`, `ℓ = ellT L lam τ ≥ 1`, `Cd⁺ = max(Cd,0)`.
Targets restated: for every `τ', D' > 0`, `‖G_τ(x,y)‖·1[W^{τ'}ℓ_τ ≤ |[x]-[y]|_∞] ≺ W^{-D'}`, both charges, `s ≤ τ ≤ t ≤ lemT z`, input `STStep2Concl` at `[s,t]`, `STGbEXPij`.

### (i) Exponent table and route (merged statement used at each step)

| # | quantity | value / bound | constraint, slack, merged statement |
|---|---|---|---|
| 1 | `c₀` (size of `W^{-d}B_{τ,K}`) | `W^{-d}B_{τ,K} ≤ W^{-2𝔡} + N^{-ε/2} ≤ 2W^{-c₀}`, `c₀ = min(2𝔡, dε/2)` | first term: `(g²+1-τ)⁻¹ ≤ g⁻² ≤ W^{d-2𝔡}`; second: `(L^d(1-τ))⁻¹W^{-d} ≤ N^{-ε/2}`, `N ≥ W^d`. Flow instance: `c₀ = 0.15` (`STflowE`, `Bctl`/`STWB` in `Induction/Defs.lean:69`) |
| 2 | `ε₀` of `STindMax` | `ε₀ = c₀/4` (instance 0.0375) | `STLocalEntryU` at the section `τ` (`Step34Pins.lean:199`), Prec exponent `τ'' = 𝔠c₀/4`: `N^{τ''} ≤ W^{c₀/4}`, so off a bad event of probability `≤ N^{-D}`, `‖G-M‖²_max ≤ 2W^{-3c₀/4} ≤ W^{-2ε₀}` iff `W^{c₀/4} ≥ 2` (eventually; the `∃ (x,y)` union is inside `Prec`) |
| 3 | `(GijGEX)` at `τ`, `ε₀` | `1_Ω |G_xy|² ≺ STgexRHS` for `x ≠ y` (charge `true`) | `RBM.Green.stGbEXPij_of_v3 (RBM.Green.gbEXPV3 hd)` (`Green/Pins.lean:1137`, `Green/GbEXP.lean:806`), needs `0 ≤ τ`, `τ ≤ lemT z` (`s ≤ τ ≤ t ≤ lemT z`): slack none needed |
| 4 | far set is off the diagonal | `ℓ ≥ 1`, `W^{τ'} ≥ 1` give `W^{τ'}ℓ > 0`, so `|[x]-[y]|_∞ ≥ 1`, `[x] ≠ [y]`, `x ≠ y` | the `1_{|a-b|≤1}` term of `STgexRHS` vanishes: `W^{τ'}ℓ > 1` (eventually `W^{τ'} > 1`) |
| 5 | neighbour count | `\|{v : zdistInf v ≤ 1}\| = 3^d`; pairs `(a',b')`: `3^{2d}`, with 2 charges `2·3^{2d}` (d = 3: 729, 1458) | **Ticket says `(2d+1)²`: that is the `zdistD` ball of `SB`; `STgexRHS` (`Induction/Defs.lean:92`) filters by `zdistInf ≤ 1`, a cube**. Constant only, absorbed in the `≺` (script below: 27 points at `d = 3, L = 7`) |
| 6 | far pair separation | `r ≥ ℓ(W^{τ'} - 2)` | triangle `zdistInf(a-b) ≤ zdistInf(a'-b') + 2`: script, 0 violations; `≥ ℓW^{τ'}/2` once `W^{τ'} ≥ 4` |
| 7 | loss prefactor of `STGdecayW` (`Step34Pins.lean:208`), `D = 2D'` | `((1-s)/(1-τ))^{Cd}·Bctl^{1/5}·STWB ≤ 4N^{Cd⁺+6/5} ≤ 4W^{(Cd⁺+6/5)/𝔠}` | `(1-s)/(1-τ) ≤ N^{1-ε/2}` (RangeCond), `Bparam ≤ 2(1-τ)⁻¹`, `W^{-d} ≤ 1`; `Cd` of either sign |
| 8 | closing the exponential | `K = (Cd⁺+6/5)/𝔠 + 2D'`; need `4W^{K}e^{-(W^{τ'}-2)^{1/2}} ≤ 1`, i.e. `(W^{τ'}-2)^{1/2} ≥ ln4 + K ln W` | holds eventually (`w^A e^{-c w^β} → 0`). Sample `d=3, 𝔠=1/6, Cd=1, D'=1` (`K=15.2`): `τ'=1/2` from `ln W ≥ 23.7`; `τ'=1/10` from `ln W ≥ 156.8` (script). Only an eventual statement; no hypothesis needs it |
| 9 | `𝒦` part (`‖𝒦_{(a',b')}‖ ≤ W^{-2D'}`) | **chosen: merged `B45_far_main`** (`Induction/B45.lean:1493`, `k = 2`) for the drafted pin | it gives `(‖𝓛‖+‖𝓛-𝒦‖)·1[ℓ_u W^{τ''} ≤ STdiamInf a] ≺ W^{-D'}` uniformly in `u ∈ [s,t]` from `STStep2Concl`, with `stKcalDecay_holds`/`inst_stKcalDecay_admissible` (`W^{-Q} ≤ g`, `Q = d/2` from WO) inside; `STdiamInf ![a',b']` is the `zdistInf` diameter (`DecayLoopA.lean:71`); take `τ'' = τ'/2` (`W^{τ'}-2 ≥ W^{τ'/2}` eventually). Rows 5–8 are then already inside this lemma. Reason: `KLmaxDist` is the `zdistD` (ℓ¹) diameter, `STdiamInf ≤ KLmaxDist`, so the `zdistInf` far condition suffices; no second derivation of the loss absorption |
| 10 | `𝒦` part for a log-scale threshold | **`RBM.Path.kellStarEv`** (`Path/KellStar.lean:173`), `δ = 1`: `‖Θ_u(a,b)‖ ≤ W^{-D}` for `zdistInf(a-b) ≥ (log W)^{3/2}ℓ_u`, `0 ≤ s ≤ u ≤ t` | hypotheses from `STFlow`: `SizeTendsto`, `Bandwidth 𝔠`, `RangeCond (ε/2) t`, `t < 1` (`v3_premises_of_stFlow`), `0 < lam ≤ 𝔡⁻¹` eventually (WO). `𝒦^{(2)} = W^{-d}(mσ₁mσ₂)Θ_{t mσ₁mσ₂}` (`KLK_two`, `KLTree.lean:211`) and `mσ·m(!σ) = 1` (`KLmSigma_mul_not`, `:445`) for `σ ∈ {(+,-),(-,+)}`. `stKcalDecay_holds` is not usable here: it needs `W^{τ}ℓ` (power), not `(log W)^{3}ℓ` |
| 11 | `STStep2Concl` at the section | only `STLocalEntryU` and `STGdecayW` used (`STAvgU` not) | `StochDomAt.precomp_param` with `p ↦ (⟨τ n, hs, ht⟩, p)` (as `STLK_of_STLKU`, `Step34Pins.lean:287`); target 3 is this one-line section, private |
| 12 | charge `σ = false` | `‖G^-_{xy}‖ = ‖G^+_{yx}‖` (`Gres σ=false` uses `z̄`, `H` Hermitian) | far set symmetric (`zdistInf(-v) = zdistInf v`); `Prec` precomposition `(x,y) ↦ (y,x)` |
| 13 | square root | `ξ² ≺ ζ²` gives `ξ ≺ ζ` | `N^{τ/2}ζ < ξ ⇔ N^{τ}ζ² < ξ²` |

Dictionary RBM2D (`c9a24cf`, `Evolution/FarEntry.lean`) to RBM3D: `Step2LocalPT` to `STLocalEntryU` section at `τ`; `Step2DecayPT` to `STGdecayW` section; `GbEXPHypV3` + `gijGEXPTSwap_giiGEXPT_of_V3` to `stGbEXPij_of_v3 (gbEXPV3 hd)`; `kellStarEv`/`Kpm` to `kellStarEv`/`KLK_two` (row 10) or `B45_far_main` (row 9); `farOff` (5 points) to the `3^d` cube (row 5); `zdist2` to `zdistInf` (rows 5–6); `gexRHS … q.1 p.1` (swapped) to `STgexRHS … [x] [y]` (not swapped); `feInd` to the `if W^{τ'}ℓ ≤ …` of the pin. RBM2D `farEntryDecayPT` uses `ellStar = (log W)^{3/2}ℓ` only inside `kellStarEv`; its indicator is `W^{τ'}ℓ`.

**Consumer check (ticket item).** The consumer `STCltIsoConcl` (`git show 7b2b789:RBM3D/Probe/T2134Pins.lean`, line 427) is at the CLT time `s` (`ellT … (s n)`), index set pairs of blocks (matches the pin's `Idx × Idx`), both charges. But its labels are isolated only at scale `10 (log W)^3 ℓ_s` (window `(log W)^3 ℓ_s`; paper `3_5:2245`), while the pin's indicator is `W^{τ'}ℓ`, and `(log W)^3 < W^{τ'}` eventually for every `τ' > 0`. RBM2D's `cltstep_core` (`CltStep.lean:270-290` at `c9a24cf`) used far entries at `W^{τ}ℓ` with isolation `W^{2τ}ℓ` (`hiso`), a scale which `STCltIsoConcl` does not provide. So the drafted pin does **not** serve the consumer.
**Proposed pin** `STFarEntryAtLog`: same as item 1 but `∀ c > 0, D' > 0` and indicator `c * (Real.log W)^3 * ellT … ≤ dist`. The route closes for it (rows 4–8 with `r ≥ (c(log W)^3-2)ℓ`, `(r/ℓ)^{1/2} ≳ √(c/2)(log W)^{3/2} ≫ K log W`; row 10 for `𝒦`: `(log W)^{3/2} ≤ c(log W)^3 - 2` eventually). It implies the drafted pin (`W^{τ'} ≥ c(log W)^3` eventually; indicator monotone), so the drafted pin is a corollary. Cost: rows 10 and the full `STGdecayW` chain (rows 7–8) must be written, `B45_far_main` is not enough.

### (ii) Nondegenerate instance (d = 3, flow instance `sz0`, `z0`, `flow_z0`)

`sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `z_n = 1/2 + i N^{-4/5}`; `κ = ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`; `s = sInst = 0`, `t = tInst = 1/16`, `τ = s`, `Cd = 1`, `τ' = 1/10`, `D' = 1` (`Induction/Defs.lean:413-440`, `Defs/Sizes.lean:260`). Checked per `n`: STFlow parts, `t ≤ lemT z`, `RangeCond ε/2`, far set `{ℓW^{τ'} ≤ L/2}` nonempty (`ℓ = 1`), and row 1. Command and output:

```
$ python3 scratchpad/T2141/pre.py
c0=min(2dd,d*eps/2)=0.1500 eps0=c0/4=0.03750
n  L  W  N  lam | flow:ReOK ImRange ImLe1 WO Band lemT>=t | RangeCond(eps/2) | ell W^tp<=L//2 | W^-d B<=2W^-c0 (tau=s,t)
0 4 32 2.097e+06 1.56e-02 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=1.41 L//2=2 True | [True, True]
1 8 1024 5.498e+11 2.44e-04 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=2.00 L//2=4 True | [True, True]
2 12 7776 8.125e+14 2.14e-05 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=2.45 L//2=6 True | [True, True]
5 24 248832 2.130e+20 3.35e-07 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=3.46 L//2=12 True | [True, True]
10 44 5153632 1.166e+25 8.82e-09 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=4.69 L//2=22 True | [True, True]
100 404 336323216032 2.509e+42 1.47e-14 | [True, True, True, True, True, True] lemT=1.0000 | True | ell=1.00 W^tp=14.21 L//2=202 True | [True, True]
L=7,d=3: #{v: |v|_inf<=1} = 27  (3^d=27, 2d+1=7)
triangle |a-b|_inf <= |a'-b'|_inf + 2 violations over all (b,a',b'): 0
W^tau' pin: Cd=1.0 c=0.167 tau'=0.50 D'=1.0 K=15.20: inequality N^C e^{-(W^tau'-2)^{1/2}}<=W^{-2D'} holds for ln W >= 23.7 (W~e^24)
W^tau' pin: Cd=1.0 c=0.167 tau'=0.10 D'=1.0 K=15.20: inequality N^C e^{-(W^tau'-2)^{1/2}}<=W^{-2D'} holds for ln W >= 156.8 (W~e^157)
log pin: c=1.0 (c(logW)^3 ell): holds for ln W >= 233.4
log pin: c=0.1 (c(logW)^3 ell): holds for ln W >= 2324.6
sz0 n=1000: (log W)^3 ell_0=5.491e+04 <= L//2=2002 : False
sz0 n=100000: (log W)^3 ell_0=2.273e+05 <= L//2=200002 : False
sz0 n=300000: (log W)^3 ell_0=2.944e+05 <= L//2=600002 : True
sz0 n=1000000: (log W)^3 ell_0=3.818e+05 <= L//2=2000002 : True
```

Reading: every deterministic hypothesis of `stFarEntryAt` holds at every `n` of `sz0` (no `N = 0`, empty index, collapsed window), the far set of the drafted pin is nonempty from `n = 0`. For the log-scale pin the far set of the `sz0` family is empty until `n ≈ 3·10^5` (`(log W)^3 ≤ L/2`), so a compiled instance of the proposed pin needs size data with `L ≳ (log W)^3` (a sequence like `szCL` of the T2134 probe, `L = 2(n+24)^5`, `W = 2^{n+24}`) in place of `sz0`.
Exponent closing (rows 7–8) is eventual (`ln W ≥ 24` to `157` for the drafted pin, `233` for `c = 1` of the log pin); it is the content of `Prec` and no hypothesis of the instance depends on it.

External hypothesis `STStep2Concl` (another gate's pin, kept as a hypothesis): limit computation at the instance, first term of the `STGdecayW` right side at the farthest pair `r = L/2`, `Cd = 1`, `D' = 1`, vs `W^{-2D'}` (script `ext.py`):
```
$ python3 scratchpad/T2141/ext.py
n=0 u=0.0000: term1=3.245e-07  W^-2=9.766e-04  term1/W^-2=3.323e-04
n=0 u=0.0625: term1=3.740e-07  W^-2=9.766e-04  term1/W^-2=3.830e-04
n=1 u=0.0000: term1=3.979e-13  W^-2=9.537e-07  term1/W^-2=4.172e-07
n=1 u=0.0625: term1=4.586e-13  W^-2=9.537e-07  term1/W^-2=4.809e-07
n=10 u=0.0000: term1=2.740e-28  W^-2=3.765e-14  term1/W^-2=7.278e-15
n=10 u=0.0625: term1=3.158e-28  W^-2=3.765e-14  term1/W^-2=8.388e-15
n=100 u=0.0000: term1=1.056e-50  W^-2=8.841e-24  term1/W^-2=1.195e-27
n=100 u=0.0625: term1=1.217e-50  W^-2=8.841e-24  term1/W^-2=1.377e-27
```
The ratio tends to 0 along `sz0`, so the hypothesis is consistent with the conclusion at the far pairs and not vacuous (the loss factor `(16/15)^{Cd}` at `u = t` is visible and harmless).

### Verdicts
- **Target 1 (pin `STFarEntryAt`, ticket form `W^{τ'}ℓ`)**: BLOCKED by the ticket's consumer check. The statement is true and provable (rows 1–9, 11–13), but it does not serve `STCltIsoConcl` (isolation `10(log W)^3ℓ_s < W^{τ'}ℓ_s`). Dispatcher decision needed: keep the drafted pin (S5-21 then needs another source for the isolated scale) or adopt `STFarEntryAtLog` above (route rows 4–8, 10; compiled instance on `szCL`-type data, not `sz0`).
- **Target 2 (`stFarEntryAt`)**: PASS for the drafted pin (route closes; shortest proof via merged `B45_far_main` at `k = 2`, rows 9, 11–13 plus rows 1–6 for `(GijGEX)`); PASS for the proposed log pin with the row-10 route. Correction to the ticket: neighbour count is `3^{2d}`, not `(2d+1)²` (row 5), no change of exponents.
- **Target 3 (section lemma)**: PASS (row 11, private one-liner `precomp_param`).

## (a′) Preflight corrections — Sun Oct  4 17:29:11 UTC 2026
None changes a verdict.  Stage 1b follows Amend 1 of the ticket (log-scale pin `STFarEntryAtLog`, instance on `Step5Inst.szCL`); the Verdicts block of (a) (target 1 BLOCKED, drafted pin) and rows 9, (ii) (`sz0`) are superseded by it.
1. Row 3: `RBM.Green.stGbEXPij_of_v3` quantifies `0 < κ`, `0 < ε`, `0 < 𝔡` (`Green/Pins.lean:1137`); the theorem therefore carries `hε : 0 < ε` (the ticket lists `0 < κ` only); `s < t` is not used and is dropped.
2. Rows 1, 7 are sharper than needed: Lean uses `c₀ = min(2𝔡, ε/2)` (`N ≥ W` suffices, no `d`) and the loss bound `4 N^{max(Cd,0)+2}` (instead of `4 N^{Cd⁺+6/5}`); both follow from the rows of (a).
3. Row 5 holds as stated: `2·9^d` loops in total (`farEntry_gexRHS_le`).

## (b) Script output — stage 1b (Sun Oct  4 17:29:11 UTC 2026)
```
$ lake build RBM3D.Evolution.FarEntry 2>&1 | grep -E 'FarEntry|Build completed'
Build completed successfully (3804 jobs).
```

```
$ lake build 2>&1 | tail -1   # full library (root does not yet import the new module)
Build completed successfully (3889 jobs).
```

```
$ lake env lean precheck.lean > precheck.out 2>&1; echo exit=$?; head -1 precheck.out; lake env lean pre0.lean 2>&1 | head -1   # registry pre-check (CONTROL §20). precheck.lean: import RBM3D, import RBM3D.Evolution.FarEntry, #assert_rbm_axioms (output line 2); pre0.lean: the same without the new module (output line 3)
exit=0
axiom audit: 4437 theorems, 1577 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
axiom audit: 4432 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

```
$ lake env lean ax.lean | head -7   # ax.lean: import RBM3D, import RBM3D.Evolution.FarEntry, #print axioms of the 5 public theorems and 2 public defs
'RBM.Gauss.Sizes.STFarEntryAtLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stFarEntryAtLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.prec_timeIcc_section' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.farEntry_FarNonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.farEntry_farNonempty_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.farEntry_szCL_far_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.farEntry_szCL_stFarEntryAtLog' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
$ grep -cE 'sorry|admit|native_decide|^axiom' FarEntry.lean; wc -l; grep -c '^private'; git diff --stat main...t/T2141 | tail -2; git log -1 --format='%h %cd' --date=iso-strict
0
     940 RBM3D/Evolution/FarEntry.lean
22
 RBM3D/Evolution/FarEntry.lean | 940 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 940 insertions(+)
f13a06b 2026-10-04T10:22:51-07:00
```

Target statements, extracted from the file by script (`python3 extract.py`):
```
def STFarEntryAtLog (sz : Sizes d) (E τ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' →
    sz.Prec (U := fun n => Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖Gt sz n (E n) (τ n) p.1 ω p.2.1 p.2.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2) : ℕ) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

theorem stFarEntryAtLog (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd) :
    STFarEntryAtLog sz (STflowE z) τ

theorem prec_timeIcc_section {d : ℕ} (sz : Sizes d) {s t τ : ℕ → ℝ} (hsτ : ∀ n, s n ≤ τ n)
    (hτt : ∀ n, τ n ≤ t n) {V : ℕ → Type*} {ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) :
    sz.Prec (U := V) (fun n v ω => ξ n (⟨τ n, hsτ n, hτt n⟩, v) ω)
      (fun n v ω => ζ n (⟨τ n, hsτ n, hτt n⟩, v) ω)
```

Compiled nonempty instance (`python3 extract_inst.py`; `szCL`, `zCL`, `sCL`, `tCL`, `flow_zCL`, `lemT_zCL`, `szCL_hst` are merged, `Induction/Step5Pins.lean`):
```
theorem farEntry_szCL_stFarEntryAtLog (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    STFarEntryAtLog szCL (STflowE zCL) sCL ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
  ⟨stFarEntryAtLog (by norm_num) szCL (κ := 1 / 10) (ε := 1 / 10) (by norm_num) (by norm_num)
    flow_zCL (fun _ => le_rfl) lemT_zCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2,
   farEntry_szCL_far_nonempty⟩

theorem farEntry_szCL_far_nonempty (n : ℕ) : farEntry_FarNonempty szCL sCL 1 n

def farEntry_FarNonempty (sz : Sizes d) (τ : ℕ → ℝ) (c : ℝ) (n : ℕ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ)

example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) : True := by
  have _h1 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2.1
  have _h3 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le)
    (hStep2.2.2 2 (by norm_num))
  trivial
```

```
$ for n in <the 7 new public names>; do count files containing n (worktree, other than FarEntry.lean; main c8e4f17 via git grep); done
STFarEntryAtLog: files elsewhere in worktree=0, in main c8e4f17=0
stFarEntryAtLog: files elsewhere in worktree=0, in main c8e4f17=0
prec_timeIcc_section: files elsewhere in worktree=0, in main c8e4f17=0
farEntry_FarNonempty: files elsewhere in worktree=0, in main c8e4f17=0
farEntry_farNonempty_of: files elsewhere in worktree=0, in main c8e4f17=0
farEntry_szCL_far_nonempty: files elsewhere in worktree=0, in main c8e4f17=0
farEntry_szCL_stFarEntryAtLog: files elsewhere in worktree=0, in main c8e4f17=0
```

```
$ git -C ../RBM2D log -1 --format=%h c9a24cf; git -C ../RBM2D diff --stat c9a24cf HEAD -- RBM2D/Evolution/FarEntry.lean | tail -2   # port source RBM2D FarEntry.lean at c9a24cf (895 lines; RBM2D HEAD is 9e0f275); RBM1D source: none
c9a24cf
 RBM2D/Evolution/FarEntry.lean | 132 ++++++++----------------------------------
 1 file changed, 24 insertions(+), 108 deletions(-)
```

```
$ python3 ext2.py   # limit check of the external hypothesis `STStep2Concl`: `STGdecayW` right side, first term, at the farthest pair r = L/2, `τ = s = 0`, `Cd = D' = 1`, on `szCL` (logs in nats)
n  m  logW   far thr (logW)^3  r=L/2=m^5   log(term1)   log(W^-2D')  log(term1/W^-2D')
   0   24    16.64       4603.7        7962624        -2898.4        -33.3        -2865.2
   1   25    17.33       5203.5        9765625        -3204.3        -34.7        -3169.7
   5   29    20.10       8122.1       20511149        -4619.0        -40.2        -4578.8
  20   44    30.50      28368.4      164916224       -12971.5        -61.0       -12910.5
 100  124    85.95     634952.8    29316250624      -171554.2       -171.9      -171382.3
 500  524   363.21   47914862.3 39505397402624     -6286671.6       -726.4     -6285945.2
far set {1*(log W)^3*ell_0 <= |[x]-[y]|_inf} contains m^5 for all n<100000: True
```

```
$ lake env lean whnf.lean | head -2   # (d) 3: example 1 `x = x` for `x : Idx 3 (szCL.L n) (szCL.W n)` (line 5), example 2 for `x : Zd 3 (szCL.L n)` (line 6); maxHeartbeats 20000; only line 5 errors
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2141/whnf.lean:5:52: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (20000) has been reached
Note: Use `set_option maxHeartbeats <num>` to set the limit.
```


Narrative (stage 1b; every statement is backed by the output above or the file):
- New file `RBM3D/Evolution/FarEntry.lean` (940 lines, 22 private declarations), commit `f13a06b` on `t/T2141`; the diff against `main` is that one file.  The worktree had been created at `f22c63c`, before main `c8e4f17` (T2138, `Induction/Step5Pins`, which the Amend needs for `szCL`); I ran `git merge --ff-only main` in it (the branch had no commits) and refreshed `.lake/build` by `cp -c -R <main>/.lake/build/. .lake/build/`.
- Pin `STFarEntryAtLog` and theorem `stFarEntryAtLog` are as in Amend 1 (the drafted `STFarEntryAt` is neither stated nor proved).  Hypotheses of the theorem: those of the ticket, plus `hε : 0 < ε` ((a′) item 1), minus the unused `s < t`.
- Proof of the charge `+` core (`farEntry_core`): three failure events, merged by the private 3-event union `farEntry_union3` (`3 N^{-(D+1)} ≤ N^{-D}`): `STLocalEntryU` at `τ` (exponent `𝔠 c₀/4`, `c₀ = min(2𝔡, ε/2)`), `STGijGEX` at `ε₀ = c₀/4` (exponent `τ₀/2`), `STGdecayW` at `τ`, `D = 2D'` (exponent `τ₀/2`); the sections are `prec_timeIcc_section` (target 3, public).  RBM2D's `perTimeCalc` chain (`finset_sum_of`, transitivity, `sqrt_of`) is replaced by one deterministic estimate at a fixed `n` outside the three events.
- That estimate: `farEntry_indMax_eq_one` (`STindMax = 1`: `‖G_τ-M‖²_max ≤ N^{𝔠c₀/4} W^{-d}B ≤ 2W^{-3c₀/4}`, from `farEntry_stwb_le`); `farEntry_gexRHS_le` (far set: `STgexRHS ≤ 2·9^d B`, the `W^{-d}` term vanishes since `|a-b|_∞ ≥ 2 > 1`); `farEntry_neighbour` (`|a'-b'|_∞ ≥ (c(log W)³-2)ℓ_τ` by `farEntry_zdistInf_tri`; `‖𝒦‖ ≤ W^{-2D'}` by `farEntry_K_le` and `kellStarEv` at `δ = 1`; `𝓛-𝒦` by the `STGdecayW` bound; loss and `B` are `≤ 4N^{max(Cd,0)+2}` by `farEntry_loss_le`; closing `4W^{K}e^{-√y} ≤ 1`, `K = (max(Cd,0)+2)/𝔠 + 2D'`, `y ≥ c(log W)³-2`, for `log W ≥ X₀(c,K)` by `farEntry_exp_arith`); final `‖G‖² ≤ 6·9^d N^{τ₀}W^{-2D'} ≤ (N^{τ₀}W^{-D'})²` once `6·9^d ≤ N^{τ₀}`.
- Eventual-in-`n` inputs: `N^𝔠 ≤ W`, `RangeCond (ε/2) t`, `(eq:WO)`, the `kellStarEv` event, `X₀ ≤ log W`, `2 ≤ W^{c₀/4}`, `6·9^d ≤ N^{τ₀}`.
- Charge `-`: `Gres H z false = (Gres H z true)ᴴ` (`farEntry_Gres_false`, copy of `ST_Gres_false`, `Step2Iterate.lean:1198`) and `StochDomAt.precomp_param` along `(σ,x,y) ↦ (x,y)` / `(y,x)`; the far set is symmetric (`farEntry_zdistInf_comm`).
- Not used: `B45_far_main` ((a) row 9: power threshold `W^{τ'}`, not `c(log W)³`), `stKcalDecay_holds` (same reason), `s1_gexRHS_le` (asks a bound for all `(σ,b)` and keeps the `W^{-d}` term; its proof is copied with the neighbour-only hypothesis).
- Instance on `szCL` (`flow_zCL`, `s = τ = 0`, `t = 1-L^{-2}`, `Cd = 1`): all deterministic hypotheses discharged, `STStep2Concl` stays a hypothesis (limit check above: the ratio first term of `STGdecayW` / `W^{-2D'}` at the farthest pair is `e^{-2865.2}` at `n = 0` and `e^{-6285945.2}` at `n = 500`); the far set is nonempty at every `n` (`farEntry_szCL_far_nonempty`, `c = 1`, blocks `(x_n, 0)` with `|x_n|_∞ = m⁵`).  `sz0` is not used.
- Registry: no line added (`Axioms.lean` untouched); the pre-check exits 0, `+5` theorems, `+2` definitions.
- Scripts of (b) are in the scratchpad `T2141/` (`precheck.lean`, `pre0.lean`, `ax.lean`, `whnf.lean`, `ext2.py`, `extract.py`, `extract_inst.py`).

## (c) Verified names
Mathlib, present (all used and compiled): `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_one`, `Real.rpow_def_of_pos`, `Real.rpow_one_add'`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.sqrt_eq_rpow`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`, `Real.add_one_le_exp`, `Real.exp_add`, `Real.exp_le_exp`, `Real.exp_pos`, `Real.tendsto_log_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `pow_le_pow_iff_left₀` (`n := 2`), `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `le_div_iff₀`, `div_le_iff₀`, `div_le_div_iff₀`, `div_le_one`, `one_le_mul_of_one_le_of_one_le`, `le_mul_of_one_le_right`, `Finset.card_le_two`, `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.sup_le`, `Finset.sup_congr`, `Finset.le_sup`, `ENNReal.ofReal_add`, `ENNReal.ofReal_le_ofReal`, `MeasureTheory.measure_mono`, `MeasureTheory.measure_union_le`, `Matrix.conjTranspose_apply`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `norm_star`, `Equiv.apply_symm_apply`, `Complex.norm_natCast`, `Nat.le_self_pow`, `Nat.le_mul_of_pos_right`, `Set.mem_ofPred_eq`.
Project (merged), present: `RBM.Green.stGbEXPij_of_v3` (`Green/Pins.lean:1137`), `RBM.Green.gbEXPV3` (`GbEXP.lean:806`), `RBM.Green.v3_premises_of_stFlow` (`Pins.lean:1049`), `RBM.Path.kellStarEv` (`KellStar.lean:173`), `RBM.Loop.KLK_two` (`KLTree.lean:211`), `RBM.Loop.KLmSigma_mul_not` (`:445`), `RBM.StochDomAt.precomp_param` (`Defs/StochDomAt.lean:335`), `RBM.Gauss.Sizes.tendsto_size` (`Defs/StochDomAt.lean:735`), `RBM.Gauss.Sizes.size_rpow_le_W_rpow`, `RBM.Gauss.Sizes.lam_sq_mul_pow_ge`, `RBM.Gauss.Sizes.seqHflow_isHermitian`, `RBM.Ind.s1_near_card`, `RBM.Ind.PerTimeCalc.Unif.perTimeCalc_of_imp`, `RBM.eventually_le_rpow`, `RBM.Gauss.Step5Inst.{szCL, zCL, sCL, tCL, flow_zCL, lemT_zCL, szCL_hst, zdistInf_xCL, szCL_ellT_s, szCL_log_W_le, szCL_one_le_log_W}`.
Absent or deprecated here: `RBM.zdistInf_le_zdistD` (it is `RBM.Gauss.zdistInf_le_zdistD`), `RBM.Gauss.Sizes.s1_near_card` (it is `RBM.Ind.s1_near_card`), `if_neg` (deprecated, "Use `ite_eq_right`"; replaced by `simp [h]`), `Set.mem_setOf_eq` (deprecated, "Use `Set.mem_ofPred_eq`"), `import Mathlib` (no `Mathlib.olean` in `.lake/packages/mathlib/.lake/build`: scratch checks import a project module).

## (d) Open issues and paper-delta candidates
1. **T2141a** (log-scale threshold, `3_5:2245`): the far set is `{c (log W)³ ℓ_τ ≤ |[x]-[y]|_∞}` for every `c > 0` (consumer `STCltIsoConcl`: isolation `10 (log W)³ ℓ_s`), not RBM2D's `W^{τ'} ℓ_u`; the drafted pin follows by `W^{τ'} ≥ c (log W)³` eventually.  The paper omits the proof of `(eq:bound_isolated)` and cites [DYYY25, (7.39)] (`3_5:2245`).
2. **T2141b** (hypotheses): the theorem needs `0 < ε` (quantifier of `STGbEXPij`; the paper's `𝐃_{κ,ε}`, `ε > 0` small); `s < t` of the ticket is not needed.  The statement is for both charges and all pairs `(x,y)` of fine lattice points (RBM2D: `σ = +` only, the consumer transposes).
3. **Elaboration trap for the instance writers of S5-20/S5-21** (output above): a statement that spells a type `Idx 3 (szCL.L n) (szCL.W n)` (symbolic `n`, `L = 2(n+24)^5`, `W = 2^{n+24}`) times out at `whnf` (even at 2·10⁶ heartbeats); `Zd 3 (szCL.L n)` is fine.  Workaround used here: state the nonempty-set witness by a generic definition `farEntry_FarNonempty (sz) …` applied to `szCL`, and prove it from `farEntry_farNonempty_of` (generic `sz`, blocks `(a,b)` ↦ points by `splitEquiv`).
4. Name policy: `prec_timeIcc_section` is a ticket target (item 3) kept public with a docstring and an unprefixed name; if the dispatcher wants the stem prefix (CLAUDE.md §3 (E)), rename before S5-20 imports it.  The other new public names carry the prefix `farEntry_` or are the pinned `STFarEntryAtLog`/`stFarEntryAtLog`.
5. Consumer check (ticket item): not re-done here; (a) found that `STCltIsoConcl` (time `s`, pairs of blocks, both charges, scale `10 (log W)³ℓ_s`) is served by the log pin, and the Amend adopted it.  per the ticket, S5-20 uses it with `D'+1` and a union bound (RBM2D `cltFarEntry_whp`, `CltGood.lean:531`).
