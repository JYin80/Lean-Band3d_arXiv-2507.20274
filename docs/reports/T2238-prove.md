Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 01:26:38 UTC 2026
Scratch dir `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2238` (python3 + numpy; `num.py` reuses T2205's `ba.py`: torus spectrum `2Σcos`, continuation Newton for the real-axis `(self_m)`). Notation: `g₀ = √t₀ g` (`BAflowLam0`), `g₀'` that of the member `z'`, `u = 1 - c₁`, `𝓛 = BALloop`, `W^{-d}` the volume factor.

### (i) Exponent table (pin `BATrivialLmax`, `d = 3`, `sz0`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `c₁ = 1/3`)
| # | quantity | value / derivation | constraint | slack |
|---|---|---|---|---|
| 1 | time `u = 1 - c₁` | `0 < c₁ ≤ 1/2`, so `max 0 (1-c₁) = 1-c₁`, `u ∈ [1/2, 1)` | `0 ≤ u < 1` (`s1_Wd_le_Bctl`, `STBctl_pos`) | `u = 2/3`; `1-u = c₁ > 0` |
| 2 | `t₀'` of a member (`BAFamZ`, `u ≡ 0`) | `min(t₀, 1-c₁) ≤ t₀' ≤ t₀`, `0 < t₀ < 1` (`BAflow_T0_bounds`) | `t₀' ≥ (1-c₁) t₀` | case `t₀ ≤ 1-c₁`: `t₀' ≥ t₀ ≥ (1-c₁)t₀`; case `t₀ > 1-c₁`: `t₀' ≥ 1-c₁ > (1-c₁)t₀`. sz0 `n=0`: `0.66667 ≥ 0.46249`, slack 0.204; grid min slack `c₁ t₀ → 0` as `t₀ → 0` (non-strict, closes) |
| 3 | window `g₀'/g₀` | `g₀' = √t₀' g ∈ [√(1-c₁) g₀, g₀]` (`sqrt_mul`, `lam n > 0`) | `BAWinBulk` hypothesis range | `√(1-c₁) = 0.8165`; extreme member `g₀'/g₀ = 0.9803` at `n=0` |
| 4 | `Im m` at the member's coupling | `BAWinBulk` at `g' = g₀'` (member's `E' = E`, first conjunct of `BAFamZ`): `Im m(E,g₀') ≥ κ` | `≥ κ` | sz0: `0.99951 ≥ 0.5` (`n=0`), `1.00000` (`n=1,2`); slack factor 2.0 |
| 5 | `η_u = Im z_u` | `ztOf_im`: `(1-u) Im m = c₁ Im m(E,g₀') ≥ c₁κ` | `η ≤ Im z_u`, `η > 0` | `η = c₁κ = 1/6`; actual `0.3332` (`n=0`), `0.3333`; `‖G‖ ≤ 1/η`: 6 vs actual 3.0015 |
| 6 | loop envelope | `‖𝓛^{(k)}‖ ≤ η^{-k} (W^{-d})^{k-1}` (`norm_loopM_le_sharp`, `H` Hermitian, `η ≤ |Im z|`) | `k ≥ 1` | k=1: 6 vs 3.0015 |
| 7 | volume vs control | `W^{-d} ≤ (lam²+1) Bctl(u)` (`s1_Wd_le_Bctl`, `Bparam ≥ (g²+1)^{-1}`) | `0 ≤ u < 1` | sz0 `n=0`: `3.05e-5 ≤ 9.29e-5` (3.0x); `n=1`: 3.0x; `n=2`: 3.0x |
| 8 | coupling bound | `lam n ≤ 𝔡⁻¹` eventually (`(eq:WO)`, 2nd conjunct of `WO`, 5th of `Admissible`); `lam² + 1 ≤ 𝔡⁻² + 1` | eventual in `n` | sz0: `lam ≤ 1/64 ≤ 10 = 𝔡⁻¹` for all `n`; `𝔡⁻²+1 = 101` vs `lam²+1 = 1.0002` |
| 9 | constant `C(k)` | `(c₁κ)^{-k} (𝔡⁻²+1)^{k-1}`: depends on `k, c₁, κ, 𝔡` only, not on `n`, `N`, `ε`, `𝔠`, `L`–`W` | `C` before `n` | `k=1,2,3`: `6, 3636, 2203416`; no power of `N` |
| 10 | `≺` absorption | `ξ ≤ C ζ` eventually, `ζ = Bctl(u)^{k-1} > 0` (`STBctl_pos`); `C ζ ≺ ζ` since `N^τ ≥ C` eventually (`N → ∞`, `SizeTendsto`), any `τ, D > 0`; law irrelevant (bad set eventually empty) | `τ' = τ` | needs `N^τ ≥ C` only; e.g. `τ = 1/10`, `k=2`: `N ≥ 3636^{10}` (eventual, no witness size needed: `≺` is asymptotic) |
| 11 | actual vs `Cζ` | `η^{-k}(W^{-d})^{k-1}` vs `C Bctl^{k-1}` at `n=0`, `k=2`: `2.75e-4 ≤ 0.338` | `ξ ≤ Cζ` | factor 1229; actual `ξ/ζ = 2.96, 2.99, 3.00` at `n = 0,1,2` (`k=2`) |
`ε`, `𝔠`, `0 < ε` and the third component of `BAdom` (`Im z ≤ 1`) are not used; of `BAdom` only `Im m ≥ κ` and `N^{-1+ε} ≤ Im z` enter (through `BAflow_T0_bounds`, `Im z_n > 0`); `d` enters through `W^{-d}` only (no `3 ≤ d`, no `L`–`W` relation).

### (ii) Concrete nondegenerate instance (hypotheses of all 6 public theorems at once)
Data: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`), `z_n = zS(L_n, lam_n)` (`w = 6i/5`), `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)` (`flow_sz0`, `Admissible`: `adm.out` of T2205, `N = 2.1e6, 5.5e11, 8.1e14` at `n = 0,1,2`, `N^{1/6} ≤ W`), `c₁ = 1/3`, window `[√(2/3) g₀, g₀]`, members: the main flow (`BAFamZ_main`) and the lowest member `t₀' = min(t₀, 2/3)`. `lam_n > 0` all `n`; `0 < κ, ε, 𝔡`; `0 < c₁ ≤ 1/2`.
`cd $S && python3 num.py`:
```
sz0, d=3, kappa=1/2, dd=1/10, c1=1/3, u=1-c1=2/3, Cbound(k)=eta^-k (dd^-2+1)^(k-1), eta=c1*Im m(E,g0')
n=0: Im z=0.3675 t0=0.69374 E=3.124e-18 g0=1.3014e-02; Im m(E,g0)=0.99949; window min Im m=0.99949>=1/2: True
      member t0'=min(t0,1-c1)=0.66667: g0'=1.2758e-02 in [1.0626e-02,1.3014e-02]: True, Im m(E,g0')=0.99951; eta=c1 Im m=0.33317, ||G||<=1/eta=3.0015
      k=1: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 6.0000; actual eta^-k (W^-d)^(k-1)=3.0015e+00 <= C*Bctl^(k-1)=6.0000e+00: True
      k=2: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 3636.0000; actual eta^-k (W^-d)^(k-1)=2.7493e-04 <= C*Bctl^(k-1)=3.3784e-01: True
      k=3: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 2203416.0000; actual eta^-k (W^-d)^(k-1)=2.5183e-08 <= C*Bctl^(k-1)=1.9023e-02: True
      W^-d=3.0518e-05 <= (lam^2+1)Bctl(2/3)=9.2939e-05: True; lam=1.5625e-02<=1/dd=10: True
n=1: Im z=0.3667 t0=0.69444 E=2.439e-20 g0=2.0345e-04; Im m(E,g0)=1.00000; window min Im m=1.00000>=1/2: True
      member t0'=min(t0,1-c1)=0.66667: g0'=1.9934e-04 in [1.6612e-04,2.0345e-04]: True, Im m(E,g0')=1.00000; eta=c1 Im m=0.33333, ||G||<=1/eta=3.0000
      k=1: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 6.0000; actual eta^-k (W^-d)^(k-1)=3.0000e+00 <= C*Bctl^(k-1)=6.0000e+00: True
      k=2: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 3636.0000; actual eta^-k (W^-d)^(k-1)=8.3819e-09 <= C*Bctl^(k-1)=1.0179e-05: True
      k=3: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 2203416.0000; actual eta^-k (W^-d)^(k-1)=2.3419e-17 <= C*Bctl^(k-1)=1.7268e-11: True
      W^-d=9.3132e-10 <= (lam^2+1)Bctl(2/3)=2.7994e-09: True; lam=2.4414e-04<=1/dd=10: True
n=2: Im z=0.3667 t0=0.69444 E=6.626e-21 g0=1.7861e-05; Im m(E,g0)=1.00000; window min Im m=1.00000>=1/2: True
      member t0'=min(t0,1-c1)=0.66667: g0'=1.7500e-05 in [1.4584e-05,1.7861e-05]: True, Im m(E,g0')=1.00000; eta=c1 Im m=0.33333, ||G||<=1/eta=3.0000
      k=1: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 6.0000; actual eta^-k (W^-d)^(k-1)=3.0000e+00 <= C*Bctl^(k-1)=6.0000e+00: True
      k=2: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 3636.0000; actual eta^-k (W^-d)^(k-1)=1.9141e-11 <= C*Bctl^(k-1)=2.3213e-08: True
      k=3: bound eta^-k(dd^-2+1)^(k-1) at eta=c1*kappa: 2203416.0000; actual eta^-k (W^-d)^(k-1)=1.2213e-22 <= C*Bctl^(k-1)=8.9806e-17: True
      W^-d=2.1268e-12 <= (lam^2+1)Bctl(2/3)=6.3842e-12: True; lam=2.1433e-05<=1/dd=10: True
```
`cd $S && python3 win.py` (the elementary step of `BAFamZ_lam0_window`, row 2-3):
```
grid 500x500 (c1 in (0,1/2], t0 in (0,1)): violations of t0'>=(1-c1)t0 / sqrt: 0 ; min slack t0'-(1-c1)t0 = 9.999999999994822e-09
u=1-c1=0.6667 in [1/2,1); sqrt(1-c1)=0.8165; eta_min=c1*kappa=0.1667; 1/eta_min=6.0
n=0 slack: t0=0.69374, min(t0,1-c1)=0.66667, (1-c1)t0=0.46249, diff=0.20417; g0'/g0=0.9803 vs sqrt(1-c1)=0.8165
C(k)=(c1 kappa)^-k (dd^-2+1)^(k-1): [6, 3636, 2203416]
```
External hypothesis: none (every input is merged: T2013, T2197, T2227, T2189, T2079). `BAWinBulk` stays a hypothesis of the instance `example` (its `sz0` instance is BA-S3's, T2227 Not targets); its content at this data is the `window min Im m ≥ 1/2: True` column above (min `0.99949`, `1.00000`, `1.00000` at `n = 0,1,2`, 200-point grid of the window). Limit computation for the window premise: `lam_n → 0` and `g₀ = √t₀ lam_n = 1.3e-2, 2.0e-4, 1.8e-5 → 0` while `Im m(E,g₀) = 0.99949, 1.00000, 1.00000 → 1 ≥ 1/2` (script `num.py`); `BAFlow`'s limits: `N_n → ∞`, `W^6/N → ∞`, `lam_n/W^{-1.4} = 2(n+1) → ∞`, `lam_n ≤ 1/10` (T2205 `adm.out`).

### Pin table, paper, §29, two-data line, consumers, registry, script
**Pin table.**
- `BATrivialLmax`: `(lRB1)` at the single time `1-c₁` for every member of `Fam(0)`: `max|𝓛^{(k)}| ≺ (W^{-d}B_{s₀,0})^{k-1}`; paper `7_8:1987-1990` ("same as [RBSO1D, §7.1]", D536 = T2205b, `docs/paper-deltas.md:1495`, cite only); class: proved here (`BATrivialLmax_holds`); consumer: `hT` of `BAStep1_of_parts` (BA-S3).
- `BAFamZ`: the family `Fam(u)` (route (A): same `E`, `t₀' ∈ [min(t₀, max(u,1-c₁)), t₀]`); class: structural (portmap P.2 `T2205-portmap.md:21`); consumers: all family pins (BA-S2b, BA-S3, BA-V2a/b).

**Against the paper (verdict PASS, both).** `lem:main_ind_BA` Step 1 (`7_8:1990`) is `(lRB1)`, `(Gtmwc)` "as in [RBSO1D, §7.1]" with `W^{-d}B_{s,0}` in place of `(W^dℓ_s^dη_s)^{-1}` (`7_8:1987`). The merged band model is `s1_loop_det` (`Step1Setup.lean:653`, `‖𝓛‖ ≤ (2/c₁)^k (W^{-d})^{k-1}` for `u ≤ 1/2`) and the second branch of `s1_h55` (`:732-758`). Here the time is `1-c₁ ≥ 1/2` and `Im z_u = (1-u) Im m(E,g₀') ≥ c₁κ` replaces `Im m ≥ c₁` (T2205 `(a)(i)` rows 5, 8): same estimate, one fixed time, constant `(c₁κ)^{-k}(𝔡⁻²+1)^{k-1}`. `BAFamZ` is `Fam(u)` of route (A) (T2205 `(a)(i)` header, D536). No new paper delta (D536 covers the family; docstring change (c1) only).

**§29 (1)-(7).** (1) one time `u = 1-c₁ ∈ [1/2,1)`; (2) no gate; (3) no `L`-`W` relation, `𝔡` through `(eq:WO)` only; (4) `∀ n` premises (`0 < lam n`, `BAFamZ`), conclusion `≺` eventual in `n`, constant `C(k,c₁,κ,𝔡)` before `n`; (5) law irrelevant (deterministic bound); (6) `0 < κ, ε, 𝔡, c₁ ≤ 1/2`; (7) no loss in `κ`: the member's own `Im m ≥ κ` from `BAWinBulk` at `κ`.

**Two data, one model (PASS).** `BAWinBulk` constrains `m(E, g')` only for `g'` in `[√(1-c₁)g₀, g₀]` (statement of `BAWinBulk`, `CouplingWindow.lean:799`), and the proof reads `Im m` only at `g₀'` of the member, which lies in that window (rows 2-4). Two flows with the same window values and different `m(E, g')` below `√(1-c₁)g₀` therefore satisfy the same hypotheses and give the same `C`; consistent with portmap P.6 row `BATrivialLmax` ("independent", `T2205-portmap.md:114`).

**Consumer check (§45 O2, PASS).** B4 is the probe text the consumers compiled against (probe `:1830-1870`, `:2101`, `:3696`): application only, none unfolds `BATrivialLmax`; definitions it mentions are textually equal to `main` (script below).

**Registry plan.** No line (ticket Targets 4): `BATrivialLmax` is concluded by `BATrivialLmax_holds`; binder heads `BAFlow`, `BAWinBulk`, `BAFamZ` are concluded by `flow_sz0`, `BAWinBulk_of_dom`, `BAFamZ_main`; pre-check by stage 1b.

**Script** (`cd $S && python3 blocks.py`; `probe.txt = git --no-optional-locks show 96e4087:RBM3D/Probe/T2205Pins.lean`, 3989 lines; the `main` side is `RBM3D/BA/FlowPins.lean` at `cc4d165`, definition bodies whitespace-normalised):
```
B1 :1250-1254 lines=5 first='/-- Route (A) family at time `u`, the horizon cone: spectral' last='    min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz'
B2 :1284-1291 lines=8 first='/-- In the chain domain `Im z > 0`, `Im m(z, g) > 0` and `0 ' last='  exact ⟨hzpos, hmpos, BAt0_pos hzpos hmpos, BAt0_lt_one hzp'
B3 :1293-1295 lines=3 first='/-- *Proved.* The main flow is a member of the family at eve' last='  fun _ => ⟨rfl, min_le_left _ _, le_rfl⟩'
B4 :1775-1784 lines=10 first='/-- **(lRB1) is deterministic below `1 - c₁`** (BA-S2): at t' last="          STLmaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0))"
PrecL      probe=found main=found equal=True
FlowFM     probe=found main=found equal=True
STLmaxgL   probe=found main=found equal=True
BAmF       probe=found main=found equal=True
BAMfine    probe=found main=found equal=True
BAGt       probe=found main=found equal=True
BALloop    probe=found main=found equal=True
BAKloop    probe=found main=found equal=True
BAKsol     probe=found main=found equal=True
BAMLoop    probe=found main=found equal=True
baFM       probe=found main=found equal=True
BAflowT0   probe=found main=found equal=True
BAflowEs   probe=found main=found equal=True
BAflowLam0 probe=found main=found equal=True
BAFlow     probe=found main=found equal=True
baFMz      probe=found main=found equal=True
```
Name-clash grep (`grep -rnE` of the 8 public and 2 private names over `RBM3D/`, excluding `Probe/`, main worktree `cc4d165`): 0 hits; `grep -rn Step1Trivial RBM3D docs/queue/CONTROL.md`: 1 hit (CONTROL.md:16, the release line of T2238). `docs/tickets/T2237.md` mentions none of `BAFamZ`, `BAflow_T0_bounds`, `BATrivialLmax`.

### Verdicts
- Targets 1 (move B1-B4): PASS (blocks have 5, 8, 3, 10 lines; definitions used are textually equal to `main`).
- `BAFamZ_lam0_window`: PASS (rows 2-3). `BAFamZ_im_m_ge`: PASS (row 4). `baFM_loop_det`: PASS (rows 5-6). `BATrivialLmax_holds`: PASS (rows 7-11). `BAflow_T0_bounds`, `BAFamZ_main`: PASS (moved). Instance (ii): PASS.

## (b) Script output — Tue Oct  6 01:52:28 UTC 2026
Branch `t/T2238` commit `2738b7e` (base cc4d165); files: `RBM3D/BA/Step1Trivial.lean` (208 lines, new), `RBM3D/Test/Axioms.lean` (+2/-1: one registry line, see below).
```
$ git diff --stat main...t/T2238
 RBM3D/BA/Step1Trivial.lean | 208 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   3 +-
 2 files changed, 210 insertions(+), 1 deletion(-)
$ lake build RBM3D.BA.Step1Trivial   (after touch; no linter output other than longLine warnings from the moved docstrings)
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3751 jobs).
$ lake env lean RBM3D/BA/Step1Trivial.lean 2>&1 | grep -v "^$\|^Note\|exceeds"
(no output)
$ lake env lean ax.lean   (import RBM3D.BA.Step1Trivial; #print axioms of the 6 public theorems)
'RBM.BA.BAflow_T0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_lam0_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_im_m_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFM_loop_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATrivialLmax_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/Step1Trivial.lean
(no hits)
$ python3 verb.py   (B1-B4 from git show 96e4087:RBM3D/Probe/T2205Pins.lean, B4 after (c1), contiguous in the file)
B1 1250-1254 True 1624
B2 1284-1291 True 2054
B3 1293-1295 True 2697
B4 1775-1784 (c1) True 6687
```

**Targets, extracted by script** (`sed -n` of the declaration up to `:=`; B1-B4 are the moved text):
```
--- RBM3D/BA/Step1Trivial.lean:42,44
def BAFamZ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (z' : ℕ → ℂ) : Prop :=
  ∀ n, BAflowEs sz z' n = BAflowEs sz z n ∧
    min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n ∧ BAflowT0 sz z' n ≤ BAflowT0 sz z n
--- RBM3D/BA/Step1Trivial.lean:47,49
theorem BAflow_T0_bounds {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im ∧ 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im ∧ 0 < BAflowT0 sz z n ∧ BAflowT0 sz z n < 1 := by
  obtain ⟨hκm, hz1, -⟩ := h.2 n
--- RBM3D/BA/Step1Trivial.lean:56,57
theorem BAFamZ_main (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) : BAFamZ sz z c₁ u z :=
  fun _ => ⟨rfl, min_le_left _ _, le_rfl⟩
--- RBM3D/BA/Step1Trivial.lean:61,65
theorem BAFamZ_lam0_window {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hlam : ∀ n, 0 < sz.lam n) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) {z' : ℕ → ℂ}
    (hfam : BAFamZ sz z c₁ (fun _ => 0) z') (n : ℕ) :
    Real.sqrt (1 - c₁) * BAflowLam0 sz z n ≤ BAflowLam0 sz z' n ∧ BAflowLam0 sz z' n ≤ BAflowLam0 sz z n := by
  obtain ⟨-, -, ht0, ht1⟩ := BAflow_T0_bounds hκ hflow n
--- RBM3D/BA/Step1Trivial.lean:86,90
theorem BAFamZ_im_m_ge {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hlam : ∀ n, 0 < sz.lam n) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hwin : BAWinBulk sz z c₁ κ)
    {z' : ℕ → ℂ} (hfam : BAFamZ sz z c₁ (fun _ => 0) z') (n : ℕ) :
    κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := by
  obtain ⟨h1, h2⟩ := BAFamZ_lam0_window hκ hflow hlam hc₁ hc₁' hfam n
--- RBM3D/BA/Step1Trivial.lean:119,123
theorem baFM_loop_det (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u η : ℝ) (hη : 0 < η)
    (hz : η ≤ (ztOf (BAmF sz lam0 E n) (E n) u).im) (k : ℕ) (hk : 1 ≤ k) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖(baFM sz lam0 E).L n u σ a ω‖ ≤ η⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
--- RBM3D/BA/Step1Trivial.lean:139,145
def BATrivialLmax (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
          STLmaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 1 - c₁)

--- RBM3D/BA/Step1Trivial.lean:150,151
theorem BATrivialLmax_holds (d : ℕ) : BATrivialLmax d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hfam k hk
```
**Compiled nonempty instance** (`RBM3D/BA/Step1Trivial.lean:194-206`, `d = 3`, merged T2197 data `sz0`, `zSeq`; `BAWinBulk` is the only hypothesis, its `sz0` instance is BA-S3's):
```
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- Instance at `d = 3` and the merged data `sz0`, `zSeq` of T2197; the window premise `BAWinBulk` (its `sz0` instance
belongs to BA-S3) is the only hypothesis. -/
example (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 - 1 / 3) :=
  BATrivialLmax_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin zSeq
    (BAFamZ_main sz0 zSeq (1 / 3) (fun _ => 0))

end Instance
```
**Check-file equality** (`eq.lean` = check-file imports + `import RBM3D.BA.Step1Trivial` + rest of `docs/tickets/checks/T2238-check.lean` + the 8 examples of the acceptance list; `lake env lean`):
```
$ lake env lean eq.lean > eq.out; echo exit $?; grep -c error eq.out
exit 0
0
$ tail -8 eq.lean
example {d : ℕ} : @RBM.BA.T2238Check.BAFamZ d = @RBM.BA.BAFamZ d := rfl
example : RBM.BA.T2238Check.BATrivialLmax = RBM.BA.BATrivialLmax := rfl
example : RBM.BA.T2238Check.BAflow_T0_bounds_pin := @RBM.BA.BAflow_T0_bounds
example : RBM.BA.T2238Check.BAFamZ_main_pin := @RBM.BA.BAFamZ_main
example : RBM.BA.T2238Check.BAFamZ_lam0_window_pin := @RBM.BA.BAFamZ_lam0_window
example : RBM.BA.T2238Check.BAFamZ_im_m_ge_pin := @RBM.BA.BAFamZ_im_m_ge
example : RBM.BA.T2238Check.baFM_loop_det_pin := @RBM.BA.baFM_loop_det
example : RBM.BA.T2238Check.BATrivialLmax_holds_pin := @RBM.BA.BATrivialLmax_holds
```
**Name-clash grep** (worktree base cc4d165, `RBM3D/` minus `Probe/` and the new file):
```
$ grep -rnE "BAFamZ|BAflow_T0_bounds|BATrivialLmax|BAFamZ_lam0_window|BAFamZ_im_m_ge|baFM_loop_det|Step1Trivial_" RBM3D --include=*.lean | grep -v "^RBM3D/Probe\|^RBM3D/BA/Step1Trivial.lean" | cut -c1-110
(0 hits outside the new file; the only hit in Test/Axioms.lean is my registry comment naming BAFamZ_im_m_ge, BATrivialLmax)
```

**Registry pre-check and full build** (worktree; temp file `reg.lean` = `import RBM3D` + `import RBM3D.BA.Step1Trivial` + `#assert_rbm_axioms`, uncommitted):
```
$ lake env lean reg.lean > reg.out; echo exit $?; grep -c error reg.out
exit 0
0
$ grep -n "registry:" reg.out | cut -c1-120
151:registry: 2 borrowed + 141 owed + 89 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.
(first run, before the registry line: error "1 premise(s) ... in none of borrowedProps, owedProps, structuralProps, refutedProps: [RBM.BA.BAWinBulk]")
$ lake build   (worktree, library as on t/T2238; RBM3D.lean does not yet import Step1Trivial: the hub adds it at merge)
Build completed successfully (4040 jobs).
```

**Narrative.**
- New file `RBM3D/BA/Step1Trivial.lean` (208 lines): B1-B3 verbatim (`BAFamZ`, `BAflow_T0_bounds`, `BAFamZ_main`), then the three new theorems `BAFamZ_lam0_window`, `BAFamZ_im_m_ge`, `baFM_loop_det`, then B4 (`BATrivialLmax`, change (c1) only, docstring), `BATrivialLmax_holds`, and the instance `example`.
- `BAFamZ_lam0_window`: `max 0 (1-c₁) = 1-c₁`, `t₀' ≥ min(t₀, 1-c₁) ≥ (1-c₁)t₀` by cases, `Real.sqrt_mul`, `Real.sqrt_le_sqrt`.
- `BAFamZ_im_m_ge`: `BAWinBulk` at `g' = BAflowLam0 sz z' n`; the member's energy equals `BAflowE (z n) (BAm …)` by the first conjunct of `BAFamZ` (then `rw`).
- `baFM_loop_det`: `norm_loopM_le_sharp` as in `s1_loop_det`; Hermitian helpers are the private `Step1Trivial_seqHflowBA_herm` (re-proved, text of `FlowPins.lean:1077-1083`) and `Step1Trivial_blockMat_herm` (text of `Step1Setup.lean:644`).
- `BATrivialLmax_holds`: constant `C = (c₁κ)⁻ᵏ(𝔡⁻²+1)^{k-1}`; `StochDomAt.refl` and `.const_mul_left` give `Cζ ≺ ζ`, `StochDomAt.of_subset` with `τ' = τ` transfers it to the family via the eventual pointwise bound (eventual in `n` from `WO 𝔡`, `hflow.1.2.2.2.2`). The hypotheses `0 < ε`, `0 < 𝔡` (and the third conjunct of `BAFamZ`) are unused beyond their roles in `BAFlow`; `ε`, `h𝔡` are not flagged by the linter (the elaborator reported no unused-variable warnings for this file).
- Registry: the pre-check flagged `RBM.BA.BAWinBulk` (it is a binder head of `BAFamZ_im_m_ge`, and `BAWinBulk_of_dom` concludes `BAWinBulk_of_dom_stmt`, not `BAWinBulk`); per ticket Targets 4 it is registered in `structuralProps` (one line, `Test/Axioms.lean:336`, ticket-permitted second writable file). `BAFamZ`, `BAFlow`, `BATrivialLmax` were not flagged.
- **Merge note for the hub:** `t/T2238` is based on cc4d165; `main` has moved on and `Test/Axioms.lean` differs there (other tickets' lines). Apply the Axioms change as the patch `git diff cc4d165 t/T2238 -- RBM3D/Test/Axioms.lean` (3 lines: `qd2Bad]` becomes `qd2Bad,` plus one new line `RBM.BA.BAWinBulk]`), not as a file copy. `git diff main...t/T2238` is the three-dot diff shown above.
- No import beyond the ticket's list (`RBM3D.BA.CouplingWindow`, `RBM3D.BA.FlowPins`, `RBM3D.Induction.Step1Setup`) plus the two Mathlib modules of the check file (`Mathlib.LinearAlgebra.Matrix.Hermitian`, `Mathlib.Analysis.Real.Sqrt`).

## (c) Verified Mathlib names (all compile in `Step1Trivial.lean`)
- `Matrix.IsHermitian.submatrix`, `Matrix.IsHermitian.add`, `Matrix.conjTranspose_smul`, `Complex.conj_ofReal`.
- `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `le_abs_self`, `pow_le_pow_left₀`, `mul_pow`, `min_eq_left`, `min_eq_right`, `max_eq_right`, `le_total`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`.
- Merged: `RBM.Ind.s1_hsize`, `RBM.Ind.s1_Wd_le_Bctl`, `RBM.Gauss.Sizes.STBctl_pos`, `RBM.StochDomAt.refl`, `.const_mul_left`, `.of_subset`, `RBM.Gauss.norm_loopM_le_sharp`, `RBM.Gauss.ztOf_im`.
- Verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- No new paper-delta candidate: D536 (T2205b, `docs/paper-deltas.md:1495`) covers the family; (c1) is a docstring change only.
- Preflight (a) numerics: unchanged; no correction (a′) needed.
- `Test/Axioms.lean` registry: `RBM.BA.BAWinBulk` in `structuralProps` (see narrative); dispatcher may reclassify.
- Not claimed: `(lRB1)` at every `u ≤ 1 - c₁` (remark in the `BATrivialLmax` docstring), `sz0` window instance (BA-S3).
