Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:53:26 UTC 2026

Notation: `N = (W L)^d`, `a = min(2𝔠𝔡, ε/2)`, `L0 = (log W)^3 ℓ_s`, `ℓ_s = ellT L lam s` (`Defs/Params.lean:30`).
HClt at `(sz, κ, ε, 𝔠, 𝔡, z, s, τ, t, Cd)`: `3 ≤ d`, `0<κ`, `0<ε`, `STFlow sz κ ε 𝔠 𝔡 z`, `0 ≤ s ≤ τ ≤ t ≤ lemT z`, `STStep2Concl sz (STflowE z) s t Cd`; `E = STflowE z`.

### (i) Exponent table

Dictionary of item 1 (RBM2D `Evolution/CltGood.lean:62` `HClt` at `c9a24cf` → merged RBM3D):

| RBM2D hypothesis | RBM3D replacement (location) |
|---|---|
| `SizeTendsto`, `Bandwidth d 𝔠` (`W ≥ N^𝔠`), `0<𝔠` | `STFlow.1 = Admissible 𝔠 𝔡` (`Defs/Sizes.lean:177`) |
| `(eq:WO)` (absent in 2D) | `Admissible.WO 𝔡`; enters via `lam_sq_mul_pow_ge` (`Sizes.lean:193`): `lam² W^d ≥ W^{2𝔡}` |
| `\|E n\| ≤ 2-κ`, `t n < 1` | `v3_premises_of_stFlow` (`Green/Pins.lean:1049`): `\|STflowE z n\| < 2-κ/2`, `t n < lemT(z n) < 1` |
| `RangeCond d δ t` | same lemma, `δ = ε/2`: `N^{-1+ε/2} ≤ 1 - t n` eventually |
| `Step2LocalPT` on `[s₀,t₀]` | `STStep2Concl.1 = STLocalEntryU` (`Step34Pins.lean:199`), section at `τ`: `prec_timeIcc_section` (`FarEntry.lean:63`) |
| `Step2DecayPT` | `STStep2Concl.2.2 = STGdecayW` (used only inside `stFarEntryAtLog`, `FarEntry.lean:835`) |
| `GbEXPHypV3` | not a hypothesis: proved, `stGbEXPij_of_v3 (gbEXPV3 hd)` inside `stFarEntryAtLog` (needs `hd : 3 ≤ d`) |
| `\|m\| = 1` (`normSqSpectralMOne`) | `norm_mE (hE : \|E\| ≤ 2) : ‖mE E‖ = 1` (`Defs/Semicircle.lean:63`) |
| `Step2*PT` is per-time, `D+2` and a union over `N²` pairs | `Prec` has the union over the index inside `P` (`badSetAt`, `StochDomAt.lean:53`): index `(x,y)` / `(σ,x,y)` is in `U`, so no extra exponent: charge `D`, not `D+2` |

Constants and constraints:

| # | Quantity | Value / constraint | Slack |
|---|---|---|---|
| 1 | variance of a coordinate | `gvarF ≤ svarF = W^{-d} sbKernelR ≤ W^{-d}`: `sbKernelR ≥ 0` and `∑_x sbKernelR = 1` (`Defs/Block.lean`, `sum_sbKernelR`, `3 ≤ L`) so each value `≤ 1`. Worst value: diagonal coordinate, `W^{-d}(1+2d g²)^{-1}`; `d=3`, `g=1`: `W^{-3}/7`. | `C = 1`, no condition on `g` |
| 2 | coordinate tail (item 2) | `B = W^{-1/2}`, `B²/(2v) ≥ W^{d-1}/2 ≥ W²/2` (`d ≥ 3`; `d ≥ 2` suffices), `P(\|ω c\|>B) ≤ 2 exp(-W^{d-1}/2)`; need `≤ N^{-D}`; `W ≥ N^𝔠` gives `exp(-N^{2𝔠}/2)`, super-polynomially small. | at `szCL`, `n=0`: exponent `3.5 W² = 9.9e14` vs `D ln N = 997` (D=10) |
| 3 | `STWB sz n u K` for `u ≤ t_n ≤ lemT z_n`, any `K` | `STWB = W^{-d}[(g²+1-u)^{-1}(K+1)^{-(d-2)} + (L^d(1-u))^{-1}] ≤ (g²W^d)^{-1} + (N(1-u))^{-1} ≤ W^{-2𝔡} + N^{-ε/2} ≤ 2 N^{-a}` (uses `(K+1)^{d-2} ≥ 1`, WO, `W ≥ N^𝔠`, RangeCond). Same computation as `DecayLoopA_STWB_le` (`DecayLoopA.lean:485`, private) and `st5_Bctl_le_one` (`Step5Kit.lean:362`, only `≤ 1`, not enough). | uniform in `K` |
| 4 | item 3 exponent `τ'` in `Prec` | need `N^{τ'}·STWB ≤ 1` eventually: `2N^{-a+τ'} ≤ 1` iff `τ' < a`; take `τ' = a/2`, then `2 N^{-a/2} ≤ 1` iff `N ≥ 2^{2/a}`. Then `‖G-M‖² ≤ 1`, `‖G_{xy}‖ ≤ 1 + ‖M_{xy}‖ ≤ 1 + \|m\| = 2` (sharp, strict `2 <` is excluded). | `szCL`: `a = 1/30`, `τ' = 1/60`, `N ≥ 2^{60}`; `ln N ≥ 99.66 > 41.6` |
| 5 | item 3, charge `-` | `G(-) = G(+)ᴴ` for Hermitian `H_τ` (`Hflow` Hermitian), so `‖G(-)_{xy}‖ = ‖G(+)_{yx}‖`; the pair `(y,x)` is in the index set of `STLocalEntryU` | exact |
| 6 | item 4 (`stFarEntryAtLog` at `c`, `D'+1`) | far set `θ = c (log W)^3 ℓ_τ` (`ellT L lam τ`), `Prec` threshold `N^{𝔠'}·W^{-(D'+1)}`; take `𝔠' = 𝔠`: `N^𝔠 ≤ W` (Bandwidth) gives `N^𝔠 W^{-(D'+1)} ≤ W^{-D'} < ‖G‖·1`. Both charges are in `STFarEntryAtLog`, no transposition. | uses `Bandwidth` with the exact exponent `𝔠`; `szCL`: `N^{1/6}` vs `W`: `16.61 ≤ 16.64` (`n=0`, `W/L = 1.05`) |
| 7 | item 5 (`cltGood_whp`) | `¬cltGoodAt ⊆ E3 ∪ E4` (`cltGoodAt`: `CltPath.lean:83`, same `gEntry`, `Hflow`, `split`, `zdistInf` as the events); items 3, 4 at `D+1`: `2 N^{-(D+1)} ≤ N^{-D}` iff `N ≥ 2` | `N → ∞` |
| 8 | transfer | `cltTransfer` (`CltSwap.lean:323`) is for integrals; for events use `seqP_map_slice` + `Measure.map_apply`, needs `MeasurableSet`: `walk_measurable_Gres_apply` (`Path/Walk.lean:737`) with `measurable_Hflow` (`FineModel.lean:~455`); `gEntry … (Hflow … (slice ω)) σ x y = Gt sz n E τ σ ω x y` by unfolding (`gEntry := Gres M (zt E s) σ x y`, `Gt := Gres (seqHflow …) (zt E t) σ`) | definitional |
| 9 | `16 W^{-1/2} ≤ 1`, `\|s-ω₀ c\| ≤ 2W^{-1/2}` of `CltPathBound` (`CltPath.lean:110`) | coordinates `\|ω c\|,\|ω' c\| ≤ W^{-1/2}` (item 2) give `\|ω' c - ω c\| ≤ 2W^{-1/2}`; `W ≥ 256` | `szCL`, `n=0`: `W^{1/2} = 4096` |

### (ii) One concrete nondegenerate instance

`szCL` (`Step5Pins.lean:640`): `d=3`, `m=n+24`, `L_n = 2m^5`, `W_n = 2^m`, `lam ≡ 1`; `zCL n = 1/2 + i L^{-2}/2`; `κ=ε=1/10`, `𝔠=1/6`, `𝔡=1/10`; `s = τ = sCL ≡ 0`, `t = tCL = 1 - L^{-2} ≤ lemT zCL` (`lemT_zCL`), `sCL < tCL` (`szCL_hst`), `Cd = 1`; `flow_zCL : STFlow szCL (1/10) (1/10) (1/6) (1/10) zCL`.
`D = 10`, `D' = 5`, far constants `c = 10` (item 4) and `c = 3` (item 5, with `R = 10 L0`, `ρ = L0`: `3 L0 ≤ 5 L0 - L0 - 1`). Only `STStep2Concl` stays a hypothesis (another gate's pin); every other hypothesis is discharged by the merged facts above, and the numbers below are the check of the deterministic arithmetic.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2149/inst2.py`

```
n=0 m=24 L=15925248 W=2^24 lnN=99.66 L0=4603.7 a=0.0333 tau'=0.0167 ln(N^tau'STWB)=-48.9,-48.2 2N^(-a/2)=0.380
   all checks True 13
n=10 m=34 L=90870848 W=2^34 lnN=125.68 L0=13089.2 a=0.0333 tau'=0.0167 ln(N^tau'STWB)=-69.3,-68.6 2N^(-a/2)=0.246
   all checks True 13
```

The 13 checks (script text, scratchpad `T2149/inst2.py`, evaluated with exact `Fraction` for `STWB` inputs and logarithms for sizes), per `n`:
kernel total `a + 2d g² a = 1` (`a = 1/7`); coordinate tail `ln(2 exp(-3.5 W²)) ≤ -D ln N`; `Bandwidth N^{1/6} ≤ W`; `RangeCond L^{-2} ≥ N^{-1+ε/2}` (`1-t_n = L^{-2}`); `N^{τ'} STWB ≤ 1` at `1-u = 1` (`τ = s = 0`) and at `1-u = L^{-2}` (`u = t_n`), `K = 0` (`STWB = W^{-3}[(1+1-u)^{-1} + (L^3(1-u))^{-1}]`); general bound `2 N^{-a/2} ≤ 1`; `|E| ≤ |Re z| = 1/2 < 2-κ/2`; `N^𝔠 W^{-(D'+1)} ≤ W^{-D'}`; far set nonempty `c·L0 ≤ ⌊L/2⌋` for `c = 10` (merged `farEntry_szCL_far_nonempty`, `c = 1`, `FarEntry.lean:904`); `θ ≤ R/2 - ρ - 1`; `16 W^{-1/2} ≤ 1`; `N ≥ 2`.
Limit computation for the one asymptotic input with explicit threshold: item 3 needs `2 N^{-a/2} ≤ 1`, i.e. `ln N ≥ 60 ln 2 = 41.6`; `ln N ≥ 99.66` for every `n ≥ 0` (`N_n` increasing). The other "eventually" statements (`W^{2𝔡} ≥ 2`, `N^{ε/2} ≥ 4`, `exp(-N^{2𝔠}/2) ≤ N^{-D}`) are limits of `N^x → ∞` along `szCL_tendsto`.
Nonempty: the index set of `Prec` in items 3 to 5 is `Idx × Idx` of size `N² > 0`, the far set is nonempty at every `n` (`farEntry_szCL_far_nonempty`), `cltGoodAt` at `ω = 0` is the merged `cltpath_chk_good` (`CltPath.lean:~464`, `szCL`, `n = 0`).

### Consumer check (iv)

RBM2D `Evolution/CltStep.lean:600-621` (`cltStep`, at `c9a24cf`): applies `cltCoord_tail` at `D''`, `cltGmax_whp` (H_clt) at `D''` and `cltFarEntry_whp` at `(τ, D' = D''/𝔠, D'')`, all at the single time `u n`, with isolation `W^{2τ} ℓ_u` and `W^{-D'} ≤ N^{-D''}` by Bandwidth.
RBM3D consumer `STCltIsoConcl sz E s _t` (`Step5Pins.lean:415`): time `s n`, labels `|b_k0 - b_k1|_∞ ≤ (log W)^3 ℓ_s`, isolation `10 (log W)^3 ℓ_s`, bound `W^{-D}`. So the events are taken at `τ = s` (`s ≤ s ≤ t`), `θ = c (log W)^3 ℓ_s` with `c` free in `(0, 5 - ρ/L0 - 1/L0)` (`ρ = L0` gives `c = 3`), `D'' ` as in RBM2D with `D' = D''/𝔠` (`W^{-D'} ≤ N^{-D''}`).
No per-time law at a stopping time is used: items 2 to 5 use only single-time marginals, hence `HClt` suffices (DECISIONS §7).

### Verdicts

- Item 1 `HClt`: PASS (bundle as in the dictionary; `Cd` and `3 ≤ d` are parameters).
- Item 2 `CltCoordTail`/`cltCoord_tail`: PASS (variance `≤ W^{-d}`, no hypothesis on `g`; needs `Admissible`: `W ≥ N^𝔠`, `N → ∞`).
- Item 3 `CltGmaxWhp`/`cltGmax_whp`: PASS (`τ' = a/2` with `a = min(2𝔠𝔡, ε/2)`; exponent `D`, no `D+2`; needs `WO` and RangeCond through `STWB ≤ 2N^{-a}`, a new private bound).
- Item 4 `CltFarEntryWhp`/`cltFarEntry_whp`: PASS (`stFarEntryAtLog` at `(c, D'+1)`, `N^𝔠 ≤ W`).
- Item 5 `cltGood_whp`: PASS (`2 N^{-(D+1)} ≤ N^{-D}`).

## (b) Script output (stage 1b, written Sun Oct  4 18:08:45 UTC 2026)

Commit on `t/T2149`: `f0f46c7` (only `RBM3D/Evolution/CltGood.lean`, 680 lines). Scripts in scratchpad `T2149/` (`evid.sh`, `extract.py`).

```
$ lake build RBM3D.Evolution.CltGood   (tail; exit code 0)
⚠ [3794/3808] Replayed RBM3D.Green.IBPRem
warning: RBM3D/Green/IBPRem.lean:14:100: This line exceeds the 100 character limit, please shorten it!

ℹ [3806/3808] Replayed RBM3D.Evolution.CltResolvent
info: RBM3D/Evolution/CltResolvent.lean:1114:0: '_private.RBM3D.Evolution.CltResolvent.0.RBM.Evol.cltres_chk_witness' depends on axioms: [propext,
info: RBM3D/Evolution/CltResolvent.lean:1115:0: '_private.RBM3D.Evolution.CltResolvent.0.RBM.Evol.cltres_chk_near' depends on axioms: [propext,
info: RBM3D/Evolution/CltResolvent.lean:1116:0: '_private.RBM3D.Evolution.CltResolvent.0.RBM.Evol.cltres_chk_half' depends on axioms: [propext,
ℹ [3807/3808] Replayed RBM3D.Evolution.CltPath
⚠ [3808/3808] Replayed RBM3D.Evolution.CltGood
warning: RBM3D/Evolution/CltGood.lean:19:100: This line exceeds the 100 character limit, please shorten it!

Build completed successfully (3808 jobs).

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Evolution/CltGood.lean | wc -l
       0
$ git diff --stat main...t/T2149
 RBM3D/Evolution/CltGood.lean | 680 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 680 insertions(+)
$ lake build   (full library, exit code 0; the new module is imported by the hub at merge)
Build completed successfully (3896 jobs).
$ registry pre-check: lake env lean RegCheck.lean (RBM3D.lean + import RBM3D.Evolution.CltGood), exit code 0
axiom audit: 4509 theorems, 1615 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 88 (borrowed 0, owed 68, structural 20).

$ axioms of the targets (#print axioms at the end of the file, build output):
info: RBM3D/Evolution/CltGood.lean:672:0: 'RBM.Evol.cltCoord_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:673:0: 'RBM.Evol.cltGmax_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:674:0: 'RBM.Evol.cltFarEntry_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:675:0: 'RBM.Evol.cltGood_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltGood.lean:676:0: 'RBM.Gauss.Step5Inst.cltGood_hclt_szCL' depends on axioms: [propext, Classical.choice, Quot.sound]

$ name-clash grep (new public names, whole RBM3D tree on main and in the worktree outside CltGood.lean)
HClt: main=       0 worktree-other-files=       0
CltCoordTail: main=       0 worktree-other-files=       0
CltCoordConcl: main=       0 worktree-other-files=       0
CltGmaxWhp: main=       2 worktree-other-files=       2
CltGmaxConcl: main=       0 worktree-other-files=       0
CltFarEntryWhp: main=       2 worktree-other-files=       2
CltFarEntryConcl: main=       0 worktree-other-files=       0
CltGoodWhp: main=       0 worktree-other-files=       0
CltGoodConcl: main=       0 worktree-other-files=       0
cltCoord_tail: main=       0 worktree-other-files=       0
cltGmax_whp: main=       0 worktree-other-files=       0
cltFarEntry_whp: main=       0 worktree-other-files=       0
cltGood_whp: main=       0 worktree-other-files=       0
cltGood_hclt_szCL: main=       0 worktree-other-files=       0
(helpers are private, prefix cltGood_)
9
(the CltGmaxWhp/CltFarEntryWhp hits are docstring mentions: CltSwap.lean:57, CltPath.lean:81)

$ RBM2D port: git -C ../RBM2D --no-optional-locks log -1 --format=%h ; diff --stat c9a24cf HEAD
9e0f275
 RBM2D/Evolution/CltGood.lean | 148 ++++++++-----------------------------------
 RBM2D/Evolution/CltStep.lean |  47 +++++---------
 2 files changed, 42 insertions(+), 153 deletions(-)
$ RBM1D diff-stat: no RBM1D file was copied (the matrix-inverse measurability of RBM1D is replaced by the merged walk_measurable_Gres_apply)
```

Target statements, extracted from the file by script (docstrings stripped; line numbers of `RBM3D/Evolution/CltGood.lean`):

```
56: section Pins
58: variable {d : ℕ} (sz : Sizes d)
64: def HClt (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ) : Prop :=
65:   3 ≤ d ∧ 0 < κ ∧ 0 < ε ∧ STFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ τ n) ∧
66:     (∀ n, τ n ≤ t n) ∧ (∀ n, t n ≤ lemT (z n)) ∧ STStep2Concl sz (STflowE z) s t Cd
70: def CltCoordConcl (D : ℝ) : Prop :=
71:   ∀ᶠ n : ℕ in atTop, ∀ c : CoordF d (sz.L n) (sz.W n),
72:     PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
73:       ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
77: def CltCoordTail : Prop :=
78:   2 ≤ d → ∀ 𝔠 : ℝ, 0 < 𝔠 → sz.SizeTendsto → sz.Bandwidth 𝔠 →
79:     ∀ D : ℝ, 0 < D → CltCoordConcl sz D
83: def CltGmaxConcl (E τ : ℕ → ℝ) (D : ℝ) : Prop :=
84:   ∀ᶠ n : ℕ in atTop,
85:     PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
86:         2 < ‖gEntry d (sz.L n) (sz.W n) (E n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
87:       ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
91: def CltGmaxWhp : Prop :=
92:   ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
93:     ∀ D : ℝ, 0 < D → CltGmaxConcl sz (STflowE z) τ D
97: def CltFarEntryConcl (E τ : ℕ → ℝ) (c D' D : ℝ) : Prop :=
98:   ∀ᶠ n : ℕ in atTop,
99:     PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
100:         c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
101:             ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
102:               (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
103:           ((sz.W n : ℕ) : ℝ) ^ (-D') <
104:             ‖gEntry d (sz.L n) (sz.W n) (E n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
105:       ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
110: def CltFarEntryWhp : Prop :=
111:   ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
112:     ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D →
113:       CltFarEntryConcl sz (STflowE z) τ c D' D
117: def CltGoodConcl (E τ θ : ℕ → ℝ) (D' D : ℝ) : Prop :=
118:   ∀ᶠ n : ℕ in atTop,
119:     PF d (sz.L n) (sz.W n) (sz.lam n)
120:         {ω | ¬ cltGoodAt d (sz.L n) (sz.W n) (E n) (τ n) (θ n) D' ω} ≤
121:       ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
125: def CltGoodWhp : Prop :=
126:   ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
127:     ∀ (c : ℝ) (θ : ℕ → ℝ), 0 < c →
128:       (∀ n, c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤ θ n) →
129:       ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D → CltGoodConcl sz (STflowE z) τ θ D' D
323: theorem cltCoord_tail {d : ℕ} (sz : Sizes d) : CltCoordTail sz := by
414: theorem cltGmax_whp {d : ℕ} (sz : Sizes d) : CltGmaxWhp sz := by
491: theorem cltFarEntry_whp {d : ℕ} (sz : Sizes d) : CltFarEntryWhp sz := by
561: theorem cltGood_whp {d : ℕ} (sz : Sizes d) : CltGoodWhp sz := by
```

The four theorems are stated `(sz : Sizes d) : <Pin> sz`; the pins' conclusions are the generic definitions
`CltCoordConcl`, `CltGmaxConcl`, `CltFarEntryConcl`, `CltGoodConcl` (elaboration trap of T2141: no `Idx 3 (szCL.L n)` is spelled).

Compiled nonempty instances (same file, namespace `RBM.Gauss.Step5Inst`, `d = 3`, `szCL`, `zCL`, `sCL`, `tCL`; only `STStep2Concl` is a hypothesis; `flow_zCL`, `lemT_zCL`, `szCL_hst`, `szCL_tendsto`, `szCL_bandwidth` discharge the rest):

```
627: namespace RBM.Gauss.Step5Inst
629: open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Evol
632: theorem cltGood_hclt_szCL (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
633:     HClt szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1 :=
634:   ⟨le_refl 3, by norm_num, by norm_num, flow_zCL, fun _ => le_rfl, fun _ => le_rfl,
635:     fun n => (szCL_hst n).le, lemT_zCL, hStep2⟩
639: example : CltCoordConcl szCL 10 :=
640:   cltCoord_tail szCL (by norm_num) (1 / 6) (by norm_num) szCL_tendsto szCL_bandwidth 10
641:     (by norm_num)
644: example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
645:     CltGmaxConcl szCL (STflowE zCL) sCL 10 :=
646:   cltGmax_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
647:     (cltGood_hclt_szCL hStep2) 10 (by norm_num)
651: example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
652:     CltFarEntryConcl szCL (STflowE zCL) sCL 1 5 10 ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
653:   ⟨cltFarEntry_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
654:     (cltGood_hclt_szCL hStep2) 1 (by norm_num) 5 (by norm_num) 10 (by norm_num),
655:    farEntry_szCL_far_nonempty⟩
658: example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
659:     CltGoodConcl szCL (STflowE zCL) sCL
660:         (fun n => 1 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n))
661:         5 10 ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
662:   ⟨cltGood_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
663:     (cltGood_hclt_szCL hStep2) 1
664:     (fun n => 1 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n))
665:     (by norm_num) (fun _ => le_rfl) 5 (by norm_num) 10 (by norm_num),
666:    farEntry_szCL_far_nonempty⟩
```

Narrative (stage 1b):
- Item 2 (`cltCoord_tail`): `gvarF ≤ svarF = W^{-d} sbKernelR ≤ W^{-d}` from `sum_sbKernelR` (`3 ≤ L`), then the sub-Gaussian bound with `B = W^{-1/2}`: `P(B < |ω c|) ≤ 2 exp(-W/2)` (uses `d ≥ 2`), and `2 exp(-W/2) ≤ N^{-D}` from `W ≥ N^𝔠`. RBM2D had `(5W²)⁻¹` and `exp(-5W/2)`.
- Item 3 (`cltGmax_whp`): `prec_timeIcc_section` on `STStep2Concl.1` (`STLocalEntryU`) of `HClt` at `τ`, scale exponent `a/2`, `a = min(2𝔠𝔡, ε/2)`, charge `D` (no `+2`, no extra union: the union over `(x,y)` is inside `Prec`). Private `cltGood_STWB_le`: `STWB ≤ (ilambda² W^d)⁻¹ + (N(1-u))⁻¹ ≤ 2 N^{-a}` (eventually, uniform in `K`, `u ≤ t_n`; `lam_sq_mul_pow_ge`, `Bandwidth`, `RangeCond` of `v3_premises_of_stFlow`); then `N^{a/2} STWB ≤ 2/N^{a/2} ≤ 1`, so `‖G_xy - m δ_xy‖ ≤ 1`, `‖G_xy‖ ≤ 1 + ‖mE‖ = 2` (`norm_mE`), charge `-` by `G(-)_xy = conj G(+)_yx` (private port of `Gres_conjTranspose`). Transfer by `seqP_map_slice` + `Measure.map_apply` for the measurable event `T` (entries via the merged `walk_measurable_Gres_apply` and `measurable_Hflow`); `Sizes.slice`-pullback of `T` is contained in `badSetAt`.
- Item 4 (`cltFarEntry_whp`): `stFarEntryAtLog` at `(c, D'+1)`, `Prec` exponent `𝔠`, `N^𝔠 W^{-(D'+1)} ≤ W · W^{-(D'+1)} = W^{-D'}`; both charges are in the pin, no transposition; the far condition is `(split x).1` = `STblk` by definitional unfolding.
- Item 5 (`cltGood_whp`): `¬ cltGoodAt ⊆ E3 ∪ E4` (the far threshold `θ n ≥ c (log W)^3 ℓ_τ`, so `θ ≤ dist ⟹ c … ≤ dist`), items 3, 4 at `D+1`, `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`.
- `HClt` takes `(κ ε 𝔠 𝔡 z s τ t Cd)`; `E = STflowE z`; `3 ≤ d` is a conjunct. The preflight dictionary of (a) item 1 was used as written; no `(a′)` was needed.
- `cltTransfer` (integral form, `CltSwap.lean:323`) is not used: the events need only `seqP_map_slice`; `CltSwap` is not imported.

## (c) Verified Mathlib names (all compile in `CltGood.lean`)

`HasSubgaussianMGF.measure_ge_le`, `HasSubgaussianMGF.id_map_iff`, `HasSubgaussianMGF.neg` (`Mathlib/Probability/Moments/SubGaussian.lean`); `mgf_id_gaussianReal`, `integrable_exp_mul_gaussianReal`, `Measure.infinitePi_map_eval`; `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`; `ofReal_measureReal` (`Measure/Real.lean:65`); `Measure.map_apply`, `measure_union_le`, `measure_mono`; `measurableSet_lt`, `Measurable.of_eval`; `Finset.single_le_sum`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `pow_le_pow_right₀`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow`, `Real.rpow_add`, `Real.rpow_mul`, `Matrix.conjTranspose_nonsing_inv`, `norm_sub_norm_le`.
Observation: `if_pos` is reported deprecated by this toolchain (warning in the first build); replaced by `simp only [hf', ↓reduceIte, mul_one]`.

## (d) Open issues and paper-delta candidates

- `T2149a` (Lean/paper): the coordinate-tail pin `CltCoordTail` carries the hypothesis `2 ≤ d` (needed for `W^{d-1} ≥ W`), not `3 ≤ d`; the bound `W^{-1/2}` is the step length of `CltPathBound` (the paper has no explicit statement; RBM2D `7:522`).
- `T2149b` (Lean-only route): the replacement-step good event (`HClt`, items 2-5) is part of the i.i.d.-copy route that is not in the paper (see `CltSwap.lean` header); `HClt` bundles `STFlow`, `0 ≤ s ≤ τ ≤ t ≤ lemT z`, `STStep2Concl`: only `STLocalEntryU` (item 3), and through `stFarEntryAtLog` `STLocalEntryU` + `STGdecayW` (item 4) are used; `STAvgU` is not.
- `T2149c` (Lean/paper): `CltGoodWhp` takes the far threshold as a sequence `θ n ≥ c (log W)^3 ℓ_τ` (the consumer's `θ = 4 (log W)^3 ℓ_s - 1` of `CltPath.lean` needs `c = 1 ≤ 4 - 1/L0`), not the exact threshold; `cltGoodAt` is antitone in the far requirement.
- No per-time law at a stopping time is needed (DECISIONS §7); no registry line (pre-check above passes with the module imported). The hub adds `import RBM3D.Evolution.CltGood` after the last import of `RBM3D.lean` at merge.
- Downstream (S5-21): events at `τ = s`; `θ` free in `[c (log W)^3 ℓ_s, …)`; `D' = D''/𝔠` as in RBM2D `CltStep.lean:600-621` is the consumer's choice (`W^{-D'} ≤ N^{-D''}` by `Bandwidth`).
