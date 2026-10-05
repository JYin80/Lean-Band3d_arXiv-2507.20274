Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:03:34 UTC 2026

Notation: `m = msc z`, `t₀ = lemT z = |m|²`, `E = lemE z = -2 Re m/|m|`, `r = √(κ(4-κ))`, `u = 1 - t₀`, `η = Im z`.
Paper lines: `paper/tex/1_2_Intro_model_result.tex` (`1_2:`). Sources read: probe `97d958e:RBM3D/Probe/T2192Pins.lean` `:472-663`, `:776-1059`, `:2236-2272`; merged `Endpoints.lean:56-95, 218-252, 545-560`, `Loop/GLoopFlow.lean:72-185`, `Loop/GLoop.lean:55`, `Induction/Defs.lean:64-80`, `Loop/KLTree.lean:211`, `Defs/Semicircle.lean:36-42, 179-200, 355-372`, `Defs/Params.lean:36`.

### (i) Exponent / constant / pin table

| # | Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | `d` | `3 ≤ d` (`MABtBt` hypothesis) | proof of `btBt` uses only `hd2 : 2 ≤ d` (`omega`) for `calB_blk_eq_STWB`; other pins have no `d` bound | 1 unit in `d` (3 vs 2); instance `d = 3` |
| 2 | domain `𝐃` | `0 < Im z ≤ 1`, `|Re z| ≤ 2-κ`, `κ > 0` | `lemma28_quant` hypotheses (`Semicircle.lean:359`) | scan below: `2-κ-|E|` min `-2.2e-16` (roundoff at `|Re z| = 2-κ`, `t₀ = 1`; math: `|E| = 2√t₀|Re z|/(1+t₀) ≤ |Re z|`) |
| 3 | `t₀` lower bound (`MAZRange`) | `t₀ ≥ 1/16` | `t₀ ≥ ((1+|z|)²)⁻¹` (merged `lemT_ge`, `Semicircle.lean:331`) and `|z| ≤ |Re z|+Im z ≤ 3` | scan: min `16 t₀ = 3.72` (slack factor 3.7) |
| 4 | `1 - t₀` (`MAZRange`) | `= η/(Im m + η)`; `≥ η/2` | `(eq:t0E0)` `1_2:789` gives `|m|²(Im m+Im z) = Im m`; `Im m ≤ |m| < 1`, `η ≤ 1 ⇒ Im m + η ≤ 2` | scan: min `(1-t₀)/(η/2) = 1.236` |
| 5 | `Im m` lower bound (`im_msc_ge`) | `Im m ≥ r/8` | `√t₀ ≥ 1/4`, `Im mE = √(4-E²)/2 ≥ r/2` as `4-E² ≥ 4-(2-κ)² = κ(4-κ)` | scan: min `Im m/(r/8) = 2.44` |
| 6 | `MABtBt` upper constant | `2` | `STWB_compare` first clause needs `η ≤ 2u` (row 4 with `η = Im z`): `g²+η ≤ 2(g²+u)` | equality possible only as `Im m → 0`; instance ratio `STWB/calB ≈ 0.97-0.99` vs `2` |
| 7 | `MABtBt` lower constant | `r/8`, `C = 8/r ≥ 1` | `u = η/(Im m+η) ≤ η/Im m ≤ (8/r)η` (rows 4-5); `C ≥ 1` since `r ≤ 2` (`κ ≤ 2` from `|Re z| ≥ 0`) | instance `r/8 = 0.0781` vs ratio `0.97-0.99` |
| 8 | `STWB_compare` | `η>0, u>0, η ≤ 2u, 1 ≤ C, u ≤ Cη` | each of `(g²+x)⁻¹`, `(L^d x)⁻¹` changes by factor `≤ 2` resp. `≤ C`; `g² = lam² ≥ 0`, no lower bound on `lam` | none needed (no `L^d ≤ W^K`, no `∀ᶠ n`) |
| 9 | `calB` vs `STWB` (merged, `calB_blk_eq_STWB`) | `calB(η, Wk) = STWB(1-η, k)` (`W²·W^{d-2}(k+1)^{d-2} = W^d(k+1)^{d-2}`; `1/(Nη) = W^{-d}/(L^dη)`) | `N = (WL)^d` | exact identity |

Pins (one line each: statement / paper line / class / consumer; all "proved here, not registered"):

| Pin | Says | Paper | Consumer |
|---|---|---|---|
| `MAZRange` | `|E| ≤ 2-κ`, `1/16 ≤ t₀ < 1`, `1-t₀ = Im z/(Im m+Im z) ≥ Im z/2` | `(eq:t0E0)` `1_2:789`, `zztE` `1_2:787-795` | `btBt`; MA-04 (`|ξ| = t₀`) |
| `MAZGreen` | `√t₀ Gt(lemE,lemT,+) = Gn z` pointwise in `ω` (merged `Gt_lemT`) | `(eq:zztE)` 3rd clause `1_2:792` | `zLocal`, `zAve`, `zTrace` |
| `MAZLocal` | `|G_xy - M_xy|² = t₀ |STGM(lemE,lemT)_xy|²` | `(G_bound)` `1_2:388` from `(Gt_bound)` `1_2:1220` | MA-03 `locSCFixed_of_ML` `:1205` |
| `MABtBt` | `STWB ≤ 2 calB` and `(r/8) calB ≤ STWB` at block distance `k` | `(eq:BtBt)` `1_2:1111` | MA-03 `:1202,1228,1313,1339,1440` |
| `MAZAve` | `W^{-d} Σ_{x∈[a]} G_xx = √t₀ Lloop^{(1)}(+,a)` | `(G_bound_ave)` `1_2:391`, `ML:GLoop` `1_2:1193` | MA-03 `:1234` |
| `MAZTrace` | `avg2(G_xy G_yx) a b = t₀ Lloop^{(2)}(+,+;(b,a))`, `avg2(|G_xy|²) a b = t₀ Lloop^{(2)}(+,-;(b,a))` | `(eq:diffu1,2)` `1_2:490-499` | MA-03 `qd_exp_core`, `QDiffFixed_of_ML` |
| `MAZProfile` | `profPM = t₀ STKloop(+,-;(b,a))`, `profPP = t₀ STKloop(+,+;(b,a))` | `(Kn2sol)` `1_2:1175` | same |

Per-pin verdicts against the paper (all PASS):
- `MAZRange` PASS: `E = -2Re m/|m|`, `t₀ = |m|²` are `lemE`, `lemT` (`Semicircle.lean:190-193`); `Re z = E(1+t₀)/(2√t₀)` gives `|E| ≤ |Re z|`.
- `MAZGreen` PASS: paper states `G(z) =ᵈ √t₀ G_{t₀;E}` (equality in distribution); Lean states the pointwise identity on the model space for the single-time carrier `H_u = √u X` (`Gt_lemT`, `GLoopFlow.lean:181`); stronger, same use, no statement difference for consumers.
- `MAZLocal` PASS: `m = √t₀ mE` (`msc_eq_sqrt_mul_mE`), `M = m I`; `G - M = √t₀ (Gt - mE I)`; factor `t₀ ≤ 1` is the whole transfer.
- `MABtBt` PASS: paper `≍` becomes the two explicit constants (rows 6-7); paper-delta already exists as D501 (`L^∞` block distance) — not re-proposed.
- `MAZAve` PASS: `E_a = W^{-d} 1_{[a]}` (`Eblk`, `GLoop.lean:55`); `tr(G E_a)`.
- `MAZTrace` PASS: `loopM` is `tr ∏ᵢ Gres(σᵢ) E_{aᵢ}` (`GLoopFlow.lean:92`), so `a = ![b,a]` gives `tr(G E_b G^σ E_a) = W^{-2d} Σ_{x∈[a],y∈[b]} G_xy G^σ_yx`, and `avg2 F a b = W^{-2d} Σ_{x∈[a]} Σ_{y∈[b]} F x y` (`Endpoints.lean:75`): index order `(b,a)` is right (numerically confirmed below); paper-delta D506 exists.
- `MAZProfile` PASS: `KLK_two` gives `t₀ W^{-d} mΣ₁mΣ₂ Θ(t₀ mΣ₁mΣ₂)(b,a)`; `|mE| = 1` gives `|m|²Θ(|m|²)/W^d` and `m²Θ(m²)/W^d`; `Theta_transpose` turns `(b,a)` into `(a,b)`: no statement change (D506).

§29 (1)-(7): (1) single time `t₀ = lemT z ∈ (0,1)`; no `s`, `u`. (2) boundary `1-ilambda²/L²` does not occur. (3) no `L^d ≤ W^K`; `MABtBt` asks only `3 ≤ d`. (4) no `∀ᶠ n`: every pin holds at every `n`. (5) no probability: random pins are `∀ ω`, pointwise. (6) no lower bound on `lam` (`g² ≥ 0` only). (7) `MABtBt` compares `STWB` (flow-output scale) with `calB` (endpoint scale) at the block distance `k`.
Two data, one model (O1): all seven pins quantify only over `sz, n, z, κ, ω`, indices `x, y, a, b, k`; `msc, lemE, lemT, mE, Theta, calB, STWB, Lloop, STKloop` are functions of these: PASS for each pin, no free `(m, ρ)`-type object.
Consumer check (§45 O2): consumers are unwritten MA-03 probe text compiled against the same statements (per ticket: T2192 audit §1); no merged consumer exists.

### (ii) One concrete nondegenerate instance

`d = 3`, `sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = (WL)^d = 2097152`; `κ = 1/10`; `z = 1/2 + i N^{-4/5}` (MA-01 `zI`, `Endpoints.lean:550`). All hypotheses of all seven pins/`inst_*` hold at once (no `N = 0`, no empty index, `W, L > 0`); `k` ranges over every block distance (checked `k = 0,1,2,3,5,100`).
Command: `python3 .../scratchpad/T2219/inst.py` (pure Python/numpy checks of the mathematics; no Lean). Output:
```
N 2097152 Im z 8.763872947670244e-06 m (-0.24999886858886752+0.968241454625957j) t0 0.999990948751903 E 0.49999999999487965
D: 0<Imz<=1 True |Re z|<=2-k True
zRange: |E|<=2-k True t0>=1/16 True t0<1 True 1-t0=Imz/(Imm+Imz) True Imz/2<=1-t0 True
im_msc_ge: r/8= 0.07806247497997998 <= Im m= 0.968241454625957 True
zztE: sqrt(t0) mE(E)=m True zt=sqrt(t0) z True
k 0 STWB 0.17321335172589997 calB 0.17507779836300508 ratio 0.9893507534676705 <=2: True >= r/8=0.0781: True
k 1 STWB 0.11294763752324577 calB 0.11474360428450645 ratio 0.9843480011591097 <=2: True >= r/8=0.0781: True
k 2 STWB 0.09285906612236104 calB 0.09463220625834023 ratio 0.981262825774783 <=2: True >= r/8=0.0781: True
k 3 STWB 0.08281478042191867 calB 0.08457650724525712 ratio 0.9791700215494861 <=2: True >= r/8=0.0781: True
k 5 STWB 0.07277049472147631 calB 0.07452080823217401 ratio 0.9765124191186374 <=2: True >= r/8=0.0781: True
k 100 STWB 0.05387530379985206 calB 0.05560414672241371 ratio 0.9689080217129783 <=2: True >= r/8=0.0781: True
btBt all True
sqrt(t0)*Gt==Gn True
zTrace(+,+) (b,a): True (+,-): True
zAve: True
```
The last three lines: random Hermitian `X` on a small lattice (`d = 3, L = 3, W = 2`, `n = 216`), `H_t = √t₀ X`, `z_t = E + (1-t₀) mE(E)`, blocks of size `W^d`; `tr(G E_b G^σ E_a)` against `W^{-2d} Σ_{x∈[a],y∈[b]} G_xy G^σ_yx` with the loop order `(b, a)` and `σ = (+,+), (+,-)`.
Domain scan and `MAZLocal` check: `python3 .../scratchpad/T2219/scan.py` (5 values of `κ` x 41 values of `Re z` x 6 values of `Im z` in `[1e-9, 1]`):
```
scan 5 kappa x 41 Re x 6 Im; min of (16 t0, (1-t0)/(Imz/2), 2-k-|E|, Im m/(r/8)) = {'t0': 3.717, 'half': 1.236, 'E': -2.2e-16, 'imr': 2.444}
zLocal max rel err 1.0043993515908378e-14
```
(`E` min `-2.2e-16` is floating-point roundoff at `|Re z| = 2-κ`.)
External hypotheses: none of the seven pins takes an external (unproved) hypothesis; the transfer needs only merged `lemma28_quant`, `Gt_lemT`, `KLK_two`, `calB_blk_eq_STWB`. No limit computation owed.

### Verdicts
- `MAZRange`: PASS. `MAZGreen`: PASS. `MAZLocal`: PASS. `MABtBt` (with `STWB_compare`, `im_msc_ge`): PASS. `MAZAve`: PASS. `MAZTrace`: PASS. `MAZProfile`: PASS.
- Paper-delta candidates: none new (D501, D506 cover the differences; `≍` replaced by explicit constants is the `MABtBt` content, already in the ticket).

## (b) Script output — Mon Oct  5 22:07:56 UTC 2026

Commit: `b07371e` on `t/T2219`. `git diff --stat main...t/T2219`:
```
 RBM3D/Main/ZTransfer.lean | 577 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 577 insertions(+)
```
Build (`lake build RBM3D.Main.ZTransfer`, tail; the module is not in the root import until the hub merges):
```

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3330 jobs).
```
Axioms (`#print axioms`, scratch file `import RBM3D.Main.ZTransfer`, 14 public theorems + 6 instances; `std3` = `[propext, Classical.choice, Quot.sound]`, the verbatim output text replaced by `std3`):
```
'RBM.Endpoints.im_identity' : std3
'RBM.Endpoints.zRange' : std3
'RBM.Endpoints.zGreen' : std3
'RBM.Endpoints.zLocal' : std3
'RBM.Endpoints.im_msc_ge' : std3
'RBM.Endpoints.STWB_compare' : std3
'RBM.Endpoints.btBt' : std3
'RBM.Endpoints.Gres_blockMat'' : std3
'RBM.Endpoints.sum_vtx' : std3
'RBM.Endpoints.trace_four' : std3
'RBM.Endpoints.trace_two' : std3
'RBM.Endpoints.zAve' : std3
'RBM.Endpoints.zTrace' : std3
'RBM.Endpoints.zProfile' : std3
'RBM.Endpoints.Inst.inst_zRange' : std3
'RBM.Endpoints.Inst.inst_btBt' : std3
'RBM.Endpoints.Inst.inst_zLocal' : std3
'RBM.Endpoints.Inst.inst_zAve' : std3
'RBM.Endpoints.Inst.inst_zTrace' : std3
'RBM.Endpoints.Inst.inst_zProfile' : std3
```
Registry pre-check (`import RBM3D` + `import RBM3D.Main.ZTransfer` + `#assert_rbm_axioms`, `lake env lean`): first lines of output and exit code.
```
axiom audit: 6457 theorems, 2229 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
... (premise ledger follows; omitted here)
ZTransfer/MAZ/MABtBt lines in output: 0
exit 0
```
Full `lake build` (library; ZTransfer is not yet in `RBM3D.lean`, the hub adds the import at merge):
```
Build completed successfully (4021 jobs).
```
No `sorry`/`admit`/`native_decide`/`axiom` in the file: `grep -cE 'sorry|admit|native_decide|^axiom'` = 0. Declarations: `grep -E '^(private )?(theorem|def) '` =       31 (defs 7, private theorems 4).

### Verbatim check (python, `git show 97d958e:RBM3D/Probe/T2192Pins.lean | sed -n a,bp` in `ZTransfer.lean`, in order)
```
B0 probe:215-223 lines=9 block in text: True  after previous block: True
B1 probe:472-663 lines=192 block in text: True  after previous block: True
B2 probe:776-1059 lines=284 block in text: True  after previous block: True
B3 probe:2236-2272 lines=37 block in text: True  after previous block: True
```
Diff of the file against the concatenated blocks (probe 215-223, 472-663, 774, 776-1059, 2112-2114, 2236-2272), added lines only, non-blank: copyright/import/module docstring/3 set_options/noncomputable/3 opens/namespace/`end Scalars`/one `/-! ## … -/` header before B1/`end Inst`/`end RBM.Endpoints`; probe 774 header before B2 and 2112-2114 before B3 are verbatim:
```
> /-
> Copyright (c) 2026 Jun Yin. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Jun Yin
> -/
> import RBM3D.Endpoints
> /-!
> # MA-02: the `zztE` transfer and `(eq:BtBt)` (Theorems 2.1-2.5, assembly)
> Ticket T2219 (MA-02 of the T2192 assembly split).  Moved verbatim from the compiled probe
> `RBM3D/Probe/T2192Pins.lean` at `97d958e` (branch `t/T2192`, never merged); the probe
> namespace `RBM.Probe.T2192` becomes `RBM.Endpoints`, its `Inst` becomes `RBM.Endpoints.Inst`.
> Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`).
> * The `zztE` transfer at `t₀ = lemT z`, `E = lemE z` (`1_2:787-795`) as identities: `zRange`,
>   `zGreen`, `zLocal`, `zAve`, `zTrace`, `zProfile`.  The loop indices `(b, a)` of `zTrace`
>   are D506 (the docstrings' `T2192g`).
> * `(eq:BtBt)` (`1_2:1111`) with the explicit constants `2` and `√(κ(4-κ))/8`: `btBt`, with
>   its carrier-free scalar core `STWB_compare` and the bulk bound `im_msc_ge`.
> * The private helpers `W_pos_real`, `L_pos_real` are re-declared here because those of MA-01
>   (`RBM3D/Endpoints.lean`) are private.
> * Consumers: MA-03 (`Main/FixedZ`), MA-04 (`Main/ZNet`).  Nothing is registered: every pin of
>   this file is proved here.
> -/
> set_option linter.style.longLine false
> set_option linter.unusedSectionVars false
> set_option linter.unusedVariables false
> noncomputable section
> open MeasureTheory ProbabilityTheory Filter Matrix Topology
> open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
> open scoped NNReal ENNReal
> namespace RBM.Endpoints
> end Scalars
> /-! ## The `zztE` transfer and `(eq:BtBt)` -/
> end Inst
> end RBM.Endpoints
removed (probe-side) lines other than the '--' separators: 0
```
### Target statements (the seven pins, extracted by script from the file)
```lean
def MAZRange : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧ lemT z < 1 ∧
      1 - lemT z = z.im / ((msc z).im + z.im) ∧ z.im / 2 ≤ 1 - lemT z

def MAZGreen : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ω : sz.SeqΩ,
    (Real.sqrt (lemT z) : ℂ) • sz.Gt n (lemE z) (lemT z) true ω = sz.Gn n z ω

def MAZLocal : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2 = lemT z * ‖STGM sz n (lemE z) (lemT z) ω x y‖ ^ 2

def MABtBt : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (κ : ℝ), 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → ∀ k : ℕ,
      STWB sz n (lemT z) k ≤ 2 * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt (κ * (4 - κ)) / 8) * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ≤ STWB sz n (lemT z) k

def MAZAve : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x =
      (Real.sqrt (lemT z) : ℂ) * sz.Lloop n (lemE z) (lemT z) (fun _ : Fin 1 => true) (fun _ => a) ω

def MAZTrace : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
    avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, true] ![b, a] ω ∧
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, false] ![b, a] ω

def MAZProfile : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n),
    profPM sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, false] ![b, a] ∧
    profPP sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, true] ![b, a]

```
### Compiled nonempty instances (file lines 536-577: the six `inst_*`, `d = 3`, `sz0` at `n = 0`, `z = zI`, `κ = 1/10`; every deterministic hypothesis discharged)
```lean
open RBM.Gauss.SizesInst RBM.Univ.UNInst
/-- `ZRange` at `z = zI`. -/
theorem inst_zRange :
    |lemE zI| ≤ 2 - 1 / 10 ∧ (1 / 16 : ℝ) ≤ lemT zI ∧ lemT zI < 1 ∧
      1 - lemT zI = zI.im / ((msc zI).im + zI.im) ∧ zI.im / 2 ≤ 1 - lemT zI :=
  zRange (1 / 10) (by norm_num) zI zI_im_pos zI_im_le zI_re_le

/-- `(eq:BtBt)` at `z = zI`, every block distance `k`: `2` and `√(κ(4-κ))/8` with `κ = 1/10`. -/
theorem inst_btBt (k : ℕ) :
    STWB sz0 0 (lemT zI) k ≤ 2 * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt ((1 / 10) * (4 - 1 / 10)) / 8) * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ≤
        STWB sz0 0 (lemT zI) k :=
  btBt (d := 3) le_rfl sz0 0 (1 / 10) (by norm_num) zI zI_im_pos zI_im_le zI_re_le k

/-- `(G_bound)` transfer at `z = zI`. -/
theorem inst_zLocal (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖sz0.Gn 0 zI ω x y - Mband sz0 0 zI x y‖ ^ 2 = lemT zI * ‖STGM sz0 0 (lemE zI) (lemT zI) ω x y‖ ^ 2 :=
  zLocal sz0 0 zI zI_im_pos ω x y

/-- `(G_bound_ave)` transfer at `z = zI`. -/
theorem inst_zAve (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)) :
    (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L 0) (sz0.W 0) a, sz0.Gn 0 zI ω x x =
      (Real.sqrt (lemT zI) : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) (fun _ : Fin 1 => true) (fun _ => a) ω :=
  zAve sz0 0 zI zI_im_pos ω a

/-- The two-loop transfer at `z = zI` (indices `(b, a)`). -/
theorem inst_zTrace (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    avg2 sz0 0 (fun x y => sz0.Gn 0 zI ω x y * sz0.Gn 0 zI ω y x) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a] ω ∧
    avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 zI ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ω :=
  zTrace sz0 0 zI zI_im_pos ω a b

/-- The profile identity `(Kn2sol)` at `z = zI`. -/
theorem inst_zProfile (a b : Zd 3 (sz0.L 0)) :
    profPM sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ∧
    profPP sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a] :=
  zProfile sz0 0 zI zI_im_pos a b

end Inst

end RBM.Endpoints
```
### Check-file equality (scratch = check file + `import RBM3D.Main.ZTransfer` + 20 examples; `lake env lean`)
```
example : RBM.Endpoints.T2219Check.MAZRange_pin = RBM.Endpoints.MAZRange := rfl
example : RBM.Endpoints.T2219Check.MAZGreen_pin = RBM.Endpoints.MAZGreen := rfl
example : RBM.Endpoints.T2219Check.MAZLocal_pin = RBM.Endpoints.MAZLocal := rfl
... (20 examples: 7 pins by rfl, 6 lemmas, Gres_blockMat', 6 instances)
exit 0
```
### Name-clash grep (the 29 new public/private names and the 2 helpers, in `RBM3D/` outside ZTransfer.lean)
```
RBM3D/Endpoints.lean:220:private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_p
RBM3D/Endpoints.lean:222:private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
```
Only the two private helpers of `Endpoints.lean:220,222` (the intended re-declarations; B0 compiled, no clash). Imports: exactly `RBM3D.Endpoints`; none added. Ports: none from RBM1D/RBM2D (probe move only), so no RBM diff-stat.

Narrative: file = copyright, import, module docstring, `:36-44` of the probe, `namespace RBM.Endpoints`, blocks B0-B3 as above; no proof edited; no statement changed; no hypothesis added. All 20 public theorems of the ticket compile on the first build; the six instances are the probe's B3 text verbatim. The probe's `:2104-2111` instance header docstring is not copied (the ticket allows only `:2112-2114` before B3).

## (c) Verified Mathlib names
No Mathlib name was written or checked by this ticket (verbatim move; all moved proofs compile unchanged).

## (d) Open issues and paper-delta candidates
None. D506 (T2192g) and D501 (T2192b) cover the loop index order and the L^∞ block distance; no `T2219a`. Registry: no line needed (pre-check exit 0, no ZTransfer premise).
