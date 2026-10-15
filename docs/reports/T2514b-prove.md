Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 07:48:16 UTC 2026 (row b: B1-B6; branch `t/T2514b` = `t/T2514` = 112ffba2, `BA/MAPins` committed)

Notation: `N = (W L)^d`, `T = t*_n = ouTStar sz τs n = N^{-1+τs}` (`τs ∈ (0,1)`), `a = e^{-T/2}`, `λ̂ = λ e^{T/2} = λ/a` (`lamHat`), `X = W^{τ/2}`, `m̃ = BAm d L λ̂`, `m = BAm d L λ`, `s̃(ζ) = stieltjesN (H_{λ̂}) ζ`.
`BASelf g z m ⇔ Im m > 0 ∧ m = L^{-d} tr (gΨ − z − m)⁻¹`; `BAbulk g κ E ⇔ κ ≤ Im m(E+i0)/π ⇔ ∃ real-axis solution with Im ≥ πκ` (MFixedPoint:830). Script: `.../scratchpad/T2514b/inst.py` (numpy, no Lean).

### (i) Exponent table
| # | quantity (target) | value | constraint | slack at S0 (`d=3`, `L=4`, `λ=0.222327`, `κ=κ_*=0.283075`, `E=E_*=0`) |
|---|---|---|---|---|
| 1 | window enlargement `r` (B1; B2, B4) | `r = (πκ/2)³/8`; `∀x∈[E−δ,E+δ]: ∀ᶠ BAbulk(κ/2)x` ⇒ `∀ᶠ ∀x, |x−E| ≤ δ+r → BAbulk(κ/4)x` | finite cover `x_j = min(E−δ+jr, E+δ)` (`⌈2δ/r⌉+1` points), `BAbulk_window` (MReg:122: `|x−x_j| ≤ (π(κ/2))³/8`) at each `n`; a finite `∀ᶠ`-intersection | `r = 0.01099`, `δ = (πκ)³/8 = 0.08792`; min ρ on `[E−δ−r, E+δ+r]` = 0.28277 ≥ κ/4 = 0.07077 |
| 2 | bulk levels | `κ → κ/2` (hyp) `→ κ₂ = κ/4` (B1) `→ κ̃ = κ₂/4 = κ/16` (B4, at `λ̂`); `c = πκ₂`, `c₁ = c/2` | `κ̃ > 0`; `c ≤ Im m ≤ 1` (`BAm_norm_le_one` Ward:136) so `c ≤ 1` whenever the bulk is nonempty | `κ₂ = 0.07077`, `c = 0.22233`, `c₁ = 0.11116`, `κ̃ = 0.01769` |
| 3 | B2 (TrLocal) | P4 `UNLocAvgBAAt d` at `(κ/4, ε, τ, D)`, same `(ε,τ,D)`; domain `|z.re−E| ≤ δ ⇒ BAbulk(κ/4)z.re` (row 1) | trace deviation `> W^τ Bctl` ⇒ some block deviation `> W^τ Bctl` (`BUniv_trace_le`, BUnivHolds:172, private); no constant lost, no threshold besides row 1 | exact; the hypothesis `∀ᶠ BAbulk κ E` is unused |
| 4 | `T`, `a`, `λ̂` (B4) | `0 < T ≤ 1` for every `n` (`size n ≥ 1`: `W_pos`, `three_le_L`); `a ∈ [e^{-1/2},1)`, `a⁻¹ ≤ 2`, `a ≥ 1/2`, `1−a² ≤ T`, `a⁻¹−1 ≤ T`, `a⁻¹(1−a²) ≤ 2T` | `admissible_lamHat` (UNPins:503) needs `∀ n, 0 ≤ T ≤ 1`: yes; gives `sz.withLam λ̂` admissible at `(𝔠, 𝔡/2)` | `T_1 = 3.81e-6`; `λ̂/λ = 1.0000019`, `λ̂ ≤ (𝔡/2)⁻¹ = 20` |
| 5 | law and matrix at `sz' = sz.withLam λ̂` | `ouInit (UNModelC.ba sz) n T ω = a • H_{λ̂}` (`ouInit_ba`, UNPins:472); the law of `UNModelC.ba sz'` is `seqP (sz'.withLam 0)` (docstring UNPins:62) and does not see the coupling (`ouP_ba_withLam`, UNPins:438, is `rfl`) | `stieltjesN (a•H) z = a⁻¹ s(z/a)` (`PinsC2_stieltjesN_smul`, PinsC2:489, private: a 25-line copy) | exact |
| 6 | **`Bctl` at `λ̂` against `λ` (NEW, B4)** | `Bctl n (1−η) = W^{-d}[(λ²+η)⁻¹ + (L^d η)⁻¹]` (`Bparam`, Params.lean:36, `K=0`, `Sizes.Bctl` Sizes.lean:214), so `sz'.Bctl n (1−η') ≤ sz.Bctl n (1−η)` for `η' ≥ η > 0` | `λ̂² = e^T λ² ≥ λ²` (no sign of `λ`); no coupling-Lipschitz bound is needed (the docstring `UNPins:175-180` "with the BA-D8 coupling Lipschitz bound" is not used) | script: `Bctl' ≤ Bctl` True on a grid |
| 7 | window at `ζ = z/a` | `|Re ζ − E| ≤ (1+T)δ + T|E| ≤ δ + T(δ+|E|) ≤ δ + r`; `Im z ≤ Im ζ ≤ 1+T ≤ 2` | `T ≤ T₀ ∋ r/(δ+|E|+1)` (eventual: `N→∞`) | `r/(δ+|E|+1) = 0.0101` |
| 8 | **scaling identity (NEW, exact)** | `BASelf g z m` (`Im z ≥ 0`) ⇒ `BASelf (g/a) ζ″ (a m)`, `ζ″ = (z + (1−a²)m)/a = z/a + a⁻¹(1−a²)m`; hence `BAm (g/a) ζ″ = a·BAm g z` (`BASelf_unique`, MFixedPoint:715) | `(gΨ/a − ζ″ − a m) = a⁻¹(gΨ − z − m)`; merged `BAzztE_inv_core` (CouplingWindow:239) is this at real `E` (`τ = a²`, `√τ = a`, `ztOf m E τ = E+(1−τ)m`); the complex-`z` case is a 30-line twin (same algebra) | script: `max |m̃(ζ″) − a m|` = 2.2e-16 (T = 1e-2, 1e-4; 25 points `z`) |
| 9 | **bulk at `λ̂` (F5, NEW)** | `x` real, `|x−E| ≤ δ+r` ⇒ `BAbulk λ κ₂ x` (row 1) ⇒ real `m_x`, `Im ≥ c`; row 8 at `(z=x)`: `BASelf λ̂ w (a m_x)`, `Im(a m_x) ≥ c/2 = c₁`, `Im w ≤ 2T`, `|Re w − x| ≤ T(|x|+2)`; **lemma Cplx→Real** (twin of `BAbulk_window`, base point complex): `BASelf g w m`, `c ≤ Im m`, `Im w ≤ c³/16`, `|y−Re w| ≤ c³/16` ⇒ `‖z_η−w‖ ≤ c³/8` (`z_η = y+iη`, `0<η≤c³/16`) ⇒ `‖m−m_η‖ ≤ c/4` (`BASelf_sub_le`, ImmLower:252: `(Im m²+Im m_η²)‖Δ‖ ≤ 2‖Δz‖`, `Im m² ≥ c²`) ⇒ `Im m_η ≥ 3c/4`; limit `η→0` (Bolzano–Weierstrass, `‖m_η‖ ≤ 1`, `BASelf_of_tendsto` Boundary:164) ⇒ real solution at `y` with `Im ≥ 3c/4 ≥ c/2` | at `c := c₁`, `y := x`: `BAbulk λ̂ κ̃ x`, `κ̃ = c₁/(2π)`; needs `T ≤ c₁³/(16(|E|+δ+r+2))` and `2T ≤ c₁³/16` (eventual) | script: min `ρ_{λ̂}` on `[E−δ−r,E+δ+r]` = 0.28250 (T=1e-2), 0.28277 (T=1e-4) ≥ κ̃ = 0.01769 |
| 10 | lower bounds of `Im m` | `c̃ = (πκ̃)⁵/2048` for `m̃(x+iη)`, `0<η≤10`, `BAbulk λ̂ κ̃ x` (`BAm_im_lower_window` at `E'=x`, MReg:227); `c₀ = (πκ₂)⁵/2048` for `m(z)`, `|Re z−E| ≤ δ`, `0<Im z ≤ 1` (row 1, same lemma) | uniform in `n`, `λ`, `L`; ζ, `ẑ=⟨Re ζ, min(Im ζ,1)⟩` share the real part | `c̃ = 2.590e-10`, `c₀ = 2.652e-07` |
| 11 | error budget (B4, `ẑ` = P4 point at `(ε, τ/2, D)`) | `‖a⁻¹s̃(ζ) − m(z)‖ ≤ t₁+t₂+t₃+t₄`: `t₁ = a⁻¹‖s̃(ζ)−s̃(ẑ)‖ ≤ 2T` (`stieltjesN_vert_le`, PinsC2:426, `Im ζ−1 ≤ T`); `t₂ ≤ 2X·Bctl n(1−Im z)` (P4 + `BUniv_trace_le` + row 6 + `Bctl` anti in `η`, PinsC2:200 private); `t₃ = a⁻¹‖m̃(ζ)−m̃(ẑ)‖ ≤ 2T/c̃²` (`BAm_sub_le_of_im`, MReg:84, both `Im ≥ c̃`); `t₄ = a⁻¹‖m̃(ζ)−m̃(ζ″)‖ ≤ 32T/c₀²` (`BASelf_sub_le` with only `Im m̃(ζ″) = a Im m(z) ≥ c₀/2`, `‖ζ−ζ″‖ ≤ 2T`; row 8 gives `m(z) = a⁻¹m̃(ζ″)`) | total `≤ 2X B + C′T`, `C′ = 2 + 2/c̃² + 32/c₀²`; need `≤ X²(B+T)`: `X = W^{τ/2} ≥ max(2, C′)` (eventual: `W→∞`, `Admissible.Bandwidth`) | `C′ = 2.981e+19`; observed shift `|a⁻¹m̃(z/a)−m(z)|/T ≤ 0.359` (bound `32/c₀² = 4.55e14`) |
| 12 | eventual thresholds (S0, `τs=1/2`, `ε=τ=1/10`, `D=1`) | `T₀ = min(1, r/(δ+|E|+1), c₁³/(16(xmax+2)), c₁³/32)`, `xmax = |E|+δ+r`; `N ≥ T₀⁻²`; `W^{1/20} ≥ max(2,C′)` | all `∀ᶠ n` (`SizeTendsto`, `Bandwidth`): quantifiers of the targets, not hypotheses | `T₀ = 4.09e-5`: first `n = 1`; `W_n^{1/20} ≥ C′`: first `n ≈ 3.9e77` (lossy constants; not used as a witness) |
| 13 | B3, B5 | `UNTrLocalBARow`, `UNTrLocalInitBARow'` = `UNLocAvgBA → ∀d, 3≤d → …`: `Iff.rfl` (P6, `MAPins:196-203`) + B2, B4 | the `UNLocAvgBA` binder is split by `d ≥ 3` | n/a |

Fill-in table (§269 (5), row b). **(i)** B1 = row 1 (`BAbulk_window`); B2 = `unTrLocalBandRow` (BUnivHolds:205) twin; B4 = `unTrLocalInit'_of_unTrLocal` (PinsC2:590) twin with `m` replaced by `m_n`, rows 5-11; B3, B5 = one line from P6.
**(ii)** n/a (A1 is row a). **(iii)** n/a (F3 is row a). **(iv) F5: no new upward-coupling Newton step.** The merged window (`BAwindow_step` CouplingWindow:448, `g' ≤ g`) is not used: the shift and the bulk at `λ̂` come from the scaling identity (row 8, exact) and Cplx→Real (row 9); private helpers in the file: complex-`z` scaling identity ≈ 30, Cplx→Real ≈ 50, B1 ≈ 40, `Bctl` comparison ≈ 10 lines; no probe needed. **(v)** below. **(vi)** n/a here (registry scan is 1b: B3, B5 conclude the heads `UNTrLocalBARow`, `UNTrLocalInitBARow'`; premise `UNLocAvgBAAt d` is `Iff`-read from the merged `UNLocAvgBA`, so no new unregistered premise in B3, B5). **(vii)** n/a (no size estimates in 1a). **(viii)** greps are 1b's. **(ix)** n/a (A5 is row a).

### (ii) One concrete nondegenerate instance (all targets, `d = 3`)
Data: Lean class `S0 = clsSz 4 (fp 4 _).g0`, `(𝔠, 𝔡) = (1/6, 1/10)` (`S0_adm`, UNPins:887): `L_n = 4`, `W_n = (2(n+1))⁵`, `λ_n = g₀ = √t₀·(3/10) = 0.222327` (flow point of `(L,g)=(4,3/10)`, MFixedPoint:877), `κ = κ_* = Im m₀/π = 0.283075`, `E = E_* = 0`, `δ = (πκ_*)³/8` (as in `MAPins:243-253`), `τs = 1/2`, `ε = τ = 1/10`, `D = 1`.
Hypotheses of B2, B4: `3 ≤ d` (d = 3); admissible (`S0_adm`); `κ>0`; `∀ᶠ BAbulk κ E` (`S0_bulk`, UNPins:891); `δ>0`; window `∀x∈[E−δ,E+δ], ∀ᶠ BAbulk (κ/2)x` (`BAbulk_window` from `S0_bulk`; numerically min ρ = 0.28284 ≥ κ/2 = 0.14154); `UNLocAvgBAAt 3` is another gate's pin (row a A8) and stays a hypothesis of the `example`. No other external hypothesis.
Limit computations (`Admissible` at S0): `N_n = 64 (2(n+1))^{15} → ∞`; `W ≥ N^{1/6}` (`N = (4W)³`, `N^{1/6} = 2W^{1/2} ≤ W` for `W ≥ 4`; script at n = 1: 64.00 ≤ 1024); `W^{-d/2+𝔡} = W^{-1.4} → 0 < λ_n = 0.222 ≤ 𝔡⁻¹ = 10`.

Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2514b && python3 inst.py`
```
S0 flow point: t0=0.549212 g0=lam=0.222327 E*=0.000000 m0=-0.000000+0.889306j kappa*=Im m0/pi=0.283075  rho(E*)=0.283075
delta=(pi k)^3/8=0.08792: min rho on [E*-delta,E*+delta]=0.28284 >= k/2=0.14154
B1: r=(pi k/2)^3/8=0.01099: min rho on [E*-delta-r,E*+delta+r]=0.28277 >= k/4=0.07077
k2=k/4=0.07077 c=pi k2=0.22233 c1=c/2=0.11116 ktilde=c1/(2pi)=k/16=0.01769=0.01769  ctilde=2.590e-10 c0=2.652e-07  C'=2+2/ct^2+32/c0^2=2.981e+19
T=0.01: a=0.99501248 lam-hat=0.22344095; Bctl'<=Bctl: True; scaling identity max |BAm_lhat(zeta'')-a m|=2.22e-16; shift max |a^-1 m~(z/a)-m(z)|/T=0.359 <= 32/c0^2=4.55e+14
   rho_lhat on [E*-delta-r,E*+delta+r]: min=0.28250 >= ktilde=0.01769: True
T=0.0001: a=0.99995000 lam-hat=0.22233765; Bctl'<=Bctl: True; scaling identity max |BAm_lhat(zeta'')-a m|=2.23e-16; shift max |a^-1 m~(z/a)-m(z)|/T=0.359 <= 32/c0^2=4.55e+14
   rho_lhat on [E*-delta-r,E*+delta+r]: min=0.28277 >= ktilde=0.01769: True
T0=min(1, r/(delta+|E|+1), c1^3/(16(xmax+2)), c1^3/32)=4.090e-05;  need T_n=N^(-1/2)<=T0  <=>  N>=T0^-2 ; need W^(tau/2)=W^(1/20)>=max(2,C')
first n with T_n<=T0: 1; first n with W_n^(1/20)>=max(2,C'): 3.949e+77  (eventual thresholds, not used as a witness)
S0 n=1: W=1024 N=6.8719e+10 N^(1/6)=64.00<=W: True; W^(-d/2+1/10)=6.10e-05<=lam=0.2223<=1/dd=10: True
T_1=N^(-1/2)=3.81e-06<=1; lam-hat/lam=e^(T/2)=1.000001907350<=2; lam-hat=0.222327<=(dd/2)^-1=20
```
Reading: at S0 every hypothesis of B2-B5 holds with the bulk, the window and the `λ̂`-bulk nonempty (ρ ≈ 0.28 against `κ/4 = 0.071` and `κ̃ = 0.018`); the numerical `Bctl' ≤ Bctl`, scaling identity, shift and `λ̂`-bulk checks agree with rows 6, 8, 9, 11. The `∀ᶠ` thresholds (row 12) are eventual and are not hypotheses.

### Verdicts
- **B1: PASS** (row 1; proved at radius `δ+r`, used at `δ` by B2 and at `δ+r` by B4; private).
- **B2, B3: PASS** (rows 1, 3, 13; no exponent beyond row 1).
- **B4, B5: PASS**, route differs from the ticket's F5 text and needs no probe: (1) `Bctl` at `λ̂` is `≤` `Bctl` at `λ` (row 6), so no BA-D8 coupling-Lipschitz bound; (2) the `m`-shift is `t₄ ≤ 32T/c₀²` via the exact scaling identity (row 8) and a one-sided `BASelf_sub_le`; (3) the `ρ`-bulk at `λ̂` is Cplx→Real (row 9) with level `κ̃ = κ/16`. Statement of B4 unchanged (the only `withLam` is P4 at `sz.withLam (lamHat sz (ouTStar sz τs))`, as UBA-C1).
- **B6: PASS** (instances at S0 with `UNLocAvgBAAt 3` as a binder, `κ_*`, `E_*`, `δ = (πκ_*)³/8` as in `MAPins:243-253`).
- No pin, row or stop line moves: no `1a-audit needed`. Paper-delta candidates: none (all three differences are proof routes). Overall verdict: **PASS**.
## (b) Script output (row b: B1-B6; branch `t/T2514b`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2514b`)
### b1 time, commits, diff, size, build, axioms
```
$ date -u
Thu Oct 15 08:22:42 UTC 2026
$ git log --oneline -4
c02bf2ab T2514b: registry whitespace fix
f3c524a2 T2514b: BA/MATrLocalBA instances, RBM3D.lean import, registry lines
3c126caa T2514b: BA/MATrLocalBA B1-B5 (TrLocal rows through per-d cores)
112ffba2 T2514a: BA/MAPins (MN1 pin texts P1-P6, per-d readings, instances)
$ git diff --stat 112ffba2 HEAD   # row b alone, on top of row a
 RBM3D.lean                |   1 +
 RBM3D/BA/MATrLocalBA.lean | 521 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |   6 +-
 3 files changed, 524 insertions(+), 4 deletions(-)
$ git diff --stat b2326aac...HEAD   # from the base of t/T2514 (row a is the first commit)
 RBM3D.lean                |   1 +
 RBM3D/BA/MAPins.lean      | 260 +++++++++++++++++++++++
 RBM3D/BA/MATrLocalBA.lean | 521 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |   6 +-
 4 files changed, 784 insertions(+), 4 deletions(-)
$ wc -l RBM3D/BA/MATrLocalBA.lean   # ticket: bottom-up 255 / 365 / 760, calibrated 350-467, stop line 800
     521 RBM3D/BA/MATrLocalBA.lean
$ lake build RBM3D.BA.MATrLocalBA 2>&1 | tail -1
Build completed successfully (3900 jobs).
$ lake env lean <scratch>/axioms.lean   # #print axioms of the four public declarations
'RBM.BA.unTrLocalBAAt_of_locAvg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalBARow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalInitBAAt'_of_locAvg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalInitBARow'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b2 target statements (extracted by script) and their equality with the check's pins
```
$ awk: lines of each target from `theorem <name>` to the first `:=` in RBM3D/BA/MATrLocalBA.lean
theorem unTrLocalBAAt_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d := by
theorem unTrLocalBARow_holds : UNTrLocalBARow :=
theorem unTrLocalInitBAAt'_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d := by
theorem unTrLocalInitBARow'_holds : UNTrLocalInitBARow' :=
$ <scratch>/pins.lean = docs/tickets/checks/T2514-check.lean + `import RBM3D.BA.MATrLocalBA` + these six examples (uncommitted); lake env lean <scratch>/pins.lean
example : T2514_TrLocalCore := unTrLocalBAAt_of_locAvg
example : T2514_TrLocalInitCore := unTrLocalInitBAAt'_of_locAvg
example : T2514_Rows := ⟨unTrLocalBARow_holds, unTrLocalInitBARow'_holds⟩
example : T2514_TrLocalCore ↔ ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d := Iff.rfl
example : T2514_TrLocalInitCore ↔ ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d := Iff.rfl
example : T2514_Rows ↔ UNTrLocalBARow ∧ UNTrLocalInitBARow' := Iff.rfl
exit=0 error-lines=0
```
### b3 the compiled nonempty instances (B6), verbatim
```
$ sed -n 472,521p RBM3D/BA/MATrLocalBA.lean | grep -v blank/docstring/end lines   # six `example`s at S0, d = 3, kappa_* = clsκ 4 _, E_* = (fp 4 _).E, delta = (pi kappa_*)^3/8
example (hL : UNLocAvgBAAt 3) :
    UNTrLocal S0 (UNModelC.ba S0).toUNModel (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalBAAt_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin
example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
    |z.re - (fp 4 MATrLocalBA_hg).E| ≤ (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 ∧ Nsz S0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 1 ∧
      ((S0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * S0.Bctl n (1 - z.im) < ‖stieltjesN ((UNModelC.ba S0).H n ω) z - BAm 3 (S0.L n) (S0.lam n) z‖} ≤
      ENNReal.ofReal (Nsz S0 n ^ (-1 : ℝ)) :=
  unTrLocalBAAt_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)
example (hL : UNLocAvgBA) :
    UNTrLocal S0 (UNModelC.ba S0).toUNModel (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalBARow_holds hL 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin
example (hL : UNLocAvgBAAt 3) :
    UNTrLocalInit' S0 (UNModelC.ba S0) (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalInitBAAt'_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin
example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
    |z.re - (fp 4 MATrLocalBA_hg).E| ≤ (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 ∧ Nsz S0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 1 ∧
      ((S0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (S0.Bctl n (1 - z.im) + ouTStar S0 (1 / 2) n) <
        ‖stieltjesN (ouInit (UNModelC.ba S0) n (ouTStar S0 (1 / 2) n) ω) z - BAm 3 (S0.L n) (S0.lam n) z‖} ≤
      ENNReal.ofReal (Nsz S0 n ^ (-1 : ℝ)) :=
  unTrLocalInitBAAt'_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin (1 / 2) (by norm_num) (by norm_num) (1 / 10) (1 / 10) 1
    (by norm_num) (by norm_num) (by norm_num)
example (hL : UNLocAvgBA) :
    UNTrLocalInit' S0 (UNModelC.ba S0) (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalInitBARow'_holds hL 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin
```
### b4 registry: diff and scan before / after
```
$ git diff -U0 112ffba2 HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean | grep -E "^[-+@]" | cut -c1-110
--- a/RBM3D.lean
+++ b/RBM3D.lean
@@ -645,0 +646 @@ import RBM3D.BA.MainIndTermBA
+import RBM3D.BA.MATrLocalBA
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
@@ -181,2 +180,0 @@ def owedProps : List Name :=
-   `RBM.Univ.UNTrLocalBARow, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1)
-   `RBM.Univ.UNTrLocalInitBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1, BA 
@@ -383 +381 @@ def structuralProps : List Name :=
-   `RBM.Univ.UNTrLocal, -- bulk universality: a condition on the data of the generic lemmas (an arbitrary `UN
+   `RBM.Univ.UNTrLocal, -- bulk universality: a condition on the data of the generic lemmas (an arbitrary `UN
@@ -387 +385 @@ def structuralProps : List Name :=
-   `RBM.Univ.UNTrLocalInit', -- bulk universality: tolerance `W^τ (Bctl + t*)`, primed successor of the refut
+   `RBM.Univ.UNTrLocalInit', -- bulk universality: tolerance `W^τ (Bctl + t*)`, primed successor of the refut
$ BEFORE (HEAD 112ffba2, `lake build` of the whole library, scan lines)
info: RBM3D.lean:648:0: axiom audit: 15449 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Univ.UNTrLocalBARow: 3 [no certificate]
  RBM.Univ.UNTrLocalInitBARow': 4 [no certificate]
premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 120 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4418 jobs).
$ AFTER, branch as committed (row b alone), `lake build`
error: RBM3D.lean:649:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`
  [RBM.BA.UNLocAvgBAAt]
error: build failed
$ AFTER, scratch stub `theorem scratch_UNLocAvgBAAt_stub : ∀ d, 3 ≤ d → False → UNLocAvgBAAt d` before `#assert_rbm_axioms` (uncommitted, reverted; stands for row a's A6)
info: RBM3D.lean:653:0: axiom audit: 15457 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 53, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 118 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4420 jobs).
```
### b5 hypothesis-rule greps and name clash
```
$ grep -nE 'mE\b|\|E\| ≤ 2|SB d|M = m|m • 1|etaT|STFlow|lemT|lemE|msc|locDomain|Mband|sz\.Gn'   # C1
hits 0
$ grep -nE '^(private )?(noncomputable )?(def|abbrev|structure) '   # X1-C4: no def/abbrev/structure
hits 0
$ grep -nE 'ℕ → Prop\)|· = 3'   # MN-D3
hits 0
$ grep -nE 'unMLOutBA_three|baMLOutTL_three'   # F1
hits 0
$ grep -nE 'sorry|admit|native_decide|^axiom'   # hygiene
hits 0
$ grep -nE 'withLam'   # UBA: no target statement has withLam; hits are the private Bctl lemma, a docstring, B4's shifted model
hits 3
203:    (hg : sz.lam n ^ 2 ≤ g n ^ 2) : (sz.withLam g).Bctl n (1 - η') ≤ sz.Bctl n (1 - η) := by
234:`UNLocAvgBAAt d` at `sz.withLam λ̂` (admissible at `(𝔠, 𝔡/2)`) and `τ/2` bounds `stieltjesN H_{λ̂} ẑ - m(ẑ, λ̂)` by 
300:  set sz' : Sizes d := sz.withLam (lamHat sz (ouTStar sz τs)) with hsz'
$ grep -nE '∃'   # U5S-C3: the 4 hits are two `obtain` in a private proof and two instance event sets
hits 4
165:  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun k : ℕ => c ^ 3 / 16 * (1 / ((k : ℝ) + 1)) := ⟨_, rfl⟩
177:  obtain ⟨zs, hzsdef⟩ : ∃ zs : ℕ → ℂ, zs = fun k : ℕ => (y : ℂ) + (η k : ℂ) * Complex.I := ⟨_, rfl⟩
479:example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
501:example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
$ name clash: grep -rnE '<the four public names>' RBM3D RBM3D.lean --include='*.lean' | grep -v RBM3D/BA/MATrLocalBA.lean | cut -c1-70
RBM3D/Test/Axioms.lean:381:   `RBM.Univ.UNTrLocal, -- bulk universalit
RBM3D/Test/Axioms.lean:385:   `RBM.Univ.UNTrLocalInit', -- bulk univer
(both hits are the owner texts written by this ticket)
```

### b6 narrative (report written Thu Oct 15 08:22:56 UTC 2026; stage 1b began 07:49:52 UTC, first `date -u` of this stage)
- **Targets.** B2 `unTrLocalBAAt_of_locAvg`, B3 `unTrLocalBARow_holds`, B4 `unTrLocalInitBAAt'_of_locAvg`, B5 `unTrLocalInitBARow'_holds`; B1 is the private `MATrLocalBA_unif`. b2: each equals the check's `T2514_TrLocalCore`, `T2514_TrLocalInitCore`, `T2514_Rows` (the `example`s compile, exit 0). B6: six `example`s at `S0`, `d = 3` (b3); only `UNLocAvgBAAt 3` / `UNLocAvgBA` (row a's A8 / A7) are hypotheses; `S0_adm`, `clsκ_pos`, `S0_bulk`, `δ > 0` and the window (merged `BAbulk_window`) are discharged. Both cores hold for every `d ≥ 3`; like the merged rows they are conditional on the `UNLocAvgBA` reading (not unconditional local laws).
- **Routes** (merged `file:line` at base b2326aac). B1: `BAbulk_window` (MReg:122) at the centres of a finite cover of `[E-δ, E+δ]` by balls of radius `(π κ/2)³/8` (level `κ/2 → κ/4`). B2: twin of `unTrLocalBandRow` (BUnivHolds:205), `BUniv_trace_le` (BUnivHolds:172) by `open private`, P4 at `κ/4`. B3, B5: `UNTrLocalBARow_iff_at.2`, `UNTrLocalInitBARow'_iff_at.2`, `UNLocAvgBA_iff_at.1` (P6, MAPins). B4: twin of `unTrLocalInit'_of_unTrLocal` (PinsC2:590) for the BA datum `m(·, λ_n)`; P4 at `sz.withLam (lamHat sz (ouTStar sz τs))` (`ouInit_ba` UNPins:472, `admissible_lamHat` UNPins:503); 13 private helpers of PinsC2 by `open private` (listed in the file, line 224).
- **F5 as used.** No upward-coupling Newton step, no probe; `BAwindow_step`, `BAmWindow_holds` (CouplingWindow) are not used. Three private lemmas replace it: `MATrLocalBA_scale` (the exact identity of `(self_m)` at complex `z`, `g₀ = a g`: `BASelf g₀ z m ⇒ BASelf g (z/a + a⁻¹(1-a²) m) (a m)`; twin of the real-`E` `BAzztE_inv_core`, CouplingWindow:239), `MATrLocalBA_cplx_real` (complex base point `w`, `‖w-y‖ ≤ c³/16`, `Im m ≥ c` ⇒ `BAbulk g (c/(2π)) y`; twin of `MReg_key` MReg:95 and `BAbulk_window`), `MATrLocalBA_Bctl_le` (`Bctl` at `λ̂² ≥ λ²` and a larger height is smaller; no coupling-Lipschitz bound).
- **Differences from the 1a route** (no pin, row or stop line moves; not mistakes of (a), so no (a′)): B1 is used at radius `δ` only: the real base solution is taken at `x = Re z` and scaled to `ζ = z/a`, so the `δ + r` window of 1a rows 1, 7 is not needed. The error terms `t₃, t₄` of 1a row 11 are one `BASelf_sub_le` between `m(ẑ, λ̂)` and the scaled solution `a m(z)`: `‖·‖ ≤ 24 T/c₀²`, `c₀ = (π κ/4)⁵/2048`, `Cb = 2 + 48/c₀²`, no `c̃` bound. Smallness: `T ≤ c₁³/32` (`c₁ = π κ/8`) and `W^{τ/2} ≥ max(2, Cb)`. Levels: B1 `κ/4`, P4 at `κ/16`. All constants are fixed before `∀ᶠ n`; `hE` is unused (1a row 3). B4 carries `set_option maxHeartbeats 1000000 in`, as its twin.
- **Registry (b4).** Two lines deleted (`UNTrLocalBARow`, `UNTrLocalInitBARow'`, by content), two owner texts replaced; the list header line is untouched (row a edits it). With the stub standing for row a's A6: found 128 → 126, owed 55 → 53 (−2), 0 new. **On this branch alone** the one unregistered premise is `UNLocAvgBAAt` (premise of B2, B4; concluded by row a's A6 `unLocAvgBAAt_of_locSCL`, absent here), so the full `lake build` fails at `#assert_rbm_axioms` until row a is merged and this branch is rebased. No registry line was added for it (not in the ticket).
- **Size.** 521 lines vs bottom-up 255 / 365 / 760, calibrated 350-467, stop line 800; B4 is lines 237-445 (209) vs 240 [170, 540].
- **Ports.** None from RBM1D/RBM2D (no diff-stat applies); twins of merged RBM3D files, last commits `git log -1 --format=%h -- <file>`: BUnivHolds c0a77475, PinsC2 122f2998, MReg 3deaafe8, CouplingWindow e1fec218, UNPins 88d76764.

## (c) Verified Mathlib names (each compiled in this file)
`IsCompact.finite_cover_balls` (alias of `finite_cover_balls_of_compact`, Pseudo/Basic.lean:263-268); `Set.Finite.eventually_all` (alias of `Filter.eventually_all_finite`, Order/Filter/Finite.lean:252-256); `isCompact_Icc`; `Metric.mem_ball`; `Real.dist_eq`; `Set.mem_iUnion₂`; `tendsto_subseq_of_bounded`; `Metric.isBounded_closedBall`; `tendsto_one_div_add_atTop_nhds_zero_nat`; `Real.exp_nat_mul`; `Real.add_one_le_exp`; `Real.one_le_exp`; `one_le_pow₀`; `inv_anti₀`; `pow_le_pow_left₀`; `mul_le_of_le_one_right`; `norm_add₃_le`; `Complex.coe_smul`; `Complex.re_add_im`; `Complex.im_ofReal_mul`; `Matrix.inv_smul`; `Matrix.isUnit_iff_isUnit_det`; `Matrix.nonsing_inv_eq_ringInverse`; `invertibleOfNonzero`; `Real.rpow_le_one_of_one_le_of_nonpos`; `tendsto_rpow_atTop`; `le_div_iff₀`; `div_le_iff₀`; repo: `RBM.isUnit_sub_smul_of_isHermitian` (Analysis/Resolvent.lean:132). Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- **Merge order.** Row b needs row a first: B2, B4 take `UNLocAvgBAAt d`, which only row a's A6 concludes (b4). After rebase on `main`: `RBM3D.lean` import lines are a union with row a's; the registry lines are located by content (T2511 row b shifts line numbers).
- **Premise `UNLocAvgBAAt`** stays unregistered on this branch alone (b4). If the dispatcher wants this branch to build alone, the registry line for it is a dispatcher decision (not in the ticket).
- Paper-delta candidates: none (statements equal the check's pins; the route differences from 1a are proof routes only).
