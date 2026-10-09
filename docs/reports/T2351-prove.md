Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 00:06:27 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `a₀ = 32 n₀ + 64`, `K = gueGridK = (N+1)^{a₀}`, `Δ = (t₀−t₁)/K`, `m ≤ 2 n₀`, `τ ≤ 1` (general `τ` reduces by `min τ 1`), `λ₀ = N^{-(40 n₀+80)}`, `ε_Y = N^{-(2 n₀+2)}`. Source: RBM2D `Universality/GUEPhase/DuhamelC.lean` (the bounds are quoted from its `DuhamelC_num_*` lemmas, lines 614-840, and header lines 66-81).

### (i) Exponent table

| # | Quantity / bound (all eventual in `N`) | Value at `n₀=1` (`a₀=96`) | Constraint | Slack |
|---|---|---|---|---|
| 1 | grid `K Δ ≤ 1` ⇒ `Δ ≤ N^{-a₀}`, `NΔ ≤ 1` | `Δ ≤ N^{-96}` | `a₀ ≥ 1` | exponent `a₀−1 = 95` |
| 2 | top dyadic level: `32m²Δ(N^{2m+2}+2mN^{2m+4}Δ) < 2^N λ₀` (`ℓ ≤ N`) | LHS `≤ N^{-(a₀−2m−4)}·32m²(1+2m)` | `N^{40n₀+81} ≤ 2^N` | `N`-linear vs `(40n₀+81)·log₂N`; log10 slack `6.3e5` at `N=2^21` |
| 3 | E1 floor: `2N^{τ/4}√(Kλ₀) ≤ N^{-m}/5` | `Kλ₀ ≤ 2^{a₀}N^{-(8n₀+16)}`, √ `= N^{-(4n₀+8)}` | `10 N^{m+1} ≤ N^{4n₀+7}` | exponent `(4n₀+7)−(m+1) ≥ 2n₀+6` (`=8`) |
| 4 | E2 shift: `16mN^{τ/4}√(2mN^{2m+4}Δ) ≤ N^{-m}/5` | `√(…Δ) ≤ N^{-(2n₀+3)}` | `80m N^{m+1} ≤ N^{2n₀+3}` | exponent `(2n₀+3)−(m+1) ≥ 2` |
| 5 | E3: `ε_Y = N^{-(2n₀+2)} ≤ N^{-m}/5` | `N^{-4}` | `N² ≥ 5` | exponent 2; `N ≥ 3` (`N ≥ 3^d`) |
| 6 | Y remainder: `16K(b_T+λ₀)² ≤ ε_Y²/N = N^{-(4n₀+5)}`, `b_T = m(m+1)/2·N^{m+6}Δ` | `K b_T² ≲ N^{2m+12−a₀}` | `2m+4n₀+17 < a₀` and `36n₀+69 < 80n₀+160` | `a₀−(2m+4n₀+17) ≥ 24n₀+47` (`=71`); `44n₀+91` for `λ₀`-part |
| 7 | E4 truncation bias: `K‖B‖ ≤ (KΔ)16e²m(m+1)N^{m+6}e^{-N/4} ≤ N^{-m}/5` | exponent `2m+6` | `80e²m(m+1)N^{2m+6}e^{-N/4} ≤ 1` | exponential vs polynomial; log10 slack `2.3e5` at `N=2^21` |
| 8 | E5 drift: `K·16(m+3)⁴N⁴(1+N)^{m+4}Δ^{3/2} ≤ N^{-m}/5` (`envConst`, `Duhamel_drift_remainder_ae`) | `√Δ ≤ N^{-(16n₀+32)}` | `2m+8 < 16n₀+32` | `16n₀+24−2m ≥ 12n₀+24` (`=36`) |
| 9 | prefactor `16 m N^{τ/4} ≤ N^τ` | — | `N^{3τ/4} ≥ 16m` | log10 slack `3.24` at `N=2^21`, `τ=1` |
| 10 | assembly: five terms `≤ N^{-m}/5` sum to `N^{-m}`; `N^{-m} ≤ N^τ (Nη_{u_k})^{-m}` | — | `η ≤ 1`, `N ≥ 1`, `τ ≥ 0` | exact (`1`-sided) |
| 11 | label count `(N+1)(K+1)2^m(L^d)^m ≤ N^{2a₀+2m+3}` | exponent `199` (`m=2`) | `N+1 ≤ N²`, `K+1 ≤ N^{2a₀+1}`, `2^m ≤ N^m`, `(L^d)^m ≤ N^m` | needs `N ≥ 2`; at `n=0`: log10 LHS `617.4` vs `1258.0` |
| 12 | Azuma failure: `card · 4e^{-N^{τ/2}} ≤ N^{-D}` for every fixed `D` | `card ≤ N^{199}` | `N^{199+D}·4e^{-N^{τ/2}} ≤ 1` | eventual, `D`-dependent only |
| 13 | `hscale`: `(Nη_{t₀})⁻¹ ≤ N^{-τU}` ⇒ `η_{t₀} ≥ N⁻¹` (`heta`) | `10/N ≤ N^{-1/2}` | `N ≥ 100` (at `η=1/10`, `τU = 1/2`) | `N = 2^21`: `4.8e-6 ≤ 6.9e-4` |
| 14 | `N ≥ 1` (all `d`); `L^d ≤ N` (all `d`, from `L ≤ WL`); `N ≥ 2` | `N = (WL)^d ≥ 3^d` | `N ≥ 2` needs `d ≥ 1` | `d ≥ 1` follows from `hsize` (see below) |

The Taylor constant `C₂ = m(m+1) N η^{-(m+2)}` (`Duhamel_bddC2C_Phi`, merged `DuhamelB.lean:687-699`), the envelope `envConst = 16(m+3)⁴N⁴(1+η⁻¹)^{m+4}` (`Path/OneStep.lean:78-79`) and the bounds `C₂/2·v·N⁴`, `16e²C₂ v N⁴ e^{-N/4}` (`DuhamelA2.lean:601,825`) have the same `N`-exponents as RBM2D (`RBM2D/Path/OneStep.lean:71-72`); the only `d`-dependence of the whole chain is through `N` and the three facts of row 14, so rows 1-13 are the `d = 2` exponents unchanged.

**`d = 2` token table (`DuhamelC.lean` of RBM2D) and the `d`-replacement.**
| Token (source line) | Replacement |
|---|---|
| `Z2 (d.L n)` (`:98,151,356,947-991,1015,1074-1088,1135-1502`) | `Zd d (sz.L n)`; `ZMod.card` count `(L·L)^m` becomes `Fintype.card (Fin d → ZMod L) = L^d`, i.e. `(L^d)^m` |
| `9 ≤ d.size n` via `3^2 ≤ (W L)^2` (`:926-932`) | `N ≥ 2` only is used (`:949`) and `N ≥ 1` (`:1096,1147,1164,1293`); `3^d ≥ 3` needs `d ≥ 1` (row 14); the constant `9` becomes `3^d` (or `≥ 2`) |
| `L·L ≤ d.size n` (`:935-939`, `ring` on `(WL)·(WL)`) | `L^d ≤ (W L)^d`: `pow_le_pow_left` from `L ≤ W L`, no `ring` |
| `N^2` / `h1 : N+1 ≤ N^2` (`:960`) | not a dimension: `N ≥ 2` squares, unchanged |
| all other `^ 2` (`:140-340`: `√(a+b)`, `a_j²`, `(8mMk)²`, `Mk²`, `ε²`) | not dimension tokens, unchanged |
| `(W L)²` / `S = L W = N` in docstrings (`:51-53`) | `(W L)^d` |
| `size` (`d.size n`, all occurrences) | `sz.size n` (`def size = (W L)^d`, `Defs/Sizes.lean:157`); `unfold Sizes.size` unchanged |
| `log` (`:571,573,574`) | only `Real.log 2` in `ev_two_pow` (`N^a ≤ 2^N`): no `d`; unchanged (also the `log L` of `d=2` lattice sums does not occur) |

**Finding (d-dependent hypothesis).** `Sizes d` does not carry `1 ≤ d` (`Defs/Sizes.lean:138-146`), and `N = (WL)^0 = 1` at `d = 0`. Rows 11 and the private lemma `DuhamelC_card_le` (source `:944`, used with `Eventually.of_forall` at `:1022,:1140`) need `2 ≤ N` for every `n`, which the source gets from `9 ≤ N`. In the pinned statement there is no `hd`; mathematically it is still true: if `d = 0` then `size n = 1` for all `n`, contradicting `hsize : Tendsto size atTop atTop` (the hypothesis set is empty), so `1 ≤ d` and `N ≥ 3^d ≥ 3 ≥ 2` follow from `hsize` inside the proof. Stage 1b must derive `1 ≤ d` from `hsize` (or carry a private `2 ≤ size n` hypothesis supplied eventually); the public signature stays the source's. Paper-delta candidate: none (proof device).

### (ii) One concrete nondegenerate instance

Data (all hypotheses of `gueGrid_loop_duhamel`): `d = 3`, the merged sequence `SizesInst.sz0` (`Defs/Sizes.lean:260-265`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, so `N_n = 2^21 (n+1)^18`, `N_0 = 2097152`), `E_n = 0`, `κ = 1`, `τU = 1/2`, `n₀ = 1`, `m = 2 ≤ 2n₀` (`1 ≤ m`), the `Grid.lean` §`GridCheck` times `t₀ = 9/10`, `t₁ = e^{-1/20} t₀` (`ouZeta x = 1 − e^{-x}`, `ZeroModeProfile.lean:55`), `K = (N+1)^{96}`, `Δ = (t₀−t₁)/K`; `η_{t₀} = (1−t₀)·Im m_0 = 1/10` (`etaT = (1-t)(mE E).im`, `Loop/GLoop.lean:75`; `mE 0 = i`, `Defs/Semicircle.lean:38`). External hypotheses `hsize`, `hscale` (limit computation): `N_n = 2^21 (n+1)^18 → ∞`; `(N_n η)⁻¹ = 10/N_n ≤ N_n^{-1/2}` iff `N_n ≥ 100`, true for all `n` (rows printed). No `N = 0`, no empty index, no collapsed window (`t₀−t₁ = 0.0439`), thresholds of rows 1-13 are met already at `n = 0`.

Commands (scripts in the scratchpad, real arithmetic only, `mpmath` at 400 bits): `python3 .../scratchpad/T2351/inst.py` (instance) and `python3 .../scratchpad/T2351/chk.py | head -4` (smallest `L = n+3`, `W = 1`, `d = 3` sequence from which rows 1-9 all hold).

```
$ python3 inst.py
t1 = 0.856106  t0 = 0.900  0<=t1<=t0<1: True ; |E|=0 <= 2-kappa=1.0: True
m=2, 1<=m<=2*n0=2: True
n=0 L=4 W=32 N=2097152  N>=3^d*... N>=2:True  hscale (N*eta)^-1=4.768e-06 <= N^-tauU=6.905e-04: True
n=1 L=8 W=1024 N=549755813888  N>=3^d*... N>=2:True  hscale (N*eta)^-1=1.819e-11 <= N^-tauU=1.349e-06: True
n=2 L=12 W=7776 N=812479653347328  N>=3^d*... N>=2:True  hscale (N*eta)^-1=1.231e-14 <= N^-tauU=3.508e-08: True
closed form N_n = 2^21 (n+1)^18: True
hsize: sizes strictly increasing on n=0..2: True ; d>=1 gives N>=3^d
n=0 (N=2097152): all exponent bounds hold: True ; min log10-slack = 1.36 (step: Delta<=N^-a0)
n=1 (N=549755813888): all exponent bounds hold: True ; min log10-slack = 1.36 (step: Delta<=N^-a0)
n=2 (N=812479653347328): all exponent bounds hold: True ; min log10-slack = 1.36 (step: Delta<=N^-a0)
detail n=0 (log10 LHS, RHS, slack):
  step: Delta<=N^-a0                      -608.23    -606.88       1.36
  step: N*Delta<=1                        -601.91       0.00     601.91
  Q top level                             -568.20  630547.06  631115.26
  E1 floor                                 -73.98     -13.34      60.64
  E2 shift                                -275.44     -13.34     262.10
  E3 epsY                                  -25.29     -13.34      11.94
  Y remainder                             -506.29     -56.89     449.39
  E4 bias                              -227643.32     -13.34  227629.98
  E5 drift                                -238.26     -13.34     224.92
  prefactor 16 m N^(tau/4)<=N^tau            3.09       6.32       3.24
card bound at n=0: log10 LHS=617.41 <= log10 N^(199)=1258.00: True
$ python3 chk.py | head -4
n0=1 m=1: a0=96 card exp=197; all bounds hold for L=n+3, n>=4, N=(n+3)^3>=343
n0=1 m=2: a0=96 card exp=199; all bounds hold for L=n+3, n>=4, N=(n+3)^3>=343
n0=2 m=4: a0=128 card exp=267; all bounds hold for L=n+3, n>=5, N=(n+3)^3>=512
n0=3 m=6: a0=160 card exp=335; all bounds hold for L=n+3, n>=5, N=(n+3)^3>=512
```

The instance shows rows 1-14 simultaneously at `n = 0, 1, 2` of `sz0` (printed `True`); the smallest slack is row 1 (`Δ = 0.9·(1−e^{-1/20})/(N+1)^{96}` vs `N^{-96}`, log10 `1.36`, not a failure: the ratio is `(t₀−t₁) < 1` times `(N/(N+1))^{96}`) and the next is row 9 (`3.24`). Nothing is astronomically large beyond the nominal `K = (N+1)^{96}` (a proof device in the source and in `Grid.lean:104-106`); the main target is instantiated on the sequence `sz0` (not at a single `n`), since `hsize` is a statement about the sequence; at fixed `n` only the real-variable core (rows 1-14 at `n = 0`) is concrete.

### Verdict
- `gueGrid_loop_duhamel`: **PASS** (hypothesis set satisfiable at the instance; all exponents close with the slacks above; the `d`-dependent step is the `d ≥ 1` derivation from `hsize`, row 14 / Finding; no missing input).

## (b) Script output — Fri Oct  9 00:16:55 UTC 2026

```
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2351 log -1 --format="%h %an %s"; wc -l RBM3D/Universality/GUEPhase/DuhamelC.lean
a2e6b55 Jun Yin T2351: UN-39/40 Universality/GUEPhase/DuhamelC (port of RBM2D DuhamelC, d >= 3)
    1602 RBM3D/Universality/GUEPhase/DuhamelC.lean
$ git diff --stat main...t/T2351
 RBM3D/Universality/GUEPhase/DuhamelC.lean | 1602 +++++++++++++++++++++++++++++
 1 file changed, 1602 insertions(+)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/DuhamelC.lean
0
$ lake build RBM3D.Universality.GUEPhase.DuhamelC   (run 00:12:56 UTC, cached; tail -3)
info: RBM3D/Universality/GUEPhase/DuhamelA1.lean:1266:0: 'RBM.Univ.GUEPhase.DuhamelA1Inst.contDiffAt_loop_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3796 jobs).
exit=0
(the compile of the final file earlier in the tool log: "✔ [3796/3796] Built RBM3D.Universality.GUEPhase.DuhamelC (11s)".
 No warning mentions DuhamelC.lean: grep -c DuhamelC.lean on the build logs = 0, 0.  Full 'lake build' in the worktree: Build completed successfully (4163 jobs)., exit=0.)
$ lake env lean ax2.lean    # import RBM3D.Universality.GUEPhase.DuhamelC; #print axioms <names>
'RBM.Univ.GUEPhase.gueGrid_loop_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelCInst.hscale_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelCInst.gueGrid_loop_duhamel_check' depends on axioms: [propext, Classical.choice, Quot.sound]
$ registry pre-check: scratch file = {import RBM3D; import RBM3D.Universality.GUEPhase.DuhamelC; #assert_rbm_axioms}; lake env lean <it>
  (first 3 lines of the output, then the exit code; the full output is 190 lines of the existing premise ledger)
axiom audit: 10473 theorems, 3076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0
$ name-clash grep (RBM3D/ of the worktree and of main, outside Probe/ and outside the new file):
  gueGrid_loop_duhamel     hits:        0
  DuhamelCInst             hits:        0
  hscale_check             hits:        0
  DuhamelC_                hits:        0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; same with -- RBM2D/Universality/GUEPhase/DuhamelC.lean ; diff --stat 9e0f275 HEAD -- <file>
9e0f275
81fca44
(empty: HEAD = 9e0f275; the source file is 1521 lines, last changed in 81fca44)
```

### Target statement, extracted by script (`sed -n 1485,1505p`)
```lean
theorem gueGrid_loop_duhamel {d : ℕ} (sz : Sizes d) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (m : ℕ) (_hm1 : 1 ≤ m) (hm : m ≤ 2 * n0) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 (gueGridK sz n0) n (2 * m) j ω))
        + (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ m) :=
  DuhamelC_main sz hκ hτU n0 (gueGridK sz n0) (fun _ => rfl) hsize hE ht1 ht10 ht0 hscale m hm
```

### Compiled nonempty instance (`sed -n 1546,1549p;1566,1598p`); `hscale_check` is its `hscale`, `MarkovInst.sz0_size_tendsto_nat` (merged) its `hsize`
```lean
/-- `hscale` at `sz0`: `(N η_{t₀})⁻¹ = 10 / N ≤ N^{-1/2}` as soon as `N ≥ 100`. -/
theorem hscale_check :
    ∀ᶠ n in atTop, (gueScale sz0 (fun _ => (0 : ℝ)) n (DuhamelCInst_t0 n))⁻¹
      ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  ...
/-- **`gueGrid_loop_duhamel` at `sz0`** (`d = 3`), `κ = 1`, `τU = 1/2`, `n₀ = 1`, `E = 0`,
the `GridCheck` times, loops of length `m = 2`: every hypothesis is discharged. -/
theorem gueGrid_loop_duhamel_check :
    StochDomAt (Pgue sz0) sz0.size
      (fun n (p : Fin (gueGridK sz0 1 n + 1) × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) ω =>
        ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1 ω))
            (zt 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1))
            (loopOf p.2.1 p.2.2)
          - loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n 0 ω))
            (zt 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n 0))
            (loopOf p.2.1 p.2.2)
          - (gridStep DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n : ℂ) *
            ∑ j ∈ Finset.range p.1,
              genMatGUE 3 (sz0.L n) (sz0.W n) 0
                (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j)
                (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j ω)
                (loopOf p.2.1 p.2.2)‖)
      (fun n p ω =>
        Real.sqrt (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1
            - DuhamelCInst_t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz0.size n : ℕ) : ℝ))⁻¹ *
            (RBM.Gauss.etaT 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j))⁻¹
              ^ 2 *
            gueLmax sz0 (fun _ => (0 : ℝ)) DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n
              (2 * 2) j ω))
        + (gueScale sz0 (fun _ => (0 : ℝ)) n
            (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1))⁻¹ ^ 2) :=
  gueGrid_loop_duhamel sz0 (κ := 1) (τU := 1 / 2) one_pos (by norm_num) 1
    (E := fun _ => (0 : ℝ)) (t1 := DuhamelCInst_t1) (t0 := DuhamelCInst_t0)
    MarkovInst.sz0_size_tendsto_nat (fun n => by norm_num) (fun _ => GridCheck.t1_pos)
    DuhamelCInst_t1_le_t0 (fun _ => by norm_num) hscale_check 2 (by norm_num) (by norm_num)
```

### Translation (RBM2D source -> this file)
Mechanical image: `perl port.pl < RBM2D/Universality/GUEPhase/DuhamelC.lean` on the body (from `set_option linter.style.longLine` on; header rewritten); `port.pl`:
```
local $/ = undef;
my $s = <STDIN>;
# split: header docstring (lines before 'set_option linter.style.longLine') kept separately
my ($head, $body) = split(/(?=^set_option linter\.style\.longLine)/m, $s, 2);
# body renaming
$body =~ s/\bd\.L n\b/sz.L n/g;
$body =~ s/\bd\.W n\b/sz.W n/g;
$body =~ s/\bd\.size\b/sz.size/g;
$body =~ s/\bd\.three_le_L\b/sz.three_le_L/g;
$body =~ s/\bd\.W_pos\b/sz.W_pos/g;
$body =~ s/\bd\b/sz/g;
$body =~ s/\(sz : Sizes\)/{d : ℕ} (sz : Sizes d)/g;
$body =~ s/\{sz : Sizes\}/{d : ℕ} {sz : Sizes d}/g;
$body =~ s/Z2 \(sz\.L n\)/Zd d (sz.L n)/g;
$body =~ s/Z2 L\b/Zd d L/g;
$body =~ s/Idx \(sz\.L n\) \(sz\.W n\)/Idx d (sz.L n) (sz.W n)/g;
$body =~ s/gloop \(sz\.L n\) \(sz\.W n\) \(blockMat/loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)/g;
$body =~ s/genMatGUE \(sz\.L n\)/genMatGUE d (sz.L n)/g;
$body =~ s/loopMax \(sz\.L n\)/loopMax d (sz.L n)/g;
$body =~ s/envConst \(sz\.L n\)/envConst d (sz.L n)/g;
$body =~ s/loopMax d \(sz\.L n\) \(sz\.W n\) \(blockMat \(/loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (/g;
$body =~ s/\bspectralZ_im\b/zt_im/g;
$body =~ s/\bspectralZ\b/zt/g;
print $head . $body;
```
Token counts, source body vs. this file before the instance section (`python3 table.py`; the port has extra uses from the manual edits below):
```
RBM2D token                                                    -> RBM3D replacement                            src  port
d.L n / d.W n / d.size  (port adds new uses)                   -> sz.L n / sz.W n / sz.size                    274  294
Z2 (d.L n)                                                     -> Zd d (sz.L n)                                 22   23
Idx (d.L n) (d.W n)                                            -> Idx d (sz.L n) (sz.W n)                        7    7
gloop (d.L n) (d.W n) (blockMat M)                             -> loopL d .. (blockMat d .. M)                  13   13
genMatGUE (d.L n)                                              -> genMatGUE d (sz.L n)                           6    6
RBM.Ind.loopMax (d.L n)                                        -> RBM.Ind.loopMax d (sz.L n)                     7    7
envConst (d.L n)                                               -> envConst d (sz.L n)                            5    5
spectralZ / spectralZ_im                                       -> zt / zt_im                                    38   38
Pgue d / PathΩ d / gueH d / gueScale d / gueLmax d / gueGridK d -> ... sz                                        94   94
Duhamel{Zinc,Yst,B,Phi,v,Zst,Vp,r,T} d                         -> ... sz                                        68   68
variable {d : Sizes} / (d : Sizes)                             -> {d : ℕ} {sz : Sizes d} / (sz : Sizes d)        7    7
(d := d)                                                       -> (sz := sz)                                     5    5
etaT (RBM.Path.etaT in RBM2D)                                  -> etaT (RBM.Gauss.etaT, same name)              35   35
(d.L n * d.L n)  [card of Z2 L, L*L]                           -> (sz.L n ^ d)  [card of Zd d L, L^d]            4    4
```
Manual deviations from the mechanical image (`diff -U0 body.lean final_body.lean`): hunks / changed lines:
```
23 hunks, 74 changed lines
(the hunks: `open ... RBM.Loop`; `DuhamelC_size_ge` -> `DuhamelC_size_pos`, `DuhamelC_L_sq_le` -> `DuhamelC_L_pow_le`; `DuhamelC_card_le`, `DuhamelC_card_le'` (+ `hN : 2 ≤ N`, `L*L` -> `L^d`); the two `highProbAt_iInter` card hypotheses; the 5 uses of the size lemma; two docstring lines)
```

### Narrative (facts from the files and the logs above)
- Deliverable: `RBM3D/Universality/GUEPhase/DuhamelC.lean`, 1602 lines (source 1521), commit `a2e6b55` on `t/T2351`; `git diff --stat main...t/T2351` lists only this file. 1602 is below the ticket's 1800 and below the stop size 2100; the pre-named cut (central estimate above 1900) is not triggered, one file.
- Public declarations: the target `gueGrid_loop_duhamel` and, in `RBM.Univ.GUEPhase.DuhamelCInst`, `hscale_check` and `gueGrid_loop_duhamel_check`. The chain behind the target is 42 `private` declarations with the prefix `DuhamelC_` (CLAUDE.md §3 (E)). Registry: none.
- Statement = RBM2D `DuhamelC.lean:1495` under the port map of the ticket (table above); hypotheses and quantifier order unchanged; no `hd : 1 ≤ d`; no hypothesis added, nothing weakened.
- `d`-lines (the only places the port differs from the mechanical image): (1) the label set `Fin m → Zd d L` has `(L^d)^m` elements (`Fintype.card_fun`, `ZMod.card`), bounded by `N^m` through `L^d ≤ (W L)^d = N` (`DuhamelC_L_pow_le`); (2) the source's `9 ≤ N` (`(W L)^2 ≥ 3^2`) becomes `1 ≤ N` for every `n` and `d` (`DuhamelC_size_pos`) and `2 ≤ N` only `∀ᶠ n`, taken from `hsize` (`eventually_ge_atTop 2`) in the two `highProbAt_iInter` card hypotheses; this resolves the Finding of (a) (`Sizes d` has no `1 ≤ d`) without touching the public signature; (3) the `log` token is `Real.log 2` in `DuhamelC_ev_two_pow`, no `d`; (4) all exponent bounds `DuhamelC_num_*` are `∀ᶠ N` statements in `N` alone and are the source's, as stated in (a).
- RBM2D `Path/PerTime`: the only declaration used here, `RBM.Path.highProbAt_iInter`, is `RBM3D/Defs/StochDomAt.lean:279` (same name, reached through the imports). No RBM2D `Path/GoodEvent.lean` lemma, `gloopProd_*`, `Eblk_*` is used; `Real.one_le_rpow` (Mathlib) is used at `DuhamelC.lean:1466`.
- Instance (ticket option 1): the main target on the `Grid.lean` §`GridCheck` sizes: `sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`), `κ = 1`, `τU = 1/2`, `n₀ = 1`, `E = 0`, `t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀`, `m = 2`. Every hypothesis is discharged: `hsize` by the merged `MarkovInst.sz0_size_tendsto_nat`, `hscale` by `hscale_check` (`η_{t₀} = 1/10`; `(N/10)⁻¹ ≤ N^{-1/2}` for `N ≥ 100`, eventually), `hE`, `ht0`, `1 ≤ m`, `m ≤ 2 n₀` by `norm_num`, `ht1` by `GridCheck.t1_pos`, `ht10` by the private `DuhamelCInst_t1_le_t0`. No `N = 0`, no empty index set, no external hypothesis left.
- (a) is not edited and there is no (a′): its file:line citations were re-read (`DuhamelB.lean:687`, `DuhamelA2.lean:594/818` bounds at `601/825`, `Path/OneStep.lean:78`, `Defs/Sizes.lean:157, 260-265`, `ZeroModeProfile.lean:55`, `Loop/GLoop.lean:75`, `Grid.lean:106`) and agree; its exponent rows are not re-derived here (the Lean statements are `∀ᶠ N` and the build is the check).
- Paper: the GUE-phase loop Duhamel is an internal lemma of the §7.2 universality chain (design UN-D1, `docs/reports/T2162-portmap.md:233-234`); `grep -c GUE` on `paper/tex/{3_5,6,7_8,A,B}*.tex` gives 0, so there is no paper statement to compare. The grid size `gueGridK` and the size-scale `StochDomAt` are the merged `Grid.lean` definitions.

## (c) Verified Mathlib names (`lake env lean names.lean`, `#check` of each, exit 0, 0 error lines)
`Nat.one_le_pow`, `Nat.pow_le_pow_left`, `Nat.le_mul_of_pos_left`, `Fintype.card_fun`, `ZMod.card`, `Real.sqrt_eq_rpow`, `Real.mul_self_sqrt`, `Real.sqrt_pos`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.rpow_neg`, `Real.exp_le_one_iff`, `inv_anti₀`, `eventually_ge_atTop`. All other Mathlib names are those of the RBM2D source; `lean-toolchain` is `leanprover/lean4:v4.34.0` in both projects and the file compiles. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates — Fri Oct  9 00:17:47 UTC 2026
- Paper-delta candidates: none (no paper statement; the `d`-lines are proof devices, no Lean/paper statement difference).
- Observation: the full `lake build` in the worktree does not contain this module (the root import is added by the hub at merge), so the registry pre-check above is the `#assert_rbm_axioms` evidence for it.
- Observation: the ticket says RBM2D HEAD `9e0f275`; the source file itself was last changed in `81fca44` (diff-stat against HEAD is empty).
- Downstream: UN-50 `PathBounds` applies `gueGrid_loop_duhamel` with `hsize : Tendsto (fun n => sz.size n) atTop atTop` and `hscale` as stated in the target block above.
