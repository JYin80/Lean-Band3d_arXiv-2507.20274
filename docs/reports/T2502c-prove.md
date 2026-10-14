Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 07:19:33 UTC 2026

Row c only (targets 14-16, `Chain/ExpAvgGen`; worktree `RBM3D-wt/T2502c` at `bd5531ea`, row a merged `d3351df4`). Statement: `(res_ELK_n=1)` `max_a |E L^(1)_(u,sigma,a) - m_sigma| ≺ Bctl(u)^2` for `u <= T0 < 1` under `LWAvgLawgL`, `STLKgL`, `CltRepg` (`H0` Hermitian, `mu = seqP(sz.withLam g')`, `G_u = Gres(H0 + sqrt(u) X, ztOf m E u)`, `ztOf m E u = E + (1-u) m`, `Loop/GLoopFlow:55`) plus W1. Route (band `Induction/ExpAvg:295-378`, `:479-537`): Stein on the Gaussian part, `x = u X x + y` with `x_a = E g_a - m`, then inversion by `Step2Gen_uKer C n sigma sigma 0 u = Theta_u(X)`, `X = Step2Kern_Mss C n sigma sigma * C.S n` (`Chain/Step2Gen:182-193`).

### (i) Exponent table
| # | quantity | value | constraint | slack (script output below) |
|---|---|---|---|---|
| 1 | `T0`, `u` range | `0 <= u <= T0 < 1` | `Step2EventsGen_Flow` (`Step2EventsGen:68-71`) gives `T0 < 1`; `Bctl`, floor need `u < 1` | BA/band instance: `u_max = 0.9962 / 0.9957` |
| 2 | `Cs` of W1 (ii) | band `1.2792`, BA `1.0000` measured | `Cs` before `(sz, z)`, expected to depend on kappa only: `max_a sum_b |uKer(s,t)_ab| <= Cs` for `0 <= s <= t < 1`, no `(1-t)^-1` | sup over grid `s<=t` in `{0,.25,.5,.9,.99,1-1e-6,1-1e-12}`; merged proofs: band `ekSameRow_holds` (`Evolution/XiPins:357`), BA `baEKSameRow_holds` (`BA/EKPins:568`) |
| 3 | same-charge pole | band `X = m^2 S`, `\|1 - t m^2\| >= 1` for `t >= 0` at `E = 1/2` | `Re m^2 = -0.875 < 0` | band `rho(X) = 1.0000`, BA `0.9636`; row sums bounded at `t = 1-1e-12` (row 2) |
| 4 | W1 (i) self-consistency | `(H0 - E - C.m) M = 1` | with `z_u = E + (1-u)m`: `H0 - z_u - u m = M^-1` (algebra, checked) so the Stein diagonal `u m` cancels | residual `<= 1.2e-15` |
| 5 | W1 (i) block average | `tr(E_a M) = C.m n` for every block `a` | NOT implied by row 4: counterexample below; needed for `x_a = (E g_a - tr(E_a M)) + (tr(E_a M) - m)` | band/BA `max_a dev <= 9.4e-16` |
| 6 | `S` of the carrier | `C.S n = SB d (L n) (g' n)`, row sums 1 (`L >= 3`) | Stein covariance is `SB(g')`; the operator in `uKer` is `Mss * C.S`; cancellation of `u m` needs `S 1 = 1` | band `g'=1/2`, BA `g'=0` (`S = I`): row-sum dev `<= 1.1e-16`. NOT in the drafts `T2502_W1SelfConsDraft/W1SameRowDraft`; table row 10 of the ticket lists it for rows 10-13 only |
| 7 | envelope `\|G_u\| <= eta_u^-1 <= N` | `eta_u = (1-u) Im m`, `N = (WL)^d` | `Gres` of Hermitian matrix; `eta_u >= N^(-1+eps)` for `u <= T0`; eventual in `n` (`expAvg_eta_inv_le`, `:631`) | `eta = N^-0.9 = 3.64e-3`, `\|G\| = 267.5 <= 1/eta = 274.4 <= 512` |
| 8 | floor `N^-1 <= Bctl(u)` | `Bctl = W^-d ((lam^2+(1-u))^-1 + (L^d (1-u))^-1)` | `0 <= u < 1`, any `lam >= 0` (second term alone, `expAvg_Bctl_ge:604`) | `N^-1 = 1.95e-3 <= min Bctl = 3.19e-3` |
| 9 | flow constants | `kappa = eps = 1/10`, `kappa_m` | `\|E\| <= 2-kappa`; family row 3: `kappa_m <= Im m` | band `Im m = 0.9682 >= sqrt(2 kappa)/2 = 0.2236`; BA `Im m = 0.8442`, `kappa_m = 0.4221` |
| 10 | moments exponent | `E\|g_b - m\|^2 <= K`, `K = Bctl^2` (`expAvg_moment:711`, from `LWAvgLawgL`) | band: `\|x\| <= C K` for `K = Bctl^2` (`expAvg_expErr_le:530`) | not a number; no loss: exponent 2 in, 2 out |
| 11 | correlator at non-scalar `M` | band `tr(E_a E_p G) = delta_ap g_a` | at `M = M^B ⊗ I`: `tr(E_a M E_p G) = M^B_ap W^-2d sum_i G_((p,i),(a,i))` (checked), not a loop `g_a` for `a != p` | open item for the gate (verdict below) |

### (ii) One concrete nondegenerate instance
`d = 3`, `L = 4`, `W = 2` (fine dimension 512, `N = 512`), `kappa = eps = 1/10`, `E = 1/2`, fixed size `n`. Band-type: `H0 = 0`, `M = m I`, `m = msc(1/2) = -1/4 + i sqrt(15)/4`, `S = SB(g' = 1/2)`. BA-type: `H0 = g Psi^(B) ⊗ I_8`, `g = 1/4`, `m` the root of `m = L^-d tr(g Psi - E - m)^-1`, `Im m > 0` (Newton), `M = (g Psi - E - m)^-1 ⊗ I_8`, `S = SB(0) = I`. `Mss` is computed from the fine matrix by its definition `W^-d sum_(x in a, y in b) M_yx M_xy`. Command and output (`python3` with numpy; script not Lean):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502c/inst.py
floor N^-1=1.953e-03 <= Bctl for lam in{0,1/64,1/8,1,10}, t in{0,.5,.9,1-1e-9}: True; min Bctl=3.191e-03
band m=msc(1/2)=-0.250000+0.968246j; |m^2+Em+1|=0.0e+00; |m|=1.000000; Re m^2=-0.8750; Im m=0.9682 >= sqrt(2kap)/2=0.2236
[band H0=0, S=SB(g'=1/2)] m=-0.250000+0.968246j Im m=0.9682>=kap_m? ; |(H0-E-m)M-1|=4.5e-16; H0 herm dev=0.0e+00; max_a|blockavg M_xx - m|=2.2e-16; max row-sum dev of S=1.1e-16; g'=0.5
      Stein cancellation |H0-z_u-um-M^-1| (u=0,.3,.9)=2.2e-16; spectral radius X=M^(++)S: 1.0000; sup_(0<=s<=t<1-1e-12) max_a sum_b|uKer_ab| = 1.2792 at (s,t)=(0, 0.999999999999)
      envelope: u_max=1-N^(-1+eps)/Im m=0.996236, eta=3.6447e-03=N^(-0.9)=3.6447e-03, ||G||=2.00<=1/eta=274.37<=N=512
draft (i) alone: H0=0, C.m=i: M=-(E+m)^-1 I solves (H0-E-m)M=1 (resid 0.0e+00) but block average of M = -0.4000+0.8000j != C.m = 1j
BA g=1/4: self_m residual |m-L^-d tr(g Psi-E-m)^-1|=1.1e-16, Im m=0.8442; Ward max_a sum_b|M^B_ab|^2=1.000000; M^B symmetric dev=3.8e-16
[BA H0=g Psi (g=1/4), S=SB(g'=0)=I] m=-0.192224+0.844190j Im m=0.8442>=kap_m? ; |(H0-E-m)M-1|=1.2e-15; H0 herm dev=0.0e+00; max_a|blockavg M_xx - m|=9.4e-16; max row-sum dev of S=0.0e+00; g'=0
      Stein cancellation |H0-z_u-um-M^-1| (u=0,.3,.9)=1.1e-15; spectral radius X=M^(++)S: 0.9636; sup_(0<=s<=t<1-1e-12) max_a sum_b|uKer_ab| = 1.0000 at (s,t)=(0.5, 0.5)
      envelope: u_max=1-N^(-1+eps)/Im m=0.995683, eta=3.6447e-03=N^(-0.9)=3.6447e-03, ||G||=267.53<=1/eta=274.37<=N=512
      SB(0)=I: 0.0e+00; BA flow facts: kappa_m=Im m*(1/2)=0.4221 <= Im m=0.8442
identity tr(E_a M E_p G)=M^B_ap W^-2d sum_i G_(p,i),(a,i): |diff|=2.2e-19; M^B_ap=3.180e-02 (a,p non-adjacent)
```
External hypotheses (not provable here, limit statements of TEAM lesson 14): `LWAvgLawgL` and `STLKgL` are `≺` statements along `n -> infinity` and are inputs of the target (family premises 5-7, V1-BA). The only limit entering the arithmetic of row c: `eta_u^-1 <= N` for `u <= T0` holds from `N^eps >= 4/c0`, `c0 = sqrt(2 kappa)/2 = 0.2236`, i.e. `N^(1/10) >= 17.9`, `N >= 3.4e12` (band `expAvg_eta_inv_le:631`); at `N = 512` the displayed envelope row holds with `eta = N^(-1+eps)` directly (`267.5 <= 274.4 <= 512`).

### Findings and verdict
- **No merged W1 text.** `grep -rln "SameRow\|SelfCons" RBM3D/Chain RBM3D/Probe` = 0 files (no `RBM3D/Probe` directory in the worktree). The only merged same-row bounds over a carrier have the loss: `GridAssemblyGen_row_le` `Step2Gen_uKer v w` row `<= 1 + (1-w)^-1` (`Chain/GridAssemblyGen:227`), `GridRepTailGen:57` row `<= (1-v)/(1-w)`; `Step5KerGen_ThDecay` has `C6/(1-t)` (ticket). `ekSameRow_holds` and `baEKSameRow_holds` are at the band and BA kernels, not at `Step2Gen_uKer C`. `T2502_W1SelfConsDraft`, `T2502_W1SameRowDraft` are drafts in the check file only (ticket: not binding).
- **The draft W1 (i) is too weak (table rows 5, 6).** Counterexample in the output above: `H0 = 0`, `C.m = i`, `M = -(E+m)^-1 I` solves `(H0 - E - C.m) M = 1` while its block average is `-0.4+0.8i != C.m`. The gate text must add `tr(E_a M) = C.m n` (ticket W1 (i) already says it; the draft omits it) and `C.S n = SB d (L n) (g' n)`.
- **Row 11 (for the gate).** The band self-consistency `expAvg_selfcons` (`:370-378`) closes because `E_a E_p = 0` gives `tr(E_a E_p G) = delta_ap g_a`, so the error is `E[(g_p - m)(g_a - m)]`, a second moment of `LWAvgLawgL`. With non-scalar `M` the error is `E[Dev_p M^B_ap G~_pa]` (`G~_pa = W^-2d sum_i G_((p,i),(a,i))`), not a loop at `L^(1)`; the gate (D1 inline texts plus the probe) must state which premise gives `Bctl^2` for it (e.g. decay of `M^B` with `sum_p |M^B_ap| <= C`, plus an entrywise bound on `G - M`), or show the probe at `sz0`/BA exact type. Not settled by this section.
- Rows, layout and cut unchanged (c = `ExpAvgGen` alone, imports `Step6KitGen`, `Induction/ExpAvg`, `Chain/CltGen`, `Evolution/XiPins`; no 1a-audit needed for that reason).
- Verdict 14 (fixed size, W1 (i)/(ii) inputs): BLOCKED (no merged W1 text; draft (i) insufficient).
- Verdict 15 (sequence part: envelope row 7, floor row 8, moments row 10): PASS arithmetic (slacks above).
- Verdict 16 (`stExpAvgAtgL_of`, `stImproveExpAvergL_of`): BLOCKED on 14; hypothesis set satisfiable once W1 (i) includes the block average and `S` (instances above).
- **Overall: BLOCKED — W1 gate needed.** The hub reruns row c with the narrow W1 gate (probe `RBM3D/Probe/T2502Pins.lean`, then a 1a-audit) before 1b.

## (a″) W1 gate probe — Wed Oct 14 07:42:31 UTC 2026

Gate of ticket answer (7) / H295 (3); section (a) not edited. Probe `RBM3D/Probe/T2502Pins.lean` on `t/T2502c` (never merged, no root import), commits `ec36d6ac`, `0f0ad532`; the branch diff against `main` is that one file (`git diff --stat main...t/T2502c`: 1 file changed, 291 insertions). It imports `Chain/Step2Kern` (imports BA) and `BA/TwistPins`; the merged `ExpAvgGen` must not.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2502c && lake env lean RBM3D/Probe/T2502Pins.lean; echo "exit=$?"
@BATwistAvgLaw : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → Prop
'RBM.BA.T2502c_band_W1fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2502c_ba_W1fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2502c_band_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ wc -l RBM3D/Probe/T2502Pins.lean; grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Probe/T2502Pins.lean
     291
0
$ sed -n 41,52p RBM3D/Probe/T2502Pins.lean   # D1: W1 (i) strengthened, W1 (ii) eventual
def T2502c_W1i (C : FlowFM sz) (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (g' E : ℕ → ℝ) (n : ℕ) : Prop :=
  C.S n = SB d (sz.L n) (g' n) ∧
  (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Matrix.of (fun x y => C.M n x y) = 1 ∧
  ∀ a : Zd d (sz.L n), (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, C.M n x x = C.m n
def T2502c_W1ii (C : FlowFM sz) (Cs : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b : Zd d (sz.L n), ‖Step2Gen_uKer C n σ σ s t a b‖ ≤ Cs
$ sed -n 57,63p RBM3D/Probe/T2502Pins.lean   # family text, rows 9 + 14 (one witness (H₀, g', E))
def T2502c_W1fam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Cs : ℝ, 0 < Cs ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ (∀ n, T2502c_W1i (mk sz z) H₀ g' E n) ∧ T2502c_W1ii (mk sz z) Cs
$ grep -n "^theorem T2502c\|^example" RBM3D/Probe/T2502Pins.lean | cut -c1-60   # discharges and instances
70:example (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx 
78:example (n : ℕ) (σ : Bool) (t : ℝ) :
88:theorem T2502c_band_W1i (sz : Sizes d) (E : ℕ → ℝ) (hE : 
108:theorem T2502c_window (sz : Sizes d) {𝔠 𝔡 : ℝ} (h : sz.A
114:theorem T2502c_flowE {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ
121:theorem T2502c_band_W1fam (d : ℕ) :
153:theorem T2502c_band_collapse (sz : Sizes d) (E : ℕ → ℝ) 
187:example (C : FlowFM sz) (n : ℕ) (a q : Zd d (sz.L n)) : 
197:example : ∃ C : FlowFM RBM.Gauss.SizesInst.sz0,
227:theorem T2502c_ba_W1i {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : 
249:theorem T2502c_ba_W1fam (d : ℕ) :
270:example : ∃ Cs : ℝ, 0 < Cs ∧ ∃ (H₀ : ∀ n, Matrix (Idx 3 
277:example : ∃ Cs : ℝ, 0 < Cs ∧ ∃ (H₀ : ∀ n, Matrix (Idx 3 
```

Evidence for findings (3), (4) (commands run in the worktree; python is a Monte Carlo check, not Lean):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502c/stein2.py   # BA toy d=1, M=M^B⊗I, S=I, H₀=gΨ⊗I; x_a = E g_a - m vs u Σ_q E[(g_q - m) t_aq]; "wrong" drops the −m shift
L=3 Wd=1 g=0.5 u=0.6: max|x|=0.0256 max|x-rhs|=2.14e-03 (std err 6.3e-04) max|x-wrong|=2.37e-01
L=3 Wd=2 g=0.5 u=0.6: max|x|=0.0064 max|x-rhs|=6.10e-04 (std err 2.9e-04) max|x-wrong|=2.42e-01
L=4 Wd=1 g=0.8 u=0.8: max|x|=0.1325 max|x-rhs|=2.57e-03 (std err 2.7e-03) max|x-wrong|=6.22e-01
$ sed -n 115,118p RBM3D/Chain/Carrier.lean
def STLocalMaxgL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))
$ sed -n 153,157p RBM3D/BA/TwistPins.lean
/-- **TL1 producer** (T.7, row TL1; fixed time, no induction): inputs (I2) `LWAvgLawgL` and (I3) `STLmaxgL` (`n = 2, 4`) at the time sequence `t`. -/
def BATwistAvgProd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t
$ grep -n "theorem baTwistAvgProd_holds" RBM3D/BA/TwistAvgB.lean; grep -n "private theorem CltFlowBA_MB_decay" RBM3D/BA/CltFlowBA.lean
451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
221:private theorem CltFlowBA_MB_decay (hd : 3 ≤ d) {κ 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
$ grep -n -A1 "theorem BAflow_lam0_window" RBM3D/BA/GreenSchur.lean
72:theorem BAflow_lam0_window {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) :
73-    ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
$ grep -rln "SteinRem\|T2502c_W1" RBM3D --include="*.lean"   # no merged text for (iii), (iv)
RBM3D/Probe/T2502Pins.lean
```

### Outcome (narrative; every number is in the script output above or in section (a))
| text | band (`bandFM`, `H₀ = 0`, `g' = sz.lam`) | BA (`baFMz`, `H₀ = g₀Ψ`, `g' = 0`) |
|---|---|---|
| W1 (i)′ | `T2502c_band_W1i` :88, every `E` with `abs (E n) ≤ 2` | `T2502c_ba_W1i` :227, every `BAFlow` with `0 < κ` |
| W1 (ii)′ | in `T2502c_band_W1fam` :121, every `STFlow` (`ekSameRow_holds d 𝔡⁻¹ (√(2κ)/2)`, `Step2Kern_uKer_band`) | in `T2502c_ba_W1fam` :249, every `BAFlow` (`baEKSameRow_holds d 𝔡⁻¹ κ`, `Step2Kern_uKer_BA`) |
| instance, `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`) | :270, `flow_z0`, `E = STflowE z0`, `(κ,ε,𝔠,𝔡) = (1/10,1/10,1/6,1/10)` | :277, `zSeq`, `flow_sz0`, exact type `baFMz sz0 zSeq`, `(1/2,1/10,1/6,1/10)` |
Each instance gives `Cs > 0`, `CltRepg`, (i)′ for every `n`, (ii)′; no `N = 0`, no collapsed window.

1. **Draft (i) too weak: settled.** `(H₀ - E - C.m) M = 1` does not force `tr(E_a M) = C.m n`: compiled counterexample (:197, exit 0): `H₀ = 0`, `E = 1/2`, `C.m = i`, `M = -(1/2 + i)⁻¹ • 1`. The text adds conjunct (c), `(W^d)⁻¹ Σ_{x∈Iblk a} C.M n x x = C.m n`, which the Stein step uses (`E g_a = tr(E_a M) + …`, `x_a = E g_a - m`). BA: `BAMB_diag_eq` + `BAMfine_eq`; band: `M = mE • 1`.
2. **Missing `C.S n = SB d (L n) (g' n)`: settled** as conjunct (a) of the same text: the Gaussian covariance of `μ = seqP (sz.withLam g')` is `SB(g')` (`CltRepg`, `CltGen:84`), while the kernel of `Step2Gen_uKer` is `Mss * C.S`; `S 1 = 1` (`sum_SB_row`, `Defs/Block:108`, `sz.three_le_L`) turns `D(g) - m` (the Stein diagonal minus `m`) into `Σ_p S (g_p - m)`. Band `rfl` with `g' = sz.lam`; BA `EMn2BA_SB_zero` with `g' = 0`. The cancellation `H₀ - z_u - u m = M⁻¹` follows from (b) (example :70); `uKer 0 t = Θ_t(Mss * S)` is :78.
3. **Stein error at non-scalar `M`: settled for the band; for BA reduced to two named premises, not discharged here.** Under (a)–(c) the Stein step (math) gives `x = u (Mss * S) x + R`, `x_a = 𝔼 g_a - m`, `R_a = u Σ_{q,p} S_{qp} 𝔼[(g_p - m)(t_{aq} - Mss_{aq})]`, `t_{aq} = tr(E_a M P_q G)` (`T2502c_SteinRem` :147, `T2502c_tM` :142); Monte Carlo above (lhs–rhs differences 2.1e-3, 6.1e-4, 2.6e-3 against rhs standard errors 6.3e-4, 2.9e-4, 2.7e-3, the lhs mean has its own noise; the variant without the `-m` shift is off by 0.24–0.62).
   - Band: `t_{aq} - Mss_{aq} = δ_{aq} m (ḡ_a - m)` (compiled pointwise, `T2502c_band_collapse` :153), so `R_a = u m Σ_p S_{ap} 𝔼[(g_p - m)(g_a - m)]`: second moments of `LWAvgLawgL` only (step of target 15, as band `expAvg_moment`). No premise beyond (i)′, (ii)′.
   - BA: `t_{aq} - Mss_{aq} = M^B_{aq}(G̃_{qa} - M^B_{qa})`, `G̃_{qa} = W^{-d} Σ_o G_{(q,o),(a,o)}` (numeric check in (a) table row 11, `|diff| = 2.2e-19`; merged identity `TwistPins_circ_term`, `BA/TwistPins:439`, private). None of the family premises 1–14 bounds this by `Bctl²`: `LWAvgLawgL` and `STLKgL` are diagonal-block laws, `STLocalMaxgL` is `Bctl^{1/2}` (output above), which gives `Bctl · Bctl^{1/2}` by Cauchy–Schwarz. The premise that does is TL1 `BATwistAvgLaw` (`|G̃ - M^B| ≺ Bctl`, `BA/TwistPins:91`, registry `Test/Axioms:192`), produced by the merged `baTwistAvgProd_holds` (`BA/TwistAvgB:451`) from `LWAvgLawgL` and `STLmaxgL` (`n = 2, 4`). The pinned target has premises `LWAvgLawgL`, `STLKgL` only, so `STLmaxgL` is a further family premise at BA (possibly derived from `STLKgL` and the K bound, ticket answer (6), K12; not checked here). Summing the L^d terms `q` needs `Σ_q |M^B_{aq}| ≤ CM`: BA source `CltFlowBA_MB_decay` (private, output above) and `sum_radial_exp_decay_le` (`Defs/RadialSum:275`).
   - Proposed inline texts (compile, no BA discharge in the probe): `T2502c_W1iii` :182 (`‖t_{aq} - Mss_{aq}‖ ≺ ‖M^B_{aq}‖ Bctl`; `T2502c_MB` is `twMB` by `rfl`, :187), `T2502c_W1iv` :190 (`Σ_q ‖M^B_{aq}‖ ≤ CM`, eventual). Not in D1 until the dispatcher chooses: (A) row c generic with (iii), (iv) as guarded family premises (band: collapse and `= 1`; BA: TL1 and `MB_decay`; TL1 owner per `Test/Axioms:192`: TL stage, closed, and BA-V per `u`); (B) row c for band-type carriers (`M = m • 1`; D1 as is) and BA's reading of `lem:improve_exp_aver` left to V1-BA. This is not settled within the ticket and the merged texts.
4. **New finding: draft (ii) is `∀ n`; the text is `∀ᶠ n`.** `ekSameRow_holds`/`baEKSameRow_holds` need `0 < g ≤ Λ`, which `Admissible` gives only eventually (`T2502c_window` :108; `BAflow_lam0_window`, `∀ᶠ`, output above). The same-row text keeps `∀ σ`, `0 ≤ s ≤ t < 1`; `Cs` depends on `(d, κ, 𝔡)` only (`Λ = 𝔡⁻¹`; `ε` is unused).
5. **One witness.** W1 (i)′ is stated for the `(H₀, g', E)` of `CltRepg`: the family text merges premise rows 9 and 14 in one `∃` (`T2502c_W1fam` :57); `0 < (C.m n).im` stays a fixed-size premise from row 3.
6. **Not probed (1b items):** the Stein step at `H₀ ≠ 0` over `Idx` (band `expAvg_stein` is at `HflowBlock`, `H₀ = 0`; BA twin `BAExpand_hasDerivAt_baG`, `Graph/BAExpand:158`; generic `hasDerivAt_green_moving`, used at `StepDecompGen:220`), the fine/block transport, the moment conversion of target 15, the assembly. No budget estimate here.

Result: probe compiles (exit 0), axioms printed for `T2502c_band_W1fam`, `T2502c_ba_W1fam`, `T2502c_band_collapse`: the standard three; no `sorry`; W1 (i)′ and (ii)′ are discharged at the band (every flow) and at BA (every flow, exact type of `baFMz`) and have compiled nonempty instances at `sz0`. Findings (1), (2), (4), (5) settled; (3) settled for the band, open for BA as stated. This section and the probe go to the 1a-audit and the dispatcher before any 1b.

## (a′) Preflight corrections — Wed Oct 14 09:36:39 UTC 2026
Found while proving; the verdict of (a), (a″) (PASS) is unchanged. Each item is checked in `RBM3D/Chain/ExpAvgGen.lean`.
1. (a) row 7 and "the only limit entering the arithmetic": no `η⁻¹ ≤ N` and no `N^ε ≥ 4/c0` is used. The carrier tuple gives `T0 < 1` and `κm ≤ Im m` (family row 3) and no gap `1 - T0 ≥ N^{-1+ε}`. The proof uses the floor `(N(1-u))⁻¹ ≤ Bctl` (`ExpAvgGen_Bctl_floor` `:1134`): `‖𝓛^(1) - m‖ ≤ (2/κm) N Bctl`, `‖t - M^(++)‖ ≤ (κm⁻²+1) N² Bctl` (`ExpAvgGen_envelope` `:1166`), and the reverse bridge is applied to `Y/ζ ≺ 1` (`ExpAvgGen_moment` `:1086`, envelope relative to the control).
2. (a) rows 4-6 and (a″) finding 3 do not list the invertibility of `1 - u M^(++) S`, which `x = Θ_u R` needs. W1 (ii) does not give it (`Ring.inverse` of a singular matrix is `0`, so the row bound holds trivially). It is proved from W1 (i) alone: Ward identity of `M` (`ExpAvgGen_ward` `:604`), `Σ_q |M^(++)_(aq)| ≤ 1` (`ExpAvgGen_Mss_row` `:694`), Levy-Desplanques (`ExpAvgGen_isUnit_one_sub` `:644`).
3. The binding shapes `T2502_Target16a/16b` list `T2502_W1fam` (and row 15) only. The proofs also read the family premise row 3 `Step5CasesGen_FlowFacts` (`SizeTendsto` from `Admissible`, `T0 < 1`, `κm ≤ Im m`; the conjunct `eta = (1-t) Im m` is unused). `T2502_W1fam` gives neither `T0 < 1` nor a lower bound of `Im m` (`Flow` is an arbitrary predicate). The theorems take row 3 as `hFF` (ticket table row 3 lists targets 15, 16); see (d).

## (b) Script output
```
$ lake build RBM3D.Chain.ExpAvgGen 2>&1 | tail -1;  lake build 2>&1 | tail -1      # the full build runs #assert_rbm_axioms
Build completed successfully (3867 jobs).
Build completed successfully (4390 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Chain/ExpAvgGen.lean; wc -l RBM3D/Chain/ExpAvgGen.lean     # bottom-up row c figure 1,260; stop 1,750
0
    1587 RBM3D/Chain/ExpAvgGen.lean
$ #print axioms of: ExpAvgGen_W1fam ExpAvgGen_W1iii ExpAvgGen_W1iiiOfLW STImproveCoregL stImproveCoregL_of stImproveExpAvergL_of stExpAvgUgL_of_core ExpAvgGen_band_W1fam ExpAvgGen_band_W1iiiOfLW stImproveExpAver_of_gL   | grep -c "[propext, Classical.choice, Quot.sound]"
10
$ grep -n "^/-! ## " RBM3D/Chain/ExpAvgGen.lean | cut -d: -f1 | tr '\n' ' '       # section starts, §1..§10 (file end 1587)
51 122 198 597 764 927 1080 1360 1433 1541
```
Target statements (script `sig.sh`: text up to the first line ending in `:=`):
```
theorem stImproveCoregL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hFF : Step5CasesGen_FlowFacts d Flow mk T0) :
    ExpAvgGen_W1fam d law Flow mk → STImproveCoregL d law Flow mk T0 := by
theorem stImproveExpAvergL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hFF : Step5CasesGen_FlowFacts d Flow mk T0) :
    ExpAvgGen_W1fam d law Flow mk → ExpAvgGen_W1iiiOfLW d law Flow mk T0 → STImproveExpAvergL d law Flow mk T0 :=
theorem stExpAvgUgL_of_core {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hCore : STImproveCoregL d law Flow mk T0) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ)
    (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z) (hμ : IsProbabilityMeasure (law sz)) (hsz : sz.SizeTendsto)
    (hK1 : ∀ (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ T0 sz z n) (ht1 : ∀ n, t n < 1)
    (hS2 : STStep2CoregL (mk sz z) (law sz) s t) (hLKU : STLKUgL (mk sz z) (law sz) s t)
    (hiii : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u) :
    STExpAvgUgL (mk sz z) (law sz) s t := by
```
Public defs against the Amend 1 check (script: strip docstrings, apply the name map `T2502_X ↦ ExpAvgGen_X`, `T2502_ImproveCoregL ↦ STImproveCoregL`, compare):
```
T2502_W1i -> ExpAvgGen_W1i: IDENTICAL
T2502_W1ii -> ExpAvgGen_W1ii: IDENTICAL
T2502_tM -> ExpAvgGen_tM: IDENTICAL
T2502_MB -> ExpAvgGen_MB: IDENTICAL
T2502_W1iii -> ExpAvgGen_W1iii: IDENTICAL
T2502_W1iv -> ExpAvgGen_W1iv: IDENTICAL
T2502_W1fam -> ExpAvgGen_W1fam: IDENTICAL
T2502_W1iiiOfLW -> ExpAvgGen_W1iiiOfLW: IDENTICAL
T2502_ImproveCoregL -> STImproveCoregL: IDENTICAL
ALL IDENTICAL
```
Auditor-style shapes (scratch `scratchpad/T2502c/Shapes.lean` = the Amend 1 check plus two examples; not committed): `lake env lean Shapes.lean` exit 0, 0 errors, 16a printed `[propext, Classical.choice, Quot.sound]`:
```
example ... (hFF : Step5CasesGen_FlowFacts d Flow mk T0) : T2502_Target16a d law Flow mk T0 := stImproveCoregL_of hFF
example ... (hFF : Step5CasesGen_FlowFacts d Flow mk T0) : T2502_Target16b d law Flow mk T0 := stImproveExpAvergL_of hFF
```
Compiled nonempty instances (`grep -n "^example"`, lines `:1551 :1558 :1565 :1571 :1583`, all in the file; `d = 3`, `sz0`, `z0`, `(κ,ε,𝔠,𝔡) = (1/10,1/10,1/6,1/10)`, `u ≡ 1/16`, `L = 4`, `W = 32`, `lam = 1/64` at `n = 0`):
```
:1551 family texts at (sz0,z0): ∃ Cs CM > 0, CltRepg, W1 (i) ∀ n, (ii), (iv)           -- ExpAvgGen_band_W1fam 3 .. flow_z0, nothing assumed
:1558 16a stImproveCoregL_of  at (sz0,z0,tInst)  -- hypotheses kept: LWAvgLawgL, STLKgL, ExpAvgGen_W1iii (stochastic pins)
:1565 16b stImproveExpAvergL_of at (sz0,z0,tInst) -- hypotheses kept: LWAvgLawgL, STLKgL
:1571 16c stExpAvgUgL_of_core at (sz0,z0,0,1/16)  -- hypotheses kept: STStep2CoregL, STLKUgL; W1 (iii) at every u is row 15 from LWAvgLawgL_of_STAvgUgL_at
:1583 STImproveExpAver 3 := stImproveExpAver_of_gL 3   -- band pin through 16b
```
Name-clash, diff, importers (`ev4`):
```
$ git grep -nE "ExpAvgGen_|STImproveCoregL|stImproveCoregL_of|stImproveExpAvergL_of|stExpAvgUgL_of_core|stImproveExpAver_of_gL" main -- RBM3D | wc -l   # on main (the registry text of the pin STImproveExpAvergL)
       1
$ grep -rnE <same pattern> RBM3D RBM3D.lean | grep -v RBM3D/Chain/ExpAvgGen.lean | cut -c1-60   # on t/T2502c
RBM3D/Test/Axioms.lean:226:   `RBM.BA.STImproveExpAvergL, --
RBM3D/Test/Axioms.lean:227:   `RBM.BA.ExpAvgGen_W1fam, -- th
RBM3D/Test/Axioms.lean:228:   `RBM.BA.ExpAvgGen_W1iii, -- W1
RBM3D/Test/Axioms.lean:229:   `RBM.BA.ExpAvgGen_W1iiiOfLW, -
$ git diff --stat main...t/T2502c
 RBM3D.lean                 |    1 +
 RBM3D/Chain/ExpAvgGen.lean | 1587 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2502Pins.lean |  291 ++++++++
 RBM3D/Test/Axioms.lean     |    5 +-
 4 files changed, 1883 insertions(+), 1 deletion(-)
$ git diff --stat main...t/T2502c -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Gauss RBM3D/Evolution RBM3D/Chain/Step6Gen.lean RBM3D/Chain/Step6KitGen.lean | wc -l
       0
$ grep -rln "import RBM3D.Chain.ExpAvgGen" RBM3D RBM3D.lean   # importers
RBM3D.lean
```
Hypothesis rules (script over the statements of the non-private declarations outside §9, §10):
```
$ python3 stmtgrep.py   # C1/X1-C1 pattern over the statements of the 12 non-private declarations before §9 (§9 = band bridge, lines 1433-1540; §10 = instances, lines 1541-end)
hits: 0
$ grep -nE "STGridRepNgL|import RBM3D.BA|import RBM3D.Chain.Step2Kern" RBM3D/Chain/ExpAvgGen.lean | wc -l ;  grep -n "^import" ...
0
6:import RBM3D.Chain.Step6KitGen   7:import RBM3D.Induction.ExpAvg   8:import RBM3D.Chain.CltGen   9:import RBM3D.Evolution.XiPins
$ grep -nE "^(noncomputable )?(def|abbrev|structure) " RBM3D/Chain/ExpAvgGen.lean | cut -d: -f1 | tr '\n' ' '     # the 9 defs of Amend 1 item 3, none else
59 67 72 76 81 87 93 104 115
U5S-C3 `grep -n "∀ (sz : Sizes d)"`: lines 94-95 (W1fam: rows 9 + 14), 105-106 (STImproveCoregL), 116-117 (row 15), 1366-67, 1408-09, 1417-18 (16a, 16b, 16c). UBA `sz.withLam|gK`: lines 781-916, 1217-18 (private lemmas reading `CltRepg`); none in a statement.
```
Registry (`RBM3D/Test/Axioms.lean`, scan with scratch roots: `RootBefore.lean` = `RBM3D.lean` without the new import, `RBM3D.lean` = after):
```
before: axiom audit: 15210 theorems, 4697 definitions, 0 axioms; premises found by scanning: 143 (borrowed 1, owed 64, structural 58, refuted 6, superseded 14)
after : axiom audit: 15216 theorems, 4706 definitions, 0 axioms; premises found by scanning: 143 (borrowed 1, owed 64, structural 58, refuted 6, superseded 14)
first full build with the import and before the registry edit:  error: RBM3D.lean:620:0: axiom audit: 1 premise(s) ... none of `borrowedProps`, `owedProps`, ...:  [RBM.BA.ExpAvgGen_W1iii]
after all edits, `lake env lean RBM3D.lean | sed -n '114,117p;186,188p'` (owed ledger usage; the registered premises that carry nothing yet):
  RBM.BA.STImproveExpAvergL: 6 [no certificate]
  RBM.BA.ExpAvgGen_W1fam: 3 [no certificate]
  RBM.BA.ExpAvgGen_W1iii: 1 [no certificate]
  RBM.BA.ExpAvgGen_W1iiiOfLW: 2 [no certificate]
  ...
 RBM.BA.STImproveExpAvergL,
 RBM.BA.ExpAvgGen_W1fam,
 RBM.BA.ExpAvgGen_W1iiiOfLW,
```
Added to `owedProps` after the `STImproveExpAvergL` line (`:227-229`): `ExpAvgGen_W1fam`, `ExpAvgGen_W1iii` (owner text of Amend 1 item 4), `ExpAvgGen_W1iiiOfLW` (band-only); the `STImproveExpAvergL` text (`:226`) now reads "generic: proved by `stImproveExpAvergL_of` ... BA: not produced". Ports: no text copied from `../RBM1D` or `../RBM2D` (diff-stat n/a); the proof adapts band `Induction/ExpAvg` (`expAvg_stein_coord`, `expAvg_stein`, `expAvg_moment`, `STExpAvgAt_of_LWAvgLaw`) and reuses by `open private`: `expAvg_integral_slice` (`ExpAvg:681`), `expAvg_integrable_of_cont_bdd` (`:111`), `expAvg_integrable_coord_smul` (`:96`), `expAvg_norm_trace_mul3_le` (`:87`), `Step6KitGen_K1_band` (`Step6KitGen:909`; instances only).

Family table as used by 16a/16b/16c, and UBA-C1 (ticket acceptance (5), (6)); names from the file and the ticket table:
```
row  premise                         read by        band discharge                           BA source (owner)
1    IsProbabilityMeasure (law sz)   16c (hμ)       isProbabilityMeasure_seqP; 16a/16b: from CltRepg (ExpAvgGen_prob, :872)   isProbabilityMeasure_seqP
2    Step2EventsGen_Flow             not read       (SizeTendsto, T0 < 1 come with row 3)    -
3    Step5CasesGen_FlowFacts (hFF)   16a, 16b       step5CasesGen_flowFacts_band             baStep5CasesGen_flowFacts (U2-BA)
9+14 ExpAvgGen_W1fam (Cs CM before (𝔠,sz,z))  16a, 16b   ExpAvgGen_band_W1fam (ekSameRow_holds, CM = 1)   probe T2502c_ba_W1fam + CltFlowBA_MB_decay (V1-BA)
15   ExpAvgGen_W1iiiOfLW             16b            ExpAvgGen_band_W1iiiOfLW                 none (band-only)
-    ExpAvgGen_W1iii (per time)      16a, 16c       from row 15 (instance :1571)             TL1 BATwistAvgLaw via TwistPins_circ_term (V1-BA)
-    LWAvgLawgL, STLKgL (per time)   16a (STLKgL unused)   Iff.rfl readings                  V1-BA
-    hK1, STStep2CoregL, STLKUgL     16c            Step6KitGen_K1_band; the two pins stay hypotheses   V1-BA
UBA-C1: no gK, no R1; the size level enters through `Bctl` and `CltRepg`'s `g'`; the kernel is `Step2Gen_uKer C n + + 0 u` (same charge, no `(1-t)⁻¹`).
```

Narrative (facts as in the output above).
- Delivered on `t/T2502c` (head `7cf02a5f`): new `RBM3D/Chain/ExpAvgGen.lean` (1587 lines), `RBM3D.lean` (+1 import line after the last import), `RBM3D/Test/Axioms.lean` (+3 owed lines, 1 text edit). `RBM3D/Probe/T2502Pins.lean` stays on the branch, is not imported and is not a row-c output.
- Sections (starts above): §1 71 lines (nine public defs, text-identical to the check), §2 76 (fine/block transport), §3 399 (Stein at `H₀ + √u X`: `ExpAvgGen_stein_trace` `:348`, resolvent identity `:393`, `ExpAvgGen_sid1` `:415`, `ExpAvgGen_selfcons_fixed` `:470`), §4 167 (Ward, `‖M^(++)‖_∞ ≤ 1`, invertibility, solve, `M` entry bound), §5 163 (carrier: `L`, `t` as functions of the slice, bounds, `ExpAvgGen_selfcons` `:824`), §6 153 (`ExpAvgGen_core_abs` `:953`, `ExpAvgGen_core` `:1042`), §7 280 (moment bridge, floor, envelope, `ExpAvgGen_step` `:1232`, `mom1`, `mom2`), §8 73 (16a `:1365`, 16b `:1407`, 16c `:1416`), §9 108 (band), §10 47 (instances). Total 1587 (the sections above plus 50 header lines) against the bottom-up central 1260 (W1 part 440): +327; the two largest sections are §3 (399) and §7 (280).
- Route of 16a: for each `n` and `u = u_n`, `x_a = 𝔼 𝓛_a - m` satisfies `x = u (M^(++) S) x + R` (`ExpAvgGen_selfcons`, from `ExpAvgGen_stein_trace` with `P = M`, `Q = E_a`); `1 - u M^(++) S` is invertible and its inverse is `Step2Gen_uKer C n + + 0 u` (`ExpAvgGen_core`), so `|x_a| ≤ Cs max |R|` by W1 (ii) at `s = 0`; `|R_a| ≤ u α Σ_p β_ap` by Cauchy-Schwarz with `α = N^ε B` (second moments of `𝓛 - m` from `LWAvgLawgL`, `ExpAvgGen_mom1`) and `β_ap = N^ε (‖M^B_ap‖ + N⁻²) B` (second moments of `t - M^(++)` from W1 (iii), `ExpAvgGen_mom2`); `Σ_p β_ap ≤ N^ε (CM + 1) B` by W1 (iv) and `L^d ≤ N`. The `N⁻²` keeps the control positive for the bridge. `Cs (CM + 1) ≤ N^ε` eventually and `ε = τ/3` give `N^τ B²`. `STLKgL` is unused, as in the band.
- Charge `-`: `ExpAvgGen_L_false` (`:1215`, `G(-) = G(+)*` for the Hermitian `H₀ + √u X`) and `integral_conj`.
- 16b is 16a with W1 (iii) from row 15; 16c is `st6_expAvgU_of_ping` (`Step6KitGen:338`) with `hAvg` replaced by `STImproveCoregL` and the per-flow premise `hiii`.
- Band (§9): `ExpAvgGen_band_W1fam` (`Cs` from `ekSameRow_holds`, `CM = 1` from `‖mE‖ = 1`, `H₀ = 0`, `g' = sz.lam`), `ExpAvgGen_band_W1iiiOfLW` (`t_(aq) - M^(++)_(aq) = δ_(aq) m (ḡ_a - m)`, as the probe `T2502c_band_collapse`), `stImproveExpAver_of_gL` (band `stImproveExpAver_holds` through 16b, `:1534`).
- Stop rules of the ticket: file under 1750; no `BA/*` or `Chain/Step2Kern` import; no band file and no merged `Chain/*` file in the diff (the root import, the registry lines and the probe are the allowed exceptions); no kernel, class or comparison defined; no `STGridRepNgL`; no `sorry`. One point is flagged, not decided: the premise `hFF` beyond the shapes of `T2502_Target16a/b` ((a′) 3, (d) 1; no counterexample to the literal shapes was compiled).

## (c) Verified Mathlib names
- `Matrix.submatrix_mul_equiv`, `Matrix.submatrix_one_equiv`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.mul_diagonal`, `Matrix.trace_mul_comm`, `Matrix.conjTranspose_mul`, `Matrix.trace_conjTranspose`, `Matrix.mulVec_mulVec`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.IsHermitian.add`, `.submatrix`: used and compiled.
- `det_ne_zero_of_sum_row_lt_diag` (root namespace, `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:63`); `mul_eq_one_comm` (root, `Algebra/Group/Monoid.lean:54`). Absent: `Matrix.det_ne_zero_of_sum_row_lt_diag`, `Matrix.mul_eq_one_comm`.
- `Finset.sum_fiberwise`, `Finset.sum_erase_eq_sub`, `Complex.sub_conj`, `Complex.im_le_norm` (`Analysis/Complex/Norm.lean:192`), `Complex.conj_mul'`, `Complex.im_ofReal_mul`, `Complex.star_def`, `integral_conj`, `integral_finsetSum`, `integral_mono_of_nonneg`, `norm_integral_le_integral_norm`, `Integrable.of_bound`, `integrable_finsetSum`, `continuous_finsetSum`, `Real.rpow_add_one`, `tendsto_natCast_atTop_atTop`, `Filter.Tendsto.eventually_ge_atTop`, tactic `module`. Absent or deprecated: `integrable_finset_sum`, `continuous_finset_sum` (deprecated), `Complex.le_abs_im`, `measureReal_univ_eq_one`, unqualified `star_def`.

## (d) Open issues and paper-delta candidates
1. **Shape of 16a/16b.** The theorems carry the extra premise `hFF : Step5CasesGen_FlowFacts d Flow mk T0` (ticket table row 3), which the binding shapes `T2502_Target16a/16b` do not list; the auditor-style examples above apply the theorems to it. Needed by the proof (a′ 3); the dispatcher may fold row 3 into the shapes by an amend. Row-a wrappers already take `hFF` (`Step6KitGen:677`).
2. **Registry.** The scan reports one unregistered premise, `ExpAvgGen_W1iii`, now in `owedProps`. `ExpAvgGen_W1fam` and `ExpAvgGen_W1iiiOfLW` are registered as the Amend 1 text asks, although the scan does not report them (by the rule of `scanPremises`, a theorem whose conclusion head is the premise counts as a proof: `ExpAvgGen_band_*` conclude them at the band tuple; `certificates` is not edited): the final `#assert_rbm_axioms` output lists them, and `STImproveExpAvergL` (now concluded by 16b), among the registered premises that carry nothing yet (above). The block choice is the auditor's.
3. **Row 15 is band-only** (no BA discharge, by design); BA goes through 16a and 16c with W1 (iii) per time (V1-BA, TL1 `BATwistAvgLaw`).
4. **Size.** 1587 lines against the 1260 bottom-up figure (stop 1750); `ExpAvgGen2` is not needed.
5. **Paper delta `T2502ca` = D727, confirmed.** `paper/tex/6_Step6_two_loop.tex:10-21`: the lemma holds "in the setting of lem:main_ind" given `(Gt_avgbound_flow)`, `(Eq:L-KGt-flow)` uniformly in `u ∈ [s,t]`; the proof is "the same as [YY_25, Lemma 5.15]". Lean differs in three statements: (i) a matrix `M` (W1 (i), `M = (H₀ - E - m)⁻¹` with block average `m`) instead of the scalar `m I`; (ii) the remainder is controlled by the new premises W1 (iii), (iv) (`ExpAvgGen_W1iii`, `ExpAvgGen_W1iv`) and the kernel bound W1 (ii) (eventual in `n`); (iii) the statement is per time `u`, the uniform-in-`u` form is 16c. The scalar case is the band instance (`ExpAvgGen_band_W1fam`, `ExpAvgGen_band_W1iiiOfLW`).
