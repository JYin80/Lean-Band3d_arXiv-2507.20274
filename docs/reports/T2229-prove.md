Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 00:06:05 UTC 2026

Script: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2229/pre.py` (Python/numpy, no Lean); full output in `out.txt` there (32 lines).
Targets restated: pin `STExpWardII d` (`Step6Pins.lean:376`): for `σ₁≠σ₂`, `‖f_u - Q^{({1,2})}f_u‖ ≤ N^τ B_u³` eventually, uniformly in `u∈[s,t]`, `a`, given `STExpAvgU` (`‖𝔼𝓛^{(1)}_{u,b,x} - m_b‖ ≤ N^τ B_u²`), with `f = STExpErr`, `B_u = Bctl n u`. Route: `f - Q^{(1)}f = Im α(a₂)/(Nη)`, `f - Q^{(2)}f = Im α(a₁)/(Nη)` (`α(x)=𝔼𝓛^{(1)}_{u,+,x}-m`), `f - Q^{(1)}Q^{(2)}f = (f-Q^{(1)}f) + Q^{(1)}(f-Q^{(2)}f)`, `‖Q^{(1)}‖_{∞→∞} ≤ 2`, so `‖f-Q^{({1,2})}f‖ ≤ 3 max_x|Im α(x)|/(Nη)`; `(Nη_u)⁻¹ = (Im m)⁻¹ W^{-d}(L^d(1-u))⁻¹ ≤ (Im m)⁻¹ B_u`; `Im m ≥ √(2κ)/2`.

### (i) Exponent table (all numbers from `pre.py` unless a file line is cited)
| quantity | value | constraint | slack |
|---|---|---|---|
| `𝔠_d` (pin, `Step6Pins.lean:111-114`: `0 < 𝔠d ≤ 1/100`) | `1/100` | only the bounds `0<𝔠d≤1/100`; the proof uses no `𝔠d` (premise `STConStInd sz 𝔠d s t` unused) | none needed |
| `E_n` along the flow | `\|E_n\| ≤ 2-κ` (`st6_flowE_le`, `Step6Kit.lean:535`); at `zB`: `lemE = 0.499984` | `\|E\|<2` for `stWardII_identity`, `etaT_pos` | `2-κ-\|E\| = 1.4` at `κ=1/10` |
| time `u` | `0 ≤ s ≤ u ≤ t ≤ lemT z < 1` (`st5_t_lt_one`, `Step5Kit.lean:192`); at `zB`: `lemT = 0.983992`, `t = 31/32 = 0.96875` | `0 ≤ u < 1`, `η_u=(1-u)Im m>0` | `1-lemT = 0.016`; `lemT - t = 0.0152` |
| `Im m(E)` | `Im m ≥ √(2κ)/2` (`st6_mE_im_ge`, `Step6Kit.lean:544`); `κ=1/10`: `0.2236`; `Im m(0)=1`, `Im m(lemE zB)=0.9682` | `(Im m)⁻¹ ≤ 2/√(2κ)` | bulk, `κ>0` fixed |
| `(Nη_u)⁻¹ ≤ (Im m)⁻¹ B_u` | exact: `(Nη)⁻¹=(Im m)⁻¹W^{-d}(L^d(1-u))⁻¹`; `B_u = W^{-d}[(λ²+\|1-u\|)⁻¹+(L^d\|1-u\|)⁻¹]` (`Bctl`/`Bparam`, `Params.lean:36`, `Sizes.lean:214`) | the first summand of `B` is `≥ 0` | `szB`, `n=0`, `E=0`: ratio `(Nη)⁻¹/B` = `0.2099` (`u=15/16`), `0.3402` (`u=31/32`); ratio is E- and n-independent (table below); true for every `d`, regime, `λ≥0` |
| number of slots / constant `3` | `‖f-Q^{(1)}Q^{(2)}f‖ ≤ ‖f-Q^{(1)}f‖ + ‖Q^{(1)}(f-Q^{(2)}f)‖ ≤ M + 2M` | `‖Q^{(1)}‖_{∞→∞} = 2(1-L^{-d}) ≤ 2` (`norm_zeroModeOp_le`/`norm_zeroModeSet_le`, `ZeroModeCalc.lean:124,163`) | `d=3,L=3`: `1.9259 ≤ 2`; numeric `max\|f-Q^{(12)}f\| ≤ 3M` with slack factor `1.4`-`1.6` (lines below) |
| premise exponent | `STExpAvgU` at `τ/2` (`st6_prec_det_iff`, `Step6Kit.lean:81`, deterministic `Prec`): `\|α\| ≤ N^{τ/2}B_u²` | each `τ>0`, eventually in `n`, uniform in `(u,x)` | `B·B² = B³` exactly, no loss |
| threshold `N^{τ/2} ≥ 6/√(2κ)` | `6/√(2κ) = 13.4164` (`κ=1/10`) so `(6/√(2κ))N^{τ/2} ≤ N^τ` | eventual, `SizeTendsto` (`tendsto_size`) | `τ=1`: `N≥180` (szB `n≥0`); `τ=1/2`: `N≥3.24e4` (`n≥4`); `τ=1/10`: `N≥3.57e22` (`n≥8232180`); an `∀ᶠ`, not a witness of any instance |
| regime `STReg5II` (`Step5Pins.lean:48`) | `λ²/L^d ≤ 1-t ≤ 1-s ≤ λ²/L²`; `szB`: `1/64 ≤ 1/32 ≤ 1/16 ≤ 1/16` | not used by the proof (bound holds for all `t<1`) | `1-s ≤ λ²/L²` is tight (equality) |
| `L,W` relation, `λ` | `N=(WL)^d` only; `λ=0` harmless (`B ≥ W^{-d}(L^d(1-u))⁻¹`) | none | — |
| integrability (`k+1=1,2`) | `‖𝓛‖ ≤ (η_u⁻¹)^{k+1}` (`norm_Lloop_le`, `GLoopFlow.lean:700`, `u<1`, `\|E\|<2`), measurable (`walk_measurable_Lloop`) | finite sums under `∫` | `η_u⁻¹ = 16` at `E=0,u=15/16` |
| `KLK_rotate` (`KLUnique.lean:604`) | hyp: `3≤L`, `1≤W`, `\|E\|<2`, `u∈[0,1)`, `σ.length=a.length` | list form `⟨[σ₁,σ₂],[a₁,a₂]⟩ ↦ ⟨[σ₂,σ₁],[a₂,a₁]⟩` (`s::σ ↦ σ++[s]`) | `L=4`, `W≥4` |

### (ii) One concrete nondegenerate instance
Data: `d=3`, `szB` (`L=4`, `W_n=n+4`, `λ=1`; `Step34Pins.lean:710`), `n=0` (`W=4`, `N=4096`), flow `zB = 1/2 + i/64`, `κ=1/10`, `ε=1/10`; `(s,t) = (15/16, 31/32)`; `u ∈ {15/16, 31/32}`; `E=0` (`m=i`, `Im m=1`) and `E=lemE zB`; `σ=(+,-)`, `a=(0,0)`. All hypotheses: `|E|<2`, `0≤u<1`, `σ₁≠σ₂`, `STReg5II` (above), `t ≤ lemT zB` (`0.96875 ≤ 0.983992`), `STFlow`: `N^{-1+ε} = 5.6e-4 ≤ Im zB = 1/64`, `|lemE zB| = 0.499984 ≤ 1.9`.
Command and output (excerpts of `out.txt`; same script, no edits):
```
$ python3 pre.py
zB: lemE=0.499984 |E|<=2-k(k=0.1): True  lemT=0.983992  31/32=0.968750  lemT<1: True  Im m(Ef)=0.9682 >= sqrt(2k)/2=0.2236
N^(-1+eps) <= Im zB at n=0 (eps=1/10): 5.609e-04 <= 1.562e-02
regime (ii) lam^2/L^d <= 1-t <= 1-s <= lam^2/L^2 : 0.015625 <= 0.03125 <= 0.0625 <= 0.0625
E        n   u         N        (N eta)^-1   (Im m)^-1 B  B            ratio
0.0000   0   0.93750   4096     3.9062e-03   1.8612e-02   1.8612e-02   0.210
0.0000   0   0.96875   4096     7.8125e-03   2.2964e-02   2.2964e-02   0.340
0.0000   100 0.93750   71991296 2.2225e-07   1.0590e-06   1.0590e-06   0.210
0.5000   0   0.93750   4096     4.0343e-03   1.9222e-02   1.8612e-02   0.210
0.5000   0   0.96875   4096     8.0687e-03   2.3717e-02   2.2964e-02   0.340
exact n=0,E=0,u=15/16: (N eta)^-1=1/256=3.90625e-03, B=81/4352=1.86121e-02, ratio=0.2099
exact n=0,E=0,u=31/32: (N eta)^-1=1/128=7.81250e-03, B=97/4224=2.29640e-02, ratio=0.3402
6/sqrt(2k)=13.4164
tau=1    need N>=1.8000e+02  i.e. szB n>=0 (N=(4(n+4))^3)
tau=0.5  need N>=3.2400e+04  i.e. szB n>=4 (N=(4(n+4))^3)
tau=0.1  need N>=3.5705e+22  i.e. szB n>=8232180 (N=(4(n+4))^3)
d=3 L=3 W=1 N= 27 E=0.0 u=0.9375 sigma=(+,-) slot0 resid=2.2e-15 slot1 resid=2.6e-15 decomp resid=9.4e-16 paper-form resid=3.8e-15  max|f-Q12 f|=1.587e+00 <= 3M=2.458e+00 : True
d=3 L=3 W=1 N= 27 E=0.0 u=0.9375 sigma=(-,+) slot0 resid=2.6e-15 slot1 resid=2.2e-15 decomp resid=1.0e-15 paper-form resid=3.7e-15  max|f-Q12 f|=1.587e+00 <= 3M=2.458e+00 : True
d=3 L=3 W=1 N= 27 E=0.3 u=0.9688 sigma=(+,-) slot0 resid=6.6e-15 slot1 resid=6.3e-15 decomp resid=3.6e-15 paper-form resid=1.0e-14  max|f-Q12 f|=3.123e+00 <= 3M=4.427e+00 : True
d=3 L=3 W=2 N=216 E=0.0 u=0.9375 sigma=(+,-) slot0 resid=2.2e-16 slot1 resid=2.2e-16 decomp resid=2.2e-16 paper-form resid=3.9e-16  max|f-Q12 f|=3.111e-02 <= 3M=4.786e-02 : True
d=3 L=3 W=2 N=216 E=0.3 u=0.9688 sigma=(-,+) slot0 resid=6.9e-16 slot1 resid=8.2e-16 decomp resid=3.3e-16 paper-form resid=1.6e-15  max|f-Q12 f|=8.013e-02 <= 3M=1.297e-01 : True
||Q^(1)||_{inf->inf}=2(1-L^-d)=1.9259 <= 2 (d=3,L=3)
rotation L_{(+,-),(a1,a2)} - L_{(-,+),(a2,a1)} max resid W=1: 1.7e-16 ; W=2: 2.9e-17
```
Meaning of the identity rows (script, one random Hermitian `H` per row, `d=3`, `L=3`, `W∈{1,2}`, `G_±=(H-z_u)⁻¹,(H-\bar z_u)⁻¹`, `𝓛^{(2)}=tr(G_{σ₁}E_{a₁}G_{σ₂}E_{a₂})`, `E_a=W^{-d}1_{[a]}`, model `𝒦^{(2)}=(W^d(1-u))⁻¹δ_{a₁a₂}`, `𝒦^{(1)}=m_σ`, both satisfy `(WI_calK)`): `slot0` = `max|(f-Q^{(1)}f)(a) - Im α(a₂)/(Nη)|` (target 2), `slot1` = same with `Q^{(2)}`, `α(a₁)` (target 3, the rotated slot), `decomp` = `max|(f-Q^{(1)}Q^{(2)}f) - [(f-Q^{(1)}f)+Q^{(1)}(f-Q^{(2)}f)]|` (target 4 identity), `paper-form` = residual against `Im[tr(G̃(E_{a₁}+E_{a₂})) - N⁻¹tr G̃]/(Nη)` of `6:137-141`, `3M = 3 max_x|Im α(x)|/(Nη)`. All residuals `≤ 1.1e-14` while the quantities are `3e-2`-`3`. The last row checks the rotation `𝓛_{(σ₁σ₂),(a₁a₂)} = 𝓛_{(σ₂σ₁),(a₂a₁)}` (trace cyclicity) used for the second slot.
External hypotheses: the only non-deterministic hypothesis of the pin is `STExpAvgU` (premise of the conclusion, `Step6Pins.lean:198`, `Step6Kit.lean:557` builds it from `STImproveExpAver`); the proof uses it only as the deterministic statement `\|α_n(u,x)\| ≤ N^{τ/2}B_u²` eventually for each `τ`; concrete limit computation: the conclusion's threshold is `N^{τ/2} ≥ 6/√(2κ)` (table: `N≥180, 3.24e4, 3.57e22` for `τ=1,1/2,1/10`), finite for every `τ>0`, `κ=1/10`, `N=(4(n+4))^3 → ∞`. The deterministic one-size statements (targets 2-6) are at `n=0`, no threshold.

Checklist (ticket §29/§45 O2 items, math): (1) time `0≤s≤u≤t≤lemT<1`: table row 3. (2) regime (ii) not used: table row 9. (3) no `L`-`W` relation: `N=W^dL^d`. (4) hypotheses `∀n`, conclusion `Prec` of a deterministic family: `st6_prec_det_iff`. (5) uniformity in `u`: inherited from `STExpAvgU` (index `TimeIcc s t n × Bool × Zd`), no grid lift. (6) `λ=0` harmless. (7) scale `N`. Consumer (`Step6Kit.lean:865-870`, `Step6Pins.lean:613-616`): `STExpWardII d` is the premise `hWd` and `inst_expWardII` takes `STExpWardII 3`; statement-compatible.

### Verdicts
- Targets 1-4 (bridges, slots 0/1, two-slot bound): PASS (identity verified samplewise, residual `≤ 1.1e-14`; rotation exact; `Q^{(1)}` norm `≤ 2`; `toList univ` order irrelevant since the bound `M+2M` holds in either order).
- Targets 5-6 (`(Nη)⁻¹ ≤ (Im m)⁻¹B`, one-size bound `3(Im m)⁻¹B max|α|`): PASS (exact inequality, ratio `0.21`-`0.34`).
- Target 7 (`STExpWardIIConcl_of_avgU`, `stExpWardII_holds`): PASS (constant `6/√(2κ)` absorbed eventually; exponents close with `B·B²=B³`, no loss).
- Target 8 (instances at `szB`, `zB`, `κ=1/10`, `(15/16,31/32)`, `n=0`): PASS (all deterministic hypotheses hold at the numbers above).
Overall verdict: PASS.

## (b) Script output - Tue Oct  6 00:23:02 UTC 2026
Branch `t/T2229`, commit `e259f2e` (author `Jun Yin <321276894+JYin80@users.noreply.github.com>`); files: `RBM3D/Induction/ExpWardII.lean` (517 lines, new) and `RBM3D/Test/Axioms.lean` (one line deleted). Scratch scripts and outputs: scratchpad `T2229/`.
### Build and hygiene (module build at 00:19:33 UTC on the committed content)
```
$ lake build RBM3D.Induction.ExpWardII 2>&1 | grep -v '^info:\|^trace\|^ℹ' | tail -1
Build completed successfully (3859 jobs).
$ lake env lean RBM3D/Induction/ExpWardII.lean; echo exit=$?     # no linter warning from the file
exit=0 (0 output lines)
$ grep -c 'sorry\|admit\|native_decide' RBM3D/Induction/ExpWardII.lean ; grep -c '^axiom' RBM3D/Induction/ExpWardII.lean
0
0
```
### `#print axioms` of every public declaration (`lake env lean axioms.lean`)
```
RBM.Gauss.Sizes.expWII_slot0: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expWII_slot1: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expWII_two_slot_bound: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expWII_inv_Neta_le: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.expWII_det_bound: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.STExpWardIIConcl_of_avgU: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stExpWardII_holds: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWardII_holds: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_skeleton6II_Wd: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_concl: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_inv_Neta_le: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_slot0: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_slot1: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_det_bound: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step6Inst.inst_expWII_two_slot_bound: [propext, Classical.choice, Quot.sound]
```
### Target statements, extracted from the file by script (`extract.py`; `sz : Sizes d`, `{d : ℕ}` come from the section `variable`, `{d L : ℕ} [NeZero L]` for `expWII_two_slot_bound`)
```
theorem expWII_slot0 (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)   -- ExpWardII.lean:182
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a - zeroModeOp d (sz.L n) 0 (fun b => STExpErr sz n E u σ b) a =
      ((((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a 1) ω ∂(sz.seqP)) -
          mSigma E true).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (etaT E u : ℂ)) :=
theorem expWII_slot1 (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)   -- ExpWardII.lean:223
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STExpErr sz n E u σ a - zeroModeOp d (sz.L n) 1 (fun b => STExpErr sz n E u σ b) a =
      ((((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a 0) ω ∂(sz.seqP)) -
          mSigma E true).im : ℝ) : ℂ) /
        (((sz.size n : ℕ) : ℂ) * (etaT E u : ℂ)) :=
theorem expWII_two_slot_bound (T : (Fin 2 → Zd d L) → ℂ) {M : ℝ}   -- ExpWardII.lean:251
    (h0 : ∀ b, ‖T b - RBM.zeroModeOp d L 0 T b‖ ≤ M) (h1 : ∀ b, ‖T b - RBM.zeroModeOp d L 1 T b‖ ≤ M)
    (a : Fin 2 → Zd d L) :
    ‖T a - RBM.zeroModeSet d L (Finset.univ : Finset (Fin 2)) T a‖ ≤ 3 * M :=
theorem expWII_inv_Neta_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1) :   -- ExpWardII.lean:303
    (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤ ((mE E).im)⁻¹ * sz.Bctl n u :=
theorem expWII_det_bound (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)   -- ExpWardII.lean:329
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) {M : ℝ}
    (hM : ∀ x : Zd d (sz.L n),
      ‖(∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => x) ω ∂(sz.seqP)) - mSigma E true‖ ≤ M)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STExpErr sz n E u σ a -
        zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (fun b => STExpErr sz n E u σ b) a‖ ≤
      3 * (M * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹) :=
theorem STExpWardIIConcl_of_avgU (hsz : sz.SizeTendsto) {κ : ℝ} (hκ : 0 < κ) {E s t : ℕ → ℝ}   -- ExpWardII.lean:364
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (_hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hAvg : STExpAvgU sz E s t) : STExpWardIIConcl sz E s t :=
theorem stExpWardII_holds (d : ℕ) : STExpWardII d :=   -- ExpWardII.lean:419
```
### Compiled nonempty instances (same file, namespace `RBM.Gauss.Step6Inst`; statements extracted by script)
```
theorem inst_expWardII_holds :   -- ExpWardII.lean:439
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
theorem inst_skeleton6II_Wd (hLW : LWtermEXP 3) (hInt : STExpIntII 3) :   -- ExpWardII.lean:446
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
theorem inst_expWII_concl :   -- ExpWardII.lean:453
    STExpAvgU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
theorem inst_expWII_inv_Neta_le :   -- ExpWardII.lean:461
    (((szB.size 0 : ℕ) : ℝ) * RBM.Gauss.etaT 0 (15 / 16))⁻¹ ≤ ((RBM.mE 0).im)⁻¹ * szB.Bctl 0 (15 / 16) :=
theorem inst_expWII_slot0 :   -- ExpWardII.lean:466
    szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeOp 3 (szB.L 0) 0 (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0] =
      ((((∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
          RBM.mSigma 0 true).im : ℝ) : ℂ) /
        (((szB.size 0 : ℕ) : ℂ) * (RBM.Gauss.etaT 0 (15 / 16) : ℂ)) :=
theorem inst_expWII_slot1 :   -- ExpWardII.lean:475
    szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeOp 3 (szB.L 0) 1 (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0] =
      ((((∫ ω, szB.Lloop 0 0 (15 / 16) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
          RBM.mSigma 0 true).im : ℝ) : ℂ) /
        (((szB.size 0 : ℕ) : ℂ) * (RBM.Gauss.etaT 0 (15 / 16) : ℂ)) :=
theorem inst_expWII_det_bound :   -- ExpWardII.lean:485
    ‖szB.STExpErr 0 0 (15 / 16) ![true, false] ![0, 0] -
        RBM.zeroModeSet 3 (szB.L 0) (Finset.univ : Finset (Fin 2))
          (fun b => szB.STExpErr 0 0 (15 / 16) ![true, false] b) ![0, 0]‖ ≤
      3 * (((RBM.Gauss.etaT 0 (15 / 16))⁻¹ + 1) *
        (((szB.size 0 : ℕ) : ℝ) * RBM.Gauss.etaT 0 (15 / 16))⁻¹) :=
theorem inst_expWII_two_slot_bound (a : Fin 2 → Zd 3 4) :   -- ExpWardII.lean:506
    ‖(1 : ℂ) - RBM.zeroModeSet 3 4 (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℂ)) a‖ ≤ 3 * 1 :=
```
Open hypotheses: `inst_expWardII_holds`, `inst_expWII_concl` keep `STExpAvgU` and (inside `InstIng6Concl`) the stochastic premises of `STIngR6`; `inst_skeleton6II_Wd` keeps `LWtermEXP 3`, `STExpIntII 3` (other gates' pins). Deterministic hypotheses (`|0| < 2`, `0 ≤ 15/16`, `15/16 < 1`, `![true,false] 0 ≠ ![true,false] 1`) are discharged by `norm_num`/`decide`; `inst_expWII_det_bound` also discharges the one-point bound with `M = η⁻¹ + 1` (`norm_Lloop_le`, `norm_mSigma`); `inst_expWII_two_slot_bound` uses `T = 1`, `d = 3`, `L = 4` (`Q^{(i)} T = 0`).
### Check-file equality (`check_eq.lean`: check-file imports + `import RBM3D.Induction.ExpWardII` + sections 1-2 + `example : T2229Check.X := @X` per `def X` of section 2 + the pin example + one `example : <statement> := @Step6Inst.<name>` per section-3 instance)
```
$ lake env lean check_eq.lean > check_eq.out 2>&1; echo exit=$?     # 00:16:31 UTC
exit=0 (error lines: 0)
$ grep -c '^example' check_eq.lean
13   (7 section-2 examples + 1 pin example + 5 section-3 instances)
```
Section 2 of the check file has 7 `def`s (the ticket text says 8); all 7, the pin example and the 5 section-3 instances compile.
### Name-clash grep (`clash2.sh`)
```
worktree (RBM3D/ + RBM3D.lean), hits outside ExpWardII.lean, fixed-string grep -rn -F:
  expWII_: 0
  STExpWardIIConcl_of_avgU: 0
  stExpWardII_holds: 0
  inst_expWardII_holds: 0
  inst_skeleton6II_Wd: 0
  inst_expWII_: 0
  Induction.ExpWardII: 0
  ExpWardII.lean: 0
main worktree (main 6b4fe24), grep -rlE of all new names in RBM3D/, RBM3D.lean, docs/queue/CONTROL.md:        0 files
```
### Registry pre-check (`precheck.lean` = `import RBM3D`, `import RBM3D.Induction.ExpWardII`, `#assert_rbm_axioms`; `lake env lean` exit 0; baseline = same file against the branch-base `Axioms.lean`)
```
base : axiom audit: 6718 theorems, 2268 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
base : premises found by scanning: 123 (borrowed 1, owed 89, structural 27, refuted 6).
base : registry: 2 borrowed + 141 owed + 84 structural + 7 refuted; 111 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
base : occurrences of the name `STExpWardII` (not `...Concl`) in the output: 2
after: axiom audit: 6718 theorems, 2268 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after: premises found by scanning: 123 (borrowed 1, owed 89, structural 27, refuted 6).
after: registry: 2 borrowed + 140 owed + 84 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
after: occurrences of the name `STExpWardII` (not `...Concl`) in the output: 0
```
After the change `STExpWardII` is absent from the owed ledger and from the "carry nothing yet" list; owed 141 -> 140; scanned premises 123 both; no unregistered premise; the structural `STExpWardIIConcl` entry stays (`Axioms.lean:325` -> `:324`).
### Full library build (temporary uncommitted `import RBM3D.Induction.ExpWardII` after the last import of `RBM3D.lean`, removed afterwards; `git status --short` empty)
```
$ lake build     # started 00:20:32 UTC
info: RBM3D.lean:274:0: axiom audit: 6718 theorems, 2268 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 140 owed + 84 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4034 jobs).
```
### Diffs
```
$ git diff --stat main...t/T2229
RBM3D/Induction/ExpWardII.lean | 517 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   1 -
 2 files changed, 517 insertions(+), 1 deletion(-)
$ git diff dc2d99b HEAD -- RBM3D/Induction/Step6Pins.lean | wc -l ; git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l
0
0
$ git diff -U0 dc2d99b HEAD -- RBM3D/Test/Axioms.lean | tail -2 | cut -c1-110
@@ -235 +234,0 @@ def owedProps : List Name :=
-   `RBM.Gauss.Sizes.STExpWardII, -- `6:137-141` Ward term, regime (ii): S6-12; S6-01 (T2204, DECISIONS §67: o
```
### Ports (copies from merged RBM3D files; no RBM1D/RBM2D source, so no RBM1D/RBM2D diff-stat)
```
$ git log -1 --format=%h dc2d99b -- <file>:  WardII.lean 8ec98a6 ; ExpIniI.lean f2766db ; Step6Pins.lean cda3bb2 ; Step6Kit.lean 9e0d6a7
$ grep -n 'private theorem' of the copied sources (facts.out):
WardII.lean:31:wardII_loopL_rot (s t : Bool) (b a : Zd d L) :
WardII.lean:105:wardII_STLM_eq (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n
WardII.lean:121:wardII_STKloop_eq (n : ℕ) (E u : ℝ)
WardII.lean:126:wardII_STKloop_eq1 (n : ℕ) (E u : ℝ) (s : Bool) (a : Zd d (
WardII.lean:131:wardII_zeroMode (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ) (
ExpIniI.lean:176:expIniI_integrable_L (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu 
ExpIniI.lean:183:expIniI_expErr_eq (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u
```
### Narrative
- Route as implemented. `expWII_slot0` integrates the merged samplewise `stWardII_identity` (`WardII.lean:143`) at `H = seqHflow n u ω`: `expWII_zeroModeOp_eq0` gives `T a - Q^{(1)}T a = L^{-d} Σ_c T(c,a₂)`, then `integral_finsetSum`, `integral_const_mul`, `integral_div`, `integral_ofReal`, `integral_im` and `expWII_avg_eq` (`KLK_one`, `isProbabilityMeasure_seqP`) turn it into `Im(𝔼𝓛^{(1)}_{u,+,a₂} - m)/(Nη_u)`.
- `expWII_slot1`: the private rotation `expWII_STLKM_swap` is `expWII_STLM_swap` (trace cyclicity, copy of `wardII_loopL_rot`) plus `expWII_STKloop_swap` (`KLK_rotate`); `expWII_STExpErr_swap` carries it through `∫`; the slot-1 average is `expWII_zeroModeOp_eq1`, and the result is `expWII_slot0` at `(![σ 1, σ 0], ![a 1, a 0])` (`![σ 1, σ 0]` is again mixed).
- `expWII_two_slot_bound`: only `Finset.length_toList` (`= 2`) and `List.length_eq_two` are needed (`toList univ = [i, j]`, each slot bound holds for either index by `fin_cases`); `Finset.nodup_toList` is not used. Linearity of `Q^{(i)}` over `-` is proved inline.
- `expWII_inv_Neta_le`: `(Nη_u)⁻¹ = (Im m)⁻¹ (N(1-u))⁻¹` and `(N(1-u))⁻¹ = W^{-d}(L^d(1-u))⁻¹ ≤ Bctl` (the other summand of `Bparam` is `≥ 0`); every `d`, regime and `λ`; needs only `|E| < 2`, `u < 1`.
- `STExpWardIIConcl_of_avgU`: `st6_prec_det_iff` is applied twice (premise `STExpAvgU` at `τ/2`, conclusion at `τ`); `tendsto_rpow_atTop` with `tendsto_size` gives eventually `3·(2/√(2κ)) ≤ N^{τ/2}`; `st6_mE_im_ge` gives `(Im m)⁻¹ ≤ 2/√(2κ)`; `N^{τ/2}·N^{τ/2} = N^τ` by `Real.rpow_add`. No regime, no flow, no grid lift (DECISIONS §64 (4): both sides deterministic).
- `stExpWardII_holds d`: `𝔠_d = 1/100`; uses `hflow.1.2.2.1`, `st6_flowE_le`, `hs0`, `hst` (as `≤`), `st5_t_lt_one` and the conclusion premise `STExpAvgU`; unused: `hd`, `ε`, `𝔡` with their positivity hypotheses, and the premises `hR` ... `hS5` of `STIngR6`.
- Differences from the ticket text (none changes a pin or a target): (i) the check file has 7 `def`s in section 2, not 8; (ii) `Axioms.lean` line was `:235` on the branch base `dc2d99b` (located by its text), `:236` in the ticket; (iii) three instances beyond the ticket's five (`inst_expWII_slot1`, `inst_expWII_det_bound`, `inst_expWII_two_slot_bound`); (iv) the unused hypothesis of `STExpWardIIConcl_of_avgU` is named `_hst`; (v) the file imports the seven RBM3D modules of the check file and no Mathlib module directly.
- No hypothesis added, no pinned or frozen signature changed (`Step6Pins.lean` diff: 0 lines), no primed successor, no `T2229a` for a missing hypothesis: every step of the ticket's route compiled as stated. `STExpIntII` (`Axioms.lean:234`) is untouched.

## (c) Verified Mathlib names (module of the declaration, `Environment.getModuleIdxFor?` script `names.lean`)
```
Mathlib.MeasureTheory.Integral.Bochner: MeasureTheory.integral_finsetSum, MeasureTheory.integral_sub, MeasureTheory.integral_const_mul, MeasureTheory.integral_div, integral_ofReal, integral_im, MeasureTheory.integral_const, MeasureTheory.integral_congr_ae, MeasureTheory.norm_integral_le_of_norm_le_const
Mathlib.MeasureTheory.Integral.IntegrableOn: MeasureTheory.Integrable.of_bound
Mathlib.MeasureTheory.Function.L1Space: MeasureTheory.Integrable.sub, MeasureTheory.integrable_const
Mathlib.Data.Finset.Card: Finset.length_toList
Mathlib.Data.List.Basic: List.length_eq_two
Mathlib.Analysis.SpecialFunctions.Pow: tendsto_rpow_atTop, Real.rpow_add
Mathlib.Order.Filter.AtTopBot: Filter.Tendsto.eventually_ge_atTop
Mathlib.Analysis.Normed.Group: pi_norm_le_iff_of_nonneg, norm_le_pi_norm, Real.norm_of_nonneg, norm_sub_le, norm_add_le, Real.norm_eq_abs
Mathlib.Algebra.Order.GroupWithZero: inv_anti₀
Mathlib.Analysis.Complex.Norm: Complex.abs_im_le_norm, Complex.norm_real, Complex.norm_natCast
Mathlib.LinearAlgebra.Matrix.Trace: Matrix.trace_mul_comm
Mathlib.Data.Finset.Insert: Finset.toList_singleton
Mathlib.Analysis.Real.Sqrt: Real.sqrt_pos
Mathlib.Algebra.Group.Basic: inv_div
Mathlib.Data.Finset.Dedup: Finset.nodup_toList
```
All 32 names exist (names checked absent: none; `Finset.nodup_toList` exists but is unused).

## (d) Open issues and paper-delta candidates
- `T2229a` (ticket (a), `6:141`): `(W^{-d}B_{t,0})²·(Nη_t)⁻¹ ≲ (W^{-d}B_{t,0})³` holds in every regime: `(N(1-t))⁻¹ ≤ W^{-d}B_{t,0}` always (`expWII_inv_Neta_le`), the factor `(Im m)⁻¹ ≤ 2/√(2κ)` is the bulk constant, uniformly in `t ∈ [s,t]`; the regime is not used.
- `T2229b` (ticket (b), `6:138-140`): Lean's decomposition is the sum of two one-slot Ward identities `f - Q^{(1)}Q^{(2)}f = (f - Q^{(1)}f) + Q^{(1)}(f - Q^{(2)}f)`, with constant `3` (`‖Q^{(1)}‖_{∞→∞} ≤ 2`, `norm_zeroModeOp_le`) instead of the closed form with `N^{-1}tr G̃`; the closed-form identity was checked numerically in section (a) (`paper-form` residual column).
- Hypotheses left in instances: `STExpAvgU`, the other premises of `STIngR6`, `LWtermEXP 3` (LW-14), `STExpIntII 3` (S6-12b): other gates' pins.
- Merge note for the hub: add `import RBM3D.Induction.ExpWardII` after the last `import` line of `RBM3D.lean` (here the last line on the branch base is `import RBM3D.Universality.GUETranslation`); the `Axioms.lean` hunk is the single deleted `STExpWardII` line (`@@ -235 +234,0 @@`); neighbouring owed lines of other tickets (`STExpDriftLo`, `STExpDriftDecay`, `RBM.Endpoints.*`, `STExpIntII`) are untouched, so conflicts are at most adjacent-hunk: keep every deleted line deleted.
