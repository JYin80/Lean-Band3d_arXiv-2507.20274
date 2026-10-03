Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-03 19:59 UTC

Notation (all from the files): `a₁ := Bctl_s = W^{-d} B_{s,0}` (`RBM3D/Defs/Sizes.lean:214`, `Bparam d L g t 0 = (g²+|1-t|)⁻¹ + (L^d|1-t|)⁻¹`, `Params.lean:36`, `g = lam`); `η_τ = (1-τ) Im m^{(E)}` (`Loop/GLoop.lean:75`), so `η_s/η_t = (1-s)/(1-t)`; `a := a₁ η_s/η_t`; `z = z_t`, `w = z̃_s = √(t/s) z_s` (`ConArgDet.lean:734`); `K := |z-w|²/(Im z · Im w)`; `E = lemE z_n`; `N = (WL)^d`.
Pin `STConArg d` (`Induction/Defs.lean:334`): for `κ,ε,𝔡,ε₁,C₀>0`, `STFlow`, `ε₁ ≤ s ≤ t < 1`, `STLmax` at `s` (`max|𝓛^{(k)}_s| ≺ a₁^{k-1}`, all `k ≥ 1`), every `k ≥ 2`: `1_{Ω_t} max|𝓛^{(k)}_t| ≺ a^{k-1}`, `Ω_t = {‖G_t‖_max ≤ C₀}` (`STomegaC`, `Defs.lean:87`).

### (i) Exponent table
| # | quantity | value / form | constraint (used by) | slack |
|---|---|---|---|---|
| 1 | scale at `s` | `a₁ = W^{-d}[(λ²+1-s)⁻¹ + (L^d(1-s))⁻¹]`, `d=3` | `a₁ > 0` (`s<1`) | `sz0, n=0, s=1/16`: `a₁=3.30522e-5` |
| 2 | `W^{-d}` (RBM2D `W⁻²`) | exponent `d` in `Bctl`, in Ward row-average `W^{-d}∑_{α∈Fin(W^d)}` and in (6.10) `W^{-d}·W^{d}=1` (merged in `ConArgDet`) | `d`-dependence cancels exactly | none lost |
| 3 | `ℓ`-factor (RBM2D `(ℓ₂/ℓ₁)^{2(k-1)} M₂^{-(k-1)}`) | replaced by `(Bctl_s η_s/η_t)^{k-1}`; no `ℓ`, `(K+1)^{d-2}` (only `K=0` is used: factor 1 for every `d`) | pin form (T2015 b, row `STConArg`) | n/a |
| 4 | `η_s/η_t` | `(1-s)/(1-t) ≥ 1` for `s ≤ t<1` (same `Im m^{(E)}>0`) | `a ≥ a₁` (recursion `ha1a`) | pairs below: `1.875, 3, 5.5e4` |
| 5 | bulk energy | `E=lemE z_n`: `z = (√lemT z)⁻¹ z_{t₀}^{(E)}` (`Semicircle.lean:270`), `Re z_{t₀}^{(E)} = E(1+t₀)/2`, so `|Re z| = |E|(1+t₀)/(2√t₀) ≥ |E|` (AM-GM) | `|E| ≤ 2-κ` for `ztTilde_arith`: **follows from `locDomain` (`|Re z| ≤ 2-κ`), `κ'=κ`; new lemma needed in 1b** | `z0`: `|E|=0.49999999999 ≤ |Re z| = 0.5 ≤ 1.9` |
| 6 | `ztTilde_arith` constant | `C = (3/c+1)+K₀²+c⁻¹`, `K₀=(3/c+1)(2/κ)`, `c = ε₁`: `|z-w|²/Im w ≤ Cη_s`, `η_s ≤ Im w ≤ Cη_s` for `c ≤ s ≤ t ≤ 1` | `s ≥ ε₁ > 0` (`w` has `√(t/s)`); `C` depends on `ε₁,κ` only | `ε₁=1/16, κ=1/10`: `C=960465`, all 5 inequalities true at 3 pairs |
| 7 | `K` | `K = |z-w|²/(η_t Im w) ≤ C η_s/η_t` hence `K a₁ ≤ C a` | recursion `hK`, `∀ n` | `(1/16,1/2)`: `Ka₁=1.19e-4 ≤ Ca=59.5` |
| 8 | size bound | `Bparam ≥ max((λ²+1)⁻¹, L^{-d})` as `0<1-s≤1`, so `a₁⁻¹ ≤ W^d min(λ²+1, L^d) ≤ W^dL^d = N`, any `λ`, any `L` vs `λ` | recursion `hN` (`a₁⁻¹ ≤ size`) | `a₁⁻¹=30255 ≤ N=2097152` |
| 9 | loop-length 1 | `Y₁ = 1_Ω max|tr(G E_a)| ≤ C₀` (`E_a = W^{-d}1_{[a]}`, entries `≤ C₀` on `Ω_t`; `Gres false = G*`) | RBM2D `hY1: ≤ 2` becomes `≤ C₀`; recursion constants depend on `C₀,k,C` only | `C₀=2` at the instance |
| 10 | loop scaling | `G̃=(H_t - z̃_s)⁻¹ = √(s/t) G_s` since `H_u = √u X` (`seqHflow_eq_smul`, `FineModel.lean:527`); loops of length `j`: factor `(s/t)^{j/2} ≤ 1` | `0<s ≤ t` | `(s/t)^{j/2} ≤ 1` |
| 11 | (6.4) / (6.11) | `Y_{2l+1}² ≤ Y_{2l}Y_{2l+2}` (`loopMax_odd_sq_le`); `Y_{2m} ≤ (m+1)(T_{2m} + K ∑_{l<m} Y_{2l+1} T_{p(2(m-l)-1)}^{1/p})` (`loopMax_two_mul_le_tilde`) | every `p ≥ 1` | see (ii) |
| 12 | `≺` loss | per step `N^{2/p}` (one `N^{1/p}` from `a₁^{-1/p} ≤ N^{1/p}`, one from `T_{2m} ≤ a^{..}N^{1/p}`); `p = p₀+1`, `1/(p₀+1) < τ/2` for the target `N^τ` | any `τ>0` | `τ` arbitrary; `D` (stoch. exponent) untouched, only `N^{-D}` events of the hypothesis |
| 13 | `t = 1` | pin has `t<1` (paper-delta T2015b); `η_1=0` | division by `η_t` | pair 3 uses `t = t₀(1-1e-12)`, `η_s/η_t = 5.5e4` |
| 14 | second bound of `(res_lo_bo_eta)` | omitted from the pin (T2015h) | not a target | n/a |

Boundary checks of DECISIONS §29 on `STConArg` (paper argument; numeric instance in (ii)):
1. Time range: `ε₁ ≤ s ≤ t < 1`, `ε₁>0` explicit. `s>0` is used (`√(t/s)`, `ztTilde_arith` needs `c ≤ s`); `t<1` is used (`η_t>0`; `a` is a division); `0 ≤ s` follows. No `t ≤ lemT z` is needed or assumed. **PASS.**
2. `λ > L`: only row 8 sees `λ` and `L`; `a₁⁻¹ ≤ W^d·min(λ²+1, L^d)` holds for every sign/size of `λ` versus `L`; `ℓ_t`, the case boundary `1-λ²/L²` (negative times when `λ>L`) do not occur in the pin. **PASS.**
3. `L^d ≤ W^K`: not used (rows 6–8 use only `SizeTendsto`, `Admissible.2.2.1` of `STFlow`; `Bandwidth`, `WO` are not used). **PASS** (nothing to add to the pin).
4. `∀ n` versus `∀ᶠ n`: `Prec` is `∀ᶠ l` (`StochDomAt`); the `∀ n` hypotheses (`ε₁ ≤ s n`, `s n ≤ t n`, `t n < 1`, `locDomain`) are used pointwise in `ztTilde_arith` and `hK` (`∀ n`); the `∀ᶠ` hypothesis `STLmax` is used only inside `PerTimeDomAt` (`∀ᶠ`). A condition at finitely many `n` is never forced. **PASS.**
5. Constants free of `W, L, λ`: `C=C(ε₁,κ)`, recursion constants `D=D(k,C,C₀)`, `p=p(τ)`. **PASS.**

How `conArg` gives `STConArg d` exactly (RBM2D `ConArgPin`, `ConArg:61`, `conArg:613` at `c9a24cf`): take `E_n = lemE z_n`, `t₁ = s`, `t₂ = t`, `c = ε₁` (RBM2D `c < t₁` is weakened to `c ≤ t₁`, which is what `ztTilde_arith` states), `a₁ = Bctl_s`, `a = a₁η_s/η_t`; hypothesis (55) is `STLmax` at `s`; bulk from row 5; `SizeTendsto` from `STFlow.1`; `Y_k = STomegaC·‖Lloop‖` (bridges `gloop_eq_loopM`, `loopM_eq_loopL`, `GLoopFlow.lean:96,127`); `Prec` is `StochDomAt` with union inside `P`, from `PerTimeDomAt` by `stochDomAt_of_perTimeDomAt` (`#U ≤ size^{2k}`). `RBM2D`'s scale relation `a = (W²ℓ₁²η₂)⁻¹` is not used: the recursion needs only rows 1, 4, 7, 8.

### (ii) One concrete instance (script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2076/pre.py`, mpmath 60 digits)
Data: `d=3`, `sz0` (MD-1) at `n=0`: `L=4, W=32, λ=1/64, N=2097152`; `z_n = 1/2 + i N^{-4/5}`, `κ=ε=1/10`, `ε₁=1/16`, `C₀=2`; pairs `(s,t)=(1/16,1/2)`, `(1/4,3/4)`, `(1/2, t₀(1-1e-12))`. Idealised loops: `T_j=a₁^{j-1}`, `Y_{2l+1}=a^{2l}` (`l ≥ 1`), `Y₁=C₀`; `D_k` = right side of (6.11) (`k=3` via (6.4): `√(D₂D₄)`).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2076/pre.py`; output (verbatim, between the fences):
```
d,L,W,lam,N = 3 4 32 0.015625 2097152
z_0 = (0.5 + 8.7638729e-6j) locDomain: |Re z|<=2-k: True  N^(-0.9)<=Im z: True  Im z<=1: True
E=lemE z = 0.499999999995  |E|<=|Re z|: True  t0=lemT z = 0.999990948752
c=eps1=1/16, kappa=1/10: K0=980.0 C=960465.0
--- pair s=0.0625 t=0.5  (c<=s<=t<1)
 ztTilde_arith 5 ineqs: [True, True, True, True, True]
 a1=Bctl_s=3.30522e-5  a=a1*eta_s/eta_t=6.19729e-5  eta_s/eta_t=1.875  a1<=a:True
 a1^-1<=N: True (a1^-1=30255.1, N=2097152)
 K=3.60579  K*a1=0.000119179 <= C*a=59.5228 : True
  p=2 k=2: D_k/a^(k-1)=1339.1  N^(1/p)=1448.2  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=2 k=3: D_k/a^(k-1)=1452.2  N^(1/p)=1448.2
  p=2 k=4: D_k/a^(k-1)=1574.8  N^(1/p)=1448.2
  p=3 k=2: D_k/a^(k-1)=240.76  N^(1/p)=128.0  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=3 k=3: D_k/a^(k-1)=260.8  N^(1/p)=128.0
  p=3 k=4: D_k/a^(k-1)=282.5  N^(1/p)=128.0
--- pair s=0.25 t=0.75  (c<=s<=t<1)
 ztTilde_arith 5 ineqs: [True, True, True, True, True]
 a1=Bctl_s=4.13126e-5  a=a1*eta_s/eta_t=0.000123938  eta_s/eta_t=3.0  a1<=a:True
 a1^-1<=N: True (a1^-1=24205.7, N=2097152)
 K=3.42397  K*a1=0.000141453 <= C*a=119.038 : True
  p=2 k=2: D_k/a^(k-1)=710.94  N^(1/p)=1448.2  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=2 k=3: D_k/a^(k-1)=680.41  N^(1/p)=1448.2
  p=2 k=4: D_k/a^(k-1)=651.2  N^(1/p)=1448.2
  p=3 k=2: D_k/a^(k-1)=132.73  N^(1/p)=128.0  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=3 k=3: D_k/a^(k-1)=126.82  N^(1/p)=128.0
  p=3 k=4: D_k/a^(k-1)=121.17  N^(1/p)=128.0
--- pair s=0.5 t=0.999990948750903  (c<=s<=t<1)
 ztTilde_arith 5 ineqs: [True, True, True, True, True]
 a1=Bctl_s=6.1959e-5  a=a1*eta_s/eta_t=3.42268  eta_s/eta_t=55240.994  a1<=a:True
 a1^-1<=N: True (a1^-1=16139.7, N=2097152)
 K=78273.5  K*a1=4.84975 <= C*a=3.28736e+6 : True
  p=2 k=2: D_k/a^(k-1)=720.05  N^(1/p)=1448.2  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=2 k=3: D_k/a^(k-1)=623.58  N^(1/p)=1448.2
  p=2 k=4: D_k/a^(k-1)=540.04  N^(1/p)=1448.2
  p=3 k=2: D_k/a^(k-1)=143.23  N^(1/p)=128.0  D_2<=2(1+C0*C*N^(1/p))*a: True
  p=3 k=3: D_k/a^(k-1)=124.04  N^(1/p)=128.0
  p=3 k=4: D_k/a^(k-1)=107.43  N^(1/p)=128.0
```
Concrete limit/check: `D_2 ≤ 2(1+C₀C N^{1/p}) a` is the derived bound (`K a₁^{1-1/p} ≤ C a N^{1/p}`), true at all three pairs, `p=2,3`; `D_k/a^{k-1}` stays within `N^{1/p}`-size multiples for `k=3,4` as well.

### Verdict
- `stConArg_holds (d : ℕ) : STConArg d` (via `conArg`): **PASS.** Pinned statement true as written (boundary checks 1-5); no counterexample. Residual item for 1b: the lemma `|lemE z| ≤ |Re z|` (row 5) is new; `STConArg`'s owed registry line can go once merged.
- `ConArgPin`/`conArg` ported form: **PASS** (same recursion, scales as rows 1,4,7,8; `Y₁ ≤ C₀`).

## (a′) Preflight corrections — Sat Oct  3 20:20:08 UTC 2026
1. Row 5 of (a) says the lemma `|lemE z| ≤ |Re z|` is new and must be written in 1b. It is merged: `abs_lemE_le` (`RBM3D/Defs/Semicircle.lean:309`) and `lemma28_quant` (`:359`, `|lemE z| ≤ 2 - κ` from `0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`); `stConArg_holds` uses `lemma28_quant`. No verdict change.
2. Row 8: only `Bparam ≥ L^{-d}` is used (`a₁⁻¹ ≤ W^d L^d = size`, `conArg_Bctl_inv_le`), not the `λ²+1` branch. No verdict change.

## (b) Script output

**b.1 Commit and scope**
```
$ date -u; git rev-parse --short HEAD; git diff --stat main...t/T2076; git status --short | head -3
Sat Oct  3 20:20:08 UTC 2026
a1c8df1
 RBM3D/Induction/ConArg.lean | 876 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 876 insertions(+)
```
**b.2 Builds** (module, then the whole library: root `#assert_rbm_axioms` included)
```
$ lake build RBM3D.Induction.ConArg 2>&1 | tail -2; lake build 2>&1 | tail -1
Build completed successfully (3323 jobs).
Build completed successfully (3789 jobs).
```
**b.3 Hygiene and axioms** of the three public declarations
```
$ grep -n "sorry\|admit\|^axiom\|native_decide" RBM3D/Induction/ConArg.lean; lake env lean axioms.lean   (axioms.lean: import RBM3D.Induction.ConArg + 3 x #print axioms)
grep exit 1
'RBM.Ind.ConArgPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.conArg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stConArg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**b.4 Registry pre-check** (ST1-COMMON item 8; scratch `precheck.lean` = `import RBM3D`, `import RBM3D.Induction.ConArg`, `#assert_rbm_axioms`; `RBM3D/Test/Axioms.lean` untouched)
```
$ lake env lean precheck.lean; echo "exit $?"; head -3 precheck.out; grep -n STConArg precheck.out; grep -c "premise(s) that no theorem" precheck.out
exit 0
axiom audit: 2442 theorems, 1046 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
23:  RBM.Gauss.Sizes.STConArg: 4 [no certificate]
106: RBM.Gauss.Sizes.STConArg,
0
```
**b.5 Target statements, extracted from the file by script** (`stmts.py`: text of `def ConArgPin` and the `theorem` headers), and the type of `stConArg_holds`
```
def ConArgPin {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 ≤ C₀ → (∀ n, c ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto →
    (∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖Sizes.Lloop sz n (E n) (s n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n)) ^ (k - 1))) →
    ∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => Sizes.STomegaC sz n (E n) (t n) C₀ ω *
          ‖Sizes.Lloop sz n (E n) (t n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n) *
          (Gauss.etaT (E n) (s n) / Gauss.etaT (E n) (t n))) ^ (k - 1))

theorem conArg {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t : ℕ → ℝ) :
    ConArgPin sz κ c C₀ E s t :=

theorem stConArg_holds (d : ℕ) : STConArg d :=
```
```
$ lake env lean typecheck.lean   (#check @stConArg_holds; example (d : ℕ) : STConArg d := stConArg_holds d)
stConArg_holds : ∀ (d : ℕ), STConArg d
exit 0
```
**b.6 Compiled nonempty instances** (section 7 of the file, `d = 3`, `sz0`, `z0`; both `example`s compile in `lake build` b.2; loop bound (55) at `s` is the only stochastic premise)
```
/-- **Instance of `conArg`** (`ConArgPin`): `d = 3`, `sz0`, `E = lemE z0`, `κ = 1/10`, `c = 1/16`,
`C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`, all deterministic hypotheses discharged; (55) at `s` is the
hypothesis `h55` (per time; it follows from `STLmax` by `perTimeOfStochDomAt`, below). -/
example (h55 : ∀ k : ℕ, 1 ≤ k →
      sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n)) ^ (k - 1))) :
    ∀ k : ℕ, 1 ≤ k →
      sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) :=
  conArg sz0 (1 / 10) (1 / 16) 2 (STflowE z0) (fun _ => 1 / 16) (fun _ => 1 / 2)
    (by norm_num) bulk_z0 (by norm_num) (by norm_num) (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) sz0_tendsto h55

/-- **Instance of `stConArg_holds`**: `d = 3`, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`ε₁ = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`; the loop bound `(eq:loopbound_s)` at `s`
(`STLmax`) stays a hypothesis. -/
example (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) :=
  fun k hk => stConArg_holds 3 (1 / 10) (1 / 10) (1 / 10) (1 / 16) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 (fun _ => 1 / 16)
    (fun _ => 1 / 2) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num) hL k hk
```
**b.7 Name clash** (new public names: `RBM.Ind.ConArgPin`, `RBM.Ind.conArg`, `RBM.Gauss.Sizes.stConArg_holds`; helpers are `private`)
```
$ git grep -n "ConArgPin\|stConArg_holds\|theorem conArg\b\|def conArg\b" main -- RBM3D; echo "git grep exit $? (1 = no match on main)"
git grep exit 1 (1 = no match on main)
```
**b.8 Port: source, drift, token accounting** (RBM2D at the ticket commit `c9a24cf`; RBM1D files not read, cited through RBM2D docstrings)
```
$ git -C ../RBM2D log -1 --format=%h; git -C ../RBM2D diff --stat c9a24cf HEAD -- RBM2D/Induction/ConArg.lean; acct.py ConArg2D.lean ConArg.lean (token counts)
9e0f275
 RBM2D/Induction/ConArg.lean | 156 ++++++++++++++------------------------------
 1 file changed, 50 insertions(+), 106 deletions(-)
token class                                 2D code  2D comm |  3D code  3D comm
W^2 / L^2 / (W*L)^2 / W⁻² / W²                   10        6 |        0        2
`d = 2`                                           0        2 |        0        3
Z2 / zdist2                                       8        1 |        0        1
scaleM/ellT/tailT/ellStar/Meta/ellz              25        0 |        0        2
3D code lines still containing a token:
```
```
$ grep -n "^theorem\|^def" ConArg2D.lean; grep -n "^theorem\|^def" ConArg.lean   (non-private declarations)
2D public:
61:def ConArgPin (κ c : ℝ) (E : ℕ → ℝ) (
613:theorem conArg (κ c : ℝ) (E t₁ t₂ : 
3D public:
655:def ConArgPin {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t
673:theorem conArg {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s 
806:theorem stConArg_holds (d : ℕ) : STConArg d := by
```
**b.9 Script diff of `ConArgPin`: RBM2D (renamed by R1-R3, `sdiff.py`) against the new statement; every residual difference is a line below**
```
tokens 2D(renamed) 231, 3D 200, similarity 0.72
insert  [] -> [{d : ℕ} (sz : Sizes d)]
insert  [] -> [C₀]
replace [: ℕ → ℝ) (s] -> [s]
insert  [] -> [0 ≤ C₀ →]
replace [<] -> [≤]
replace [loopAbs (sz.L n) (d.W n)] -> [‖Sizes.Lloop sz n]
replace [(Sizes.seqHflow d n (s n) ω) p.2.1 p.2.2)] -> [p.1 p.2 ω‖)]
replace [(scaleM (sz.L n) (d.W n) (E n)] -> [(sz.Bctl n]
replace [n))⁻¹] -> [n))]
replace [(if gMax] -> [Sizes.STomegaC sz n]
replace [(Sizes.seqHflow d] -> [C₀ ω * ‖Sizes.Lloop sz]
delete  [(t n) ω) ≤ 2 then 1 else 0) * loopAbs (sz.L n) (d.W n)] -> []
replace [(Sizes.seqHflow d n (t n) ω) p.2.1 p.2.2)] -> [p.1 p.2 ω‖)]
replace [(ellT (sz.L] -> [(sz.Bctl n (s]
replace [(t] -> [* (Gauss.etaT (E n) (s]
replace [ellT (sz.L n) (s n)) ^ (2 * (k - 1)) * (scaleM (sz.L n) (d.W] -> [Gauss.etaT]
replace [n))⁻¹] -> [n)))]
```
**b.10 How `conArg` gives `STConArg d`** (`stConArg_holds`, extracted by script; `conArg` at `E = lemE z`, `c = ε₁`, `s`, `t`)
```
theorem stConArg_holds (d : ℕ) : STConArg d := by
  intro κ ε 𝔡 ε₁ C₀ hκ hε h𝔡 hε₁ hC₀ 𝔠 sz z hflow s t hs hst ht hL k hk
  have hz0 : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (sz.STsize_pos n) _) (hflow.2 n).2.1
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n =>
    (lemma28_quant hκ (hz0 n) (hflow.2 n).2.2 (hflow.2 n).1).1
  have hsizeT : sz.SizeTendsto := hflow.1.2.2.1
  have hcon := RBM.Ind.conArg sz κ ε₁ C₀ (STflowE z) s t hκ hE hε₁ hC₀.le hs hst ht hsizeT
    (fun j hj => Path.perTimeOfStochDomAt (seqP sz) sz.size _ _ (hL j hj)) k (by omega)
  have hsz2 : ∀ᶠ n : ℕ in atTop, 2 ≤ sz.size n :=
    (sz.tendsto_size hsizeT).eventually (eventually_ge_atTop 2)
  exact stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := ((2 * k : ℕ) : ℝ)) (by positivity)
    (hsz2.mono fun n hn => RBM.Ind.conArg_card_le sz n k hn) hcon
```

### Narrative
- **Result.** `RBM3D/Induction/ConArg.lean` (commit `a1c8df1` on `t/T2076`, the only file changed) has three public declarations: `RBM.Ind.ConArgPin`, `RBM.Ind.conArg : ConArgPin sz κ c C₀ E s t` and `RBM.Gauss.Sizes.stConArg_holds (d : ℕ) : STConArg d` (type exactly the merged pin, b.5). Module and whole-library builds pass, axioms are the three standard ones, the registry pre-check exits 0 with no unclassified premise (b.2-b.4).
- **Route.** Sections 1-4 of RBM2D `ConArg.lean` are ported (recursion of §6, scaling (6.1), base case (5.6), parameter-to-max), section 5 is `conArg`, section 6 is `stConArg_holds`, section 7 the instances. `PerTimeCalc.PerTime.*` is used under the same names; `gloop`/`Gsig` become `loopL`/`Gres` (the scaling lemma is a `foldr` induction, `conArg_foldr_smul_mul`, because `loopL` is a `foldr`); `conArg_gres_blockMat_true` and `conArg_Gres_false` are copies of the private `gres_blockMat_true`, `gres_false` of `Green/Pins.lean:350,367`.
- **What changes at `d >= 3`.** (i) RBM2D `a = (W^2 l_1^2 eta_2)^{-1}`, `a_1 = M_{t_1}^{-1}` become `a = a_1 eta_s/eta_t`, `a_1 = Bctl_s = W^{-d}B_{s,0}`; `size = W^2 L^2` becomes `(W L)^d`. (ii) `a_1^{-1} <= size` follows from `Bparam >= L^{-d}` (`0 < 1-s <= 1`; `conArg_Bctl_inv_le`): any `d`, any `lam`, any `L`. (iii) `K a_1 <= C a` is `ztTilde_arith` with `C = C(eps_1, kappa)`. (iv) The base-case constant `2` of `Y_1 <= 2` is a parameter `B` of the recursion (`B = C_0`; `D_1 = (k+2)(1+(k+B)C)`). (v) `#((Fin k -> Bool) x (Fin k -> Zd d L)) = 2^k L^{dk} <= size^{2k}`; this needs `2 <= size`, automatic for `d >= 1` and obtained eventually from `SizeTendsto` (`d = 0` has `size = 1`).
- **Boundary checks (DECISIONS §29) on the pin.** `stConArg_holds` is proved for every `d`, with the pin as stated: no `3 <= d`, no relation between `lam` and `L`, no `L^d <= W^K` (not used), `s`, `t` ranges as pinned (`eps_1 <= s <= t < 1`), the `forall n` hypotheses used pointwise, constants depend on `eps_1, kappa` (`C`), `k`, `C_0` only. The pin is true as written; no counterexample.
- **Public declarations dropped: none** (RBM2D has two public ones, `ConArgPin` and `conArg`; all else is private). Private RBM2D items not carried: `conArgSizes`, `conArg_check`, `conArg_check_hyps` (the `d = 2` checks, replaced by the `d = 3` examples of b.6); `conArg_green_blockMat_diag_le` (replaced by `conArg_gres_blockMat_true`, inline in `hY1`); `conArg_Gsig_smul_mul`, `conArg_gloopProd_smul_mul`, `conArg_gloop_smul_mul` (replaced by `conArg_Gres_smul_mul`, `conArg_foldr_smul_mul`, `conArg_loopL_smul_mul`). New private: `conArg_norm_Lloop_eq`, `conArg_norm_Lloop_le_loopMax`, `conArg_Bctl_inv_le`.
- **`d = 2` tokens (b.8).** `W^2`-type: 10 code tokens (`a`, `size`, `a_1^{-1} <= size`) are replaced by `Bctl`, `etaT` and `W^d L^d`; `Z2`: 8, all become `Zd d _`; `scaleM`/`ellT`: 25, all replaced by `sz.Bctl`, `Gauss.etaT`; `d = 2`: 2 comment tokens. No token of the four classes remains in code (3D code column 0).
- **Registry.** No line is added to `RBM3D/Test/Axioms.lean` (`ConArgPin` is proved by `conArg`, nothing new is assumed). After this merge `RBM.Gauss.Sizes.STConArg` is in the scan's "carry nothing yet" list (b.4, line 106 of the output): its `owedProps` line can be removed by the cleanup ticket.
- **Instances (b.6).** `conArg` and `stConArg_holds` at `d = 3`, `sz0`, `z0`, `kappa = eps = 1/10`, `eps_1 = 1/16`, `C_0 = 2`, `s = 1/16 <= t = 1/2`; deterministic hypotheses (`STFlow`, bulk, times, `SizeTendsto`) are discharged; the loop bound (55) at `s` (`STLmax`, ST-6 pin) stays a hypothesis.

## (c) Verified Mathlib names (`#check`, `names.lean`, exit 0); none absent
- `exists_lt_of_lt_ciSup` : ∀ {α : Type u_1} {ι : Sort u_2} [inst : ConditionallyCompleteLinearOrd
- `Matrix.inv_smul` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : Decidable
- `Matrix.det_smul` : ∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type
- `Matrix.nonsing_inv_apply_not_isUnit` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : Decidable
- `Matrix.inv_submatrix_equiv` : ∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [ins
- `Matrix.conjTranspose_nonsing_inv` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : Decidable
- `Matrix.nonsing_inv_eq_ringInverse` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : Decidable
- `Matrix.trace_smul` : ∀ {n : Type u_1} {α : Type u_2} {R : Type u_3} [inst : Fintype n] [ins
- `Matrix.IsHermitian.submatrix` : ∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : Star α] {A : Ma
- `Real.rpow_pos_of_pos` : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
- `inv_anti₀` : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀]
- `mul_le_of_le_one_right` : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [i
- `ZMod.card` : ∀ (n : ℕ) [inst : Fintype (ZMod n)], Fintype.card (ZMod n) = n
- `Fintype.card_prod` : ∀ (α : Type u_1) (β : Type u_2) [inst : Fintype α] [inst_1 : Fintype β
- `Nat.pow_le_pow_left` : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
- `Nat.le_mul_of_pos_left` : ∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
- `List.length_eq_one_iff` : ∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ a, l = [a]
- Also verified by the same compile (names of the merged layer used): `RBM.Ind.{loopMax_two_mul_le_tilde, loopMax_odd_sq_le, loopMax_le, norm_gloop_le_loopMax, ztTilde_arith, Gres_eq_green_zSig, sum_bw, Eblk_eq_diagonal_bw}`, `RBM.Gauss.{loopM_eq_loopL, etaT_pos, etaT_eq_zt_im}`, `RBM.Path.{perTimeOfStochDomAt, stochDomAt_of_perTimeDomAt}`, `RBM.lemma28_quant`, `RBM.Gauss.Sizes.{tendsto_size, STBctl_pos, STsize_pos, seqHflow_eq_smul}`.

## (d) Open issues and paper-delta candidates
- **T2076a** (informational): `ConArgPin`/`conArg` state `k >= 1` (paper `lem_ConArg`: `n >= 2`; the pin `STConArg` keeps `k >= 2`) and take `0 <= C_0`; at `k = 1` the bound is `Y_1 <= C_0` (base case). Not a difference against the pin.
- **T2076b** (informational): hypothesis `c <= s` (paper `eps <= s`) replaces RBM2D `c < t_1`; `ztTilde_arith` (merged, T2063) takes `c <= t_1`.
- Signed deltas cited, not re-proposed: T2015b / D26 (`t < 1`), T2015h (second inequality of `(res_lo_bo_eta)` omitted from the pin).
- Observation: RBM2D `HEAD` (`9e0f275`) differs from the ticket commit `c9a24cf` in `ConArg.lean` by 156 lines (b.8); not examined, the port follows `c9a24cf`.
- Observation: downstream, `inst_conArg (h : STConArg 3)` of `Induction/Defs.lean` can now be fed `stConArg_holds 3`; `STLmax` (`(eq:loopbound_s)`) remains the only premise of `STConArg`.
- Observation: the proof never uses `3 <= d`, `lam` against `L`, `(eq:WO)`, `Bandwidth` or `L^d <= W^K`; `SizeTendsto` enters as `Tendsto size atTop atTop` (`hsize` of the `PerTimeCalc` lemmas) and for `size >= 1`, `size >= 2` eventually. Nothing to add to the pin.
