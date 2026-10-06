Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 23:32:25 UTC 2026

Read together: `T2197.md`, `T2197-amend-1.md`, `T2197-amend-2.md` (amendments govern). Scope after the amendments: targets 1-4; target 5 without `BAStep1`, `BAMainInd`, `BAGbEXP*`; `BAConArg'` (L5); `baSelf_none_of_gt`; `not_BAConArg_of_data` (conditional); `BAConArg'_premise_diag`; instance `inst_BAConArg'` at `s ≡ t ≡ 1/2`. Mathematics only.

### (i) Exponent table

| # | Quantity | Value / form | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | `N` | `(WL)^d = L^d W^d`; `(3,4,2)`: 512 = 64·8 | `tr(A ⊗ I_{W^d}) = W^d tr A`, so `N⁻¹ tr M = L^{-d} tr M^{(B)}` | exact identity; no relation among `L, W, d, g` needed |
| 2 | hypotheses of target 1 | `(z+m).im ≠ 0` only (1a-1c); `0 ≤ z.im` and `0 < m.im` (1d) | `gΨ^{(B)} - w` is a unit for `Im w ≠ 0` (Hermitian, `isUnit_sub_smul_of_isHermitian`); `1d`: `Im(z+m) ≥ Im m > 0` | `3 ≤ L`, `0 < g`, `3 ≤ d` not used |
| 3 | `‖Ψ^{(B)}‖` | `≤ 2d` (script: row sums `{6.0}`, `max|spec| = 6.0` at `d=3, L=4`); `Adj` is `zdistD(x-y) = 1` (`Defs/Lattice.lean:108`) | `y ∼ x` differs from `x` in one coordinate by `±1`: at most `2d` neighbours for every `L ≥ 1` | equality at `L ≥ 3` |
| 4 | `baSelf_none_of_gt` threshold | `|E| > 2 + 2d|g|`, `g` real of either sign | `w_i = gλ_i - E - m`: `Im` part gives `avg|w_i|^{-2} = 1` (script: `1.0000000000`); Cauchy-Schwarz `|m| ≤ 1`, so `|Re m| < 1` (`Im m > 0`); `|Re w_i| ≥ |E| - 2d|g| - |Re m| > 2 - 1 = 1` for all `i`, so `avg|w_i|^{-2} < 1`, contradiction | slack `|E| - (2+2d|g|) > 0` strict. **The weaker threshold `1 + 2d|g|` is false** (script: solution at `L=4, g=0.1, E=1.601`); `2 + 2d|g|` is needed as in the ticket. Then `BAm = 0` (dite default), `BArho = 0` |
| 5 | `t₀` | `Im m/(Im m + Im z)`, `Im z ≤ 1`, `Im m ≥ κ` | `κ/(κ+1) ≤ t₀ < 1` (`BAt0_lt_one`) | `κ = 1/2`: `t₀ ≥ 1/3`; along `sz0` `t₀ ≥ 0.6869901` (from `Im m ≥ 1.2/(1.44+1/64)`; `mS_im_half` gives only `5/12`) |
| 6 | `g₀/g` | `√t₀ ∈ [√(κ/(κ+1)), 1)` | `g₀ ≤ g` (`BAg0_le`) | `sz0`: `0.83291, 0.83333, 0.83333` |
| 7 | `B` comparison | `B(g,t,K) ≤ B(g₀,t,K) ≤ t₀⁻¹ B(g,t,K)` | `(g₀²+1-t) - t₀(g²+1-t) = (1-t₀)(1-t) ≥ 0`, second `Bparam` term has no `g` | slack `(1-t₀)(1-t)`; script: 0 violations in 2·10^5 random cases |
| 8 | `ℓ` comparison | `ℓ(g₀) ≤ ℓ(g) ≤ t₀^{-1/2} ℓ(g₀)` (`ellT`, `Defs/Params.lean:32`) | monotone in `g`; `max(·,1)`, `min(·,L)` | 0 violations (same run); `sz0`: ratio `1.000` (`ℓ = 1` clamp) |
| 9 | gate of `STDecayStronggL` | `g_n² ≤ 1 - τ_n` (`Induction/Defs.lean:134`) | implies `g₀² ≤ 1 - τ` | slack `(1-t₀) g²` |
| 10 | `(con_st_ind)` constant | `Bctl(g₀)^{𝔠d} ≤ t₀^{-𝔠d} Bctl(g)^{𝔠d}` | `𝔠d ≤ 1/100` | `((κ+1)/κ)^{1/100} = 1.01105` at `κ = 1/2` |
| 11 | `sz0` (`d=3`; `L=4(n+1)`, `W=(2(n+1))^5`, `g=(2(n+1))^{-6}`) | `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)` | `g²L³ ≤ 1/64` (`n=0`: `= 1/64`, tight) gives `Im m ≥ 1/2`, `Im z ∈ [11/30, 7/10]` | `Im m = 0.83249` (n=0), `0.83333`; `Im z = 0.36751, 0.36667` |
| 12 | domain `N^{-1+ε} ≤ Im z` | `N ≥ 2^21`: `2^{-18.9} = 2.04e-06` | `≤ 11/30` | huge |
| 13 | `Prec` contradiction (extra (b)) | bound `0`, loop `> 0` surely, `P(Ω) = 1` | `1 ≤ N^{-D}` false once `N > 1` (`SizeTendsto`, part of `Admissible`) | `N ≥ 2^21` along `sz0` |
| 14 | (b) hypothesis | `2 + 2d g_s < |E_n|`, `g_s = √(s/t) g₀` | data of the 1806 script: `2.7835 < 3.2` | `0.4165` |
| 15 | `BAConArg'_premise_diag` (`s = t`) | `BAlamS = g₀`; `Im m₀ = Im m/√t₀` | `Im m₀ ≥ Im m ≥ κ` (`t₀ < 1`) | `sz0`: `0.99949 ≥ 0.83249 ≥ 1/2` |
| 16 | law gap (T2173a) | `gvarF`, neighbour blocks, `sz0` `n=0` | `> 0` under `seqP sz`, `= 0` under `seqP (sz.withLam 0)` | `3.720e-09` vs `0` |

**Coupling reading (T2197b), `7_8:1816-1832`.** The omitted-notation list there is `z_t, E_t, η_t, m, M, G_t`; `B_{t,K}` (`(eq_B_param)`, defined with `ilambda`), `ℓ_t` (`lem_propTH`) and the gate `1-t ≥ ilambda²` are not in it, so the chain controls and the gate are at `g_n = sz.lam n` (the ticket's `g`-reading); the PT properties 5-8 are used at the flow parameters `(E, g₀)`. Rows 7-9 show the PT bounds at `g₀` imply their `g`-forms (`B(g₀) ≤ t₀⁻¹B(g)`; `e^{-c|a|/ℓ(g₀)} ≤ e^{-c|a|/ℓ(g)}`) and the `g`-gate implies the `g₀`-gate, with constants depending on `κ` only. Not shown: the `g`-reading of the induction pin is not a formal corollary of a `g₀`-reading (its hypotheses `STDecay`, with `ℓ(g)`, are weaker than with `ℓ(g₀)`); I found no counterexample and cannot decide it here. I recommend T2197b as an open note on the pin text (signed by §52), not a stop.

### (ii) One concrete nondegenerate instance (all targets at once)

`d = 3`, `L = 4`, `W = 2`, `N = 512`; PT pins at the flow point of `(L, g) = (4, 10)`: `Λ = 10`, `g₀ = 4.67234 ≤ Λ`, `E ≈ 0`, `m₀ = 0.56068 i`, `κ = Im m₀`, `t ∈ [0,1)`, `c = 1/2` (`BAReal` residual 1.1e-16); chain data `sz0`, `z_n = zS(L_n, g_n)`, `κ = 1/2`, `s ≡ t ≡ 1/2`, `ε₁ = 1/2`. `BAConArg'` premise `κ ≤ Im BAm(g₀,E_n)` holds with the margin of row 15. External hypotheses (PT pins, `STLmaxgL`, other stochastic premises) are owed by other tickets; their limit data (`Bctl → 0`, `N^{-0.9}`, `WO`, `W ≥ L`, `W ≥ N^{1/6}`) are the `limit rows` in the output.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2197/pf_all.py`. Output (verbatim):

```
== (A) target 1, d=3 L=4 W=2 g=10
m(i,10)=0.251349i
z=i: N=512 max|M-(M^B kron I)o split|=8.7e-16 |N^-1trM-L^-3trM^B|=1.2e-32 |m-N^-1trM|=5.0e-16
row sums of PsiB: {np.float64(6.0)} max|spec|= 6.0
flow pt: t0=0.21831 g0=4.67234 E=1.1e-15 m0=0.56068i BASelf resid=1.1e-16
real axis: N=512 max|M-(M^B kron I)o split|=2.6e-15 |N^-1trM-L^-3trM^B|=0.0e+00 |m-N^-1trM|=1.1e-15
== (B) sz0 n=0,1,2 (kappa=1/2, tau=t=1/16); limit rows n=10,100,1000
n=0 L=4 W=32 g^2L^3=0.0156 Imm=0.83249 Imz=0.36751 t0=0.69374 Imm/sqrt(t0)=0.99949 ellT(g)/ellT(g0)=1.000 Bctl(g)/Bctl(g0)=0.99992
   n=0: Bctl(g,1/16)=3.31e-05 N^(-0.9)=2.04e-06<=11/30  WO: W^(-1.4)=7.81e-03<=g=1.56e-02<=10  W>=L:True  N^(1/6)<=W:True
n=1 L=8 W=1024 g^2L^3=0.0000 Imm=0.83333 Imz=0.36667 t0=0.69444 Imm/sqrt(t0)=1.00000 ellT(g)/ellT(g0)=1.000 Bctl(g)/Bctl(g0)=1.00000
   n=1: Bctl(g,1/16)=9.95e-10 N^(-0.9)=2.72e-11<=11/30  WO: W^(-1.4)=6.10e-05<=g=2.44e-04<=10  W>=L:True  N^(1/6)<=W:True
n=2 L=12 W=7776 g^2L^3=0.0000 Imm=0.83333 Imz=0.36667 t0=0.69444 Imm/sqrt(t0)=1.00000 ellT(g)/ellT(g0)=1.000 Bctl(g)/Bctl(g0)=1.00000
   n=2: Bctl(g,1/16)=2.27e-12 N^(-0.9)=3.81e-14<=11/30  WO: W^(-1.4)=3.57e-06<=g=2.14e-05<=10  W>=L:True  N^(1/6)<=W:True
n=10 L=44 W=5153632 g^2L^3=0.0000 Imm=0.83333 Imz=0.36667 t0=0.69444 Imm/sqrt(t0)=1.00000 ellT(g)/ellT(g0)=1.000 Bctl(g)/Bctl(g0)=1.00000
   n=10: Bctl(g,1/16)=7.79e-21 N^(-0.9)=2.75e-23<=11/30  WO: W^(-1.4)=4.01e-10<=g=8.82e-09<=10  W>=L:True  N^(1/6)<=W:True
   n=100: Bctl(g,1/16)=2.80e-35 N^(-0.9)=6.93e-39<=11/30  WO: W^(-1.4)=7.29e-17<=g=1.47e-14<=10  W>=L:True  N^(1/6)<=W:True
   n=1000: Bctl(g,1/16)=3.21e-50 N^(-0.9)=5.05e-55<=11/30  WO: W^(-1.4)=7.76e-24<=g=1.55e-20<=10  W>=L:True  N^(1/6)<=W:True
== (C) baSelf_none_of_gt: Ward identity and non-existence beyond 2+2d|g|
 L=4 g=1.0 E=2.0: m=-0.0980+0.5066j avg|w|^-2=1.0000000000 |m|=0.5160<=1
 L=5 g=0.9 E=3.2: m=-0.2830+0.3491j avg|w|^-2=1.0000000000 |m|=0.4494<=1
 L=8 g=0.9 E=3.2: m=-0.2680+0.2552j avg|w|^-2=1.0000000000 |m|=0.3701<=1
 solutions with |E|>2+2d|g| (L=3..6, g in {.1,.5,1,2,-1.5}): 0 of 480
 (threshold 1+2d|g| is NOT enough: L=4,g=.1,E=1.601 has a solution: True )
== (D) not_BAConArg_of_data data: d=3, lam=1, (t0,E,g0)=(.81,3.2,.9), kappa=.2, s=eps1=.02, t=.95
 g=1.000 g_s=0.13059: 2+2d g_s=2.7835<E=3.2: True
 L=4: no real-axis solution at (g0,E)
 L=8: Im m=0.2297 (>=.2:True) z=3.4990+0.0539j Imz<=1:True BASelf(g,z,m) resid=1.4e-16 solution at (g_s,E): None
 L=12: Im m=0.1776 (>=.2:False) z=3.4845+0.0417j Imz<=1:True BASelf(g,z,m) resid=5.6e-17 solution at (g_s,E): None
== (E) comparisons (random, 2e5 trials): t0>=k/(k+1); B(g)<=B(g0)<=B(g)/t0; ell(g0)<=ell(g)<=ell(g0)/sqrt(t0)
 violations: 0
== (F) neighbour-block coordinate variance at sz0 n=0 (L=4,W=32,lam=2^-6), d=3
 seqP sz: gvarF = W^-3 g^2/(2(1+6g^2)) = 3.720e-09
 seqP (sz.withLam 0): gvarF = W^-3 g^2/(2(1+6g^2)) = 0.000e+00
```

Reading of the output: (A) the Kronecker identity, the trace identity and the residual hold on the `512 × 512` matrices at `z = i` and at the real flow point; (B) rows 11-12, 15 and the limit data; (C) rows 3-4; (D) data of the 1806 script with `L_n ≡ 8` (so `Im m = 0.2297 ≥ κ = 0.2`, `Im z = 0.0539 ≤ 1`): the hypotheses of extra (b) hold numerically except the stochastic premise `STLmaxgL` at `g_s`, which no script can check; `L = 4` and `L = 12` fail `κ ≤ Im m` and are not used. The `STLmaxgL` premise stays an assumption of (b) (hence (b) is conditional, as stated in Amend 2). Row 5 numbers: `1/(1.44+1/64) = 0.6869901`, row 10: `3^{0.01} = 1.01105` (command `python3 -c` in the tool log).

### Verdicts

- Target 1 (`BASelfFine`, 1a `BAMres_fine_kron`, 1b `BAMres_fine_apply`, 1c `BAfine_trace`, 1d `BASelf_iff_fine`): PASS. Hypotheses are those of row 2; identities exact, checked at `N = 512`.
- Target 2 (PT pins `BAProp5…BAProp8`, `BAProp5to8`; stated only): PASS. All deterministic hypotheses hold at the flow point of (ii) (`g₀ ≤ Λ`, `BAReal`, `κ ≤ Im m₀`, `t ∈ [0,1)`).
- Target 3 (flow vocabulary `BAmF … BAGM`): PASS (no law enters; `seqHflowBA` already uses `sz.withLam 0`).
- Target 4 (carrier over a law, `PrecL`, band bridges at `μ = seqP sz`): PASS; the law data of row 16 show the two laws differ, so the parameter is not vacuous.
- Target 5 as amended (`BAflowT0 … baFMz`, `STMainIndG`, `STMainInd_iff`, `BAvecEntry`, `BAlamS`, `BAConArgLoop`, `BAConArgVec`, `BAConArg'`, `STStep1_iff`): PASS. `BAConArg'` adds only `∀ n, κ ≤ (BAmF …).im`, which excludes the data of (b) by row 4 (`BAm = 0` there). Open note on the coupling reading (T2197b, above).
- Extra (a) `baSelf_none_of_gt`: PASS with threshold `|E| > 2 + 2d|g|` (row 4; not `1 + 2d|g|`).
- Extra (b) `not_BAConArg_of_data`: PASS as a mathematical statement. Proof ingredients: (a) gives `BAm(g_s, E) = 0`, `η_s = 0`, bound `0` at `k = 2`; `‖𝓛^{(2)}_{t,(+,−),(a,a)}‖ = Σ_{x,y∈[a]} |G_xy|² > 0` surely, since `H` Hermitian and `Im z_t = (1-t) Im m₀ > 0` (`BAdom`, `BAzztE_data`, `t < 1`) give `Im G_xx > 0`; the bad set is all of `Ω`, probability `1 > N^{-D}` for large `N`. The statement is droppable without affecting any other target; the drop/keep decision is for stage 1b (no size estimate here, per §4 step 1).
- `BAConArg'_premise_diag` and `inst_BAConArg'` at `s ≡ t ≡ 1/2`: PASS (row 15; `BAm(g₀, E_n) = m/√t₀` by `BAzztE_data` and `BAm_real_eq_of_self`; `z_n.im > 0` from `BAdom` and `one_le_size`; no sign of `sz.lam` needed, `BASelf_exists` holds for every real `g`). Only `κ ≤ Im m`, not `t ≤ t₀`, is needed for `BAConArg'`.

## (b) Script output — Tue Oct  6 00:16:00 UTC 2026
`S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2197` (scratch, CONTROL H28); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2197`, branch `t/T2197`.
### b.1 Commit and build
```
$ git rev-parse --short HEAD; wc -l < RBM3D/BA/FlowPins.lean; git diff --stat main...t/T2197 | tail -n 1
e854613
    1582
 2 files changed, 1591 insertions(+)
$ lake build RBM3D.BA.FlowPins 2>&1 | tail -n 1
Build completed successfully (3734 jobs).
$ lake build 2>&1 | tail -n 1   # whole library after the commit (saved in $S/fullbuild.out)
Build completed successfully (4029 jobs).
```
### b.2 Axioms (`gen_axioms.py` writes `$S/axioms.lean`, one `#print axioms` per public declaration)
```
$ python3 $S/summ_axioms.py
public declarations printed by #print axioms: 110
  109 x [propext, Classical.choice, Quot.sound]
    1 x [(none)]  RBM.BA.FlowFM
listed targets and instances on [propext, Classical.choice, Quot.sound] only: 15 of 15
forbidden tokens (sorry|admit|native_decide|axiom) in FlowPins.lean: 0
```
### b.3 Target statements, extracted by script
```
$ python3 $S/extract.py 14 BASelfFine BAMres_fine_kron BAMres_fine_apply BAfine_trace BASelf_iff_fine baSelf_none_of_gt "BAConArg'" "BAConArg'_premise_diag" not_BAConArg_of_data
-- FlowPins.lean:57
def BASelfFine (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace
-- FlowPins.lean:70
theorem BAMres_fine_kron (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
      Mres ((g : ℂ) • PsiI d L W) z m =
        ((BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) : Matrix (Vtx d L W) (Vtx d L W) ℂ)).submatrix
          (splitEquiv d L W) (splitEquiv d L W) := by
-- FlowPins.lean:100
theorem BAMres_fine_apply (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 → ∀ x y : Idx d L W,
      Mres ((g : ℂ) • PsiI d L W) z m x y =
        if (split d L W x).2 = (split d L W y).2 then BAMB d L g z m (split d L W x).1 (split d L W y).1 else 0 := by
-- FlowPins.lean:113
theorem BAfine_trace (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace =
        (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace := by
-- FlowPins.lean:139
theorem BASelf_iff_fine (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im → (BASelfFine d L W g z m ↔ BASelf d L g z m) := by
-- FlowPins.lean:785
theorem baSelf_none_of_gt (d L : ℕ) [NeZero L] (g E : ℝ) (hE : 2 + 2 * d * |g| < |E|) :
    ∀ m : ℂ, ¬ BASelf d L g (E : ℂ) m := by
-- FlowPins.lean:630
def BAConArg' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) →
        STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
        (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
-- FlowPins.lean:944
theorem BAConArg'_premise_diag {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) :
    ∀ n, κ ≤ (BAmF sz (BAlamS sz z t t) (BAflowEs sz z) n).im := by
-- FlowPins.lean:1091
theorem not_BAConArg_of_data (d : ℕ) {κ ε 𝔡 ε₁ 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (hε₁ : 0 < ε₁) (sz : Sizes d) (z : ℕ → ℂ) (hF : BAFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ)
    (hs : ∀ n, ε₁ ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hL : STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s)
    (hE : ∀ n, 2 + 2 * d * |BAlamS sz z s t n| < |BAflowEs sz z n|) :
    ¬ BAConArg d := by
```
### b.4 Compiled nonempty instances (all in `RBM.BA.FlowPinsInst`, compiled by the build of b.1; first two lines of each statement)
```
$ python3 $S/extract.py 2 inst_kron inst_apply_concrete inst_selfFine inst_selfFine_real inst_BAProp5 flow_sz0 BAMfine_sz0_kron "inst_BAConArg'" inst_premise_diag inst_none_pos seqGvar_ne_withLam_zero
-- FlowPins.lean:1155
theorem inst_kron : Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) =
    ((BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I) ⊗ₖ (1 : Matrix (Fin (2 ^ 3)) (Fin (2 ^ 3)) ℂ) :
  ...
-- FlowPins.lean:1169
theorem inst_apply_concrete :
    Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) 0 ![1, 0, 0] = 0 ∧
  ...
-- FlowPins.lean:1190
theorem inst_selfFine : BASelfFine 3 4 2 10 Complex.I (BAm 3 4 10 Complex.I) :=
-- FlowPins.lean:1194
theorem inst_selfFine_real : BASelfFine 3 4 2 P.g0 (P.E : ℂ) P.m0 :=
-- FlowPins.lean:1214
theorem inst_BAProp5 (h : BAProp5 3 10 P.m0.im) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
  ...
-- FlowPins.lean:1366
theorem flow_sz0 : BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq := by
-- FlowPins.lean:1427
theorem BAMfine_sz0_kron (n : ℕ) :
    BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n =
  ...
-- FlowPins.lean:1396
theorem inst_BAConArg' (h : BAConArg' 3)
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
  ...
-- FlowPins.lean:1440
theorem inst_premise_diag :
    ∀ n, (1 / 2 : ℝ) ≤ (BAmF sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq) n).im :=
-- FlowPins.lean:1448
theorem inst_none_pos : ∀ m : ℂ, ¬ BASelf 3 4 1 ((9 : ℝ) : ℂ) m :=
-- FlowPins.lean:1550
theorem seqGvar_ne_withLam_zero :
    ∃ c : sz0.SeqCoord, sz0.seqGvar c ≠ (sz0.withLam 0).seqGvar c := by
$ bash $S/inst_counts.sh   # inventory of section 9
section 9 starts at line 1136: theorems 40, examples 21, defs 1
instance theorems: inst_kron inst_apply inst_apply_concrete inst_trace inst_selfFine inst_selfFine_real inst_kron_real inst_BAProp5 inst_BAProp5s inst_BAProp6 inst_BAProp7 inst_BAProp8 inst_BAConArg' inst_premise_diag inst_none_pos inst_none_neg inst_BAm_zero inst_BArho_zero inst_flowPt_inside
```
### b.5 Statements against the check file and the probes; name clashes
```
$ lake env lean $S/cmp_check.lean >/dev/null; echo exit=$?; grep -c '^example' $S/cmp_check.lean   # 8 shapes of the check file + 11 rfl/term examples
exit=0
19
$ python3 $S/probe_diff2.py   # T2161 sections 4-7 vs FlowPins.lean, substitutions L1-L5 applied to the probe
declarations compared (probe T2161 82e72b3 sections 4-7 vs FlowPins.lean): 59
identical after whitespace normalisation: 29
identical after the mechanical substitutions L1-L5 of the ticket: 30
residual differences: 0
$ python3 $S/probe_diff3.py | sed -n '1p;4p'   # T2173 declarations
DIFF FlowFM.GM 1963 353
declarations copied from T2173 (a543154): 14; identical after whitespace normalisation: 13
$ python3 $S/clash.py   # new public names vs the other RBM3D files (non-Probe), last name component
public names checked: 110 declarations scanned: 13964
clashes: 0
```
### b.6 §57 (3), registry
```
$ python3 $S/grep57.py   # greps FlowPins.lean for 'Prec sz|Whp sz|sz.seqP|seqP sz' and classifies each matching line
lines matching "Prec sz|Whp sz|sz.seqP|seqP sz": 44
  band bridge theorems STMainInd_iff, STStep1_iff  6
  band bridge theorems bandFM_*                    12
  band-bridge examples (section 9, at sz0)         18
  docstring/comment                                8
lines inside a BA statement (must be 0): 0 []
$ grep -n 'Sizes.seqP (sz.withLam 0)' RBM3D/BA/FlowPins.lean   # line numbers in sections 5-8 (BA statements)
555 601 614 618 635 983 1094 
$ git diff main...t/T2197 -- RBM3D/Test/Axioms.lean | grep '^+ ' | grep -o "RBM\.[A-Za-z0-9_.]*'*"   # names added to owedProps ($S/owed_names.sh)
RBM.BA.BAProp5 RBM.BA.BAProp5s RBM.BA.BAProp6 RBM.BA.BAProp7 RBM.BA.BAProp8 RBM.BA.BAProp5to8 RBM.BA.BAConArg' RBM.BA.STLmaxgL 
$ lake env lean $S/precheck.lean > $S/precheck.out 2>&1; echo exit=$?; sed -n 1p $S/precheck.out   # $S/precheck.lean = import RBM3D, import RBM3D.BA.FlowPins, #assert_rbm_axioms (DECISIONS §20 (2)); before the 8 lines it failed on 8 unregistered premises
exit=0
axiom audit: 6669 theorems, 2299 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
### b.7 Narrative (every fact is in the output above, the files, or the tool log)
- Stage 1b: first `date -u` of the stage `Mon Oct  5 23:33:26 UTC 2026` (section (a) is dated `Mon Oct  5 23:32:25 UTC 2026`); first commit `585c56a` at `Tue Oct  6 00:01:55 UTC 2026` (`date -u` right after it); amended to `e854613` (a concrete-entry instance `inst_apply_concrete` added, `BAConArg` made `private`; `date -u` right after the amend: `Tue Oct  6 00:14:38 UTC 2026`); b.1-b.6 were run on `e854613`. Section (a) is not edited; no (a′): I found no mistake in it.
- Scope as amended: targets 1-4 as ticketed; target 5 without `BAMainInd`, `BAStep1` (BA-D3) and `BAGbEXP`, `BAGbEXPpre`, `BAGbEXPconcl` (Amend 2); `BAConArg'` is pinned, `BAConArg` is not; extras (a) `baSelf_none_of_gt`, (b) `not_BAConArg_of_data`; `BAConArg'_premise_diag`; `inst_BAConArg'` at `s ≡ t ≡ 1/2`. Not written (ticket: not targets): T2161 sections 8-12, `BAMz`, `BAlocSCConcl`, `drift_entry`, all of BA-C1b.
- Target 1: `PsiI = (PsiB ⊗ₖ 1).submatrix e e`; `gΨ - w = (A ⊗ₖ 1).submatrix e e`, `A = gΨ^{(B)} - w` a unit (`isUnit_sub_smul_of_isHermitian`); `(A ⊗ 1)(A⁻¹ ⊗ 1) = 1` by `submatrix_mul_equiv`, `mul_kronecker_mul`, `inv_eq_right_inv`; trace by `trace_kronecker`, `trace_one`, `Equiv.sum_comp`. Hypotheses used: `(z+m).im ≠ 0` (1a-1c), `0 ≤ z.im` (1d); not `3 ≤ L`, `0 < g`, `3 ≤ d` (as (a) row 2). So `BASelf`, `BAm` are the paper's `(self_m)`, `m(z, ilambda)` for every `W ≥ 1`.
- Targets 2, 3 are the probe text (b.5: identical). Target 4: twelve `L`-predicates by rule L1, three law-free verbatim, `bandFM`, `baFM`, 13 bridges at `Sizes.seqP sz` (12 `Iff.rfl`, `bandFM_STEEk` by `rfl`). b.5: 59 probe declarations compared, 29 identical, 30 identical after L1-L5, 0 residual; 13 of 14 declarations taken from T2173 identical, `FlowFM.GM` differs only in binder syntax (same signature).
- Target 5: `STMainIndG` (L2), `STMainInd_iff`, `STStep1_iff` by `Iff.rfl`; `BAConArg'` is the probe `BAConArg` after L1-L4 plus the premise `κ ≤ Im m(E_n, g_s)` after `(∀ n, t n < 1) →` (L5). Every statement of sections 5 and 8 that mentions a law carries `Sizes.seqP (sz.withLam 0)`; the 44 lines matching the §57 (3) grep are band bridges, band examples and docstrings (b.6).
- Extra (a), threshold `2 + 2d|g|` (as (a) row 4): `BAMB_trace_eq_sum` and the imaginary part of `(self_m)` give `L^{-d} Σ |w_i|^{-2} = 1`; Cauchy-Schwarz gives `|m| ≤ 1`; the eigenvalues of `Ψ^{(B)}` lie in `[-2d, 2d]` (maximal row sum, at most `2d` neighbours: the points `x` with `zdistD x = 1` are `±e_k`); so `|Re w_i| > 1`, a contradiction. Corollaries `BAm_eq_zero_of_gt`, `BArho_eq_zero_of_gt`.
- Extra (b) is kept: section 8 has 137 code lines (171 lines with docstrings, lines 969-1139). Its hypothesis is `2 + 2d|g_s| < |E_n|` with `|BAlamS|` (`Sizes.lam` is an unsigned sequence; equal to the literal Amend 2 text where `g_s ≥ 0`); the conclusion is `¬ BAConArg d`, where `BAConArg` is a `private def` of the unrepaired pin (CLAUDE.md §3 (E)) that no theorem takes as a hypothesis (so no registry line). Proof: (a) gives `η_s = 0`, the `k = 2` bound is `0`, the loop `𝓛^{(2)}_{(+,-),(0,0)} = Σ E_x E_y |G_xy|²` is positive for every sample (`Im z_t > 0`), so the bad set is all of `Ω` and has probability `1 > N^{-1}` once `N ≥ 2`. No instance (Amend 2); existence of such data is argued in supervisor 1806 §1.4, not compiled here.
- Instances (b.4): every deterministic hypothesis is discharged at `(d, L, W, g) = (3, 4, 2, 10)`, `z = i` and at the real flow point `P` (`N = 512`), with two concrete entries of `M` (`inst_apply_concrete`); PT pins at `P`; `sz0`, `z_n = z_S`, `BAFlow`, `t₀_n ≥ 2/3` (`1/2 < t₀_n`), `BAMfine` along the flow is the Kronecker matrix for every `n`; band bridges at `sz0`; T2173a witness. Left as hypotheses: the pins `BAProp5…BAProp8`, `BAConArg' 3`, and the loop bound `STLmaxgL` at `g_s` of `inst_BAConArg'` (all other gates' pins).
- Differences from the probe's `sz0` lemmas: no `BAmExists 3` hypothesis (`baMExists_holds 3`); `mS_im_half` now gives `4/5` (probe `1/2`), `t0_sz0` gives `2/3` (probe `1/16`).
- Registry: before the edit the pre-check failed on 8 premises (`STLmaxgL`, `BAProp5`, `BAProp5s`, `BAProp6`, `BAProp7`, `BAProp8`, `BAProp5to8`, `BAConArg'`), all now in `owedProps` (classes of T2161 b.2 and of the ticket); pre-check and whole-library `lake build` exit 0. `BAProp5to8` occurs in this file only in its definition (the scan finds it through its own projections). No stop condition was reached; no hypothesis was added to a target, no pinned signature changed.
- Ports (probe file:line): T2161 at `82e72b3`: `:661-736` target 2 (verbatim), `:744-811` target 3 (verbatim), `:819-1008` target 4 (L1, L4), `:1016-1191` target 5 (L2-L5), `:2027-2080` PT instances at `P`, `:2095-2199` the `sz0` lemmas (`hex` removed); T2173 at `a543154`: `:1932-2055` the carrier and five predicates, `:3824-3846` `svarF_ne_zero_profile` (verbatim), `:3851-3881` `seqGvar_ne_withLam_zero` (at `sz0`, `n = 0`). No RBM1D/RBM2D source (ticket), so no diff-stat.
- §29 checklist: PT pins keep `0 ≤ t`, `t < 1` (verbatim); `BAFlow` has `∀ n, BAdom`; `PrecL` is `StochDomAt` (union inside the probability, uniform in time, no `PrecPT`); `κ, ε, 𝔡 > 0`, `Admissible` are premises; the coupling question is T2197b.

## (c) Verified Mathlib names (`lake env lean $S/names_c.lean`, exit 0: 35 `#check` succeeded, 3 `#check_failure` confirmed absent)
Present: `Matrix.smul_kronecker`, `Matrix.add_kronecker`, `Matrix.one_kronecker_one`, `Matrix.mul_kronecker_mul`, `Matrix.trace_kronecker`, `Matrix.trace_one`, `Matrix.kroneckerMap_apply`, `Matrix.submatrix_mul_equiv`, `Matrix.submatrix_one_equiv`, `Matrix.submatrix_sub`, `Matrix.submatrix_smul`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.inv_eq_right_inv`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.mul_diagonal`, `Matrix.IsHermitian.mulVec_eigenvectorBasis`, `Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.submatrix`, `Equiv.sum_comp`, `Orthonormal.ne_zero`, `Finite.exists_max`, `Finset.add_sum_erase`, `Finset.sum_eq_zero_iff`, `Finset.card_image_le`, `Finset.card_le_card`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Complex.inv_im`, `Complex.normSq_pos`, `Complex.mul_conj`, `Complex.abs_re_le_norm`, `ZMod.natCast_zmod_val`, `ENNReal.ofReal_lt_one`, `MeasureTheory.measure_univ`, `MeasureTheory.measure_mono`, `Real.rpow_neg_one`.
Absent (use the shown route): `Matrix.sub_kronecker` (written as `add_kronecker` + `smul_kronecker` + `one_kronecker_one`), `Matrix.kroneckerMap_sub_left`, `Matrix.trace_submatrix_equiv` (written with `Equiv.sum_comp`).

## (d) Open issues and paper-delta candidates
- **T2197a** (D472 closed, `1_2:626-633`): `(def_G0)`'s `M = M^{(B)} ⊗ I_{W^d}` and `N⁻¹ tr M = L^{-d} tr M^{(B)}` are proved (`BAMres_fine_kron`, `BAfine_trace`), so the merged `BASelf`, `BAm` are the paper's `(self_m)`, `m(z, ilambda)` for every `Im z ≥ 0` and `W ≥ 1` (`BASelf_iff_fine`).
- **T2197b** (coupling, `7_8:1816-1832`): reading from (a): the omitted-notation list excludes `B_{t,K}`, `ℓ_t` and the gate `1-t ≥ ilambda²`, so the chain controls (`Bctl`, `STWB`, `ellT`, the gate of `STDecayStronggL`) are at `g_n = sz.lam n` (as written in the carrier predicates, copied from the band forms), and the PT pins at the flow point use `g₀_n`. Open as in (a): the `g`-reading of the induction pin is not a formal corollary of the `g₀`-reading; I did not decide it.
- **T2197c** (`lem_ConArg_BA`, `7_8:1956-1987`): Lean pins `BAConArg'` = the paper statement plus the premise `κ ≤ Im m(E_n, g_s)`; the unrepaired statement is false (supervisor 1806 §1.4); `not_BAConArg_of_data` compiles the refutation conditional on data with `2 + 2d|g_s| < |E_n|`.
- **T2197d** (new deterministic fact, not a paper statement): `(self_m)` has no solution for real `|E| > 2 + 2d|g|`, so `BAm = 0`, `ρ_N = 0` there (`baSelf_none_of_gt`; the weaker threshold `1 + 2d|g|` is false, (a) row 4).
- The law `seqP (sz.withLam 0)` of the BA statements is T2173a (D-number at the T2173 merge), not a new delta. `FlowFM.GM` is written with the T2161 text (variables), T2173 with explicit binders: same signature.
- Open: (1) existence of data for `not_BAConArg_of_data` (not compiled, not required); (2) the stochastic premise `STLmaxgL` at `g_s` and the pins stay hypotheses of the instances; (3) deferred by the amendments: `BAMainInd`, `BAStep1` (BA-D3), `BAGbEXP*` (first of BA-G3…G6); (4) `BAConArg` is `private`: a later ticket that needs the unrepaired pin must restate it, and register it in `refutedProps` if a theorem takes it as a hypothesis; (5) `mS_im_half` keeps its probe name though it now states `4/5`; (6) file size 1582 lines against the ticket's 900/1100/1400 estimate (section 9 instances 313 code lines, extras (a) and (b) 215 + 137).
