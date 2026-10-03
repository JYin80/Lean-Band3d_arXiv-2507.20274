Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 03:14:40 UTC 2026

### (i) Exponent table

Targets (mathematics only): the grid walk `H_k = √s X_0 + √Δ Σ_{i=1}^k X_i`, `Δ=(t−s)/K`, `X_i` iid copies of the model sample (`seqP sz`, coordinates Gaussian, variance `gvarF`: diag `S_xx`, off-diag `S_xy/2` per real part); `TransferLaw`: law of `H_k` = law of `√(u_k) X`, `u_k = s + kΔ`; `IndepIncr`: draw `k+1` independent of draws `0..k`; `GridTransferPT`: per-time `≺` on the walk ⇔ at the single-time model.

| Quantity | Value / formula | Constraint | Slack |
|---|---|---|---|
| `s_n` | 1/10 (instance) | `0 ≤ s` (`√s` real, `(√s)^2 = s`) | 1/10 |
| `t_n` | 1 | `s ≤ t` (`Δ ≥ 0`, `(√Δ)^2 = Δ`) | 9/10 |
| `K_n` | 4 | `K ≠ 0` (hypothesis of `TransferLaw`) | 4 vs 0 |
| `Δ = (t−s)/K` | 9/40 | `≥ 0` | 9/40 |
| `u_k = s+kΔ`, k=0..4 | 1/10, 13/40, 11/20, 31/40, 1 | `u_k ≥ s ≥ 0`; `u_K = t` | `u_K − t = 0` (script) |
| per-coordinate variance of `√s X_0 + √Δ Σ_{i≤k} X_i` | `(√s)^2 w + k (√Δ)^2 w = (s+kΔ) w`, `w = gvarF` | independence of the `k+1` draws; variances add (Gaussian sum of independent centred) | equality, 0 slack (exact identity, no inequality) |
| independence | coordinates of `pathP = infinitePi (seqP)` independent | `ω(k+1)` vs `σ(ω 0..ω k)` | exact |
| law of the draw `ω(k+1)` | `seqP sz` (every coordinate of the product) | — | exact |
| row sum of `S` | `Σ_y S_xy = W^{-d} · W^d · (c + 2d g² c) = 1`, `c = (1+2dg²)^{-1}`, needs `L ≥ 3` (2d distinct block neighbours) | `3 ≤ L` (`Sizes.three_le_L`) | L = 3 at the instance: 0 (equality), L = 4 at `sz0`: 1 |
| `#U_n = K_n+1` (index `Fin (K n+1) × V n` of `GridTransferPT`) | 5 | none for this ticket: `PerTimeDomAt` has the union over `u` *outside* `P`, the transfer is pointwise in `(n,k)` | n/a here. Downstream conversion `PerTime ⇒ StochDomAt` needs `#U ≤ N^C`: `N = 2097152 = 2^21`, `C = 1/10` gives `N^C = 4.287 < 5` (fails), `C = 1` gives slack `N/(K+1) = 419430.4`; `C = 1/8` gives `N^C = 2^(21/8) = 6.17 ≥ 5` (threshold `C ≥ log_N 5 ≈ 0.1106`, `N^0.1106 = 5.002`) |
| scale | `N = (WL)^d` (`sz.size`), one scale for `Prec`, `PrecPT`, `PrecGrid` | `PrecGrid` = `StochDomAt (pathP sz) sz.size`; `precGrid_of_le` needs `0 ≤ ζ`, `ξ ≤ ζ` and `1 ≤ sz.size n` (`≥ 1` since `W,L ≥ 1`) | `N_0 = 2097152 ≥ 1` |
| no `N → ∞`, no `W ≥ N^𝔠`, no `WO` | none of the four targets assumes them | — | — |
| RBM2D source | `c9a24cf`: `Path/Walk.lean` (608 lines; `map_pathH_eq` 541, `transferLaw` 580, `indepIncr` 214), `Path/Transfer.lean` (212 lines; `GridTransferPT` 35–46, `gridTransferPT` 58–80, measurability helpers 84–150; `measurable_lkErrMat` 155 and later excluded) | RBM2D HEAD is `9e0f275`; both files differ from `c9a24cf` (script below); port from `c9a24cf` as the ticket states | — |

Dimension-specific points of the port: `d` enters only through `Sizes d` (`Idx d (sz.L n) (sz.W n)`, `seqXmat`, `seqGvar`); the proof of the transfer law is coordinatewise in `SeqCoord sz` and uses only `Xlinear` additivity and Gaussian sums, so no exponent depends on `d`. The variance row sum 1 uses `L ≥ 3` (`d` neighbour pairs `±e_i` distinct).

### (ii) One concrete nondegenerate instance

`d = 3, W = 2, L = 3` (`N = (WL)^d = 216`), `ilambda = g = 1/2` (nonzero neighbour variance), `s = 1/10, t = 1, K = 4`; targets' hypotheses: `0 ≤ s` (1/10), `s ≤ t` (1/10 ≤ 1), `K ≠ 0` (4), `3 ≤ L` (3); `IndepIncr` and `PrecGrid`/`precGrid_of_le` carry no further hypothesis (`ξ = ζ = 1`, `U = Unit`); `GridTransferPT` hypotheses `∀n, 0≤s n, s n≤t n, K n≠0` hold for the constant sequences and measurability of `F` holds for `F n v u M = ‖M x y‖` (continuous). Lean instance sequence for stage 1b: `RBM.Gauss.SizesInst.sz0` (`Defs/Sizes.lean:260`; `d = 3, L_0 = 4, W_0 = 32, lam_0 = 1/64, N_0 = 2097152`), `s = 1/10, t = 1, K = 4`.

Check (exact rational profile `S_xy = W^{-d} SB_{blk x − blk y}`, `SB = c[x=0] + g²c[|x|_1=1]`; Monte Carlo of `E|(H_k)_xy|^2` against `u_k S_xy`, entrywise and as the full `216×216` matrix):

```
$ python3 mc2.py   # (scratchpad script; builds S on (Z_6)^3, blocks x//2 mod 3, Gaussian entries as above)
Delta 9/40 u_k ['1/10', '13/40', '11/20', '31/40', '1'] u_K==t True
N 216
row sums of S 1.0 1.0
diag S=0.05000 u_k*S / MC: ['0.00500/0.00499', '0.01625/0.01617', '0.02750/0.02746', '0.03875/0.03877', '0.05000/0.05004']
same block S=0.05000 u_k*S / MC: ['0.00500/0.00500', '0.01625/0.01619', '0.02750/0.02750', '0.03875/0.03875', '0.05000/0.05010']
nbr block S=0.01250 u_k*S / MC: ['0.00125/0.00125', '0.00406/0.00406', '0.00688/0.00689', '0.00969/0.00971', '0.01250/0.01255']
far block S=0.00000 u_k*S / MC: ['0.00000/0.00000', '0.00000/0.00000', '0.00000/0.00000', '0.00000/0.00000', '0.00000/0.00000']
full 216x216, 300 samples: mean_i sum_j|H_ij|^2 [0.0999 0.3251 0.5501 0.7755 1.0005] vs u_k [0.1, 0.325, 0.55, 0.775, 1.0] max|H-H*| 0
sz0 n=0 N 2097152 N^(1/10) 4.287 K+1= 5 N/(K+1) 419430.4
```
(`n = 200000` samples per entry, MC error ≈ 0.5%; the profile has `S_diag = S_same = 0.05`, `S_nbr = 0.0125`, row sum 1; the walk matrix is Hermitian at every sample.)

RBM2D drift since `c9a24cf` (read-only git):
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/Walk.lean RBM2D/Path/Transfer.lean
  RBM2D/Path/Transfer.lean | 102 +++-------------------------------------------
  RBM2D/Path/Walk.lean     | 104 +++++++++++++----------------------------------
  2 files changed, 35 insertions(+), 171 deletions(-)
```

### Verdicts
- Target 1 (pinned text, probe lines 937–1035; pins `TransferLaw`, `IndepIncr`, `PrecGrid`, `precGrid_of_le`): PASS. No hypotheses beyond `0 ≤ s, s ≤ t, K ≠ 0` (in `TransferLaw`) and `0 ≤ ζ, ξ ≤ ζ`; all hold at the instance of (ii).
- Target 2 (`transferLaw`, `indepIncr`, ported from RBM2D `Path/Walk.lean` at `c9a24cf`): PASS. Statement is true (variances add; `u_k ≥ 0`; script above), and the argument is dimension-free.
- Target 3 (`GridTransferPT`, `gridTransferPT`, RBM2D `Path/Transfer.lean:35–80`): PASS. The proof is pointwise in `(n,k)` from `transferLaw` and measurability of `F`; the union bound over `K+1` grid times is not used (it sits outside `P` in `PerTimeDomAt`). Note for stage 1b: the helpers at lines 84–150 (`Gsig`/`gloop`/`blockMat` measurability) are needed only to *instantiate* `F` with `Gt`/`Lloop`; `gridTransferPT` itself takes `F`'s measurability as hypothesis, so the compiled instance may use a continuous `F` (`‖M x y‖`) or the MD-3 `Gres` after porting the measurability of the resolvent entries.

## (a′) Preflight corrections — Sat Oct  3 03:24:45 UTC 2026

Two minor corrections to (a), neither changes a verdict:
- (a) row "RBM2D source": `gridTransferPT` spans `Path/Transfer.lean:58-78` (line 80 is the next section header); the measurability helpers are lines 84-150, as stated.
- (a)(ii) suggests `F n v u M = ‖M x y‖`; the Lean `gridTransferPT` instance below uses the resolvent entry `‖Gres M (zt (1/2) u) true 0 0‖` at `s = 1/10`, `t = 1/2` (not `t = 1`: `η_1 = 0`, so the control `η_u⁻¹` is not finite at `u = t = 1`). The `transferLaw` instance uses `s = 1/10`, `t = 1`, `K = 4` as in (a).

## (b) Script output — Sat Oct  3 03:24:45 UTC 2026

### Build
```
$ lake build RBM3D.Path.Walk
⚠ [3307/3307] Replayed RBM3D.Path.Walk
warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hK

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3307 jobs).
$ lake build   # RBM3D.lean with `import RBM3D.Path.Walk` added temporarily (reverted, not committed); lines with "axiom audit", "premises found", "registry", "error", "Build"
exit code 0
7:⚠ [3709/3711] Replayed RBM3D.Path.Walk
8:warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.
15:info: RBM3D.lean:60:0: axiom audit: 914 theorems, 341 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
34:premises found by scanning: 13 (borrowed 5, owed 1, structural 7).
35:registry: 11 borrowed + 2 owed + 13 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDecay,
49:Build completed successfully (3711 jobs).
```

### Axioms
```
$ lake env lean ax_T2018.lean | python3 group_ax.py   # `#print axioms` of every public declaration of the file (41), grouped by axiom set; "RBM." prefix dropped
41 declarations with axioms [propext, Classical.choice, Quot.sound]:
  Path.PathΩ Path.pathP Path.filt Path.gridStep Path.gridTime Path.pathH Path.TransferLaw Path.IndepIncr Path.isProbabilityMeasure_pathP 
Path.pathH_isHermitian Gauss.Sizes.PrecGrid Gauss.Sizes.precGrid_of_le Path.gridTime_last Path.measurable_pathH Path.pathH_adapted 
Path.indep_incr Path.map_incr Path.indepIncr Path.map_pathH_eq Path.transferLaw Path.GridTransferPT Path.gridTransferPT 
Gauss.walk_measurable_Gres_apply Gauss.walk_measurable_loopL Gauss.walk_measurable_blockMat Gauss.walk_measurable_loopFine 
Gauss.Sizes.walk_measurable_Gt_apply Gauss.Sizes.walk_measurable_Lloop Path.WalkInst.gridTime_sz0 Path.WalkInst.gridTime_last_sz0 
Path.WalkInst.transferLaw_sz0 Path.WalkInst.transferLaw_pin_sz0 Path.WalkInst.indepIncr_sz0 Path.WalkInst.indepIncr_pin_sz0 
Path.WalkInst.map_incr_sz0 Path.WalkInst.gridRes_prec Path.WalkInst.Fres_measurable Path.WalkInst.gridTime_le_half 
Path.WalkInst.gridTransferPT_sz0 Path.WalkInst.Fres Path.WalkInst.Zres
```

### Target statements (extracted by `sed -n` from `RBM3D/Path/Walk.lean` at commit 8eda4cd)
```
$ sed -n '83,86p;90,92p;123,125p;127,129p;160,161p;270p;598,601p;637,638p;662,676p;685,688p;737,739p;794,796p' RBM3D/Path/Walk.lean
def TransferLaw : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ s n → s n ≤ t n → K n ≠ 0 →
    (pathP sz).map (pathH sz s t K n k) =
      (Sizes.seqP sz).map (Sizes.seqHflow sz n (gridTime s t K n k))
def IndepIncr : Prop :=
  ∀ k : ℕ, Indep (filt sz k)
    (MeasurableSpace.comap (fun ω : PathΩ sz => ω (k + 1)) inferInstance) (pathP sz)
def PrecGrid (ξ ζ : ∀ n, U n → Path.PathΩ sz → ℝ) : Prop :=
  StochDomAt (Path.pathP sz) sz.size ξ ζ

theorem precGrid_of_le {ξ ζ : ∀ n, U n → Path.PathΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : sz.PrecGrid ξ ζ := by
  intro τ hτ D _
theorem gridTime_last (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    gridTime s t K n (K n) = t n := by
theorem indepIncr : IndepIncr sz := fun k => (indep_incr sz k).symm
theorem map_pathH_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hs : 0 ≤ s n) (hst : s n ≤ t n)
    (hK : K n ≠ 0) :
    (pathP sz).map (pathH sz s t K n k)
      = (Sizes.seqP sz).map (Sizes.seqHflow sz n (gridTime s t K n k)) := by
theorem transferLaw : TransferLaw sz :=
  fun s t K n k hs hst hK => map_pathH_eq sz s t K n k hs hst hK
def GridTransferPT (s t : ℕ → ℝ) (K : ℕ → ℕ) {V : ℕ → Type}
    (F : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (ζ : ∀ n, V n → ℝ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, K n ≠ 0) →
  (∀ n (v : V n) (u : ℝ), Measurable (F n v u)) →
    (PerTimeDomAt (pathP sz) sz.size (U := fun n => Fin (K n + 1) × V n)
        (fun n p ω => F n p.2 (gridTime s t K n p.1) (pathH sz s t K n p.1 ω))
        (fun n p _ => ζ n p.2 (gridTime s t K n p.1)) ↔
      PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Fin (K n + 1) × V n)
        (fun n p ω => F n p.2 (gridTime s t K n p.1)
          (Sizes.seqHflow sz n (gridTime s t K n p.1) ω))
        (fun n p _ => ζ n p.2 (gridTime s t K n p.1)))

private theorem transfer_measurable_pathH (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
theorem gridTransferPT (s t : ℕ → ℝ) (K : ℕ → ℕ) {V : ℕ → Type}
    (F : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (ζ : ∀ n, V n → ℝ → ℝ) : GridTransferPT sz s t K F ζ := by
  intro hs hst hK hF
theorem walk_measurable_Gres_apply {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (σ : Bool) (i j : n) : Measurable fun M : Matrix n n ℂ => Gres M z σ i j := by
  have h : ∀ w : ℂ,
theorem walk_measurable_loopFine (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    Measurable fun H : Matrix (Idx d L W) (Idx d L W) ℂ => loopFine d L W H z σ a := by
  have h : ∀ H : Matrix (Idx d L W) (Idx d L W) ℂ, loopFine d L W H z σ a
```

### Script diffs against the probe (item 1) and RBM2D (items 2, 3), `bash diff_T2018.sh` (rename script `rn`, docstrings stripped)
```
== item 1: pinned text, probe 5d2a4a8 lines 937-1035 vs RBM3D/Path/Walk.lean lines 43-141
IDENTICAL (99 lines)
== item 2: RBM2D Walk.lean c9a24cf 83-91,111-581 (renamed, docstrings stripped) vs RBM3D/Path/Walk.lean 159-638
1d0
< 
340c339,340
<     Measure.infinitePi_map_pi (μ := fun c : Sizes.SeqCoord sz => gaussianReal 0 (Sizes.seqGvar sz c))
---
>     Measure.infinitePi_map_pi
>       (μ := fun c : Sizes.SeqCoord sz => gaussianReal 0 (Sizes.seqGvar sz c))
== item 3: RBM2D Transfer.lean c9a24cf 35-78 (renamed, docstrings stripped) vs RBM3D/Path/Walk.lean 657-705
IDENTICAL (code lines:       39)
```
`rn` = perl substitutions `Idx (d.L n) (d.W n)`→`Idx d (sz.L n) (sz.W n)`, `d.L n`→`sz.L n`, `d.size`→`sz.size`, `(d : Sizes)`→`{d : ℕ} (sz : Sizes d)`, `<name> d`→`<name> sz` for `Sizes.*`, `pathP`, `PathΩ`, `filt`, `pathH`, `transferLaw`, …, `variable {d}`→`variable {sz}`.

### Compiled nonempty instances at `sz0` (`RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`, `N_0 = 2097152`), in the same file, `namespace RBM.Path.WalkInst`
```
$ sed -n '840,842p;845,847p;852,857p;860p;864,866p;869p;878,882p;895,897p;902,903p;918,924p' RBM3D/Path/Walk.lean
theorem gridTime_sz0 :
    gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 2 = 11 / 20 := by
  norm_num [gridTime, gridStep]
theorem gridTime_last_sz0 :
    gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 4 = 1 :=
  gridTime_last (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 (by norm_num)
theorem transferLaw_sz0 :
    (pathP sz0).map (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 2) =
      (Sizes.seqP sz0).map (Sizes.seqHflow sz0 0 (11 / 20)) := by
  have h := transferLaw sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1) (fun _ => 4) 0 2
    (by norm_num) (by norm_num) (by norm_num)
  rwa [gridTime_sz0] at h
theorem transferLaw_pin_sz0 : TransferLaw sz0 := transferLaw sz0
theorem indepIncr_sz0 :
    Indep (filt sz0 2) (MeasurableSpace.comap (fun ω : PathΩ sz0 => ω (2 + 1)) inferInstance)
      (pathP sz0) := indepIncr sz0 2
theorem indepIncr_pin_sz0 : IndepIncr sz0 := indepIncr sz0
theorem gridRes_prec : sz0.PrecGrid (U := fun _ => Unit)
    (fun n _ ω => ‖Gres (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) n 2 ω)
        (zt (1 / 2) (1 / 2)) true 0 0‖)
    (fun _ _ _ => (etaT (1 / 2 : ℝ) (1 / 2))⁻¹) := by
  have hpos : 0 < etaT (1 / 2 : ℝ) (1 / 2) := etaT_pos (by norm_num) (by norm_num)
def Fres (n : ℕ) (_ : Unit) (u : ℝ)
    (M : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) : ℝ :=
  ‖Gres M (zt (1 / 2) u) true 0 0‖
theorem Fres_measurable (n : ℕ) (v : Unit) (u : ℝ) : Measurable (Fres n v u) :=
  (walk_measurable_Gres_apply (zt (1 / 2) u) true 0 0).norm
theorem gridTransferPT_sz0 :
    PerTimeDomAt (pathP sz0) sz0.size (U := fun n => Fin ((fun _ : ℕ => 4) n + 1) × Unit)
      (fun n p ω => Fres n p.2
        (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) n p.1)
        (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) n p.1 ω))
      (fun n p _ => Zres n p.2
        (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) n p.1)) := by
```

### Name clash, RBM2D drift
```
$ git --no-optional-locks grep -nwE "<the new public names of the file>" main -- RBM3D RBM3D.lean   (main = fa2ebc7; hits are text matches, not only declarations)
main:RBM3D/Defs/StochDomAt.lean:119:pin states `≺` through `Prec`, `PrecPT`, `PrecGrid` and `Whp`, never through another scale
(hit count:        1)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/Walk.lean RBM2D/Path/Transfer.lean
 RBM2D/Path/Transfer.lean | 102 +++-------------------------------------------
 RBM2D/Path/Walk.lean     | 104 +++++++++++++----------------------------------
 2 files changed, 35 insertions(+), 171 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h   # RBM2D HEAD
9e0f275
$ git diff --stat main...t/T2018
 RBM3D/Path/Walk.lean | 949 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 949 insertions(+)
$ git log --oneline -1 t/T2018
8eda4cd T2018: grid Gaussian walk on the path space (MD-4): transfer law, independent increments, per-time transfer
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Path/Walk.lean   # exit code below
exit 1
```

### Narrative (at most 40 lines)
- One new file `RBM3D/Path/Walk.lean` (949 lines), one commit `8eda4cd` on `t/T2018`; `git diff --stat main...t/T2018` lists only that file. `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are untouched: with the root import added temporarily, the full `lake build` exits 0 and its premise scan reports 13 premises (borrowed 5, owed 1, structural 7) and no unclassified one, so no `structuralProps` entry is added for `PrecGrid` or `GridTransferPT`.
- Item 1: probe lines 937-1035 are copied verbatim (file lines 43-141); the script diff is empty (`IDENTICAL (99 lines)`).
- Item 2: `RBM2D/Path/Walk.lean` at `c9a24cf` ported under rule R1; `pathH_isHermitian` is the probe's (pinned) proof, RBM2D's is not ported. After renaming and stripping docstrings the diff to RBM2D shows only a blank line, one wrapped line (line length) and nothing else. The private helpers (`measurable_seqXentry`, `pathH_apply`, `slice_*`, `seqXmat_*`, `sumIcc_map_gaussianReal`, `weightedSum_map_gaussianReal`, `map_column_eq`, `pathP'`, `swapEquiv`, `map_combined_eq`, `map_smul_eq`, ...) stay `private`; public names are RBM2D's: `gridTime_last`, `measurable_pathH`, `pathH_adapted`, `indep_incr`, `map_incr`, `indepIncr`, `map_pathH_eq`, `transferLaw`.
- The dimension `d` enters only through `Sizes d` (`Idx d (sz.L n) (sz.W n)`, `seqXmat`, `seqGvar`): the proof is coordinatewise on `SeqCoord sz` and uses `Xmat_add`, `Xmat_smul` (merged `RBM3D/Gauss/FineModel.lean`), `gaussianReal` sums, `iIndepFun_infinitePi`; no exponent or lattice sum is involved, so no `d = 2` fact is used.
- Item 3: `GridTransferPT`, `gridTransferPT` are identical to RBM2D `Transfer.lean:35-78` after renaming (script diff). `map_pathH_eq` does not use `hK : K n ≠ 0`; the signature is kept as in RBM2D and in the pin `TransferLaw` (linter warning only).
- Measurability helpers (RBM2D lines 84-150, re-expressed, public with stem prefix `walk_`): `walk_measurable_Gres_apply` (`Gsig` becomes the generic `Gres`), `walk_measurable_loopL` (induction on the list `loopL`, as RBM2D's `gloop`), `walk_measurable_blockMat`, `walk_measurable_loopFine` (`loopFine = loopL ∘ blockMat` by `loopM_eq_loopL`), and two new compositions with `seqHflow`: `Sizes.walk_measurable_Gt_apply`, `Sizes.walk_measurable_Lloop`. RBM2D lines 155-212 (`lkErrMat`, `jStarMat`, `llErrMat`) are not ported (ST tickets).
- Instances (all in the file, hypotheses discharged, `sz0`: `d = 3`, `N_0 = 2097152`): `transferLaw_sz0` (`s = 1/10`, `t = 1`, `K = 4`, `k = 2`, grid time `11/20`), `indepIncr_sz0` (`k = 2`), pins at `sz0`, `gridRes_prec` (`precGrid_of_le` on the resolvent entry of the walk), `gridTransferPT_sz0` (`gridTransferPT` applied at `F = ‖Gres M (zt (1/2) u) true 0 0‖`; the single-time premise is proved by `precPT_of_le` and the Ward bound `norm_inverse_entry_le`, the conclusion is the same domination on the walk). No `N = 0`, empty index or `False` premise; the parameter set is `Fin 5 × Unit`.
- `main` moved from `33049c0` (branch base) to `fa2ebc7` while this ticket ran; the name-clash grep was run on the current `main` (one hit: a docstring line of `StochDomAt.lean`, not a declaration).
- Hub: the root import to add after the last `import` line of `RBM3D.lean` is `import RBM3D.Path.Walk`.

## (c) Verified Mathlib names (all resolved by `lake build`; located in `.lake/packages/mathlib/Mathlib` by `grep -rl`)
- `Measurable.of_eval_matrix`, `Measurable.eval_matrix` (`Analysis/Matrix/MeasurableSpace.lean`); `Matrix.nonsing_inv_eq_ringInverse` (`LinearAlgebra/Matrix/NonsingularInverse.lean`); `Ring.inverse_eq_inv'` (`Algebra/GroupWithZero/Units/Basic.lean`); `Continuous.matrix_submatrix`, `Continuous.matrix_det`, `Continuous.matrix_adjugate` (`Topology/Instances/Matrix.lean`).
- `iIndepFun_infinitePi`, `iIndepFun_iff_iIndep`, `indep_of_indep_of_le_left`, `indep_biSup_compl`, `iIndepFun.indepFun_finsetSum_of_notMem` (`Probability/Moments/Basic.lean:361`), `Measure.infinitePi_map_eval`, `infinitePi_map_pi`, `infinitePi_map_curry`, `infinitePi_map_curry_symm`, `infinitePi_map_piCongrLeft`, `MeasureTheory.Filtration.piLE`, `gaussianReal_add_gaussianReal_of_indepFun`, `gaussianReal_map_const_mul` (as ported from RBM2D at `c9a24cf`, same Mathlib `v4.34.0`).
- Verified absent: none searched.

## (d) Open issues and paper-delta candidates
- No open issue. All three targets and the instances build; axioms are the three standard ones.
- Paper-delta candidates: none new. The Lean/paper differences of this file (the grid walk in place of the continuous-time `(MBM)`; single-time law elsewhere; one product space) are D21, cited and not re-proposed. Observation (not a statement difference): `map_pathH_eq` holds without `K n ≠ 0`; the hypothesis stays because the pinned `TransferLaw` carries it.

Verdict (prover, Sat Oct  3 03:24:46 UTC 2026): all targets (items 1, 2, 3) built and committed on `t/T2018` at `8eda4cd`; ready for audit.
