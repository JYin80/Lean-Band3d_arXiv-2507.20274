Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 21:56:26 UTC 2026

Source: RBM2D `Universality/GUEPhase/DuhamelA.lean` lines 1-1040 (`git -C ../RBM2D log -1 --format=%h` = 9e0f275). RBM3D facts read in worktree `RBM3D-wt/T2345` (HEAD b7d4b45). Notation: `η = |Im z|`, `N = (WL)^d`, `m = |I|` (loop length; `RBM.Loop.LoopIdx.length = a.length`, `Loop/TreeRep.lean:71`).

### (i) Exponent table

| # | Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | per-coordinate bound `(Re tr(A X_c))² ≤ 2(‖A_ij‖²+‖A_ji‖²)` | 2 | `(x+y)² ≤ 2(x²+y²)`, `X_c = E_ij(1 or i) + E_ji(1 or -i)`, `‖unit‖=1` (src 135-160) | equality at `x=y`; d-free |
| 2 | variance `gueUnitVar c = if c.2.1 = c.2.2.1 then 1 else 1/2` (`GUEPhase/Grid.lean:49`) | ≤ 1 | `≤ 1` used (src 199-215) | factor 2 off the diagonal |
| 3 | `vGue ≤ 8‖A‖_F²`: `Σ_{(i,j,b)} 2(‖A_ij‖²+‖A_ji‖²) = 4‖A‖²+4‖A‖²` (b sums 2 values) | 8 | = 8 | `A=1` (script): `vGue=N`, bound `8N` (factor 8); random `A` (N=64): 4225 vs 65052 |
| 4 | Ward identity `G G* = G* G = (2iη)^{-1}(G(z)-G(z̄))`, `c² = 1/(4η²)`; glued trace = loop of length `2m` (`1+r+(r+1)`, `r=m-1`) | `‖R_k‖_F² ≤ (1/4η²)·4·loopMax(2m) = η^{-2} loopMax(2m)` | 4 terms `±` each `≤ loopMax(2m)` | equality at `M=0, z=i, m=1` (script: 0.125 = 0.125) |
| 5 | cut-sum Cauchy-Schwarz `‖Σ_{k<m} R_k‖_F² ≤ m Σ_k ‖R_k‖_F²` | `m²` | `|range| = m` | `m=2` random M: 0.001389 vs 0.04659 |
| 6 | `gradMat = -Σ_k unblock(R_k)` (Leibniz + trace pairing with Hermitian `X`) | identity | Hermitian `M`, `Im z ≠ 0` (⇒ `blockMat M - w` unit for `w ∈ {z, z̄}`) | script trace identity err 5e-8, 1e-9 |
| 7 | `vGue(∇Φ)`, `vGue(-i∇Φ)` ≤ `8·m²η^{-2}loopMax(2m)` | 8 | rows 3-5; `‖-iA‖_F=‖A‖_F` | `M=0,m=1`: max vGue = 0.125, bound 1.0 |
| 8 | `card (Vtx d L W) = (L W)^d` (`card_BlockIndex`, `Gauss/FlowCalculus.lean:701`) — **d-line**, src `(L W)²` | exponent `d` (=3) | `L^d·W^d` (`Z_L^d × Fin(W^d)`) | script: 64 = 64 at `d=3, L=W=2` |
| 9 | `‖E_a‖ ≤ (W^d)⁻¹` (`norm_Eblk_le_inv_W_sq`, FlowCalculus:663) — **d-line**, src `(W⁻¹)² ≤ 1` | `(W^d)⁻¹ ≤ 1` | `W ≥ 1` (`NeZero W`) | `W^{-dm}` dropped in crude/shift; `1/8` per factor at `W=2,d=3` |
| 10 | crude: `‖loopL‖ ≤ card·(η⁻¹(W^d)⁻¹)^m ≤ (LW)^d η^{-m}` (`norm_gloop_le_crude`, FlowCalculus:708 gives this with `η = |Im z|`, `hz = le_rfl`) | `(LW)^d |Im z|^{-m}` | row 8, 9 | `m=0` equality (64=64); `m=2`: 0.125 vs 64 |
| 11 | shift: word difference `≤ l K^l Δ`, induction step `ΔK^l + K·lK^lΔ ≤ (l+1)K^{l+1}Δ` | needs `K ≥ 1`, `‖G(z)‖,‖G(z')‖ ≤ K` | `K^l ≤ K^{l+1}` iff `K ≥ 1`; `Δ = ‖z'-z‖K²` from `G(z')-G(z) = (z'-z)G(z')G(z)`; `σ=false` by adjoint (opnorm invariant) | `K=1`: induction slack 0; instance `m=2`: 0.03125 ≤ 128.125 |
| 12 | shift trace factor `card = (LW)^d` — **d-line**, src `(LW)²` (src 1025-1027) | exponent `d` | row 8 | same as 8 |
| 13 | `N = (WL)^d = card Idx` (`Sizes.size`, `Defs/Sizes.lean:157`); `card CoordF = 2N²` | `N = 2097152` at `sz0` (`L=4, W=32, d=3`; `card_Idx_sz0`, Sizes.lean:368) | appears only through `Σ_c` over `CoordF` (a finite sum, no cardinality used) | n/a |
| 14 | `S_GUE = 1/N` of (7.43) | **absent** from the seven statements (`grep -n "size\|card" DuhamelA.lean` on lines 1-1040: only `Finset.card`/`card_BlockIndex`, no `size`); `vGue` is the unit-GUE variance, `1/N` is applied by consumers | — | no hypothesis involves `N, W, L, λ` beyond `W ≥ 1`; constants 8, 1, 4 hold for all `L, W` |

**d = 2 token table of src §1-§4 (line → replacement).** `Sizes` → `Sizes d` with `{d}` and `sz.L n, sz.W n` (src 199, 842); `Idx L W` → `Idx d L W`; `BlockIndex L W` → `Vtx d L W`; `Z2 L` → `Zd d L`; `Coord L W` → **`CoordF d L W`** (RBM3D `Gauss.Coord`, `Gauss/Model.lean:87`, is `Vtx × Vtx × Bool`, not the coordinate of `Sizes.seqXmat`; `Sizes.SeqCoord sz = Σ n, CoordF …`, `Gauss/FineModel.lean:156`; `coordinateMatrix c = Xmat (Pi.single c 1)`, FineModel:384, `Xentry` FineModel:105, `idxKey_lt_or_eq_or_lt` FineModel:116); `Gsig M z σ` → `Gres M z σ`; `gloop L W M z I` → `loopL d L W M z I`; `Eblk L W` → `Eblk d L W`; `splitEquiv` → `splitEquiv d L W : Idx d L W ≃ Vtx d L W` (`Defs/Sizes.lean:87`), `blockMat d L W M = M.submatrix splitEquiv.symm splitEquiv.symm` (`Loop/GLoopFlow.lean:105`); `(L W)² → (L W)^d` (src 872, 882, 891, 970-976 statement, 1025-1027); `(W⁻¹)^2 ≤ 1` → `((W:ℝ)^d)⁻¹ ≤ 1` (src 864-869, 884-889). Every other line (src 1-860 except the above; Ward, Leibniz, QV, telescoping) is dimension-free.

**Twins of `Gauss/LoopEnvelope`, `Hierarchy/WardResolvent`, `Gauss/Envelope` names (file:line, from grep; whether each is in the import closure of the ticket's four imports is not checked here).**
`norm_Eblk_le_inv_W_sq d L W`, `norm_foldr_Gsig_Eblk_le`, `card_BlockIndex`, `norm_gloop_le_crude`, `norm_matrix_trace_le_card_mul`: `Gauss/FlowCalculus.lean:663, 673, 701, 708, 600` (public). `green_sub_green`, `green_sub_green_conj'`, `isUnit_sub_smul_one_of_im_ne_zero`: `Induction/ConArgDet.lean:73, 97, 380` (public; the first two in namespace `RBM`, the last in `RBM.Ind`). `Gres` true/false: public `cont_Gres_true_eq_green`/`cont_Gres_false_eq_green` (`Induction/ContinuityNet.lean:430, 434`), `ST_Gres_false` (`Induction/Step2Iterate.lean:1198`); `Gres_conjTranspose` is private (`Induction/Split.lean:250`). `Eblk_isHermitian` public (`Loop/GLoop.lean:66`); `Eblk_conjTranspose` private (`Split.lean:269`). `isHermitian_add_realSmul` ↦ `OneStep_isHermitian_add_realSmul` public (`Path/OneStep.lean:1264`). Re-derive (private elsewhere): `hasDerivAt_line` (`OneStep_hasDerivAt_line`, OneStep.lean:1255, 5 lines), `hasDerivAt_lineInverse` (`OUHessian_hasDerivAt_lineInverse`, `Universality/OUHessian.lean:98`, ~20 lines), `coordinateMatrix_apply` (no RBM3D theorem of that name; unfold `Xmat`/`Xentry`, ~10 lines).
Merged signatures against the source's uses: `vGue sz n A : ℝ≥0 = linVar (gueUnitVar sz) (fun c => linTr n A (seqXmat sz n (Pi.single c 1))) (coordFinset n)` (`GUEPhase/Markov.lean:291`, `Gauss/LinearForm.lean:130`, `linTr n A X = (tr(A X)).re` `Path/Markov.lean:134`) — same shape as the source; `gradMat Φ M` (`Path/StepDecomp.lean:80`) and `fderiv_eq_trace_gradMat` (:123) — same; `loopMax d L W H z n = ⨆ x, ‖loopL …‖` (`Induction/Split.lean:515`), `norm_gloop_le_loopMax` (:520), `loopMax_le` (:533, hypothesis `∀ I, σ.length = n → a.length = n → ‖loopL I‖ ≤ M`) — same.
**§29 (DECISIONS) items:** (1)(2) time domain, case-(ii) boundary: no time variable in the seven targets, n/a; (3) `L^d ≤ W^K`: not used (only `W ≥ 1`, `L ≠ 0`); (4) all seven are statements at one fixed `n`/one fixed `(d,L,W)`, no `∀ n` forced on a limit hypothesis; constants (8, 1, 4, `m²`) do not involve `W, L, λ`; (5)-(7) no time-uniformity, no `N→∞`, no `ℓ` scale: n/a.

### (ii) Concrete nondegenerate instance (script, all seven targets)

Data: `d=3, L=W=2` (fine lattice `Z_4^3`, `N=64`, `card Vtx = 64`), `M=0` (Hermitian), `z=i` (`Im z=1≠0`), `z'=2i`, `K=1` (`‖G(i)‖=1`, `‖G(2i)‖=1/2`), loop `I=([true],[a_0])` (`WF`, `m=1`, `k=0<1`); second instance `M` random Hermitian (script `Mh`, seed 1), `z=0.3+0.5i`, `I=([true,false],[a_0,a_3])`. For `Duhamel_vGue_le` at `sz0` (`L=4, W=32, d=3`, `n=0`) with `A=1`: `vGue(1)=N=2097152 ≤ 8N=16777216` (diagonal `true` coordinates contribute `1·1`, off-diagonal and `false`-diagonal traces vanish; the script checks the same identity at `N=64`). `Duhamel_contDiffAt_loop`: `M=0` Hermitian, `Im z≠0`, so `blockMat M - w` is a unit for `w∈{z,z̄}`; the map is a trace of a product of `Ring.inverse ∘ (affine)` and constants, smooth at units (no numeric check; the finite-difference trace-identity lines below confirm differentiability and the gradient). Ticket instance for `Duhamel_loopMax_le_crude` (`d=3, L=W=2, M=0, z=i`): all `m` rows below hold, `m=0` with equality 64 = 64.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2345/pre.py` (numpy; loops built as `tr ∏ Gres_σ E_a`, `E_a = W^{-d}1_{block a}`, `gradMat` from the definition at `Path/StepDecomp.lean:80` by central differences, `vGue` by the definition sum over all `(i,j,b)`).

```
card Vtx = 64 = (L*W)^d = 64 ; N=(W L)^d = 64
loopMax_le_crude  (M=0, z=i): m, loopMax, bound (LW)^d |Im z|^-m
0 64.0 64.0 True
1 1.0 64.0 True
2 0.125 64.0 True
3 0.015625 64.0 True
loopMax_shift_le (M=0, z=i, z'=2i, K=1): m, lm(z'), lm(z)+(LW)^d m K^m |z'-z| K^2
||G(z)||,||G(z')|| = 1.0 0.5 <= K = 1.0
1 0.5 65.0 True
2 0.03125 128.125 True
3 0.001953 192.015625 True
vGue(1) = 64.0  8||A||_F^2 = 512.0  (N = 64 )
vGue(random A) = 4225.158  <= 8||A||_F^2 = 65052.021
sz0 (L=4,W=32,d=3): N = 2097152  vGue(1) = N = 2097152  8N = 16777216
[M=0,n=1] trace identity |fderiv - tr(grad X)| = 5.1602754098367786e-08
[M=0,n=1] n = 1 ||grad||_F^2 = 0.125 <= n^2 eta^-2 loopMax(2n) = 0.125
[M=0,n=1] max(vGue(g), vGue(-i g)) = 0.125 ( 0.125 0.0 ) <= 8*that = 1.0
[M=0,n=1] cut block k = 0 ||R_k||_F^2 = 0.125 <= eta^-2 loopMax(2n) = 0.125
[M rand,n=2] trace identity |fderiv - tr(grad X)| = 9.803113204318364e-10
[M rand,n=2] n = 2 ||grad||_F^2 = 0.001389 <= n^2 eta^-2 loopMax(2n) = 0.04659
[M rand,n=2] max(vGue(g), vGue(-i g)) = 0.001389 ( 0.001389 0.0 ) <= 8*that = 0.372716
[M rand,n=2] cut block k = 0 ||R_k||_F^2 = 0.000883 <= eta^-2 loopMax(2n) = 0.011647
[M rand,n=2] cut block k = 1 ||R_k||_F^2 = 0.000883 <= eta^-2 loopMax(2n) = 0.011647
```

External hypotheses: none (no hypothesis of the seven targets is another gate's pin; `Sizes d` supplies `NeZero (sz.L n)`, `NeZero (sz.W n)` as instances, `Defs/Sizes.lean:152-153`). Observation for the prover: the pinned `loopMax_le_crude` instance at `m=0` is an equality case (bound `(LW)^d`), so an instance at `m = 2` (or `m=1`) shows the bound is nonvacuous with slack 512 / 64.

### Verdict
- `Duhamel_vGue_le`: PASS. `DuhamelLoopCut` (def) / `Duhamel_frobSq_loopCut_le`: PASS (equality case in script). `Duhamel_vGue_gradMat_le`: PASS. `Duhamel_loopMax_le_crude`: PASS. `Duhamel_loopMax_shift_le`: PASS (with `(LW)^d`). `Duhamel_contDiffAt_loop` (made public): PASS.
- Overall: PASS. No hypothesis set is empty, no exponent fails to close; the only d-dependent changes are rows 8, 9, 12 and the coordinate type `CoordF` (not `Coord`).

## (b) Script output — written Thu Oct  8 22:15:39 UTC 2026

### b1. Build, axioms, hygiene
```
$ lake build RBM3D.Universality.GUEPhase.DuhamelA1 2>&1 | grep -E "DuhamelA1.lean:[0-9]+:[0-9]+: .RBM.Univ.GUEPhase.(Duhamel_|DuhamelLoopCut)[A-Za-z_]*. depends|^Build completed|: error|warning: RBM3D/Universality/GUEPhase/DuhamelA1|^error" | sed -E "s#RBM3D/Universality/GUEPhase/##"; lake build RBM3D.Universality.GUEPhase.DuhamelA1 2>&1 | grep -c "DuhamelA1.lean.*depends on axioms: .propext, Classical.choice, Quot.sound."
info: DuhamelA1.lean:1252:0: 'RBM.Univ.GUEPhase.Duhamel_vGue_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1253:0: 'RBM.Univ.GUEPhase.DuhamelLoopCut' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1254:0: 'RBM.Univ.GUEPhase.Duhamel_frobSq_loopCut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1255:0: 'RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1256:0: 'RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1257:0: 'RBM.Univ.GUEPhase.Duhamel_loopMax_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DuhamelA1.lean:1258:0: 'RBM.Univ.GUEPhase.Duhamel_contDiffAt_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3780 jobs).
15
```
```
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/GUEPhase/DuhamelA1.lean; echo "grep rc=$?"; wc -l RBM3D/Universality/GUEPhase/DuhamelA1.lean; git branch --show-current; git log --oneline main..t/T2345; git diff --stat main...t/T2345; git status --short | grep -v "^??"; echo "(status rc=$?)"
grep rc=1
    1266 RBM3D/Universality/GUEPhase/DuhamelA1.lean
t/T2345
8b8401f T2345: DuhamelA1 (UN-36): DuhamelA sections 1-4 port, instances
6df051e T2345: DuhamelA1 sections 1-4 (checkpoint, instances pending)
 RBM3D/Universality/GUEPhase/DuhamelA1.lean | 1266 ++++++++++++++++++++++++++++
 1 file changed, 1266 insertions(+)
(status rc=1)
```

### b2. Target statements (extracted by script `stmt.py` from `RBM3D/Universality/GUEPhase/DuhamelA1.lean`)
```
$ python3 stmt.py src   # statement = declaration through `:=`
== RBM3D DuhamelLoopCut (DuhamelA1.lean:427)
def DuhamelLoopCut (d L W : ℕ) [NeZero L] (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) (k : ℕ) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
== RBM3D Duhamel_frobSq_loopCut_le (DuhamelA1.lean:434)
theorem Duhamel_frobSq_loopCut_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (Zd d L)} (hI : I.WF) {k : ℕ}
    (hk : k < I.length) :
    ∑ p, ∑ q, ‖DuhamelLoopCut d L W M z I k p q‖ ^ 2
      ≤ (|z.im|⁻¹) ^ 2 * RBM.Ind.loopMax d L W M z (2 * I.length) := by
== RBM3D Duhamel_loopMax_shift_le (DuhamelA1.lean:1053)
theorem Duhamel_loopMax_shift_le {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
    (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
    RBM.Ind.loopMax d L W M z' m
      ≤ RBM.Ind.loopMax d L W M z m
          + ((L : ℝ) * (W : ℝ)) ^ d * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
== RBM3D Duhamel_contDiffAt_loop (DuhamelA1.lean:797)
theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M') z I) M :=
```
```
$ (same extraction for the three pinned targets; `{d : N} (sz : Sizes d)` of `Duhamel_vGue_le` is the section variable at line 72)
== Duhamel_vGue_le (DuhamelA1.lean:206)
theorem Duhamel_vGue_le (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (vGue sz n A : ℝ) ≤ 8 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
== Duhamel_vGue_gradMat_le (DuhamelA1.lean:926)
theorem Duhamel_vGue_gradMat_le {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    max (vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
        (vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z I) M) : ℝ)
      ≤ 8 * ((I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2
          * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * I.length)) := by
== Duhamel_loopMax_le_crude (DuhamelA1.lean:955)
theorem Duhamel_loopMax_le_crude {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    RBM.Ind.loopMax d L W M z m ≤ ((L : ℝ) * (W : ℝ)) ^ d * (|z.im|⁻¹) ^ m := by
```

### b3. Check-file equality of the three pinned statements (ticket acceptance)
```
$ lake env lean pin_eq.lean   # = docs/tickets/checks/T2345-check.lean + import DuhamelA1 + the 3 examples below
open RBM.Univ.GUEPhase in
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_vGue_le := @RBM.Univ.GUEPhase.Duhamel_vGue_le
open RBM.Univ.GUEPhase in
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_loopMax_le_crude := @RBM.Univ.GUEPhase.Duhamel_loopMax_le_crude
open RBM.Univ.GUEPhase in
example : RBM.Univ.GUEPhase.T2345Check.T2345_Duhamel_vGue_gradMat_le := @RBM.Univ.GUEPhase.Duhamel_vGue_gradMat_le
pin_eq exit=0
0
```

### b4. Translation table of the four unpinned statements (RBM2D source with the port map applied vs RBM3D)
```
$ python3 stmt.py diff   # port map: Z2 L->Zd d L, BlockIndex L W->Vtx d L W, Idx L W->Idx d L W, Gsig->Gres, gloop L W->loopL d L W, Eblk L W->Eblk d L W, blockMat X->blockMat d L W X, loopMax L W->loopMax d L W, (L W : N)->(d L W : N)
== DuhamelLoopCut: RBM2D DuhamelA.lean:348 (port map applied) vs RBM3D DuhamelA1.lean:427
(identical after the port map)
== Duhamel_frobSq_loopCut_le: RBM2D DuhamelA.lean:355 (port map applied) vs RBM3D DuhamelA1.lean:434
(identical after the port map)
== Duhamel_loopMax_shift_le: RBM2D DuhamelA.lean:970 (port map applied) vs RBM3D DuhamelA1.lean:1053
--- 2D+map
+++ 3D
@@ -6 +6 @@
-          + ((L : ℝ) * (W : ℝ)) ^ 2 * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
+          + ((L : ℝ) * (W : ℝ)) ^ d * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
== Duhamel_contDiffAt_loop: RBM2D DuhamelA.lean:713 (port map applied) vs RBM3D DuhamelA1.lean:797
--- 2D+map
+++ 3D
@@ -1 +1 @@
-private theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
+theorem Duhamel_contDiffAt_loop {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L))
```
```
$ port citation: RBM2D commit and diff-stat; count of `d`-line occurrences in the file
9e0f275
(diff-stat: empty = HEAD is 9e0f275)
d-line occurrences: 9
```

### b5. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.DuhamelA1Inst`; extracted by script `inst2.py`)
```
$ python3 inst2.py   # file line: statement through `:=`, then the term
1141: theorem frobSq_one_sz0 : ∑ i, ∑ j, ‖(1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) i j‖ ^ 2 = 2097152 := by  [by-block]
1152: theorem vGue_le_inst :
    (vGue sz0 0 (1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) : ℝ)
      ≤ 8 * ∑ i, ∑ j, ‖(1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) i j‖ ^ 2 :=
  Duhamel_vGue_le sz0 0 1
1157: theorem vGue_le_inst_value : (vGue sz0 0 (1 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ) : ℝ) ≤ 8 * 2097152 := by  [by-block]
1164: theorem loopMax_le_crude_inst :
    RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 2
      ≤ (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ 3 * (|Complex.I.im|⁻¹) ^ 2 :=
  Duhamel_loopMax_le_crude (d := 3) (L := 2) (W := 2) Matrix.isHermitian_zero (by simp) 2
1171: theorem loopMax_zero_eq : RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 0 = 64 := by  [by-block]
1193: theorem loopMax_shift_le_inst :
    RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) (2 * Complex.I) 2
      ≤ RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I 2
          + (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ 3 * ((2 : ℕ) : ℝ) * (1 : ℝ) ^ 2
              * (‖2 * Complex.I - Complex.I‖ * (1 : ℝ) ^ 2) := by
  ...
  exact Duhamel_loopMax_shift_le (d := 3) (L := 2) (W := 2)
    (M := (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)) Matrix.isHermitian_zero
    (z := Complex.I) (z' := 2 * Complex.I) (by simp) (by simp) (K := 1) le_rfl
    (hG Complex.I (by simp)) (hG (2 * Complex.I) (by norm_num)) 2
1210: theorem loopCut_loop1 : DuhamelLoopCut 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I (DuhamelA1Inst_loop1 3 2) 0 = Gres (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I true * Eblk 3 2 2 0 * Gres (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I true := by  [by-block]
1219: theorem frobSq_loopCut_le_inst :
    ∑ p, ∑ q, ‖DuhamelLoopCut 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ) Complex.I
        (DuhamelA1Inst_loop1 3 2) 0 p q‖ ^ 2
      ≤ (|Complex.I.im|⁻¹) ^ 2 * RBM.Ind.loopMax 3 2 2 (0 : Matrix (Vtx 3 2 2) (Vtx 3 2 2) ℂ)
          Complex.I (2 * (DuhamelA1Inst_loop1 3 2).length) :=
  Duhamel_frobSq_loopCut_le Matrix.isHermitian_zero (by simp) (DuhamelA1Inst_loop1_wf 3 2)
    (by simp [DuhamelA1Inst_loop1, LoopIdx.length])
1228: theorem vGue_gradMat_le_inst :
    max (vGue sz0 0 (gradMat (fun M' : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M') Complex.I
            (DuhamelA1Inst_loop1 3 (sz0.L 0))) 0) : ℝ)
        (vGue sz0 0 (-Complex.I • gradMat (fun M' : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M') Complex.I
            (DuhamelA1Inst_loop1 3 (sz0.L 0))) 0) : ℝ)
      ≤ 8 * (((DuhamelA1Inst_loop1 3 (sz0.L 0)).length : ℝ) ^ 2 * (|Complex.I.im|⁻¹) ^ 2
          * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0)
              (blockMat 3 (sz0.L 0) (sz0.W 0) (0 : Matrix DuhamelA1Inst_Idx0 DuhamelA1Inst_Idx0 ℂ))
              Complex.I (2 * (DuhamelA1Inst_loop1 3 (sz0.L 0)).length)) :=
  Duhamel_vGue_gradMat_le (sz := sz0) (n := 0) (by simp) (DuhamelA1Inst_loop1_wf 3 _)
    Matrix.isHermitian_zero
1243: theorem contDiffAt_loop_inst :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ =>
      loopL 3 2 2 (blockMat 3 2 2 M') Complex.I (DuhamelA1Inst_loop1 3 2)) 0 :=
  Duhamel_contDiffAt_loop (z := Complex.I) (by simp) _ Matrix.isHermitian_zero
```

### b6. Registry pre-check and full build
```
$ lake env lean registry.lean   # temporary, uncommitted, in the scratchpad
import RBM3D
import RBM3D.Universality.GUEPhase.DuhamelA1
#assert_rbm_axioms
registry exit=0
axiom audit: 10391 theorems, 3060 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```
```
$ lake build   # full library in the worktree; last lines
Build completed successfully (4158 jobs).
full lake build exit=0
Thu Oct  8 22:12:49 UTC 2026
```

### b7. Name-clash grep (new public names; `RBM3D/` outside `Probe/`)
```
$ cd main worktree (branch main): grep -rnE "<7 target names>|DuhamelA1Inst" RBM3D --include=*.lean -l | grep -v ^RBM3D/Probe
rc=1
```
```
$ same grep in the T2345 worktree; then every non-private top-level declaration of the file
RBM3D/Universality/GUEPhase/DuhamelA1.lean
206 Duhamel_vGue_le;427 DuhamelLoopCut;434 Duhamel_frobSq_loopCut_le;797 Duhamel_contDiffAt_loop;926 Duhamel_vGue_gradMat_le;955 Duhamel_loopMax_le_crude;1053 Duhamel_loopMax_shift_le;1141 frobSq_one_sz0;1152 vGue_le_inst;1157 vGue_le_inst_value;1164 loopMax_le_crude_inst;1171 loopMax_zero_eq;1193 loopMax_shift_le_inst;1210 loopCut_loop1;1219 frobSq_loopCut_le_inst;1228 vGue_gradMat_le_inst;1243 contDiffAt_loop_inst;
```
```
$ RBM2D helper names with no public RBM3D twin (anchored at line start, so `private` ones are not matched)
rc=1 (1 = no top-level non-private RBM3D declaration of these RBM2D names)
```

Narrative (facts from the files and the logs above; at most 40 lines).
1. Source: RBM2D `Universality/GUEPhase/DuhamelA.lean:68-1036` (sections 1-4) at commit 9e0f275 (b4: diff-stat HEAD vs 9e0f275 empty). Target `DuhamelA1.lean` (b1: 1266 lines, stop size 1600; 1114 lines at the sections 1-4 checkpoint commit 6df051e): sections 1-4 at lines 70-1113, instances 1115-1248, `#print axioms` 1252-1266.
2. The preflight token table was applied by a script (`conv.py`, scratchpad), then each compile error was fixed by hand. Final file: no warning from `DuhamelA1.lean` (b1 grep), no `sorry`/`admit`/`native_decide`/`axiom` (b1 grep rc=1).
3. `d`-lines (b4 count; statements in b2/b4): crude bound `(L W)^d` (`Duhamel_loopMax_le_crude`, via the merged `norm_gloop_le_crude d L W`), `‖E_a‖ ≤ (W^d)⁻¹ ≤ 1` (`Duhamel_norm_Eblk_le_one`, `one_le_pow₀`), shift bound `(L W)^d` with `card_BlockIndex d L W`. Coordinates are `CoordF d L W` (`Gauss.Coord` is the block coordinate, not that of `Sizes.seqXmat`).
4. Re-derived as private twins (at most 15 lines each, as the ticket allows): `Duhamel_Gres_true/false/conjTranspose` (source `Gsig_*`), `Duhamel_hasDerivAt_line`, `Duhamel_hasDerivAt_lineInverse`, `Duhamel_coordinateMatrix_apply` (`rfl`), `Duhamel_Eblk_conjTranspose` (from the public `Eblk_isHermitian`), `Duhamel_loopL_eq` (`rfl`), `Duhamel_getD_eq` (c: Mathlib `List.getD_eq_getElem` lives in `Mathlib/Data/List/GetD.lean`, which is not in the import closure; the twin uses the core `List.getD_eq_getElem?_getD`).
5. Reused public merged names: `green_sub_green`, `green_sub_green_conj'` (`Induction/ConArgDet.lean:73, 97`), `isUnit_sub_smul_of_isHermitian` (`Analysis/Resolvent.lean:132`, instead of `isUnit_sub_smul_one_of_im_ne_zero`), `OneStep_isHermitian_add_realSmul`, `Eblk_isHermitian`, `norm_Eblk_le_inv_W_sq`, `norm_gloop_le_crude`, `norm_matrix_trace_le_card_mul`, `card_BlockIndex`, `Ind.loopMax_le`, `Ind.norm_gloop_le_loopMax`, `fderiv_eq_trace_gradMat`.
6. Import added beyond the ticket's four: `RBM3D.Induction.ConArgDet` (for `green_sub_green(_conj')`; it imports `Induction.Split`, `Loop.GLoop`, `Green.EntryCore`, `Mathlib.Algebra.Order.Chebyshev`: `grep "^import"` of that file). Nothing else; never `RBM3D`.
7. Proof-level changes only: the source's simp lemmas `Gsig_true/false` become explicit `simp only [Duhamel_Gres_true, Duhamel_Gres_false]` after `cases`; in `Duhamel_loopMax_shift_le` the transposition facts `hF`, `hGd`, `hGn` are restated through `green`. No hypothesis added, weakened or reordered; the four unpinned statements equal the source's after the port map except the `d`-line and `private` (b4); the three pinned ones are definitionally the check file's (b3).
8. Instances (b5): `Duhamel_vGue_le` at `sz0`, `n = 0`, `A = 1` (value `‖1‖_F² = 2097152`, `frobSq_one_sz0`); `Duhamel_loopMax_le_crude` at `d = 3`, `L = W = 2`, `M = 0`, `z = i`, `m = 2`, and `loopMax_zero_eq` shows `loopMax … 0 = 64 = (2·2)^3`, so the bound is attained at `m = 0` and the data are not vacuous. The other five targets have instances at the same kind of data (`sz0` for `Duhamel_vGue_gradMat_le`; `d = 3`, `L = W = 2` for the rest; shift at `z' = 2 i`, `K = 1`, hypotheses `‖G‖ ≤ K` discharged by the merged `norm_Gsig_le_inv_eta`). Every deterministic hypothesis is discharged; none is another gate's pin.
9. Statements are about the unit-GUE variance `vGue`; `S_GUE = 1/N` of (7.43) does not occur in them (`gueH` carries `√(Δ/N)`, `GUEPhase/Grid.lean:77`).

## (c) Verified names (compiled in the file; `#check` run in the scratchpad `names.lean`)
```
$ lake env lean names.lean   # names only (full signatures in the tool log)
@Matrix.nonsing_inv_eq_ringInverse ;@Matrix.conjTranspose_nonsing_inv ;@Matrix.l2_opNorm_conjTranspose ;@Matrix.isHermitian_zero ;@Matrix.trace_one ;@Matrix.submatrix_mul_equiv ;@Matrix.trace_mul_single ;@List.getD_eq_getElem?_getD ;@List.zip_append ;@hasFDerivAt_ringInverse ;contDiffAt_ringInverse ;@Ring.inverse_unit ;@sq_sum_le_card_mul_sum_sq ;@Finset.sum_ite_eq ;@one_le_pow₀ ;@inv_le_one_of_one_le₀ ;@isUnit_sub_smul_of_isHermitian ;@OneStep_isHermitian_add_realSmul ;/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2345/names.lean;
```
Verified absent from the import closure: `List.getD_eq_getElem` (error `unknown identifier` in `names.lean`; Mathlib declares it at `Mathlib/Data/List/GetD.lean:33`, module not imported); `coordinateMatrix_apply`, `Gsig_true`, `Gsig_false`, `Gsig_conjTranspose` (b7 grep: no public RBM3D declaration).

## (d) Open issues and paper-delta candidates
- T2345a (documentation, no mathematical difference): the seven statements bound the unit-GUE variance `vGue`; the `S_GUE = 1/N` normalisation of (7.43) is not in them and is applied by the consumers (`gueH` has `√(Δ/N)`, `GUEPhase/Grid.lean:77`; source docstring `DuhamelA.lean:236`).
- T2345b: `Duhamel_contDiffAt_loop` is public here (`private` in the source, `DuhamelA.lean:713`); T2346 (`DuhamelA2`) may switch to it in a follow-up (ticket: not required).
- T2345c: `d`-lines `(L W)^2 -> (L W)^d`, `(W^{-1})^2 -> (W^d)^{-1}` (b4); `Coord L W -> CoordF d L W` (b2, narrative 3). Port-map entries, not mathematical deltas.
- Preflight (a): no correction needed; (a) left the import closure of the twins unchecked, resolved in narrative 5-6 (one added import, `Induction/ConArgDet.lean`).
- No open issue; no hypothesis is left open in any instance; the full `lake build` and the registry pre-check pass (b6). The audit has not been run by this stage.
