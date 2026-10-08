Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 22:06:47 UTC 2026

Sources: RBM2D `Universality/GUEPhase/EntryGrid.lean` (HEAD `9e0f275`, 902 lines) against the worktree `t/T2347` at `0e53fe5`. Scripts: scratchpad `T2347/inst.py`, `T2347/reuse.sh`. Nothing below is Lean.

### (i) Exponent table, d-lines, reuse table, merged-signature table

Exponents and constants (instance values at `sz0`, `d = 3`, `n = 0`; `N = sz.size n = (W L)^d`):

| quantity | value / form | constraint | slack |
|---|---|---|---|
| `d` | `d ≥ 3` (instance `3`) | `gueEntryMix (hd : 3 ≤ d)` (EntryTailMain:545); `2 ≤ N` needs only `d ≥ 1`, `W ≥ 1`, `L ≥ 3` | `N ≥ 3` for all `d ≥ 1` |
| `N_n` (instance) | `2^21 (n+1)^18` | `N ≥ 2`, `N+1 ≤ N^2`, `∀ n` (`gueEntryMix` needs `K n ≤ N^n0` for all `n`) | `n=0`: `N+1 = 2097153 ≤ N^2 = 4.4e12` |
| `m = 64 n0 + 128` | `n0=1`: `192` | `K_n = (N+1)^(32 n0+64) ≤ (N^2)^(32 n0+64) = N^m` | `n=0`: `K_0` has 607 digits (`log10 K_0 ≈ 606`) vs `m log10 N ≈ 1214` (script) |
| tail exponent fed to `gueEntryMix` | `D' = D + 1 + m` | `D' > 0` (since `D > 0`) | `D' > 193` |
| union arithmetic | `(K+1) N^{-(D+1+m)} ≤ N^{-D}` | `K ≤ N^m`, `N ≥ 2`: `(K+1) ≤ 2 N^m`, `2 N^{-(D+1)} ≤ N^{-D}` | factor `1 - 2/N = 0.99999905` at `n=0` |
| `c₀`, `δ_n` | `c₀ = 1/4`, `δ_n = N^{-1/4}` | `0 < c₀`, `0 ≤ δ_n`, `δ_n ≤ N^{-c₀}` eventually | equality (allowed); `δ_0 = 0.02628` |
| `W^{-d}` (threshold term) | `(W^d)^{-1}` (RBM2D: `(W^2)^{-1}`) | must equal the term in `GUEEntryMix` (EntryTail:106-110) | `n=0`: `3.05e-5` |
| `κ`, `E_n` | `κ = 1`, `E ≡ 0` | `|E_n| ≤ 2 - κ`, so `|E| ≤ 2` (zero-time lemma, `Im z_u > 0`) | `|E| = 0 ≤ 1` |
| `t₁, t₀` | `t₁ = e^{-1/20}·9/10 = 0.856106`, `t₀ = 9/10` | `0 ≤ t₁ ≤ t₀ < 1` (§29(1)), all `n` (as source) | `t₀ < 1` by `0.1`; `t₀ - t₁ = 0.0439` |
| `K` in `map_gueH_eq_mixMat` | `fun _ => 4` (no constraint on `k`) | `Δ = (t₀-t₁)/K ≥ 0` | `Δ = 0.010973` |
| `(a_k, b_k)` fed to `gueEntryMix` | `u_k>0`: `(t₁, u_k - t₁)`; `u_k = 0`: `(1/2, 0)` | `a,b ≥ 0`, `0 < a+b < 1` for `k ≤ K_n`; needs `u_k ≤ t₀ < 1` (`gridTime_last`, Walk:160, `K_n ≠ 0` by `gueGridK_ne_zero`, Grid:108) | script lines `k=0..4` |
| `Im z_u` | `(1-u) Im m(E) > 0` | `u < 1`, `|E| ≤ 2 - κ` | `0.1000` at `u = t₀` |
| variance identity | `gueUnitVar / N = gueVar d L W` (`1/N`, `1/(2N)`), `t₁ gvarF + k (Δ/N) gueUnitVar = mixVar (sz.lam n) t₁ (kΔ)` | `gridTime k - t₁ = kΔ` | exact (script) |
| admissibility (merged `sz0_admissible`, Defs/Sizes.lean) | `(𝔠,𝔡) = (1/6, 1/10)` | `W ≥ N^{1/6}`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`; `N → ∞` | `n=0`: `11.31 ≤ 32`; `0.0078125 ≤ 0.015625 ≤ 10` |

Targets restated only as far as the table needs: `map_gueH_eq_mixMat` (`Pgue.map gueH_k = ouP.map (mixMat t₁ (u_k - t₁))`, hypotheses `0 ≤ t₁ n ≤ t₀ n`, any `k`); `gueGrid_entry_bound` (Lemma 4.1 (4.2)+(4.3) on the grid, `StochDomAt (Pgue sz) sz.size`, `ζ = gueLmax _ 2 + (W^d)^{-1}`); `EntryGrid_var`, `EntryGrid_map_gueH`, `EntryGrid_pgue_preimage` as steps.

**d = 2 token table (source line : token : RBM3D replacement).**

| source lines | token | replacement |
|---|---|---|
| 379-383 | `d.size n = (W L)^2` (`rfl`), `RBM.Endpoints.gueVar (d.L n) (d.W n)`, `Coord` | `(W L)^d`, `gueVar d (sz.L n) (sz.W n)` (Universality/Pins.lean:61, namespace `RBM.Univ`), `CoordF d _ _`; still `rfl`/`unfold Sizes.size` |
| 395-397, 405-408, 423 | `d : Sizes`, `Coord`, `Xmat (d.L n) (d.W n)`, `Sizes.seqGvar d` | `sz : Sizes d`, `CoordF`, `Xmat d (sz.L n) (sz.W n)`, `Sizes.seqGvar sz` |
| 440-441, 453-455, 484-485 | `ouP (L) (W)`, `mixMat (L) (W) a b`, `mixSample (L) (W) a b` | `ouP (UNModel.band sz) n`, `mixMat sz n a b`, `mixSample sz n a b` (EntryTail:54, 120); `mixSample_law sz n ha hb` has RHS `gaussLaw d _ _ (mixVar d _ _ (sz.lam n) a b)` (:268) |
| 447-450 | `Sizes.size_eq` (private in RBM3D) | `unfold Sizes.size` + `positivity` (`sz.W_pos`, `sz.three_le_L`, Defs/Sizes.lean:145-146) |
| 468-469 | `gvar` (rfl), `mixEntry_mixVar_coe (L) (W) ht1 hb c` | `gvarF d _ _ (sz.lam n) c` (rfl), `mixEntry_mixVar_coe d _ _ (sz.lam n) ht1 hb c` (EntryTail:301): extra explicit args `d`, `g` |
| 512, 584, 607-609 | `spectralZ`, `spectralM`, `spectralM_mul` | `zt`, `mE`, `mE_mul` (Semicircle:49; `spectralM_mul` Gauss/FlowCalculus:85); `zt E 0 = E + mE E` by `simp [zt]` |
| 518-520 | `Z2 L`, `GoodEvent_measurable_gloop (pmLoop a b)` | `Zd d L`; `walk_measurable_loopFine d L W (zt E u) ![true,false] ![a,b]` (Path/Walk.lean:794; `loopPM` unfolds to `loopFine`, Pins:78) |
| 536, 553, 556, 629, 755-799, 831 | `((W:ℕ):ℝ)^2)⁻¹` | `((W:ℕ):ℝ)^d)⁻¹` (matches `GUEEntryMix` EntryTail:106-110) |
| 581-586 | `‖(green M z - m•1) i j‖ = llErrMat` by `rfl`-type unfolding | RBM3D `llErrMat` is `‖Gres M (zt E u) true i j - ite‖` (Pins:73): one rewrite `RBM.Ind.Gres_eq_green_zSig` (ConArgDet:367, `zSig z true = z`); `gueDev` (Proc:83) and the target still use `green` |
| 588-593 | `maxLoopPM ≤ loopMax L W (blockMat M) z 2`, `norm_gloop_le_loopMax (pmLoop ..)` | `loopMax d L W (blockMat d L W M) (zt E u) 2`; twin `Proc_maxLoopPM_le_loopMax` is `private` (Proc:523): re-derive (8 lines: `simp only [loopPM, loopFine, loopM_eq_loopL]`, `norm_gloop_le_loopMax (loopOf ![true,false] ![a,b])`, Split:520) |
| 612-617 | `green 0 z = m•1` | `Gres 0 (zt E 0) true = mE E • 1` for index `Idx d L W`: twin `gres_zero_true` is `private` (Pins:1181), `greenBlk_time_zero` is on `Vtx` only: re-derive (12 lines, as Pins:1181-1191) |
| 703-716 | `2 ≤ size` by `nlinarith` on `(W L)^2` | `2 ≤ (W L)^d` from `3 ≤ W L` and `d ≥ 1` (`Nat.le_self_pow`/`hd`); `gueGridK_le` same (dimension-free) |
| 719-746 | union arithmetic | dimension-free; unchanged |
| 812, 834 | `Admissible 𝔠 d`, `h𝔠`, `gueEntryMix 𝔠 h𝔠 d hadm ...` | `(hd : 3 ≤ d) (hadm : sz.Admissible 𝔠 𝔡)`, `gueEntryMix hd 𝔠 𝔡 sz hadm κ hκ E hE (64*n0+128) ...` (EntryTailMain:545 + EntryTail:94-110); `h𝔠` is `hadm.1`. Statement delta candidate `T2347a`: `hd` and `𝔡` added, `h𝔠` dropped, `W^{-2} ↦ W^{-d}` |
| not in the source | `GoodEvent_*`, `Kn` of `Loop/Kcal` | `GoodEvent_measurable_gloop` is the only RBM2D `Path.GoodEvent` use (:520); `Kn` is a local variable name (`union_arith`, :719): nothing to translate |

**Reuse table** (source `EntryGrid_X` at source line ↦ merged `GUEPhaseGrid_X` in `Grid.lean`, all `private` there). Port directly (needs `private` deleted): `seqXmat_add` (60 ↦ 128), `seqXmat_smul` (65 ↦ 133), `seqXmat_sum` (70 ↦ 138), `real_smul_matrix` (77 ↦ 145), `map_combined_eq_mixed` (282 ↦ 428), `Pgue_eq_mixed` (326 ↦ 473), `map_slice_infinitePi` (337 ↦ 484), `measurable_Xmat` (369 ↦ 516) — 8 declarations; the 8-declaration list is what `EntryGrid_map_gueH` (src :402-430) calls. Stay private (only inside those proofs): `slice_add/smul/sum` (117, 120, 123), `mixedStepMeasure` (231), `mixedRawStep` (236), `mixedRawStep_isProbabilityMeasure` (240), `mixedStepMeasure_eq` (245), `mixedStepMeasure_isProbabilityMeasure` (250), `mixedRaw` (256), `swapEquiv` (261), `measurable_swapEquiv` (267), `swapEquiv_apply` (274), `mixedRaw_swap_eq` (291), `sumIcc_map_gaussianReal_mixed` (327), `weightedSum_map_gaussianReal_mixed` (362), `map_column_eq_mixed` (404). Risk not checkable here (no Lean in this stage): the statements of `Pgue_eq_mixed`/`map_combined_eq_mixed` mention the private def `mixedStepMeasure`; if stage 1b meets an error, delete `private` on that def too and list it. Port with no twin (re-derive locally, private `EntryGrid_` prefix): `measurable_inv_apply`, `measurable_llErrMat`, `measurable_maxLoopPM`, `badMat`, `measurableSet_badMat`, `norm_green_sub*`, `maxLoopPM_le`, `green_zero`/`spectral_zero`, `zero_not_mem_badMat`, grid-time lemmas, `a/b/params`, `two_le_size`, `gridK_le`, `union_arith`, `pointwise`, `var`, `map_gueH`, `gueUnitVar_div`, and the targets.

**Merged signatures against the source's uses.** `gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d` (EntryTailMain:545), `GUEEntryMix d := ∀ 𝔠 𝔡, ∀ sz, sz.Admissible 𝔠 𝔡 → ∀ κ>0, ∀ E, (∀ n,|E n| ≤ 2-κ) → ∀ n0 K, (∀ n, K n ≤ (sz.size n)^n0) → ∀ a b : ∀ n, Fin (K n+1) → ℝ, (∀ n k, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a+b ∧ a+b < 1) → ∀ c₀ δ, 0<c₀ → (∀ n, 0 ≤ δ n) → (∀ᶠ n, δ n ≤ N^{-c₀}) → ∀ τ D, 0<τ → 0<D → ∀ᶠ n, ouP (UNModel.band sz) n {ω | ∃ k i j, N^τ (maxLoopPM d L W (E n) (a+b) (mixMat sz n a b ω) + (W^d)⁻¹) < (if ∀ x y, llErrMat … ≤ δ n then llErrMat … i j ^ 2 else 0)} ≤ ofReal (N^{-D})` (EntryTail:94-111): same argument order as RBM2D's call with `d` ↦ `hd`, `sz`, `𝔡`; event shape identical to `EntryGrid_badMat` preimage after `hab`, `ha`, `hb`. `mixMat sz n a b ω = √a • seqXmat sz n ω.1 + √b • Xmat d _ _ ω.2` (EntryTail:54); `mixMat_eq_Xmat_mixSample` (:135), `measurable_mixMat` (:145), `measurable_mixSample` (:126) exist.

**§29 (and §45 O2 items 5-7), one line each.** (1) `0 ≤ t₁ ≤ t₀ < 1`, `∀ n` as in the source; no bound forced on small `n` beyond these. (2) boundary `1 - ilambda²/L²`: not used. (3) `L^d ≤ W^K`: not used by the targets (consumed inside the merged `gueEntryMix`). (4) `hE, ht1, ht10, ht0, hδ0` are `∀ n` (as source and as `gueEntryMix`); `hδ`, `Admissible` (`Bandwidth`, `WO`) are `∀ᶠ n`. (5) union over `k ≤ K_n` and `i, j` is inside the probability (`StochDomAt`, uniform in `k`). (6) `N → ∞`, `W ≥ N^𝔠`, `(eq:WO)` are supplied by `sz.Admissible 𝔠 𝔡`. (7) scale `N^τ ζ`, `StochDomAt` with `size = sz.size`.

### (ii) One concrete nondegenerate instance

Data: `sz0` (merged `RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `n = 0`: `L=4, W=32, N=2097152`), `(𝔠,𝔡) = (1/6, 1/10)`, `κ = 1`, `E ≡ 0`, `t₀ ≡ 9/10`, `t₁ ≡ e^{-1/20}·9/10`, `c₀ = 1/4`, `δ_n = N^{-1/4}`, `n0 = 1` (`K_n = (N+1)^{96}`, which occurs only in the conclusion, never as a hypothesis witness). `map_gueH_eq_mixMat` at `n = 0`, `K ≡ 4`, `k = 2`. No `N = 0`, no empty index (`Idx 3 4 32` has `N` points), no collapsed window (`t₀ - t₁ = 0.0439 > 0`, `Δ > 0`), `u_k ∈ (0,1)`.
External-hypothesis check (`Admissible`, merged `sz0_admissible`, proved): limits `N_n = 2^21 (n+1)^18 → ∞`; `N^{1/6}/W = 2^{-3/2} (n+1)^{-2} ≤ 1`; `W^{-7/5}/lam = (2(n+1))^{-1} ≤ 1` and `lam ≤ 1/64 ≤ 10`, `lam → 0`.

```
$ cd scratchpad/T2347 && python3 -I inst.py
n=0: L,W,N,lam = 4 32 2097152 0.015625
n<200: N formula, Bandwidth, WO, N>=2, N+1<=N^2 : True
n=0 slack: N^(1/6)=11.3137 <= W=32 ; W^(-7/5)=0.007813 <= lam=0.015625 <= 10
limits: N_n=2^21(n+1)^18 -> inf; N^(1/6)/W = 2^-1.5 (n+1)^-2 <=1; W^(-7/5)/lam=(2(n+1))^-1 <=1; lam->0
t1=0.856106 t0=0.90 Delta=0.010973  0<=t1<=t0<1: True  t1<t0: True
 k=0 u_k=0.856106 a=0.856106 b=0.000000 a,b>=0,0<a+b<1: True  Im z_u=0.1439>0: True
 k=1 u_k=0.867080 a=0.856106 b=0.010973 a,b>=0,0<a+b<1: True  Im z_u=0.1329>0: True
 k=2 u_k=0.878053 a=0.856106 b=0.021947 a,b>=0,0<a+b<1: True  Im z_u=0.1219>0: True
 k=3 u_k=0.889027 a=0.856106 b=0.032920 a,b>=0,0<a+b<1: True  Im z_u=0.1110>0: True
 k=4 u_k=0.900000 a=0.856106 b=0.043894 a,b>=0,0<a+b<1: True  Im z_u=0.1000>0: True
last grid time u_K == t0: True ; |E|=0 <= 2-kappa=1: True
n0=1: m=192, K_0 has 607 digits; K_0 <= N^m: True
D=2: (K+1) N^-(D+1+m) <= N^-D  <=>  K+1 <= N^(m+1): True ; log10[(K+1)/N^(m+1)] = -613.2
slack 1-2/N = 0.999999046
K_n<=N^m for n<200: True
delta_0=N^-1/4=0.026278<=N^-c0 (equality); W^-d=3.052e-05
 diag=True unit/N==gueVar: True ; var identity: True
 diag=False unit/N==gueVar: True ; var identity: True
```

The ticket's `Grid.lean` §`GridCheck` data (`sz0`, `t₀ = 9/10`, `t₁ = e^{-1/20}·9/10`, `K ≡ 4`) is the same as above, so the instances `map_gueH_eq_mixMat` and `gueGrid_entry_bound` can reuse `GridCheck.t1_pos` (`0 ≤ t₁`, Grid.lean:800) and `SizesInst.sz0_admissible`; `t₁ ≤ t₀` is `e^{-1/20} ≤ 1`, `t₀ < 1` is `norm_num`.

### Verdicts

- `EntryGrid_var`, `EntryGrid_map_gueH`, `map_gueH_eq_mixMat`, `EntryGrid_pgue_preimage`: PASS (hypotheses hold at the instance; identities checked; every needed merged name exists, with the re-derivations listed above).
- `gueGrid_entry_bound`: PASS, with the signature change `T2347a` (`hd : 3 ≤ d` and `𝔡` added, `h𝔠` dropped, `W^{-2} ↦ W^{-d}`), all forced by the merged `gueEntryMix`/`GUEEntryMix`; the exponent `D ↦ D + 1 + 64 n0 + 128` closes with slack `1 - 2/N`.
- Overall: PASS.

## (b) Script output - Thu Oct  8 22:25:05 UTC 2026

```
$ git log --oneline -1 ; wc -l EntryGrid.lean ; for c in $(git rev-list --reverse main..t/T2347); do git show $c:$F | wc -l; done
30a4956 T2347: instance helpers private
     726
     175      453      610      726      726 (lines at the section commits, stop line 1100)
$ lake build RBM3D.Universality.GUEPhase.EntryGrid 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3759 jobs).
$ lake build 2>&1 | tail -1   (full library; started 22:25:07 UTC)
Build completed successfully (4158 jobs).
(finished 22:25:09 UTC)
$ lake env lean axioms.lean   (#print axioms of the targets and instances)
EntryGrid_var : [propext, Classical.choice, Quot.sound]
EntryGrid_map_gueH : [propext, Classical.choice, Quot.sound]
map_gueH_eq_mixMat : [propext, Classical.choice, Quot.sound]
EntryGrid_pgue_preimage : [propext, Classical.choice, Quot.sound]
gueGrid_entry_bound : [propext, Classical.choice, Quot.sound]
EntryGridInst.gueGrid_entry_bound_sz0 : [propext, Classical.choice, Quot.sound]
$ lake env lean registry.lean   (import RBM3D + import ...EntryGrid + #assert_rbm_axioms; uncommitted scratch)
exit=0
axiom audit: 10388 theorems, 3060 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -n "sorry\|admit\|native_decide\|^axiom" EntryGrid.lean | wc -l
       0
```

Target statements, extracted by script (`python3 -I extract.py <names>`):
```lean
-- RBM3D/Universality/GUEPhase/EntryGrid.lean:76-76
def EntryGrid_var (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (c : CoordF d (sz.L n) (sz.W n)) : ℝ≥0 :=
-- RBM3D/Universality/GUEPhase/EntryGrid.lean:83-87
theorem EntryGrid_map_gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    (Pgue sz).map (gueH sz t1 t0 K n k) =
      (Measure.infinitePi
        (fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0 (EntryGrid_var sz t1 t0 K n k c))).map
        (Xmat d (sz.L n) (sz.W n)) := by
-- RBM3D/Universality/GUEPhase/EntryGrid.lean:118-122
theorem map_gueH_eq_mixMat (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n) :
    (Pgue sz).map (gueH sz t1 t0 K n k) =
      (ouP (UNModel.band sz) n).map
        (mixMat sz n (t1 n) (gridTime t1 t0 K n k - t1 n)) := by
-- RBM3D/Universality/GUEPhase/EntryGrid.lean:162-168
theorem EntryGrid_pgue_preimage (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ht1 : 0 ≤ t1 n)
    (ht10 : t1 n ≤ t0 n)
    {B : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    (hB : MeasurableSet B) :
    Pgue sz (gueH sz t1 t0 K n k ⁻¹' B) =
      ouP (UNModel.band sz) n
        (mixMat sz n (t1 n) (gridTime t1 t0 K n k - t1 n) ⁻¹' B) := by
-- RBM3D/Universality/GUEPhase/EntryGrid.lean:518-537
theorem gueGrid_entry_bound (hd : 3 ≤ d) {𝔠 𝔡 κ : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ)
    (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) {δ : ℕ → ℝ} (hδ0 : ∀ n, 0 ≤ δ n)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) ×
          (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
        {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
            ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) •
                (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
            δ n}.indicator
          (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) •
                (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax sz E t1 t0 (gueGridK sz n0) n 2 p.1 ω +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
```

Translation table by script (`python3 -I stmtdiff.py`): the source statement (RBM2D `EntryGrid.lean`, HEAD 9e0f275) with the port map applied by regex (`d.L n`/`d.W n`/`d.size` to `sz.`, `Idx (..)` to `Idx d (..)`, `Coord` to `CoordF d`, `Xmat`, `ouP (d.L n) (d.W n)` to `ouP (UNModel.band sz) n`, `mixMat` to `mixMat sz n`, `X d` to `X sz` for `Pgue gueH PathΩ gueGridK gueLmax gueUnitVar EntryGrid_var Sizes.seqGvar`, `spectralZ/M` to `zt/mE`, `^ 2)⁻¹` to `^ d)⁻¹`), then a token diff against the RBM3D statement; only the residual differences are printed (none for the first four):
```
## EntryGrid_var: RBM2D :395 -> RBM3D :76
## EntryGrid_map_gueH: RBM2D :402 -> RBM3D :83
## map_gueH_eq_mixMat: RBM2D :437 -> RBM3D :118
## EntryGrid_pgue_preimage: RBM2D :480 -> RBM3D :162
## gueGrid_entry_bound: RBM2D :812 -> RBM3D :518
   - (none)   =>  + (hd : 3 ≤ d)
   - (none)   =>  + 𝔡
   - (h𝔠 : 0 < 𝔠)   =>  + (none)
   - Admissible   =>  + sz.Admissible
   - d)   =>  + 𝔡)
```

Compiled nonempty instances (`EntryGridInst`, file lines 617-724; data of the check and of `Grid.lean` GridCheck: `sz0`, d = 3, n = 0, L = 4, W = 32, N = 2097152; `t0 = 9/10`, `t1 = e^{-1/20} 9/10`, `K = 4`, k = 2):
```lean
-- :630-635  EntryGrid_var at k = 0 (`simp [EntryGrid_var]`); :645 EntryGrid_map_gueH, term only:
  EntryGrid_map_gueH sz0 _ _ _ 0 2
-- :648-656  map_gueH_eq_mixMat (n = 0, k = 2); the same for all n k at :659-667:
example :
    (Pgue sz0).map
        (gueH sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 2) =
      (ouP (UNModel.band sz0) 0).map
        (mixMat sz0 0 ((1 - ouZeta (1 / 20)) * (9 / 10))
          (gridTime (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
            (fun _ => 4) 0 2 - (1 - ouZeta (1 / 20)) * (9 / 10))) :=
  map_gueH_eq_mixMat sz0 _ _ _ 0 2 GridCheck.t1_pos t1_le
-- :693  EntryGrid_pgue_preimage (B = {M | forall i, |M_ii| <= 1}, measurable by :670-680), term only:
  EntryGrid_pgue_preimage sz0 _ _ _ 0 2 GridCheck.t1_pos t1_le measurableSet_diag_le
-- :698-716  statement of gueGrid_entry_bound_sz0 = the conclusion of the target at the data (head), term :717-722:
theorem gueGrid_entry_bound_sz0 :
    StochDomAt (Pgue sz0) sz0.size
  gueGrid_entry_bound sz0 le_rfl (𝔠 := 1 / 6) (𝔡 := 1 / 10) sz0_admissible (κ := 1) one_pos 1
    (E := fun _ => 0) (t1 := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (t0 := fun _ => 9 / 10)
    (fun n => by simp) (fun n => GridCheck.t1_pos) (fun n => t1_le) (fun n => by norm_num)
    (δ := fun n => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 1 / 4) (by norm_num)
    (Eventually.of_forall fun n => le_rfl)
$ grep -o "GUEPhaseGrid_[A-Za-z_]*" EntryGrid.lean | sort -u | tr "\n" " "   (the reused twins; the bare name is a docstring mention)
GUEPhaseGrid_ GUEPhaseGrid_map_combined_eq_mixed GUEPhaseGrid_map_slice_infinitePi GUEPhaseGrid_measurable_Xmat GUEPhaseGrid_Pgue_eq_mixed GUEPhaseGrid_real_smul_matrix GUEPhaseGrid_seqXmat_add GUEPhaseGrid_seqXmat_smul GUEPhaseGrid_seqXmat_sum ```

Name-clash grep (RBM3D/ outside Probe/ and outside the new file):
```
$ grep -rnE "^\s*(private )?(theorem|lemma|def|abbrev|structure|instance|example) .*(map_gueH_eq_mixMat|gueGrid_entry_bound|EntryGrid_|EntryGridInst)" RBM3D | grep -v "^RBM3D/Probe/\|GUEPhase/EntryGrid.lean" | wc -l
       0
$ grep -rln "map_gueH_eq_mixMat\|gueGrid_entry_bound\|EntryGrid_\|EntryGridInst" RBM3D | grep -v "^RBM3D/Probe/\|GUEPhase/EntryGrid.lean"   (comment hits only)
RBM3D/Universality/GUEPhase/EntryTailMain.lean
RBM3D/Universality/GUEPhase/BoundsA.lean
```

Allowed edit of `Grid.lean` (keyword `private` only) and file scope:
```
$ git diff --stat main...t/T2347
 RBM3D/Universality/GUEPhase/EntryGrid.lean | 726 +++++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/Grid.lean      |  16 +-
 2 files changed, 734 insertions(+), 8 deletions(-)
$ python3 -I grepdiff.py   (every -/+ line pair of the Grid.lean diff differs exactly by the prefix "private ")
removed lines: 8  added lines: 8  every pair is "private " deleted, rest identical: True
GUEPhaseGrid_seqXmat_add GUEPhaseGrid_seqXmat_smul GUEPhaseGrid_seqXmat_sum GUEPhaseGrid_real_smul_matrix GUEPhaseGrid_map_combined_eq_mixed GUEPhaseGrid_Pgue_eq_mixed GUEPhaseGrid_map_slice_infinitePi GUEPhaseGrid_measurable_Xmat 
```

Port source and downstream-fit check (scratch file, not committed):
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/EntryGrid.lean | wc -l ; wc -l <source>
9e0f275
       0
     902
$ lake env lean fit.lean   (BoundsACheck.highProbAt_HC sz E t1 t0 n0 tauU hT1 (gueGrid_entry_bound sz hd hadm ... (delta := gueDelta sz tauU) (c0 := tauU/4) ...) : HighProbAt ...)
exit=0
```

Narrative (facts from the outputs above and the files).
1. Port of RBM2D `EntryGrid.lean` (902 lines, HEAD 9e0f275, no diff since that commit) into the new file (726 lines; 175/453/610/726 at the section commits, below the 1100 stop line). The five targets are the source statements with the port map: the translation table shows no residual difference for `EntryGrid_var`, `EntryGrid_map_gueH`, `map_gueH_eq_mixMat`, `EntryGrid_pgue_preimage`, and exactly the T2347a items for `gueGrid_entry_bound`.
2. Reuse (DECISIONS §157): of source `:49-373` only the 8 `GUEPhaseGrid_` twins listed above are called; they are the 8 `private` deletions in `Grid.lean` (script-checked). The risk flagged in (a) (public statements mentioning the private `GUEPhaseGrid_mixedStepMeasure`) did not occur: the build passes with those 8 deletions only.
3. Re-derived locally, no public twin: `EntryGrid_llErrMat_eq` (`llErrMat` is `‖Gres M (zt E u) true i j - ...‖`; one rewrite `Gres_eq_green_zSig`), `EntryGrid_maxLoopPM_le` (twin `Proc_maxLoopPM_le_loopMax`, `Proc.lean:523`, is private), `EntryGrid_gres_zero_true` (twin `gres_zero_true`, `Green/Pins.lean:1181`, is private), measurability of `maxLoopPM` through `walk_measurable_loopFine`.
4. `d`-lines: `2 <= N` (source `:703-708`, `nlinarith` on `(W L)^2`) is `Nat.le_self_pow` with `1 <= d` (from `hd`); the union arithmetic (source `:719-746`) and the exponents `64 n0 + 128`, `D + 1 + 64 n0 + 128` fed to `gueEntryMix` are unchanged; `W^{-2}` is `W^{-d}` in `EntryGrid_badMat` and in the conclusion.
5. `gueGrid_entry_bound` has no unproved pin as a hypothesis (`gueEntryMix` is the merged proof): `hd : 3 <= d`, `𝔡` and `hadm : sz.Admissible 𝔠 𝔡` are the inputs of `gueEntryMix` (T2347a).
6. Instances: `sz0` (`d = 3`), `n = 0` (`L = 4`, `W = 32`, `N = 2097152`), `t0 = 9/10`, `t1 = e^{-1/20} 9/10`, `K = 4`, `k = 2`; for `gueGrid_entry_bound`: `E = 0`, `kappa = 1`, `n0 = 1`, `c0 = 1/4`, `delta_n = N^{-1/4}` (so `hdelta` holds with equality), `(𝔠, 𝔡) = (1/6, 1/10)` by the merged `sz0_admissible`. Every hypothesis is discharged; `K_n = (N+1)^96` occurs only in the conclusion. `EntryGrid_var` is a `def`: its instance is the `k = 0` evaluation, and it occurs in the `EntryGrid_map_gueH` instance.
7. Consumer fit: scratch `fit.lean` (exit 0): the conclusion of `gueGrid_entry_bound` at `delta = gueDelta sz tauU`, `c0 = tauU/4` is, without conversion, the hypothesis `h` of the merged `BoundsACheck.highProbAt_HC` (`GUEPhase/BoundsA.lean:678`).
8. No `(a')` section: nothing in (a) needed correction.

## (c) Verified names (script: env.contains over the imported environment of the new module; Lean/Mathlib names first, project names after)
```
Set.ofPred_forall ok | Nat.le_self_pow ok | Finset.measurable_sup' ok | Finset.sup'_le ok
Finset.sup'_apply ok | MeasureTheory.Measure.map_map ok | MeasureTheory.Measure.map_apply ok | MeasureTheory.measure_iUnion_fintype_le ok
Real.sq_sqrt ok | Real.rpow_add ok | Real.rpow_neg_one ok | ENNReal.ofReal_natCast ok
ENNReal.ofReal_mul ok | Set.indicator_of_mem ok | Set.indicator_of_notMem ok | Matrix.inv_def ok
Ring.inverse_eq_inv' ok | Continuous.matrix_det ok | Continuous.matrix_adjugate ok | Measurable.eval_matrix ok
Continuous.matrix_elem ok | inv_eq_of_mul_eq_one_right ok | Real.exp_le_one_iff ok | Nat.pow_le_pow_left ok
rpow_mul_rpow_neg_add ABSENT | RBM.rpow_mul_rpow_neg_add ok | RBM.Ind.Gres_eq_green_zSig ok | RBM.Ind.norm_gloop_le_loopMax ok
RBM.Ind.loopMax_nonneg ok | RBM.Gauss.walk_measurable_loopFine ok | RBM.Univ.gueEntryMix ok | RBM.Univ.mixSample_law ok
RBM.Univ.mixEntry_mixVar_coe ok | RBM.Gauss.SizesInst.sz0_admissible ok | RBM.Green.maxLoopPM_nonneg ok | RBM.Path.gridTime_last ok
```

## (d) Open issues and paper-delta candidates
- T2347a (statement): `gueGrid_entry_bound` differs from RBM2D's (`:812`) by `(hd : 3 <= d)` and `𝔡` added, `(h𝔠 : 0 < 𝔠)` dropped (it is `hadm.1`), `Admissible 𝔠 d` replaced by `sz.Admissible 𝔠 𝔡`, `W^{-2}` replaced by `W^{-d}`; all forced by the merged `gueEntryMix` / `GUEEntryMix` (`EntryTail.lean:94-111`, `EntryTailMain.lean:545`).
- T2347b (grid form not in the paper): `paper/tex/1_2_Intro_model_result.tex:569` (main worktree) says the proof of Thm B_Univ is "essentially identical" to [YY_25, Thm 2.6] and [DYYY25, Thm 2.6]; `grep -rn -i "\bgrid\b" paper/tex/*.tex` has 0 hits (run at Thu Oct  8 22:27:03 UTC 2026 by `date -u`). `map_gueH_eq_mixMat` and `gueGrid_entry_bound` are therefore Lean-side statements (the RBM1D/RBM2D grid scaffolding), conditional only on `sz.Admissible` and `3 <= d`.
- Process note (not a paper delta): `Grid.lean` now exports 8 `GUEPhaseGrid_` lemmas (list above), two of whose statements mention the private `GUEPhaseGrid_mixedStepMeasure`. `Proc_maxLoopPM_le_loopMax` and `gres_zero_true` stay private and are duplicated here (`EntryGrid_maxLoopPM_le`, `EntryGrid_gres_zero_true`); a cleanup ticket may unprivate them.
- For `docs/mathlib-api.md`: `rpow_mul_rpow_neg_add` is the project lemma `RBM.rpow_mul_rpow_neg_add` (`Defs/StochDom.lean:62`), absent from the Mathlib root namespace (script above).
- Open issues for the targets: none; every target has a compiled instance.
